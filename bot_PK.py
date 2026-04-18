#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import sys
import re
import time
import json
import secrets
import logging
import threading
import hashlib
import signal
from datetime import date
from concurrent.futures import ThreadPoolExecutor
from typing import List, Dict, Optional, Tuple
from queue import Queue, Full

from dotenv import load_dotenv
import vk_api
from vk_api.bot_longpoll import VkBotLongPoll, VkBotEventType
from openai import OpenAI
from duckduckgo_search import DDGS

# ------------------------------
# Конфигурация
# ------------------------------
MAX_REPLY_CHARS = 4000
DAILY_LIMIT = 2
MAX_WORKERS = 3
MAX_QUEUE_SIZE = 10
PRICE_FILE = "prise.txt"
USAGE_FILE = "daily_usage.json"
CACHE_ANSWERS_FILE = "answers_cache.json"
CACHE_TTL_SECONDS = 30 * 24 * 60 * 60
CACHE_BUDGET_TOLERANCE = 3000
PREMIUM_BUDGET_THRESHOLD = 230000

REPOST_OWNER_ID = -237269654
REPOST_POST_ID = 123

COMMENT_COOLDOWN_SECONDS = 60
COMMENT_DAILY_LIMIT = 3

RATE_LIMIT = 10
RATE_WINDOW = 60
API_TIMEOUT = 25.0
DEEPSEEK_TIMEOUT = 60.0
API_RETRIES = 3
API_RETRY_DELAY = 1.0

# DeepSeek настройки
DEEPSEEK_DAILY_LIMIT = 3
DEEPSEEK_MAX_QUESTION_LEN = 100
DEEPSEEK_MAX_ANSWER_LEN = 4000
DEEPSEEK_RATE_LIMIT = 1
DEEPSEEK_RATE_WINDOW = 60
FREE_DS_ATTEMPTS = 3

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger("pc_bot")

# ------------------------------
# Глобальные хранилища
# ------------------------------
user_daily_usage = {}
user_exhaustion_notified = {}
user_comment_cooldown = {}
user_comment_daily = {}
web_cache = {}
READY_BUILDS = []

user_likes_cache = {}
user_repost_cache = {}
BONUS_CACHE_TTL = 600

user_deepseek_last_call = {}
user_deepseek_lock = threading.Lock()

api_requests = []
api_lock = threading.Lock()

user_daily_usage_lock = threading.Lock()
exhaustion_lock = threading.Lock()
web_cache_lock = threading.Lock()
likes_cache_lock = threading.Lock()
repost_cache_lock = threading.Lock()
comment_lock = threading.Lock()

ANSWERS_CACHE = {}
ANSWERS_CACHE_LOCK = threading.Lock()
CACHE_SAVE_INTERVAL = 300

send_queue = Queue(maxsize=100)
send_thread = None

ai_executor = None
openrouter_client = None
deepseek_client = None

# ------------------------------
# Вспомогательные функции
# ------------------------------
def safe_trim(text: str, max_len: int = 4000) -> str:
    if len(text) <= max_len:
        return text
    cut = text[:max_len - 1]
    if " " in cut:
        cut = cut.rsplit(" ", 1)[0]
    return cut + "…"

def safe_json_dump(data, filename):
    tmp = filename + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, filename)
    except Exception as e:
        logger.error(f"Ошибка записи {filename}: {e}")

def is_subscribed(vk, group_id, user_id):
    try:
        return bool(vk.groups.isMember(group_id=group_id, user_id=user_id))
    except:
        return False

# ------------------------------
# Проверка репоста
# ------------------------------
def has_user_reposted(vk, user_id, force_refresh=False) -> bool:
    today = date.today().isoformat()
    with repost_cache_lock:
        if not force_refresh and user_id in user_repost_cache:
            cached_date = user_repost_cache[user_id].get("date")
            if cached_date == today:
                return user_repost_cache[user_id].get("has_repost", False)
    try:
        wall = vk.wall.get(owner_id=user_id, count=100, filter='owner')
        for item in wall['items']:
            if 'copy_history' in item:
                for copy in item['copy_history']:
                    if copy.get('owner_id') == REPOST_OWNER_ID and copy.get('id') == REPOST_POST_ID:
                        with repost_cache_lock:
                            user_repost_cache[user_id] = {"date": today, "has_repost": True}
                        return True
        with repost_cache_lock:
            user_repost_cache[user_id] = {"date": today, "has_repost": False}
        return False
    except Exception as e:
        logger.error(f"Ошибка репоста: {e}")
        cached = user_repost_cache.get(user_id, {}).get("has_repost", False)
        return cached

# ------------------------------
# Лимиты для основных команд
# ------------------------------
def try_consume_usage(user_id: int) -> bool:
    today = date.today().isoformat()
    with user_daily_usage_lock:
        usage = user_daily_usage.get(user_id)
        if not usage or usage.get("date") != today:
            user_daily_usage[user_id] = {
                "date": today,
                "count": 1,
                "ds_count": 0,
                "repost_date": "",
                "free_ds_used": usage.get("free_ds_used", 0) if usage else 0,
                "first_ds_date": usage.get("first_ds_date", "") if usage else ""
            }
            safe_json_dump(user_daily_usage, USAGE_FILE)
            return True
        if "count" not in usage:
            usage["count"] = 0
        if usage["count"] < DAILY_LIMIT:
            usage["count"] += 1
            safe_json_dump(user_daily_usage, USAGE_FILE)
            return True
        return False

# ------------------------------
# Проверка и списание DeepSeek
# ------------------------------
def is_deepseek_available(vk, group_id, user_id, force_refresh=False) -> Tuple[bool, str]:
    if not is_subscribed(vk, group_id, user_id):
        return False, "❌ Вы не подписаны на сообщество. Подпишитесь, чтобы использовать эту функцию."

    today = date.today().isoformat()
    with user_daily_usage_lock:
        usage = user_daily_usage.setdefault(user_id, {})
        first_ds_date = usage.get("first_ds_date", "")
        free_used = usage.get("free_ds_used", 0)

        if not first_ds_date:
            usage["first_ds_date"] = today
            usage.setdefault("ds_count", 0)
            usage.setdefault("count", 0)
            usage.setdefault("repost_date", "")
            safe_json_dump(user_daily_usage, USAGE_FILE)
            first_ds_date = today

        if first_ds_date == today and free_used < FREE_DS_ATTEMPTS:
            return True, ""

        reposted = has_user_reposted(vk, user_id, force_refresh)
        if not reposted:
            return False, "❌ Нет активного репоста. Сделайте репост закреплённого поста, чтобы получить ещё 3 запроса на сегодня."

        if usage.get("date") != today:
            return True, ""
        ds_used = usage.get("ds_count", 0)
        if ds_used < DEEPSEEK_DAILY_LIMIT:
            return True, ""
        else:
            return False, f"⛔ Лимит {DEEPSEEK_DAILY_LIMIT} запросов на сегодня исчерпан. Завтра новый день, если будет активный репост."

    return False, "Ошибка проверки"

def try_consume_deepseek(vk, group_id, user_id, force_refresh=False) -> Tuple[bool, str]:
    available, msg = is_deepseek_available(vk, group_id, user_id, force_refresh)
    if not available:
        return False, msg

    with user_daily_usage_lock:
        usage = user_daily_usage.setdefault(user_id, {})
        today = date.today().isoformat()
        first_ds_date = usage.get("first_ds_date", "")
        free_used = usage.get("free_ds_used", 0)

        if first_ds_date == today and free_used < FREE_DS_ATTEMPTS:
            usage["free_ds_used"] = free_used + 1
            if "date" not in usage:
                usage["date"] = today
            safe_json_dump(user_daily_usage, USAGE_FILE)
            return True, ""

        if usage.get("date") != today:
            usage.update({
                "date": today,
                "count": usage.get("count", 0),
                "ds_count": 1,
                "repost_date": today,
                "free_ds_used": free_used,
                "first_ds_date": first_ds_date
            })
        else:
            usage["ds_count"] = usage.get("ds_count", 0) + 1
        safe_json_dump(user_daily_usage, USAGE_FILE)
        return True, ""

    return False, "Ошибка"

def load_daily_usage():
    global user_daily_usage
    if os.path.exists(USAGE_FILE):
        try:
            with open(USAGE_FILE, "r", encoding="utf-8") as f:
                user_daily_usage = json.load(f)
            for uid, data in user_daily_usage.items():
                if "ds_count" not in data:
                    data["ds_count"] = 0
                if "repost_date" not in data:
                    data["repost_date"] = ""
                if "free_ds_used" not in data:
                    data["free_ds_used"] = 0
                if "first_ds_date" not in data:
                    data["first_ds_date"] = ""
                if "count" not in data:
                    data["count"] = 0
        except Exception as e:
            logger.warning(f"Не удалось загрузить лимиты: {e}")

# ------------------------------
# Бонусы за лайки
# ------------------------------
def get_user_likes_count(vk, community_owner_id, user_id, force_refresh=False):
    now = time.time()
    with likes_cache_lock:
        if not force_refresh and user_id in user_likes_cache:
            ts, likes = user_likes_cache[user_id]
            if now - ts < BONUS_CACHE_TTL:
                return likes
    try:
        posts = vk.wall.get(owner_id=community_owner_id, count=50)
        post_ids = [p['id'] for p in posts['items']]
    except Exception as e:
        logger.error(f"Ошибка получения постов: {e}")
        return 0

    likes_count = 0
    chunks = [post_ids[i:i+25] for i in range(0, len(post_ids), 25)]
    for chunk in chunks:
        code_parts = []
        for pid in chunk:
            code_parts.append(
                f'API.likes.isLiked({{"type":"post","owner_id":{community_owner_id},'
                f'"item_id":{pid},"user_id":{user_id}}}).liked'
            )
        code = f'return [{",".join(code_parts)}];'
        try:
            results = vk.execute(code=code)
            likes_count += sum(1 for r in results if r)
        except Exception as e:
            logger.error(f"VK execute error: {e}")
    with likes_cache_lock:
        user_likes_cache[user_id] = (now, likes_count)
    return likes_count

def get_user_bonuses(vk, community_owner_id, user_id, force_refresh=False):
    likes_count = get_user_likes_count(vk, community_owner_id, user_id, force_refresh)
    likes_bonus = 1 if likes_count >= 10 else 0
    return 0, likes_bonus, False, likes_count

# ------------------------------
# Флаги уведомления
# ------------------------------
def is_exhaustion_notified(user_id: int) -> bool:
    today = date.today().isoformat()
    with exhaustion_lock:
        data = user_exhaustion_notified.get(user_id, {})
        if data.get("date") != today:
            user_exhaustion_notified[user_id] = {"date": today, "notified": False}
            return False
        return data.get("notified", False)

def set_exhaustion_notified(user_id: int, notified: bool):
    today = date.today().isoformat()
    with exhaustion_lock:
        user_exhaustion_notified[user_id] = {"date": today, "notified": notified}

# ------------------------------
# Кэш ответов
# ------------------------------
def load_answers_cache_memory():
    global ANSWERS_CACHE
    if os.path.exists(CACHE_ANSWERS_FILE):
        try:
            with open(CACHE_ANSWERS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            now = time.time()
            filtered = {}
            for key, val in data.items():
                if isinstance(val, dict) and now - val.get("timestamp", 0) < CACHE_TTL_SECONDS:
                    filtered[key] = {"answer": val["answer"], "timestamp": val["timestamp"]}
            ANSWERS_CACHE = filtered
            logger.info(f"Загружено {len(ANSWERS_CACHE)} ответов")
        except Exception as e:
            logger.warning(f"Ошибка загрузки кэша: {e}")

def save_answers_cache_periodically():
    while True:
        time.sleep(CACHE_SAVE_INTERVAL)
        with ANSWERS_CACHE_LOCK:
            to_save = ANSWERS_CACHE.copy()
        safe_json_dump(to_save, CACHE_ANSWERS_FILE)

def find_cached_answer(budget: int, used_only: bool, query_hash: str = "") -> Optional[str]:
    key_prefix = "used" if used_only else "new"
    if query_hash:
        exact_key = f"{key_prefix}_{budget}_{query_hash}"
        with ANSWERS_CACHE_LOCK:
            if exact_key in ANSWERS_CACHE:
                return ANSWERS_CACHE[exact_key]["answer"]
    return None

def save_answer_to_cache(budget: int, used_only: bool, answer: str, query_hash: str = ""):
    global ANSWERS_CACHE
    if used_only:
        return
    key = f"{'used' if used_only else 'new'}_{budget}"
    if query_hash:
        key += f"_{query_hash}"
    with ANSWERS_CACHE_LOCK:
        ANSWERS_CACHE[key] = {"answer": answer, "timestamp": time.time()}
        if len(ANSWERS_CACHE) > 200:
            items = list(ANSWERS_CACHE.items())
            items.sort(key=lambda x: x[1]["timestamp"])
            ANSWERS_CACHE = dict(items[-200:])

# ------------------------------
# Поиск в интернете
# ------------------------------
def cleanup_web_cache():
    now = time.time()
    with web_cache_lock:
        expired = [k for k, v in web_cache.items() if now - v["ts"] > 7200]
        for k in expired:
            del web_cache[k]

def search_web(query: str, max_results=3, max_len=1200) -> str:
    cleanup_web_cache()
    cache_key = f"ddg_{query}"
    with web_cache_lock:
        if cache_key in web_cache and time.time() - web_cache[cache_key]["ts"] < 3600:
            return web_cache[cache_key]["data"]
    try:
        with DDGS() as ddgs:
            results = []
            for r in ddgs.text(query, max_results=max_results):
                body = r.get("body", "")
                if body and len(body) > 80:
                    results.append(body[:500])
            data = "\n\n".join(results)[:max_len] if results else ""
    except Exception as e:
        logger.error(f"Ошибка поиска: {e}")
        data = ""
    with web_cache_lock:
        web_cache[cache_key] = {"ts": time.time(), "data": data}
    return data

# ------------------------------
# Rate limit и вызовы
# ------------------------------
def can_call_api() -> bool:
    now = time.time()
    with api_lock:
        while api_requests and api_requests[0] < now - RATE_WINDOW:
            api_requests.pop(0)
        if len(api_requests) < RATE_LIMIT:
            api_requests.append(now)
            return True
        return False

def safe_gemini_call(messages, temp=0.3, max_tokens=1500):
    if openrouter_client is None:
        logger.error("OpenRouter клиент не инициализирован")
        return "🔄 Сервис временно перегружен, попробуй чуть позже. Приношу извинения за неудобства!"
    if not can_call_api():
        logger.warning("Достигнут лимит запросов")
        return "⚠️ Слишком много запросов. Подождите немного, пожалуйста."
    for attempt in range(API_RETRIES):
        try:
            kwargs = {
                "model": "google/gemini-3.1-flash-lite-preview",
                "messages": messages,
                "temperature": temp,
                "max_tokens": max_tokens,
                "timeout": API_TIMEOUT
            }
            resp = openrouter_client.chat.completions.create(**kwargs)
            answer = resp.choices[0].message.content.strip()
            logger.info(f"Gemini успешно ответил, длина ответа: {len(answer)}")
            return answer
        except Exception as e:
            logger.warning(f"Gemini попытка {attempt+1} ошибка: {e}")
            if attempt == API_RETRIES - 1:
                return None
            time.sleep(API_RETRY_DELAY * (2 ** attempt))
    return None

def safe_deepseek_call(question: str, max_tokens: int = 2500) -> Optional[str]:
    if deepseek_client is None:
        logger.error("DeepSeek клиент не инициализирован")
        return "🔄 Сервис временно перегружен, попробуй чуть позже. Приношу извинения за неудобства!"
    if not can_call_api():
        return "⚠️ Слишком много запросов. Подождите немного, пожалуйста."
    for attempt in range(API_RETRIES):
        try:
            resp = deepseek_client.chat.completions.create(
                model="deepseek-chat",
                messages=[{"role": "user", "content": question}],
                temperature=0.7,
                max_tokens=max_tokens,
                timeout=DEEPSEEK_TIMEOUT
            )
            answer = resp.choices[0].message.content.strip()
            logger.info(f"DeepSeek успешно ответил, длина: {len(answer)}")
            return answer
        except Exception as e:
            logger.warning(f"DeepSeek попытка {attempt+1} ошибка: {e}")
            if attempt == API_RETRIES - 1:
                return None
            time.sleep(API_RETRY_DELAY * (2 ** attempt))
    return None

# ------------------------------
# Парсер готовых сборок
# ------------------------------
def parse_price_file() -> List[Dict]:
    if not os.path.exists(PRICE_FILE):
        return []
    with open(PRICE_FILE, "r", encoding="utf-8") as f:
        content = f.read()
    blocks = re.split(r'\n\s*(?=Сборка из)', content)
    builds = []
    for block in blocks:
        lines = [l.strip() for l in block.split('\n') if l.strip()]
        if len(lines) < 3 or not lines[0].startswith("Сборка из"):
            continue
        components = None
        for line in lines[1:]:
            if any(kw in line for kw in ('Ryzen','Intel','GeForce','RTX','ГБ','SSD')):
                components = line
                break
        if not components:
            continue
        price = None
        for line in lines:
            if '₽' in line and '/мес.' not in line:
                m = re.search(r'(\d{1,3}(?:[\s]?\d{3})*)\s*₽', line)
                if m:
                    price = int(m.group(1).replace(' ', ''))
                    break
        if price:
            builds.append({"components": components, "price": price})
    logger.info("Загружено %d сборок", len(builds))
    return builds

def get_closest_build_with_tolerance(budget: int, tolerance=0.1) -> Optional[Dict]:
    """Ищет сборку, цена которой не превышает budget * (1 + tolerance)."""
    if not READY_BUILDS:
        return None
    max_price = int(budget * (1 + tolerance))
    eligible = [b for b in READY_BUILDS if b["price"] <= max_price]
    if eligible:
        eligible.sort(key=lambda x: abs(x["price"] - budget))
        return eligible[0]
    return None

def extract_budget_from_text(text: str) -> Optional[int]:
    text_lower = text.lower()
    text_no_spaces = re.sub(r'(\d)\s+(\d)', r'\1\2', text_lower)
    patterns = [
        (r'за\s*(\d{4,7})', 1),
        (r'за\s*(\d+)\s*[кk]', 1000),
        (r'за\s*(\d+)\s*тысяч', 1000),
        (r'бюджет\s*(\d{4,7})', 1),
        (r'(\d+)\s*[кk]\s*(?:руб|р)?', 1000),
        (r'(\d+)\s*тысяч', 1000),
        (r'(\d{5,7})\s*(?:руб|р)?', 1),
    ]
    for pat, mult in patterns:
        m = re.search(pat, text_no_spaces)
        if m:
            val = int(m.group(1))
            if re.search(r'\b(3060|3070|4060|5060|rx\s?\d{4})\b', text_lower) and val < 10000:
                continue
            budget = val * mult
            if 5000 <= budget <= 10_000_000:
                return budget
    nums = re.findall(r'\b\d{5,6}\b', text_no_spaces)
    return int(nums[0]) if nums else None

def wants_used_build(text: str) -> bool:
    return any(k in text.lower() for k in ['б/у', 'бу', 'used', 'вторичка'])

def normalize_query(text: str) -> str:
    text = re.sub(r'(\d+)\s*к\b', lambda m: str(int(m.group(1))*1000), text.lower())
    text = re.sub(r'(\d+)\s*тыс', lambda m: str(int(m.group(1))*1000), text)
    return re.sub(r'\d+', 'X', text).strip()

# ------------------------------
# AI функции для сборок
# ------------------------------
def get_used_budget_category(budget: int) -> str:
    if budget <= 25000:
        return "очень бюджетная (до 25000)"
    elif budget <= 35000:
        return "начального уровня (25000-35000)"
    elif budget <= 45000:
        return "среднего уровня (35000-45000)"
    elif budget <= 55000:
        return "хорошего уровня (45000-55000)"
    else:
        return "почти топ (55000-60000)"

def ask_gemini_used(budget: int) -> str:
    category = get_used_budget_category(budget)
    prompt = f"Подбери б/у сборку для игр за {budget}₽ (категория: {category}). Укажи CPU, материнскую плату, GPU, RAM, SSD, БП. Дай прогноз FPS в 5 играх (1080p). Кратко, без советов. Не пиши 'не существует'."
    resp = safe_gemini_call([
        {"role": "system", "content": "Кратко, только суть. Не исправляй названия, не спорь. Подбирай разные компоненты в зависимости от бюджета."},
        {"role": "user", "content": prompt}
    ], temp=0.5, max_tokens=700)
    return resp if resp else "Ошибка"

def ask_gemini_build(build: Dict, budget: int) -> str:
    prompt = f"""
Сборка ПК за {budget}₽: {build['components']}.

ВАЖНО:
- НЕ ИСПРАВЛЯЙ названия комплектующих.
- НЕ ПИШИ что чего-то "не существует".
- Если есть сомнения — просто оцени как есть.
- Отвечай строго по задаче.

Напиши:
1. Компоненты (кратко)
2. FPS в 5 играх (1080p, высокие)
3. Итог

Коротко, без лишнего.
"""
    resp = safe_gemini_call([
        {"role": "system", "content": "Ты не споришь с пользователем. Не исправляешь названия. Не говоришь 'не существует'. Выполняешь задачу."},
        {"role": "user", "content": prompt}
    ], temp=0.4, max_tokens=800)
    return resp if resp else "Ошибка при анализе сборки."

def ask_gemini_analyze_custom(components_text: str, budget: int) -> str:
    prompt = f"""
Пользователь хочет собрать ПК за {budget}₽ со следующими компонентами:
{components_text}

ВАЖНО:
- НЕ ИСПРАВЛЯЙ названия комплектующих.
- НЕ ПИШИ, что чего-то "не существует". Даже если модель тебе незнакома, просто оцени её как игровой компонент.
- Если сомневаешься в названии, всё равно дай прогноз, основываясь на логике.
- ОТВЕЧАЙ ТОЛЬКО ПО ЗАДАЧЕ: компоненты, FPS, итог.
- НЕ ДОБАВЛЯЙ лишних комментариев типа "устарела", "слабое звено" — только суть.

Коротко, без лишнего.

Напиши:
1. Компоненты (кратко, как есть)
2. Прогноз FPS в 5 играх (1080p, высокие/ультра настройки)
3. Итог (достаточно ли этой сборки для комфортной игры)
"""
    resp = safe_gemini_call([
        {"role": "system", "content": "Ты не споришь с пользователем. Не исправляешь названия. Не говоришь 'не существует'. Выполняешь задачу."},
        {"role": "user", "content": prompt}
    ], temp=0.4, max_tokens=800)
    return resp if resp else "Не удалось проанализировать сборку."

def ask_gemini_new_build(budget: int) -> str:
    prompt = f"""
Подбери новую игровую сборку ПК за {budget}₽. Обязательно включи дискретную видеокарту, 16 ГБ ОЗУ (или больше), SSD. Укажи CPU, GPU, материнскую плату, RAM, SSD, БП. Дай прогноз FPS в 5 играх (1080p, высокие настройки). Кратко, без советов.
"""
    resp = safe_gemini_call([
        {"role": "system", "content": "Ты эксперт по сборке ПК. Отвечай кратко, только компоненты и FPS. Не пиши 'не существует'."},
        {"role": "user", "content": prompt}
    ], temp=0.4, max_tokens=800)
    return resp if resp else "Ошибка подбора сборки"

def ask_gemini_premium(budget: int) -> str:
    prompt = f"Подбери топовую сборку за {budget}₽. Компоненты и прогноз FPS в 5 играх (1440p, ультра). Кратко."
    resp = safe_gemini_call([
        {"role": "system", "content": "Кратко, без лишнего."},
        {"role": "user", "content": prompt}
    ], temp=0.4, max_tokens=600)
    return resp if resp else "Ошибка"

# ------------------------------
# Команда !сравни (отключена)
# ------------------------------
def handle_compare_command(vk, uid, msg, admin) -> bool:
    send_msg(vk, uid, "🔧 Команда !сравни временно недоступна. Но ты всегда можешь задать вопрос через @, я постараюсь помочь!")
    return False

# ------------------------------
# Команда !собери пк
# ------------------------------
def handle_build_command(vk, uid, msg, admin) -> bool:
    query = re.sub(r'^!собери пк\s*', '', msg, flags=re.IGNORECASE).strip()
    if not query:
        send_msg(vk, uid, "🎯 Укажи бюджет, например: `!собери пк за 50000` или `!собери пк 50к`")
        return False
    budget = extract_budget_from_text(query)
    if not budget:
        send_msg(vk, uid, "🤔 Не могу определить сумму. Попробуй написать, например: `!собери пк за 50000` или `!собери пк 50к`")
        return False
    used_only = wants_used_build(query)
    qhash = hashlib.md5(normalize_query(query).encode()).hexdigest()[:8]
    cached = find_cached_answer(budget, used_only, qhash)
    if cached:
        send_msg(vk, uid, cached)
        return True
    send_typing(vk, uid)

    def task():
        logger.info(f"Начало обработки задачи для бюджета {budget}")
        try:
            if used_only:
                ans = ask_gemini_used(budget)
            elif budget >= PREMIUM_BUDGET_THRESHOLD:
                ans = ask_gemini_premium(budget)
            else:
                if budget <= 60000:
                    ans = ask_gemini_used(budget)
                else:
                    build = get_closest_build_with_tolerance(budget, tolerance=0.1)
                    if build:
                        if build["price"] > budget:
                            warning = f"⚠️ Бюджет {budget}₽, но найдена сборка за {build['price']}₽.\n\n"
                            ans = warning + ask_gemini_build(build, budget)
                        else:
                            ans = ask_gemini_build(build, budget)
                    else:
                        ans = ask_gemini_new_build(budget)
            if ans and not ans.startswith("⚠️"):
                save_answer_to_cache(budget, used_only, ans, qhash)
            # Добавляем дружелюбную фразу в конец ответа
            if ans and not ans.startswith("⚠️") and not ans.startswith("Ошибка"):
                ans += "\n\n✨ Если нужна помощь или хочешь другую сборку, просто напиши снова!"
            send_msg(vk, uid, ans)
        except Exception as e:
            logger.error(f"Ошибка в task: {e}", exc_info=True)
            send_msg(vk, uid, "🔄 Что-то пошло не так. Попробуй ещё раз или напиши позже. Приношу извинения!")
    ai_executor.submit(task)
    return True

# ------------------------------
# Отправка сообщений
# ------------------------------
def vk_send_with_retry(vk, user_id, text, retries=2):
    for i in range(retries):
        try:
            vk.messages.send(user_id=user_id, message=safe_trim(text, MAX_REPLY_CHARS), random_id=secrets.randbelow(2**31))
            return
        except Exception as e:
            if i == retries-1:
                logger.error(f"Не удалось отправить {user_id}: {e}")
            else:
                time.sleep(1)

def send_worker(vk_session):
    vk = vk_session.get_api()
    while True:
        try:
            uid, text = send_queue.get(timeout=1)
            logger.info(f"send_worker: отправка сообщения {uid}, длина {len(text)}")
            vk_send_with_retry(vk, uid, text)
            send_queue.task_done()
        except Exception as e:
            if send_queue.empty():
                continue
            logger.error(f"Ошибка в send_worker: {e}")

def send_msg(vk, user_id, text):
    try:
        send_queue.put_nowait((user_id, text))
    except Full:
        logger.error(f"Очередь переполнена, сообщение для {user_id} потеряно")
        # fallback: отправить напрямую
        vk_send_with_retry(vk, user_id, text)

def send_typing(vk, user_id):
    try:
        vk.messages.setActivity(user_id=user_id, type="typing")
    except:
        pass

# ------------------------------
# Антиспам комментариев
# ------------------------------
def check_comment_spam(user_id: int) -> Tuple[bool, str]:
    now = time.time()
    with comment_lock:
        last = user_comment_cooldown.get(user_id, 0)
        if now - last < COMMENT_COOLDOWN_SECONDS:
            return False, f"Подожди {int(COMMENT_COOLDOWN_SECONDS - (now - last))} сек, я ещё не остыл 😅"
        today = date.today().isoformat()
        daily = user_comment_daily.get(user_id, {})
        cnt = daily.get(today, 0)
        if cnt >= COMMENT_DAILY_LIMIT:
            return False, f"Лимит на сегодня {COMMENT_DAILY_LIMIT}, завтра я снова готов помогать!"
        return True, ""

def update_comment_spam(user_id: int):
    now = time.time()
    with comment_lock:
        user_comment_cooldown[user_id] = now
        today = date.today().isoformat()
        if user_id not in user_comment_daily:
            user_comment_daily[user_id] = {}
        user_comment_daily[user_id][today] = user_comment_daily[user_id].get(today, 0) + 1

def reply_comment(vk, owner_id, post_id, comment_id, text):
    try:
        vk.wall.createComment(owner_id=owner_id, post_id=post_id, from_group=1, message=safe_trim(text, 3900), reply_to_comment=comment_id)
    except Exception as e:
        logger.error(f"Ошибка комментария: {e}")

# ------------------------------
# BoundedExecutor
# ------------------------------
class BoundedExecutor:
    def __init__(self, max_workers=3, max_queue=10):
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        self.semaphore = threading.Semaphore(max_workers + max_queue)
    def submit(self, fn, *args, **kwargs):
        if not self.semaphore.acquire(timeout=0.2):
            raise RuntimeError("executor queue full")
        fut = self.executor.submit(fn, *args, **kwargs)
        fut.add_done_callback(lambda _: self.semaphore.release())
        return fut

# ------------------------------
# Очистка старых записей
# ------------------------------
def cleanup_old_records():
    today = date.today().isoformat()
    with comment_lock:
        for uid in list(user_comment_daily.keys()):
            if today not in user_comment_daily[uid]:
                del user_comment_daily[uid]
    with exhaustion_lock:
        for uid in list(user_exhaustion_notified.keys()):
            if user_exhaustion_notified[uid].get("date") != today:
                del user_exhaustion_notified[uid]
    with likes_cache_lock:
        for uid in list(user_likes_cache.keys()):
            ts, _ = user_likes_cache[uid]
            if time.time() - ts > BONUS_CACHE_TTL * 2:
                del user_likes_cache[uid]
    with repost_cache_lock:
        for uid in list(user_repost_cache.keys()):
            if user_repost_cache[uid].get("date") != today:
                del user_repost_cache[uid]

def cleanup_loop():
    while True:
        time.sleep(3600)
        cleanup_old_records()

# ------------------------------
# Обработка сообщений
# ------------------------------
def handle_private(vk, community_owner_id, group_id, admin_ids, event):
    msg = event.message.text or ""
    uid = event.message.from_id
    if hasattr(event, 'message') and hasattr(event.message, 'peer_id'):
        if event.message.peer_id != uid:
            return
    if not msg or uid <= 0:
        return
    logger.info(f"ЛС {uid}: {msg[:80]}")
    norm = ' '.join(msg.lower().strip().split())
    admin = uid in admin_ids

    # ----- Запросы через @ -----
    if msg.startswith('@'):
        if admin:
            question = msg[1:].strip()
            if not question:
                send_msg(vk, uid, "❓ Напиши вопрос после @, например: `@ как выбрать процессор?`")
                return
            if len(question) > DEEPSEEK_MAX_QUESTION_LEN:
                send_msg(vk, uid, f"❌ Слишком длинный вопрос. Максимум {DEEPSEEK_MAX_QUESTION_LEN} символов. Попробуй покороче!")
                return
            send_typing(vk, uid)
            def admin_task():
                answer = safe_deepseek_call(question, max_tokens=2500)
                if not answer:
                    answer = "😔 Не удалось получить ответ. Попробуй ещё раз или позже. Спасибо за понимание!"
                if len(answer) > DEEPSEEK_MAX_ANSWER_LEN:
                    answer = safe_trim(answer, DEEPSEEK_MAX_ANSWER_LEN)
                send_msg(vk, uid, answer)
            ai_executor.submit(admin_task)
            return

        question = msg[1:].strip()
        if not question:
            send_msg(vk, uid, "❓ Напиши вопрос после @, например: `@ как выбрать видеокарту?`")
            return
        if len(question) > DEEPSEEK_MAX_QUESTION_LEN:
            send_msg(vk, uid, f"❌ Слишком длинный вопрос. Максимум {DEEPSEEK_MAX_QUESTION_LEN} символов. Сократи немного!")
            return
        now = time.time()
        with user_deepseek_lock:
            last = user_deepseek_last_call.get(uid, 0)
            if now - last < DEEPSEEK_RATE_WINDOW:
                wait = int(DEEPSEEK_RATE_WINDOW - (now - last))
                send_msg(vk, uid, f"⏳ Подожди {wait} сек перед следующим вопросом. Я не робот, мне нужно немного времени 😊")
                return
            user_deepseek_last_call[uid] = now
        success, err_msg = try_consume_deepseek(vk, group_id, uid, force_refresh=False)
        if not success:
            send_msg(vk, uid, err_msg)
            return
        send_typing(vk, uid)
        def deepseek_task():
            answer = safe_deepseek_call(question, max_tokens=2500)
            if not answer:
                answer = "😔 Не удалось получить ответ. Попробуй ещё раз или позже. Спасибо за понимание!"
            if len(answer) > DEEPSEEK_MAX_ANSWER_LEN:
                answer = safe_trim(answer, DEEPSEEK_MAX_ANSWER_LEN)
            send_msg(vk, uid, answer)
        ai_executor.submit(deepseek_task)
        return

    # Обычные команды
    if norm in ["/start", "/help", "помощь"]:
        help_text = (
            "👋 Привет! Я бот-помощник по сборке ПК.\n\n"
            "📌 **Команды:**\n"
            "• `!собери пк за 50000` – подберу сборку с прогнозом FPS\n"
            "• `@ текст вопроса` – задай любой вопрос (например, @ как выбрать блок питания?)\n\n"
            "🎁 **Бонусы:**\n"
            "• Репост закреплённого поста → +2 запроса к команде `!собери пк`\n"
            "• 10 лайков под постами → +1 запрос\n\n"
            "🔓 **Вопросы через @:**\n"
            "• Первые 3 вопроса бесплатно (без репоста)\n"
            "• Далее нужен репост – каждый день 3 вопроса\n"
            "• 1 вопрос в минуту\n\n"
            "✨ Лимиты обновляются каждый день при активном репосте.\n"
            "Удачи в сборке! 🚀"
        )
        send_msg(vk, uid, help_text)
        return
    if norm == "/ping":
        send_msg(vk, uid, "🏓 pong! Я жив и готов помочь!")
        return

    if admin:
        if norm.startswith("!собери пк"):
            handle_build_command(vk, uid, msg, admin)
        elif norm.startswith("!сравни"):
            handle_compare_command(vk, uid, msg, admin)
        else:
            send_msg(vk, uid, "❓ Неизвестная команда. Попробуй:\n• `!собери пк за 50000`\n• `@ вопрос`")
        return

    if not is_subscribed(vk, group_id, uid):
        send_msg(vk, uid, f"📢 Чтобы я мог помогать, подпишись на сообщество: https://vk.com/club{group_id}\nСпасибо! 😊")
        return

    if not try_consume_usage(uid):
        if not is_exhaustion_notified(uid):
            set_exhaustion_notified(uid, True)
            send_msg(vk, uid, "😔 Лимит 2 запроса на сегодня исчерпан. Но ты можешь получить ещё:\n• Сделай репост закреплённого поста → +2 запроса\n• Поставь 10 лайков под постами → +1 запрос\nПосле действий повтори команду – я начислю бонусы автоматически!")
            return
        else:
            repost_bonus, likes_bonus, repost_done, likes_count = get_user_bonuses(vk, community_owner_id, uid, force_refresh=True)
            total = DAILY_LIMIT + repost_bonus + likes_bonus
            if try_consume_usage(uid):
                set_exhaustion_notified(uid, False)
            else:
                msg_text = f"⛔ Лимит {total} запросов. Репост: {'✅' if repost_done else '❌'}, лайки: {likes_count}/10"
                send_msg(vk, uid, msg_text)
                return

    if norm.startswith("!собери пк"):
        handle_build_command(vk, uid, msg, admin)
    else:
        send_msg(vk, uid, "❓ Неизвестная команда. Я понимаю только:\n• `!собери пк за 50000`\n• `@ текст вопроса`\nПопробуй ещё раз!")

def handle_comment(vk, community_owner_id, event):
    text = (event.object.get("text") or "").strip()
    if text.lower() != "!пк":
        return
    from_id = event.object.get("from_id")
    if not from_id:
        return
    allowed, msg = check_comment_spam(from_id)
    if not allowed:
        reply_comment(vk, event.object.get("owner_id"), event.object.get("post_id"), event.object.get("id"), f"@id{from_id}, {msg}")
        return
    update_comment_spam(from_id)
    reply_text = f"@id{from_id}, привет! 👋\n\n🔧 Для подбора ПК напиши мне в личные сообщения:\n👉 https://vk.com/im?sel={community_owner_id}\nКоманда: `!собери пк за 50000`\n\nБуду рад помочь! 🚀"
    reply_comment(vk, event.object.get("owner_id"), event.object.get("post_id"), event.object.get("id"), reply_text)

# ------------------------------
# Graceful shutdown
# ------------------------------
def shutdown_handler(signum, frame):
    logger.info("Получен сигнал завершения, сохраняем кэши...")
    with ANSWERS_CACHE_LOCK:
        to_save = ANSWERS_CACHE.copy()
    safe_json_dump(to_save, CACHE_ANSWERS_FILE)
    safe_json_dump(user_daily_usage, USAGE_FILE)
    logger.info("Кэши сохранены. Завершаем работу.")
    sys.exit(0)

# ------------------------------
# Main
# ------------------------------
def main():
    global openrouter_client, deepseek_client, ai_executor, send_thread

    load_dotenv()
    vk_token = os.getenv("VK_ACCESS_TOKEN")
    group_id_str = os.getenv("VK_GROUP_ID")
    openrouter_key = os.getenv("OPENROUTER_API_KEY")
    deepseek_api_key = os.getenv("DEEPSEEK_API_KEY")
    admin_ids_str = os.getenv("ADMIN_IDS", "")
    if not vk_token or not group_id_str or not openrouter_key:
        logger.error("Отсутствуют переменные в .env (VK_ACCESS_TOKEN, VK_GROUP_ID, OPENROUTER_API_KEY)")
        sys.exit(1)
    if not deepseek_api_key:
        logger.warning("DEEPSEEK_API_KEY не задан, некоторые функции могут быть недоступны")
    group_id = int(group_id_str)
    community_owner_id = -abs(group_id)
    admin_ids = [int(x.strip()) for x in admin_ids_str.split(",") if x.strip()]

    openrouter_client = OpenAI(api_key=openrouter_key, base_url="https://openrouter.ai/api/v1")
    if deepseek_api_key:
        deepseek_client = OpenAI(api_key=deepseek_api_key, base_url="https://api.deepseek.com")
    else:
        deepseek_client = None

    load_daily_usage()
    global READY_BUILDS
    READY_BUILDS = parse_price_file()

    load_answers_cache_memory()
    threading.Thread(target=save_answers_cache_periodically, daemon=True).start()
    threading.Thread(target=cleanup_loop, daemon=True).start()

    ai_executor = BoundedExecutor(max_workers=MAX_WORKERS, max_queue=MAX_QUEUE_SIZE)

    vk_session = vk_api.VkApi(token=vk_token)
    vk = vk_session.get_api()

    send_thread = threading.Thread(target=send_worker, args=(vk_session,), daemon=True)
    send_thread.start()

    signal.signal(signal.SIGINT, shutdown_handler)
    signal.signal(signal.SIGTERM, shutdown_handler)

    longpoll = VkBotLongPoll(vk_session, group_id)
    logger.info("Бот запущен. Группа: %s", group_id)
    logger.info("Загружено готовых сборок: %d", len(READY_BUILDS))
    if deepseek_client:
        logger.info("Дополнительные сервисы подключены.")
    else:
        logger.warning("Некоторые функции отключены.")

    for event in longpoll.listen():
        try:
            if event.type == VkBotEventType.MESSAGE_NEW:
                handle_private(vk, community_owner_id, group_id, admin_ids, event)
            elif event.type == VkBotEventType.WALL_REPLY_NEW:
                handle_comment(vk, community_owner_id, event)
        except Exception as e:
            logger.exception(f"Ошибка обработки события: {e}")

if __name__ == "__main__":
    main()