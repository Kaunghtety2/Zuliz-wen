# 🌐 Web Downloader & Security Bot v28.0

Telegram bot — website download + security testing tools (50+ commands).  
Termux (Android) မှာ run လို့ရသည်။

---

## ✨ Features

| Category | Commands |
|---|---|
| 📥 Download | `/dl` — single/full/JS render |
| 🔍 Scanner | `/scan` — vuln/fuzz/smart/bypass |
| 🕵️ Recon | `/recon` — tech/headers/whois/cookies |
| 🔎 Discovery | `/discover` — api/secrets/subdomains |
| 💉 Attack | `/sqli` `/xss` `/bruteforce` `/2fabypass` |
| 🤖 Auto | `/autopwn` `/bulkscan` |
| 🔬 Analysis | `/techstack` `/sourcemap` `/gitexposed` |
| 🔔 Monitor | `/monitor` — page change alerts |
| 📱 App | APK/IPA/ZIP file drop → auto analyze |

> ⚠️ Authorized testing only. သင့်ပိုင် site တွေမှာသာ သုံးပါ။

---

## 📦 Setup — Termux

### Step 1 — Packages

```bash
pkg update && pkg upgrade -y
pkg install python nodejs git -y
pip install -r requirements.txt
```

### Step 2 — Clone

```bash
git clone https://github.com/YOUR_USERNAME/YOUR_REPO.git
cd YOUR_REPO
```

### Step 3 — Config

```bash
cp .env.example .env
nano .env
```

`.env` ထဲ ဖြည့်ရမည်:
```
BOT_TOKEN=1234567890:AABBccDDeeFF...   ← @BotFather က ရ
ADMIN_IDS=987654321                     ← @userinfobot က ရ
```

### Step 4 — Run

```bash
python bot.py
```

---

## 📸 Screenshot feature (optional)

JavaScript render နဲ့ screenshot လိုရင် Puppeteer ထည့်ရမည်:

```bash
npm install puppeteer
```

> Puppeteer မထည့်လည်း bot ကအလုပ်လုပ်သည် — JS render feature သာ disable ဖြစ်မည်။

---

## 🔄 Background run (Termux)

Bot ကို background မှာ ဆက် run နေစေချင်ရင်:

```bash
# nohup
nohup python bot.py > bot.log 2>&1 &

# သို့မဟုတ် tmux
tmux new -s bot
python bot.py
# Ctrl+B then D to detach
```

---

## 📁 File structure

```
.
├── bot.py              ← Main bot
├── .env                ← Your secrets (gitignore မှာပါ)
├── .env.example        ← Template
├── requirements.txt    ← Python packages
├── .gitignore
└── downloads/          ← Auto-created on first run
    ├── bot_db.json     ← User database
    ├── web_sources/    ← Downloaded sites
    └── resume_states/  ← Download resume data
```

---

## 🔒 Security notes

- `.env` ဖိုင်ကို GitHub တင်မရ (`.gitignore` မှာ ပါပြီ)
- BOT_TOKEN ကို source code ထဲ မရေးရ
- Bot ကို public repo တင်မည်ဆိုရင် `.env.example` ကိုသာ တင်

---

## 📋 Requirements

- Python 3.10+
- Android 8+ (Termux)
- RAM: 512MB minimum
- Node.js (optional, Puppeteer only)
