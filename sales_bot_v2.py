"""
Бот контроля продавцов v2 (колл-центр, БАД).
Показатели (продавец шлёт текстом):
  Усилия, Дозвон, Длительность (ч:мин), Лид, Заказы, Сумма.
Бот считает: Конверсия (заказы/лиды), План (лиды*LEAD_PRICE),
  Выполнение плана (сумма/план), Ср. время на заказ (длительность/заказы).
/report -> ссылка на GitHub Pages (с фильтром по датам: Сегодня/Неделя/Месяц/Всё).
Контроль неактивности: WARN_DAYS предупреждение, KICK_DAYS -> подтверждение админом.

Ключи в переменных окружения (см. инструкцию внизу).
"""

import base64, json, logging, os, re, ssl, urllib.request, urllib.error
from datetime import datetime, timezone, timedelta
from pathlib import Path
import anthropic
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (ApplicationBuilder, MessageHandler, CommandHandler,
                          CallbackQueryHandler, filters, ContextTypes)

import fcntl, sys
_lock_fp = open("/tmp/salesbot.lock", "w")
try:
    fcntl.flock(_lock_fp, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    sys.stderr.write("Бот уже запущен. Выходим.\n")
    sys.exit(1)

# ── Конфиг ────────────────────────────────────────────────────────────────
TELEGRAM_TOKEN    = os.environ.get("TELEGRAM_TOKEN", "")
ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")
GITHUB_TOKEN      = os.environ.get("REPORT_GITHUB_TOKEN", "")
GITHUB_USER = os.environ.get("REPORT_GITHUB_USER", "rustamov0277-cmd")
GITHUB_REPO = os.environ.get("REPORT_GITHUB_REPO", "sales-report")
GITHUB_FILE = "index.html"
PAGES_URL   = "https://" + GITHUB_USER + ".github.io/" + GITHUB_REPO + "/"

ADMIN_IDS = {7732123506, 8003438139}
REPORT_HOUR = 21
INACTIVITY_CHECK_HOUR = 12
WARN_DAYS = 3
KICK_DAYS = 4
LEAD_PRICE = 400000
TZ = timezone(timedelta(hours=5))

BASE_DIR   = Path.home() / "sales_bot"
CACHE_FILE = str(BASE_DIR / "cache.json")
USERS_FILE = str(BASE_DIR / "users.json")
CHATS_FILE = str(BASE_DIR / "chats.json")
GOALS_FILE = str(BASE_DIR / "goals.json")
ABSENT_FILE= str(BASE_DIR / "absent.json")
BASE_DIR.mkdir(parents=True, exist_ok=True)

pending_kicks = {}
_kick_counter = 0

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
log = logging.getLogger(__name__)
client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)

# поля одного дня
def _empty_day():
    return {"usilia": None, "dozvon": None, "duration_min": None,
            "leads": None, "orders": None, "amount": None}

# ── JSON хелперы ──────────────────────────────────────────────────────────
def _load(p, d):
    if os.path.exists(p):
        with open(p, encoding="utf-8") as f: return json.load(f)
    return d
def _save(p, d):
    with open(p, "w", encoding="utf-8") as f: json.dump(d, f, ensure_ascii=False, indent=2)
def load_cache():  return _load(CACHE_FILE, {})
def save_cache(d): _save(CACHE_FILE, d)
def load_users():  return _load(USERS_FILE, {})
def save_users(d): _save(USERS_FILE, d)
def load_goals():  return _load(GOALS_FILE, {})
def save_goals(d): _save(GOALS_FILE, d)
def load_absent(): return _load(ABSENT_FILE, {})
def save_absent(d):_save(ABSENT_FILE, d)
def load_chats():  return _load(CHATS_FILE, [])
def save_chats(d): _save(CHATS_FILE, d)

def register_chat(cid):
    c = load_chats()
    if cid not in c:
        c.append(cid); save_chats(c); log.info("chat %s", cid)

# ── Имена ─────────────────────────────────────────────────────────────────
def resolve_sender(u):
    users = load_users(); uid = str(u.id)
    if uid in users: return users[uid]
    fn = u.full_name or "Unknown"
    users[uid] = fn; save_users(users)
    log.info("yangi/привязка %s -> %s", uid, fn)
    return fn

def find_user_id(name):
    for uid, n in load_users().items():
        if n == name:
            try: return int(uid)
            except ValueError: return None
    return None

# ── Отгул ─────────────────────────────────────────────────────────────────
def has_absent_keyword(t):
    if not t: return False
    t = t.lower()
    return any(k in t for k in ("отгул", "выходной", "dam", "ruxsat", "касал", "больнич"))

def mark_absent(name, date):
    a = load_absent(); a.setdefault(name, {})
    if not a[name].get(date):
        a[name][date] = True; save_absent(a); return True
    return False

def last_active_date(cache, absent, name):
    dates = []
    if name in cache:
        dates += [d for d, v in cache[name].items() if any(v.get(k) is not None for k in _empty_day())]
    if name in absent:
        dates += list(absent[name].keys())
    return max(dates) if dates else None

# ── Парс длительности "3 соат 40 мин" -> минуты ───────────────────────────
def parse_duration_to_min(text):
    if text is None: return None
    s = str(text).lower()
    h = 0; m = 0
    mh = re.search(r"(\d+)\s*(соат|саот| soat|час|ч)", s)
    mm = re.search(r"(\d+)\s*(мин|min|дақ|m)", s)
    if mh: h = int(mh.group(1))
    if mm: m = int(mm.group(1))
    if not mh and not mm:
        # чистое число — считаем минутами
        only = re.search(r"\d+", s)
        if only: m = int(only.group())
    total = h * 60 + m
    return total if total > 0 else None

# ── Извлечение через Claude ───────────────────────────────────────────────
EXTRACT_PROMPT = (
    'Это ежедневный отчёт продавца колл-центра. Извлеки показатели за день. '
    'Если это не отчёт (скриншот/чат/болтовня) — верни is_relevant:false. '
    'Верни ТОЛЬКО JSON без markdown: '
    '{"usilia":число|null,'           # усилия = попытки связи
    '"dozvon":число|null,'             # дозвон = состоявшиеся звонки
    '"duration_text":"строка"|null,'   # длительность как в тексте, например "4 соат 10 мин"
    '"leads":число|null,'              # лиды
    '"orders":число|null,'             # заказы (заказ сони)
    '"amount":число|null,'             # сумма (сум; "10.000.000" -> 10000000)
    '"is_relevant":true/false}'
)

def _claude_json(content):
    resp = client.messages.create(model="claude-opus-4-5", max_tokens=400,
                                  messages=[{"role": "user", "content": content}])
    out = re.sub(r"```json|```", "", resp.content[0].text).strip()
    return json.loads(out)

def analyze_text(text):
    try:
        return _claude_json(EXTRACT_PROMPT + "\n\nОтчёт:\n" + text)
    except Exception as e:
        log.error("analyze_text: %s", e); return None

# ── Сохранение ────────────────────────────────────────────────────────────
def store_day(sender, date, data):
    cache = load_cache(); cache.setdefault(sender, {})
    day = cache[sender].get(date, _empty_day())
    updated = []
    mapping = {"usilia": "usilia", "dozvon": "dozvon", "leads": "leads",
               "orders": "orders", "amount": "amount"}
    for src, dst in mapping.items():
        if data.get(src) is not None:
            day[dst] = data[src]; updated.append(dst)
    dur = parse_duration_to_min(data.get("duration_text"))
    if dur is not None:
        day["duration_min"] = dur; updated.append("duration_min")
    cache[sender][date] = day; save_cache(cache)
    return day, updated

LABELS = {"usilia": "Усилия", "dozvon": "Дозвон", "duration_min": "Длительность (мин)",
          "leads": "Лиды", "orders": "Заказы", "amount": "Сумма"}

def _fmt(day, updated):
    out = []
    for k in updated:
        v = day[k]
        if k == "amount":
            out.append("  Сумма: " + format(int(v), ",").replace(",", " "))
        elif k == "duration_min":
            out.append("  Длительность: " + str(int(v // 60)) + " соат " + str(int(v % 60)) + " мин")
        else:
            out.append("  " + LABELS[k] + ": " + str(int(v)))
    return "\n".join(out)

# ── Обработчик текста ─────────────────────────────────────────────────────
async def handle_text(update, context):
    msg = update.message
    if not msg or not msg.text or not msg.from_user: return
    sender = resolve_sender(msg.from_user)
    date = datetime.now(TZ).strftime("%Y-%m-%d")
    if has_absent_keyword(msg.text):
        if mark_absent(sender, date):
            await msg.reply_text("📌 " + sender + ": " + date + " — отгул, день не считается пропущенным.")
        return
    data = analyze_text(msg.text)
    if not data or not data.get("is_relevant"): return
    day, updated = store_day(sender, date, data)
    if updated:
        await msg.reply_text("✅ " + sender + ", отчёт за " + date + " сохранён:\n" + _fmt(day, updated))

# ── Сводка для дашборда (с фильтром по датам) ──────────────────────────────
def _in_range(date_str, frm):
    if frm is None: return True
    try:
        d = datetime.strptime(date_str, "%Y-%m-%d").date()
    except ValueError:
        return False
    return d >= frm

def _tonum(v):
    """Любое значение (int/float/str/None) -> число. '120' -> 120, '10 000 000' -> 10000000."""
    if v is None:
        return 0
    if isinstance(v, (int, float)):
        return v
    s = str(v).strip().replace("\xa0", "").replace(" ", "").replace(",", ".")
    if not s:
        return 0
    try:
        return float(s)
    except ValueError:
        return 0

def build_summary(cache, frm=None):
    today = datetime.now(TZ).strftime("%Y-%m-%d")
    absent = load_absent(); goals = load_goals()
    out = {}
    for person, days in cache.items():
        usilia = dozvon = dur = leads = orders = amount = 0
        has = False
        for d, v in days.items():
            if not _in_range(d, frm): continue
            usilia += _tonum(v.get("usilia"))
            dozvon += _tonum(v.get("dozvon"))
            dur    += _tonum(v.get("duration_min"))
            leads  += _tonum(v.get("leads"))
            orders += _tonum(v.get("orders"))
            amount += _tonum(v.get("amount"))
            has = True
        if not has: continue
        plan = leads * LEAD_PRICE
        conv = round(orders / leads * 100, 1) if leads else None
        plan_done = round(amount / plan * 100, 1) if plan else None
        avg_order_min = round(dur / orders, 1) if orders else None
        today_active = (today in days and any(days[today].get(k) is not None for k in _empty_day())) \
                       or (person in absent and today in absent[person])
        out[person] = {"usilia": usilia, "dozvon": dozvon, "duration_min": dur,
                       "leads": leads, "orders": orders, "amount": amount,
                       "plan": plan, "conv": conv, "plan_done": plan_done,
                       "avg_order_min": avg_order_min, "goal": goals.get(person),
                       "active_today": today_active}
    return out

# ── HTML дашборд (с кнопками-фильтрами) ────────────────────────────────────
def generate_dashboard(cache):
    updated = datetime.now(TZ).strftime("%d.%m.%Y %H:%M")
    today = datetime.now(TZ).date()
    ranges = {
        "today": today,
        "week": today - timedelta(days=7),
        "month": today - timedelta(days=30),
        "all": None,
    }
    payload = {k: build_summary(cache, frm) for k, frm in ranges.items()}
    pj = json.dumps(payload, ensure_ascii=False)
    lead_price_str = format(LEAD_PRICE, ",").replace(",", " ")

    css = (
        "@import url('https://fonts.googleapis.com/css2?family=Unbounded:wght@400;700;900&family=Inter:wght@300;400;500;600&display=swap');"
        ":root{--bg:#0a0e14;--card:#141b24;--line:#26323f;--txt:#eef3f7;--mut:#7e90a2;--accent:#22c55e;--accent2:#06b6d4}"
        "*{box-sizing:border-box;margin:0;padding:0}"
        "body{background:var(--bg);color:var(--txt);font-family:Inter,sans-serif;min-height:100vh}"
        "header{padding:1.1rem 1.6rem;border-bottom:1px solid var(--line);background:linear-gradient(135deg,#0a0e14,#0d1a22);display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:.5rem}"
        "header h1{font-family:Unbounded;font-size:1.05rem;font-weight:900;background:linear-gradient(135deg,#22c55e,#06b6d4);-webkit-background-clip:text;-webkit-text-fill-color:transparent}"
        "header .upd{font-size:.72rem;color:var(--mut)}"
        ".filters{display:flex;gap:.4rem;padding:.9rem 1.6rem;flex-wrap:wrap;border-bottom:1px solid var(--line)}"
        ".fbtn{padding:.4rem .9rem;border-radius:8px;border:1px solid var(--line);background:var(--card);color:var(--mut);font-size:.74rem;font-weight:600;cursor:pointer}"
        ".fbtn.active{background:#13312280;color:#22c55e;border-color:#22c55e}"
        ".nav{display:flex;gap:.3rem;padding:.7rem 1.6rem 0;border-bottom:1px solid var(--line);overflow-x:auto;scrollbar-width:none}"
        ".nav::-webkit-scrollbar{display:none}"
        ".tab{padding:.45rem .9rem;border-radius:8px 8px 0 0;border:1px solid transparent;border-bottom:none;cursor:pointer;font-size:.74rem;font-weight:500;white-space:nowrap;color:var(--mut);background:transparent}"
        ".tab.active{color:var(--txt);background:var(--card);border-color:var(--line)}"
        ".content{padding:1.4rem 1.6rem}.panel{display:none}.panel.active{display:block}"
        "table{width:100%;border-collapse:collapse;border-radius:10px;overflow:hidden;border:1px solid var(--line);margin-bottom:1.2rem}"
        "th{padding:.6rem .7rem;text-align:right;font-size:.6rem;color:#9fb0c0;text-transform:uppercase;letter-spacing:.04em;background:#0d141c;border-bottom:2px solid var(--line)}"
        "th:nth-child(2){text-align:left}th:first-child{text-align:center}"
        "td{padding:.65rem .7rem;text-align:right;font-size:.8rem;border-bottom:1px solid #1c2530}"
        "td:nth-child(2){text-align:left;font-weight:600}td:first-child{text-align:center}"
        "tbody tr:nth-child(odd) td{background:#0f1620}tbody tr:nth-child(even) td{background:#131c27}"
        ".rank{font-family:Unbounded;font-weight:900;font-size:.8rem;color:var(--mut)}"
        ".g1 .rank{color:#f59e0b}.g2 .rank{color:#94a3b8}.g3 .rank{color:#b45309}"
        ".g1 td:first-child{border-left:3px solid #f59e0b}.g2 td:first-child{border-left:3px solid #94a3b8}.g3 td:first-child{border-left:3px solid #b45309}"
        ".money{font-family:Unbounded;font-weight:700}"
        ".bg{background:rgba(34,197,94,.15);color:#22c55e;padding:.12rem .45rem;border-radius:5px;font-size:.72rem;font-weight:700}"
        ".by{background:rgba(245,158,11,.15);color:#fbbf24;padding:.12rem .45rem;border-radius:5px;font-size:.72rem;font-weight:700}"
        ".br{background:rgba(239,68,68,.15);color:#f87171;padding:.12rem .45rem;border-radius:5px;font-size:.72rem;font-weight:700}"
        ".cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:.7rem}"
        ".c{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:1rem}"
        ".c .l{font-size:.6rem;color:var(--mut);text-transform:uppercase;letter-spacing:.04em;margin-bottom:.35rem}"
        ".c .v{font-family:Unbounded;font-size:1.1rem;font-weight:700;line-height:1.1}"
        ".empty{color:var(--mut);text-align:center;padding:2rem}"
    )

    js = (
        "var ALL=" + pj + ";var RANGE='today';var LP='" + lead_price_str + "';"
        "function money(v){if(v==null)return '-';return Math.round(v).toLocaleString('ru-RU')}"
        "function num(v){if(v==null)return '-';return Math.round(v).toLocaleString('ru-RU')}"
        "function pct(v){if(v==null)return '-';return v+'%'}"
        "function dur(m){if(m==null||m===0)return '-';return Math.floor(m/60)+' соат '+Math.round(m%60)+' мин'}"
        "function avgmin(m){if(m==null)return '-';return Math.round(m)+' мин/заказ'}"
        "function medal(i){return i===0?'1':i===1?'2':i===2?'3':(i+1)}"
        "function rc(i){return i===0?'g1':i===1?'g2':i===2?'g3':''}"
        "function rows(){var S=ALL[RANGE]||{};return Object.keys(S).map(function(n){var o={name:n};Object.assign(o,S[n]);return o})}"
        "function convBadge(c){if(c==null)return '-';return c>=40?('<span class=\"bg\">'+pct(c)+'</span>'):c>=25?('<span class=\"by\">'+pct(c)+'</span>'):('<span class=\"br\">'+pct(c)+'</span>')}"
        "function rankTable(){var r=rows().sort(function(a,b){return (b.amount||0)-(a.amount||0)});"
        "if(!r.length)return '<div class=\"empty\">Бу давр учун маълумот йўқ</div>';"
        "var body=r.map(function(p,i){var pd=p.plan_done;var col=pd==null?'var(--mut)':pd>=100?'#22c55e':pd>=70?'#06b6d4':'#f87171';"
        "return '<tr class=\"'+rc(i)+'\"><td class=\"rank\">'+medal(i)+'</td><td>'+p.name+'</td>'"
        "+'<td class=\"money\" style=\"color:#22c55e\">'+money(p.amount)+'</td>'"
        "+'<td>'+num(p.orders)+'</td>'"
        "+'<td>'+num(p.leads)+'</td>'"
        "+'<td>'+convBadge(p.conv)+'</td>'"
        "+'<td style=\"color:'+col+'\">'+pct(p.plan_done)+'</td>'"
        "+'<td>'+num(p.dozvon)+'</td>'"
        "+'<td>'+num(p.usilia)+'</td>'"
        "+'<td style=\"color:#9fb0c0\">'+avgmin(p.avg_order_min)+'</td></tr>'}).join('');"
        "return '<table><thead><tr><th>#</th><th>Сотувчи</th><th>Сумма</th><th>Заказ</th><th>Лид</th><th>Конв.</th><th>План%</th><th>Дозвон</th><th>Усилия</th><th>Ўрт/заказ</th></tr></thead><tbody>'+body+'</tbody></table>'}"
        "function personPage(name){var S=ALL[RANGE]||{};var p=S[name];if(!p)return '<div class=\"empty\">Бу давр учун маълумот йўқ</div>';"
        "return '<div class=\"cards\">'"
        "+'<div class=\"c\"><div class=\"l\">Усилия</div><div class=\"v\">'+num(p.usilia)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">Дозвон</div><div class=\"v\">'+num(p.dozvon)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">Длительность</div><div class=\"v\" style=\"font-size:.9rem\">'+dur(p.duration_min)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">Лид</div><div class=\"v\">'+num(p.leads)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">Заказ</div><div class=\"v\">'+num(p.orders)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">Сумма</div><div class=\"v\" style=\"color:#22c55e;font-size:.9rem\">'+money(p.amount)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">Конверсия</div><div class=\"v\" style=\"color:#06b6d4\">'+pct(p.conv)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">План бажариш</div><div class=\"v\" style=\"color:'+(p.plan_done>=100?'#22c55e':'#06b6d4')+'\">'+pct(p.plan_done)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">Ўрт. заказ вақти</div><div class=\"v\" style=\"font-size:.9rem\">'+avgmin(p.avg_order_min)+'</div></div>'"
        "+'<div class=\"c\"><div class=\"l\">План</div><div class=\"v\" style=\"font-size:.85rem;color:#9fb0c0\">'+money(p.plan)+'</div></div>'"
        "+'</div>'}"
        "var nav=document.getElementById('nav'),content=document.getElementById('content');"
        "function render(){content.innerHTML='';var tabs=[['🏆 Рейтинг',rankTable]];"
        "var S=ALL[RANGE]||{};var names=Object.keys(S).sort();"
        "var html='';var act=document.querySelector('.tab.active');var actIdx=act?parseInt(act.dataset.i):0;"
        "nav.innerHTML='';"
        "var btn=document.createElement('button');btn.className='tab active';btn.textContent='🏆 Рейтинг';btn.dataset.i=0;btn.onclick=function(){sel(0)};nav.appendChild(btn);"
        "names.forEach(function(nm,k){var b=document.createElement('button');b.className='tab';b.textContent=nm;b.dataset.i=k+1;b.onclick=(function(i){return function(){sel(i)}})(k+1);nav.appendChild(b)});"
        "sel(0)}"
        "function sel(i){document.querySelectorAll('.tab').forEach(function(t){t.classList.toggle('active',parseInt(t.dataset.i)===i)});"
        "var S=ALL[RANGE]||{};var names=Object.keys(S).sort();"
        "content.innerHTML = i===0 ? rankTable() : ('<h2 style=\"font-family:Unbounded;font-size:1rem;margin-bottom:1rem\">'+names[i-1]+'</h2>'+personPage(names[i-1]))}"
        "function setRange(r,el){RANGE=r;document.querySelectorAll('.fbtn').forEach(function(b){b.classList.remove('active')});el.classList.add('active');render()}"
        "render();"
        "setTimeout(function(){location.reload()},600000);"
    )

    return ('<!DOCTYPE html><html lang="uz"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width, initial-scale=1">'
            '<title>Сотувчилар дашборди</title><style>' + css + '</style></head><body>'
            '<header><h1>📞 Сотувчилар дашборди</h1><span class="upd">Янгиланди: ' + updated + '</span></header>'
            '<div class="filters">'
            '<button class="fbtn active" onclick="setRange(\'today\',this)">Бугун</button>'
            '<button class="fbtn" onclick="setRange(\'week\',this)">Ҳафта</button>'
            '<button class="fbtn" onclick="setRange(\'month\',this)">Ой</button>'
            '<button class="fbtn" onclick="setRange(\'all\',this)">Барча давр</button>'
            '</div>'
            '<div class="nav" id="nav"></div><div class="content" id="content"></div>'
            '<script>' + js + '</script></body></html>')

# ── GitHub Pages push ─────────────────────────────────────────────────────
def push_github(html):
    if not GITHUB_TOKEN: return False
    api = "https://api.github.com/repos/" + GITHUB_USER + "/" + GITHUB_REPO + "/contents/" + GITHUB_FILE
    headers = {"Authorization": "token " + GITHUB_TOKEN,
               "Accept": "application/vnd.github.v3+json", "User-Agent": "sales-report"}
    ctx = ssl._create_unverified_context()
    sha = None
    try:
        req = urllib.request.Request(api, headers=headers)
        with urllib.request.urlopen(req, context=ctx) as r:
            sha = json.loads(r.read())["sha"]
    except urllib.error.HTTPError as e:
        if e.code != 404: log.error("SHA: %s", e)
    payload = {"message": "report " + datetime.now(TZ).strftime("%d.%m %H:%M"),
               "content": base64.b64encode(html.encode()).decode()}
    if sha: payload["sha"] = sha
    try:
        data = json.dumps(payload).encode()
        req = urllib.request.Request(api, data=data, headers=headers, method="PUT")
        with urllib.request.urlopen(req, context=ctx) as r:
            log.info("push OK %s", r.status); return True
    except Exception as e:
        log.error("push: %s", e); return False

# ── /report ───────────────────────────────────────────────────────────────
async def cmd_report(update, context):
    cache = load_cache()
    if not cache:
        await update.message.reply_text("Маълумот йўқ."); return
    await update.message.reply_text("⏳ Дашборд тайёрланмоқда...")
    html = generate_dashboard(cache)
    if push_github(html):
        await update.message.reply_text("📊 Дашборд тайёр:\n\n🌐 " + PAGES_URL +
                                        "\n\nИчида фильтр: Бугун / Ҳафта / Ой / Барча давр")
    else:
        # запасной вариант — файл
        path = str(BASE_DIR / "report.html")
        with open(path, "w", encoding="utf-8") as f: f.write(html)
        await update.message.reply_document(document=open(path, "rb"),
            filename="dashboard.html", caption="📊 Дашборд (GitHub йўқ, файл)")

# ── Неактивность ──────────────────────────────────────────────────────────
def _plural(n):
    if n % 10 == 1 and n % 100 != 11: return "день"
    if 2 <= n % 10 <= 4 and not (12 <= n % 100 <= 14): return "дня"
    return "дней"

async def daily_inactivity_check(context):
    today = datetime.now(TZ).date()
    chats = load_chats()
    if not chats: return
    cache, absent = load_cache(), load_absent()
    global _kick_counter
    for name in load_goals():
        last = last_active_date(cache, absent, name)
        if not last: continue
        try: last_d = datetime.strptime(last, "%Y-%m-%d").date()
        except ValueError: continue
        di = (today - last_d).days
        if di < WARN_DAYS: continue
        uid = find_user_id(name)
        mention = ("<a href=\"tg://user?id=" + str(uid) + "\">" + name + "</a>") if uid else name
        if di >= KICK_DAYS:
            _kick_counter += 1; tok = str(_kick_counter)
            pending_kicks[tok] = {"name": name, "user_id": uid}
            kb = InlineKeyboardMarkup([[
                InlineKeyboardButton("🚫 Кикнуть", callback_data="kick:yes:" + tok),
                InlineKeyboardButton("✋ Оставить", callback_data="kick:no:" + tok)]])
            for aid in ADMIN_IDS:
                try:
                    await context.bot.send_message(chat_id=aid,
                        text="⚠️ " + name + " — " + str(di) + " " + _plural(di) + " без отчёта.\nКикнуть?",
                        reply_markup=kb)
                except Exception as e: log.error("notify: %s", e)
        else:
            rem = KICK_DAYS - di
            txt = ("⏰ " + mention + " — нет отчёта " + str(di) + " " + _plural(di) +
                   ". Осталось " + str(rem) + " " + _plural(rem) + ". Пришлите отчёт или напишите «отгул».")
            for cid in chats:
                try: await context.bot.send_message(chat_id=cid, text=txt, parse_mode="HTML")
                except Exception as e: log.error("warn: %s", e)

async def cb_kick(update, context):
    q = update.callback_query; await q.answer()
    parts = (q.data or "").split(":")
    if len(parts) != 3 or parts[0] != "kick": return
    if q.from_user.id not in ADMIN_IDS:
        await q.answer("Только админ.", show_alert=True); return
    _, dec, tok = parts
    pend = pending_kicks.pop(tok, None)
    if not pend:
        await q.edit_message_text("⚠️ Запрос устарел."); return
    name, uid = pend["name"], pend["user_id"]
    if dec == "no":
        await q.edit_message_text("✋ " + name + " оставлен."); return
    if not uid:
        await q.edit_message_text("⚠️ " + name + ": user_id не привязан. /link."); return
    done = 0
    for cid in load_chats():
        try:
            await context.bot.ban_chat_member(chat_id=cid, user_id=uid)
            await context.bot.unban_chat_member(chat_id=cid, user_id=uid, only_if_banned=True)
            await context.bot.send_message(chat_id=cid, text="🚫 " + name + " удалён — нет отчётов " + str(KICK_DAYS) + "+ дня.")
            done += 1
        except Exception as e: log.error("kick: %s", e)
    await q.edit_message_text("🚫 " + name + " кикнут из " + str(done) + " чат(ов).")

# ── Команды ───────────────────────────────────────────────────────────────
def _is_admin(u): return bool(u) and u.id in ADMIN_IDS
def _parse_nv(args):
    if len(args) < 2: return None, None, "нужно: <имя> <число>"
    raw = args[-1].replace(",", ".").replace(" ", "")
    try: v = float(raw)
    except ValueError: return None, None, "'" + args[-1] + "' не число"
    name = " ".join(args[:-1]).strip()
    if not name: return None, None, "пустое имя"
    return name, v, None

async def cmd_whoami(update, context):
    u = update.effective_user
    await update.message.reply_text("🆔 user_id: " + str(u.id) + "\n📊 В дашборде: " + resolve_sender(u))

async def cmd_link(update, context):
    u = update.effective_user
    t = " ".join(context.args).strip() if context.args else ""
    if not t:
        await update.message.reply_text("Использование: /link Имя как в дашборде"); return
    if t not in load_cache() and t not in load_goals():
        await update.message.reply_text("❌ '" + t + "' не найден. /addmember."); return
    users = load_users(); users[str(u.id)] = t; save_users(users)
    await update.message.reply_text("✅ Вы привязаны к '" + t + "'")

async def cmd_addmember(update, context):
    if not _is_admin(update.effective_user):
        await update.message.reply_text("⛔ Только админ."); return
    name, plan, err = _parse_nv(context.args or [])
    if err:
        await update.message.reply_text("❌ " + err + "\nПример: /addmember Азиза Вафокулова 50000000"); return
    goals = load_goals(); goals[name] = plan; save_goals(goals)
    cache = load_cache()
    if name not in cache: cache[name] = {}; save_cache(cache)
    await update.message.reply_text("✅ Добавлен: " + name + " → план " +
        format(plan, ",.0f").replace(",", " ") + " сум.\nПусть вызовет /link " + name + ".")

async def cmd_setgoal(update, context):
    if not _is_admin(update.effective_user):
        await update.message.reply_text("⛔ Только админ."); return
    name, plan, err = _parse_nv(context.args or [])
    if err:
        await update.message.reply_text("❌ " + err); return
    goals = load_goals()
    if name not in goals:
        await update.message.reply_text("❌ '" + name + "' не найден."); return
    old = goals[name]; goals[name] = plan; save_goals(goals)
    await update.message.reply_text("✅ " + name + ": " + format(old, ",.0f").replace(",", " ") +
        " → " + format(plan, ",.0f").replace(",", " ") + " сум.")

async def cmd_removemember(update, context):
    if not _is_admin(update.effective_user):
        await update.message.reply_text("⛔ Только админ."); return
    name = " ".join(context.args).strip() if context.args else ""
    if not name:
        await update.message.reply_text("❌ /removemember Имя Фамилия"); return
    goals = load_goals(); cache = load_cache(); users = load_users(); absent = load_absent()
    if name not in goals and name not in cache:
        await update.message.reply_text("❌ '" + name + "' не найден. /listmembers."); return
    goals.pop(name, None); save_goals(goals)
    cache.pop(name, None); save_cache(cache)
    absent.pop(name, None); save_absent(absent)
    for uid in [u for u, n in users.items() if n == name]: users.pop(uid, None)
    save_users(users)
    await update.message.reply_text("🗑 '" + name + "' тўлиқ ўчирилди. Қолди: " + str(len(goals)))

async def cmd_listmembers(update, context):
    goals = load_goals()
    if not goals:
        await update.message.reply_text("Список пуст."); return
    linked = set(load_users().values())
    lines = ["👥 Продавцов: " + str(len(goals)), ""]
    for n in sorted(goals, key=str.lower):
        lines.append(("🔗" if n in linked else "·") + " " + n + " — " + format(goals[n], ",.0f").replace(",", " ") + " сум")
    await update.message.reply_text("\n".join(lines))

async def cmd_start(update, context):
    await update.message.reply_text(
        "👋 Я слежу за показателями продавцов.\n\n"
        "📨 Присылайте ежедневный отчёт текстом:\n"
        "Усилия, Дозвон, Длительность, Лид, Заказ, Сумма.\n\n"
        "📊 /report — дашборд (ссылка, фильтр по датам).\n"
        "✈️ «отгул» — если выходной.")
    cid = update.effective_chat.id
    register_chat(cid)

# ── Запуск ────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    if not TELEGRAM_TOKEN or not ANTHROPIC_API_KEY:
        sys.exit("❌ TELEGRAM_TOKEN и ANTHROPIC_API_KEY керак.")
    app = ApplicationBuilder().token(TELEGRAM_TOKEN).build()
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("report", cmd_report))
    app.add_handler(CommandHandler("whoami", cmd_whoami))
    app.add_handler(CommandHandler("link", cmd_link))
    app.add_handler(CommandHandler("addmember", cmd_addmember))
    app.add_handler(CommandHandler("setgoal", cmd_setgoal))
    app.add_handler(CommandHandler("removemember", cmd_removemember))
    app.add_handler(CommandHandler("listmembers", cmd_listmembers))
    app.add_handler(CallbackQueryHandler(cb_kick, pattern=r"^kick:"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))

    now = datetime.now(TZ)
    t = now.replace(hour=INACTIVITY_CHECK_HOUR, minute=0, second=0, microsecond=0)
    if now >= t: t += timedelta(days=1)
    app.job_queue.run_repeating(daily_inactivity_check, interval=86400, first=(t - now).total_seconds())

    log.info("Бот продавцов v2 запущен. Кэш: %s", CACHE_FILE)
    app.run_polling()
