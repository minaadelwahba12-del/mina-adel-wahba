#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
برنامج حسابات المطبعة  -  Printing Press Accounting
تشغيل:  python app.py     ثم افتح المتصفح على  http://127.0.0.1:8000
لا يحتاج أي مكتبات خارجية (Python 3.8+ فقط). البيانات في الملف press.db
"""
import argparse, datetime, hashlib, hmac, html, json, os, secrets, socket, sqlite3, tempfile, threading, time, webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

BASE = os.path.dirname(os.path.abspath(__file__))
DB = os.environ.get("PRESS_DB") or os.path.join(BASE, "press.db")
HTTPS = os.environ.get("PRESS_HTTPS") == "1"      # شغال ورا HTTPS (سيرفر على الانترنت)
PROXY = os.environ.get("PRESS_PROXY") == "1"      # ورا بروكسي بيبعت IP العميل الحقيقي

# (العمود, النوع)  t=نص  n=رقم عشري  i=رقم صحيح/مرجع
TABLES = {
    "customers": [("name", "t"), ("phone", "t"), ("address", "t"), ("notes", "t"), ("opening_balance", "n")],
    "orders": [("customer_id", "i"), ("title", "t"), ("qty", "n"), ("order_date", "t"),
               ("due_date", "t"), ("status", "t"), ("material_cost", "n"), ("labor_cost", "n"),
               ("finishing_cost", "n"), ("other_cost", "n"), ("price", "n"), ("notes", "t")],
    "payments": [("customer_id", "i"), ("pay_date", "t"), ("amount", "n"), ("method", "t"), ("notes", "t")],
    "expenses": [("exp_date", "t"), ("category", "t"), ("description", "t"), ("amount", "n")],
    "items": [("name", "t"), ("unit", "t"), ("min_qty", "n"), ("unit_cost", "n"), ("sell_price", "n"), ("notes", "t")],
    "stock_moves": [("item_id", "i"), ("move_date", "t"), ("qty", "n"), ("order_id", "i"), ("notes", "t")],
}
SQLTYPE = {"t": "TEXT DEFAULT ''", "n": "REAL DEFAULT 0", "i": "INTEGER"}

LIST_SQL = {
    "customers": """SELECT c.*, COALESCE(o.total,0) AS total, COALESCE(p.paid,0) AS paid,
        COALESCE(c.opening_balance,0)+COALESCE(o.total,0)-COALESCE(p.paid,0) AS balance
        FROM customers c
        LEFT JOIN (SELECT customer_id, SUM(price) total FROM orders WHERE status NOT IN ('ملغي','عرض سعر') GROUP BY customer_id) o ON o.customer_id=c.id
        LEFT JOIN (SELECT customer_id, SUM(amount) paid FROM payments GROUP BY customer_id) p ON p.customer_id=c.id
        ORDER BY c.name""",
    "orders": """SELECT o.*, c.name AS customer_name
        FROM orders o LEFT JOIN customers c ON c.id=o.customer_id ORDER BY o.id DESC""",
    "payments": """SELECT p.*, c.name AS customer_name
        FROM payments p LEFT JOIN customers c ON c.id=p.customer_id
        ORDER BY p.pay_date DESC, p.id DESC""",
    "expenses": "SELECT * FROM expenses ORDER BY exp_date DESC, id DESC",
    "items": """SELECT i.*, COALESCE((SELECT SUM(qty) FROM stock_moves m WHERE m.item_id=i.id),0) AS qty
        FROM items i ORDER BY i.name""",
    "stock_moves": """SELECT m.*, i.name AS item_name, i.unit AS unit
        FROM stock_moves m LEFT JOIN items i ON i.id=m.item_id ORDER BY m.move_date DESC, m.id DESC""",
}

# حذف مرفوض لو في بيانات مرتبطة
DELETE_GUARD = {
    "customers": [("SELECT COUNT(*) FROM orders WHERE customer_id=?", "العميل ده عنده أوردرات، احذف الأوردرات الأول."),
                  ("SELECT COUNT(*) FROM payments WHERE customer_id=?", "العميل ده عنده دفعات مسجلة، احذفها الأول.")],
    "items": [("SELECT COUNT(*) FROM stock_moves WHERE item_id=?", "الصنف ده عليه حركات مخزون، احذفها الأول."),
              ("SELECT COUNT(*) FROM order_materials WHERE item_id=?", "الصنف ده مستخدم في أوردرات.")],
}
NO_STOCK = ("ملغي", "عرض سعر")          # الحالات اللي مبتخصمش من المخزون
COST_COLS = ("material_cost", "labor_cost", "finishing_cost", "other_cost")
ROLES = ("admin", "accountant", "staff")
SETTING_KEYS = ("press_name", "press_phone", "press_address", "quote_days", "quote_terms", "country_code")
SESSIONS = {}
FAILS = {}

REQUIRED = {
    "customers": ["name"], "orders": ["customer_id", "title"], "payments": ["customer_id"],
    "items": ["name"], "stock_moves": ["item_id"],
}


def db():
    os.makedirs(os.path.dirname(os.path.abspath(DB)), exist_ok=True)
    con = sqlite3.connect(DB)
    con.row_factory = sqlite3.Row
    return con


def add_col(con, table, col, decl):
    have = [r[1] for r in con.execute(f"PRAGMA table_info({table})")]
    if col not in have:
        con.execute(f"ALTER TABLE {table} ADD COLUMN {col} {decl}")


def init_db():
    con = db()
    for t, cols in TABLES.items():
        defs = ", ".join(f"{c} {SQLTYPE[k]}" for c, k in cols)
        con.execute(f"CREATE TABLE IF NOT EXISTS {t} (id INTEGER PRIMARY KEY AUTOINCREMENT, {defs})")
    # ترحيل من النظام القديم: الدفعات بقت على حساب العميل مش على الفاتورة
    add_col(con, "customers", "opening_balance", "REAL DEFAULT 0")
    add_col(con, "payments", "customer_id", "INTEGER")
    if "order_id" in [r[1] for r in con.execute("PRAGMA table_info(payments)")]:
        con.execute("""UPDATE payments SET customer_id=(SELECT customer_id FROM orders WHERE orders.id=payments.order_id)
            WHERE customer_id IS NULL AND order_id IS NOT NULL""")
    add_col(con, "items", "sell_price", "REAL DEFAULT 0")
    add_col(con, "stock_moves", "auto", "INTEGER DEFAULT 0")
    add_col(con, "stock_moves", "unit_cost", "REAL DEFAULT 0")
    con.execute("""CREATE TABLE IF NOT EXISTS order_materials (id INTEGER PRIMARY KEY AUTOINCREMENT,
        order_id INTEGER, item_id INTEGER, qty REAL DEFAULT 0, unit_cost REAL DEFAULT 0)""")
    add_col(con, "order_materials", "name", "TEXT DEFAULT ''")          # بند من برة المخزن (item_id فاضي)
    add_col(con, "order_materials", "sell_price", "REAL DEFAULT 0")
    con.execute("""CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT UNIQUE,
        password_hash TEXT, full_name TEXT DEFAULT '', role TEXT, active INTEGER DEFAULT 1)""")
    con.execute("CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT)")
    defaults = (("press_name", "اسم المطبعة"), ("press_phone", ""), ("press_address", ""),
                ("quote_days", "7"), ("country_code", "20"),
                ("quote_terms", "العرض ساري للمدة المذكورة. يبدأ التنفيذ بعد اعتماد التصميم وسداد العربون."))
    for k, v in defaults:
        con.execute("INSERT OR IGNORE INTO settings VALUES (?,?)", (k, v))
    con.commit()
    con.close()


# ---------- المستخدمين والجلسات ----------
def hash_pw(pw, salt=None):
    salt = salt or os.urandom(16).hex()
    h = hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), bytes.fromhex(salt), 200000).hex()
    return salt + "$" + h


def check_pw(pw, stored):
    try:
        salt, h = stored.split("$")
    except ValueError:
        return False
    return hmac.compare_digest(hash_pw(pw, salt).split("$")[1], h)


def can(role, name, method):
    if role == "admin":
        return True
    if name in ("users", "backup", "restore"):
        return False
    if name == "settings":
        return method == "GET"
    if role == "accountant":
        return True
    if role == "staff":
        allow = {"customers": ("GET", "POST", "PUT"), "orders": ("GET", "POST", "PUT"),
                 "items": ("GET",), "stock_moves": ("GET", "POST"), "invoice_data": ("GET",)}
        return method in allow.get(name, ())
    return False


def scrub(role, table, data):
    """الموظف ميشوفش التكاليف والأرباح"""
    if role != "staff":
        return data
    for r in data:
        if table == "orders":
            for c in COST_COLS:
                r[c] = 0
            for m in r.get("materials", []):
                m["unit_cost"] = 0
        elif table == "items":
            r["unit_cost"] = 0
        elif table == "stock_moves":
            r["unit_cost"] = 0
        elif table == "customers":
            r["total"] = r["paid"] = r["balance"] = r["opening_balance"] = 0
    return data


def rows(con, sql, args=()):
    return [dict(r) for r in con.execute(sql, args).fetchall()]


def coerce(table, data):
    out = {}
    for col, kind in TABLES[table]:
        v = data.get(col)
        if kind == "n":
            try:
                out[col] = float(v) if v not in (None, "") else 0.0
            except ValueError:
                raise ValueError("قيمة رقمية غير صحيحة")
        elif kind == "i":
            out[col] = int(v) if v not in (None, "") else None
        else:
            out[col] = str(v if v is not None else "").strip()
    for col in REQUIRED.get(table, []):
        if out.get(col) in (None, ""):
            raise ValueError("من فضلك املأ الحقول المطلوبة")
    if table == "payments" and out["amount"] <= 0:
        raise ValueError("المبلغ لازم يكون أكبر من صفر")
    if table == "expenses" and out["amount"] <= 0:
        raise ValueError("المبلغ لازم يكون أكبر من صفر")
    if table == "stock_moves" and out["qty"] == 0:
        raise ValueError("الكمية لازم تكون مختلفة عن صفر")
    return out


def money(v):
    return f"{(v or 0):,.2f}"


def dashboard(con, month):
    today = datetime.date.today().isoformat()
    s = con.execute("""SELECT COALESCE(SUM(price),0), COALESCE(SUM(material_cost+labor_cost+finishing_cost+other_cost),0), COUNT(*)
        FROM orders WHERE substr(order_date,1,7)=? AND status NOT IN ('ملغي','عرض سعر')""", (month,)).fetchone()
    collected = con.execute("SELECT COALESCE(SUM(amount),0) FROM payments WHERE substr(pay_date,1,7)=?", (month,)).fetchone()[0]
    expenses = con.execute("SELECT COALESCE(SUM(amount),0) FROM expenses WHERE substr(exp_date,1,7)=?", (month,)).fetchone()[0]
    outstanding = (con.execute("SELECT COALESCE(SUM(opening_balance),0) FROM customers").fetchone()[0]
                   + con.execute("SELECT COALESCE(SUM(price),0) FROM orders WHERE status NOT IN ('ملغي','عرض سعر')").fetchone()[0]
                   - con.execute("SELECT COALESCE(SUM(amount),0) FROM payments").fetchone()[0])
    late = rows(con, """SELECT o.id, o.title, o.due_date, o.status, c.name AS customer_name FROM orders o
        LEFT JOIN customers c ON c.id=o.customer_id
        WHERE o.due_date!='' AND o.due_date<? AND o.status NOT IN ('تم التسليم','ملغي','عرض سعر') ORDER BY o.due_date""", (today,))
    low = rows(con, """SELECT * FROM (SELECT i.name, i.unit, i.min_qty,
        COALESCE((SELECT SUM(qty) FROM stock_moves m WHERE m.item_id=i.id),0) AS qty FROM items i)
        WHERE min_qty>0 AND qty<=min_qty ORDER BY name""")
    top = rows(con, """SELECT c.name, SUM(o.price) AS total FROM orders o JOIN customers c ON c.id=o.customer_id
        WHERE o.status NOT IN ('ملغي','عرض سعر') GROUP BY c.id ORDER BY total DESC LIMIT 5""")
    by_cat = rows(con, """SELECT category, SUM(amount) AS total FROM expenses WHERE substr(exp_date,1,7)=?
        GROUP BY category ORDER BY total DESC""", (month,))
    q = con.execute("SELECT COUNT(*), COALESCE(SUM(price),0) FROM orders WHERE status='عرض سعر'").fetchone()
    return {"month": month, "quotes_count": q[0], "quotes_total": q[1], "orders_count": s[2], "sales": s[0], "orders_cost": s[1],
            "gross_profit": s[0] - s[1], "collected": collected, "expenses": expenses,
            "net_profit": s[0] - s[1] - expenses, "outstanding": outstanding,
            "late": late, "low_stock": low, "top_customers": top, "expenses_by_category": by_cat}


def sync_order_stock(con, oid):
    """يعيد بناء حركات الخصم التلقائي للأوردر حسب خاماته وحالته. يرجع تحذيرات لو الرصيد بقى بالسالب."""
    o = con.execute("SELECT status, order_date FROM orders WHERE id=?", (oid,)).fetchone()
    con.execute("DELETE FROM stock_moves WHERE order_id=? AND auto=1", (oid,))
    warns = []
    if not o or o["status"] in NO_STOCK:
        return warns
    day = o["order_date"] or datetime.date.today().isoformat()
    for l in con.execute("SELECT * FROM order_materials WHERE order_id=? AND item_id IS NOT NULL", (oid,)).fetchall():
        con.execute("""INSERT INTO stock_moves (item_id,move_date,qty,order_id,notes,auto,unit_cost)
            VALUES (?,?,?,?,?,1,?)""", (l["item_id"], day, -l["qty"], oid, "خصم تلقائي من أوردر #%d" % oid, l["unit_cost"]))
        bal = con.execute("SELECT COALESCE(SUM(qty),0) FROM stock_moves WHERE item_id=?", (l["item_id"],)).fetchone()[0]
        if bal < 0:
            nm = con.execute("SELECT name FROM items WHERE id=?", (l["item_id"],)).fetchone()["name"]
            w = "رصيد (%s) بقى بالسالب: %g" % (nm, bal)
            if w not in warns:
                warns.append(w)
    return warns


def save_materials(con, oid, mats):
    """يحفظ خامات الأوردر (أصناف من المخزن + بنود من برة المخزن) ويرجع إجمالي تكلفتها (None لو مفيش)."""
    old = {r["item_id"]: r["unit_cost"] for r in con.execute(
        "SELECT item_id, unit_cost FROM order_materials WHERE order_id=? AND item_id IS NOT NULL", (oid,))}
    con.execute("DELETE FROM order_materials WHERE order_id=?", (oid,))
    merged, ext = {}, []
    for m in mats:
        try:
            q = float(m.get("qty") or 0)
            raw = m.get("item_id")
            iid = int(raw) if raw not in (None, "") else None
            uc, sp = float(m.get("unit_cost") or 0), float(m.get("sell_price") or 0)
        except (TypeError, ValueError):
            raise ValueError("بيانات الخامات غير صحيحة")
        if q <= 0:
            continue
        if iid is None:
            nm = str(m.get("name") or "").strip()
            if not nm:
                raise ValueError("اكتب اسم البند اللي من برة المخزن")
            if uc < 0 or sp < 0:
                raise ValueError("الأسعار لازم تكون أكبر من أو تساوي صفر")
            ext.append((nm, q, uc, sp))
        else:
            merged[iid] = merged.get(iid, 0) + q
    total = 0.0
    for iid, q in merged.items():
        uc = old.get(iid)
        if uc is None:
            it = con.execute("SELECT unit_cost FROM items WHERE id=?", (iid,)).fetchone()
            if not it:
                raise ValueError("صنف غير موجود في الخامات")
            uc = it["unit_cost"] or 0
        con.execute("INSERT INTO order_materials (order_id,item_id,qty,unit_cost) VALUES (?,?,?,?)", (oid, iid, q, uc))
        total += q * uc
    for nm, q, uc, sp in ext:
        con.execute("INSERT INTO order_materials (order_id,item_id,qty,unit_cost,name,sell_price) VALUES (?,NULL,?,?,?,?)",
                    (oid, q, uc, nm, sp))
        total += q * uc
    return total if (merged or ext) else None


def cust_totals(con, cid):
    """(حساب سابق، إجمالي الأوردرات، إجمالي المدفوع) للعميل"""
    op = con.execute("SELECT COALESCE(opening_balance,0) FROM customers WHERE id=?", (cid,)).fetchone()
    tot = con.execute("SELECT COALESCE(SUM(price),0) FROM orders WHERE customer_id=? AND status NOT IN ('ملغي','عرض سعر')", (cid,)).fetchone()[0]
    paid = con.execute("SELECT COALESCE(SUM(amount),0) FROM payments WHERE customer_id=?", (cid,)).fetchone()[0]
    return (op[0] if op else 0), tot, paid


def orders_list(con):
    data = rows(con, LIST_SQL["orders"])
    mats = {}
    for m in rows(con, "SELECT order_id,item_id,qty,unit_cost,name,sell_price FROM order_materials"):
        mats.setdefault(m["order_id"], []).append(m)
    for o in data:
        o["materials"] = mats.get(o["id"], [])
    return data


PRINT_CSS = """<style>
body{font-family:Tahoma,Arial,sans-serif;direction:rtl;margin:30px;color:#111}
h1{margin:0 0 4px}h2{margin:18px 0 6px}.muted{color:#555;font-size:14px}
table{width:100%;border-collapse:collapse;margin-top:8px}
th,td{border:1px solid #999;padding:6px 8px;text-align:right}th{background:#eee}
.tot td{font-weight:bold;background:#f6f6f6}.head{display:flex;justify-content:space-between;border-bottom:2px solid #000;padding-bottom:10px;margin-bottom:14px}
@media print{.noprint{display:none}}</style>"""


def settings(con):
    return {r["key"]: r["value"] for r in con.execute("SELECT * FROM settings")}


def press_header(st, title):
    e = html.escape
    return (f"<div class='head'><div><h1>{e(st['press_name'])}</h1>"
            f"<div class='muted'>{e(st['press_phone'])} {e(st['press_address'])}</div></div>"
            f"<div><h1>{title}</h1><div class='muted'>{datetime.date.today().isoformat()}</div></div></div>")


def invoice_html(con, oid, role="admin"):
    e = html.escape
    o = con.execute("""SELECT o.*, c.name cname, c.phone cphone, c.address caddr FROM orders o
        LEFT JOIN customers c ON c.id=o.customer_id WHERE o.id=?""", (oid,)).fetchone()
    if not o:
        return "<h3>الأوردر غير موجود</h3>"
    st = settings(con)
    op, tot, paid = cust_totals(con, o["customer_id"])
    balance = op + tot - paid                       # رصيد العميل الحالي
    counted = o["status"] not in NO_STOCK
    previous = balance - (o["price"] if counted else 0)   # الحساب السابق قبل الفاتورة دي
    due = previous + o["price"]
    return (f"<html lang='ar' dir='rtl'><head><meta charset='utf-8'><title>فاتورة {oid}</title>{PRINT_CSS}</head><body>"
            + press_header(st, f"فاتورة رقم {oid}")
            + f"<p><b>العميل:</b> {e(o['cname'] or '')} &nbsp; {e(o['cphone'] or '')}<br>{e(o['caddr'] or '')}</p>"
            f"<table><tr><th>البيان</th><th>الكمية</th><th>تاريخ الأوردر</th><th>تاريخ التسليم</th><th>السعر</th></tr>"
            f"<tr><td>{e(o['title'])}</td><td>{o['qty']:g}</td><td>{e(o['order_date'])}</td><td>{e(o['due_date'])}</td><td>{money(o['price'])}</td></tr>"
            f"<tr class='tot'><td colspan='4'>قيمة هذه الفاتورة</td><td>{money(o['price'])}</td></tr></table>"
            + (f"<h2>حساب العميل</h2><table>"
            f"<tr><td>الحساب السابق</td><td>{money(previous)}</td></tr>"
            f"<tr><td>قيمة هذه الفاتورة</td><td>{money(o['price'])}</td></tr>"
            f"<tr class='tot'><td>إجمالي المستحق</td><td>{money(due)}</td></tr></table>" if role != "staff" else "")
            + (f"<p>ملاحظات: {e(o['notes'])}</p>" if o["notes"] else "")
            + "<p class='noprint'><button onclick='print()'>طباعة</button></p></body></html>")


def quote_html(con, oid):
    e = html.escape
    o = con.execute("""SELECT o.*, c.name cname, c.phone cphone, c.address caddr FROM orders o
        LEFT JOIN customers c ON c.id=o.customer_id WHERE o.id=?""", (oid,)).fetchone()
    if not o:
        return "<h3>الأوردر غير موجود</h3>"
    st = settings(con)
    try:
        days = int(float(st.get("quote_days") or 7))
    except ValueError:
        days = 7
    try:
        d0 = datetime.date.fromisoformat(o["order_date"])
    except ValueError:
        d0 = datetime.date.today()
    valid = (d0 + datetime.timedelta(days=days)).isoformat()
    unit = (o["price"] / o["qty"]) if o["qty"] else 0
    return (f"<html lang='ar' dir='rtl'><head><meta charset='utf-8'><title>عرض سعر {oid}</title>{PRINT_CSS}</head><body>"
            + press_header(st, f"عرض سعر رقم {oid}")
            + f"<p><b>السادة:</b> {e(o['cname'] or '')} &nbsp; {e(o['cphone'] or '')}<br>{e(o['caddr'] or '')}</p>"
            f"<table><tr><th>البيان</th><th>الكمية</th><th>سعر الوحدة</th><th>الإجمالي</th></tr>"
            f"<tr><td>{e(o['title'])}</td><td>{o['qty']:g}</td><td>{money(unit)}</td><td>{money(o['price'])}</td></tr>"
            f"<tr class='tot'><td colspan='3'>الإجمالي</td><td>{money(o['price'])}</td></tr></table>"
            f"<p><b>مدة سريان العرض:</b> {days} يوم (حتى {valid})</p>"
            + (f"<p><b>مدة التنفيذ:</b> حتى {e(o['due_date'])}</p>" if o["due_date"] else "")
            + (f"<p>{e(o['notes'])}</p>" if o["notes"] else "")
            + f"<p class='muted'>{e(st.get('quote_terms',''))}</p>"
            + "<p class='noprint'><button onclick='print()'>طباعة</button></p></body></html>")


def ledger(con, cid):
    """حركات العميل مرتبة بالتاريخ: [(date, kind, id, desc, debit, credit)] + الحساب السابق"""
    c = con.execute("SELECT * FROM customers WHERE id=?", (cid,)).fetchone()
    ev = []
    for o in rows(con, "SELECT * FROM orders WHERE customer_id=? AND status NOT IN ('ملغي','عرض سعر')", (cid,)):
        ev.append((o["order_date"] or "", 0, o["id"], f"أوردر #{o['id']} - {o['title']}", o["price"], 0))
    for p in rows(con, "SELECT * FROM payments WHERE customer_id=?", (cid,)):
        ev.append((p["pay_date"] or "", 1, p["id"], "دفعة" + (f" ({p['method']})" if p["method"] else ""), 0, p["amount"]))
    ev.sort(key=lambda x: x[:3])
    return c, ev


def wa_phone(raw, cc):
    """يجهّز الرقم لواتساب بالصيغة الدولية (01012345678 -> 201012345678)"""
    d = "".join(ch for ch in str(raw or "") if ch.isdigit())
    if d.startswith("00"):
        d = d[2:]
    elif d.startswith("0"):
        d = (cc or "20") + d[1:]
    return d


def statement_text(con, cid, keep=15):
    c, ev = ledger(con, cid)
    if not c:
        raise ValueError("العميل غير موجود")
    st = settings(con)
    bal = c["opening_balance"] or 0
    lines = []
    for d, _, _, desc, debit, credit in ev:
        bal += debit - credit
        lines.append((d, desc, debit, credit, bal))
    data_rows = [{"date": d, "desc": desc, "debit": debit, "credit": credit, "bal": b} for d, desc, debit, credit, b in lines]
    opening = c["opening_balance"] or 0
    out = [f"*{st['press_name']}*", f"كشف حساب: {c['name']}", f"التاريخ: {datetime.date.today().isoformat()}", ""]
    if len(lines) > keep:
        out.append(f"(آخر {keep} حركة)")
        shown = lines[-keep:]
        out.append(f"الرصيد قبلها: {money(shown[0][4] - shown[0][2] + shown[0][3])}")
    else:
        shown = lines
        if opening:
            out.append(f"حساب سابق: {money(opening)}")
    for d, desc, debit, credit, b in shown:
        out.append(f"{d} - {desc}: " + (f"عليه {money(debit)}" if debit else f"دفع {money(credit)}"))
    out += ["", f"*المتبقي: {money(bal)} جنيه*"]
    if st.get("press_phone"):
        out.append(f"للاستفسار: {st['press_phone']}")
    return {"text": "\n".join(out), "phone": wa_phone(c["phone"], st.get("country_code")), "name": c["name"],
            "rows": data_rows, "opening": opening, "balance": bal,
            "press_name": st["press_name"], "press_phone": st.get("press_phone", ""),
            "date": datetime.date.today().isoformat()}


def invoice_data(con, oid, role):
    """بيانات الفاتورة لرسمها كصورة وإرسالها واتساب. الموظف ميشوفش حساب العميل."""
    o = con.execute("""SELECT o.*, c.name cname, c.phone cphone FROM orders o
        LEFT JOIN customers c ON c.id=o.customer_id WHERE o.id=?""", (oid,)).fetchone()
    if not o:
        raise ValueError("الأوردر غير موجود")
    st = settings(con)
    op, tot, paid = cust_totals(con, o["customer_id"])
    counted = o["status"] not in NO_STOCK
    previous = op + tot - paid - (o["price"] if counted else 0)
    show = role != "staff"
    return {"id": o["id"], "name": o["cname"] or "", "phone": wa_phone(o["cphone"], st.get("country_code")),
            "press_name": st["press_name"], "press_phone": st.get("press_phone", ""),
            "press_address": st.get("press_address", ""), "title": o["title"], "qty": o["qty"],
            "order_date": o["order_date"], "due_date": o["due_date"], "price": o["price"], "notes": o["notes"],
            "show_account": show, "previous": previous if show else 0, "due": previous + o["price"] if show else 0}


def statement_html(con, cid):
    e = html.escape
    c, ev = ledger(con, cid)
    if not c:
        return "<h3>العميل غير موجود</h3>"
    st = settings(con)
    bal = c["opening_balance"] or 0
    tr = f"<tr><td></td><td>حساب سابق (رصيد أول المدة)</td><td></td><td></td><td>{money(bal)}</td></tr>"
    td = tc = 0
    for d, _, _, desc, debit, credit in ev:
        bal += debit - credit; td += debit; tc += credit
        tr += (f"<tr><td>{e(d)}</td><td>{e(desc)}</td><td>{money(debit) if debit else ''}</td>"
               f"<td>{money(credit) if credit else ''}</td><td>{money(bal)}</td></tr>")
    return (f"<html lang='ar' dir='rtl'><head><meta charset='utf-8'><title>كشف حساب</title>{PRINT_CSS}</head><body>"
            + press_header(st, "كشف حساب عميل")
            + f"<p><b>العميل:</b> {e(c['name'])} &nbsp; {e(c['phone'])}</p>"
            f"<table><tr><th>التاريخ</th><th>البيان</th><th>مدين (أوردرات)</th><th>دائن (مدفوعات)</th><th>الرصيد</th></tr>{tr}"
            f"<tr class='tot'><td colspan='2'>الإجمالي</td><td>{money(td)}</td><td>{money(tc)}</td><td>{money(bal)}</td></tr></table>"
            f"<p><b>المتبقي على العميل: {money(bal)}</b></p>"
            "<p class='noprint'><button onclick='print()'>طباعة</button></p></body></html>")


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def reply(self, code, body, ctype="application/json; charset=utf-8", headers=None):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False)
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (headers or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def payload(self):
        n = int(self.headers.get("Content-Length") or 0)
        return json.loads(self.rfile.read(n) or b"{}")

    # ----- الجلسات -----
    def current_user(self, con):
        ck = self.headers.get("Cookie") or ""
        tok = None
        for part in ck.split(";"):
            k, _, v = part.strip().partition("=")
            if k == "sid":
                tok = v
        sess = SESSIONS.get(tok)
        if not sess or sess["exp"] < time.time():
            SESSIONS.pop(tok, None)
            return None
        u = con.execute("SELECT id,username,full_name,role,active FROM users WHERE id=?", (sess["uid"],)).fetchone()
        if not u or not u["active"]:
            return None
        sess["exp"] = time.time() + 12 * 3600
        return dict(u)

    def start_session(self, uid):
        tok = secrets.token_hex(24)
        SESSIONS[tok] = {"uid": uid, "exp": time.time() + 12 * 3600}
        return {"Set-Cookie": "sid=%s; HttpOnly; SameSite=Strict; Path=/%s" % (tok, "; Secure" if HTTPS else "")}

    def handle_any(self, method):
        u = urlparse(self.path)
        q = parse_qs(u.query)
        parts = [p for p in u.path.split("/") if p]
        con = db()
        try:
            if method == "GET" and not parts:
                return self.reply(200, INDEX_HTML, "text/html; charset=utf-8")
            if parts[:1] == ["api"] and len(parts) == 2 and parts[1] in ("me", "login", "setup", "logout"):
                return self.auth_routes(con, method, parts[1])
            me = self.current_user(con)
            if parts and parts[0] in ("invoice", "statement", "quote"):
                if not me:
                    return self.reply(401, "<h3>سجّل دخول الأول من الصفحة الرئيسية</h3>", "text/html; charset=utf-8")
                if parts[0] == "statement" and me["role"] == "staff":
                    return self.reply(403, "<h3>غير مسموح</h3>", "text/html; charset=utf-8")
                rid = int(q.get("id", [0])[0])
                fn = {"invoice": invoice_html, "statement": statement_html, "quote": quote_html}[parts[0]]
                page = fn(con, rid, me["role"]) if parts[0] == "invoice" else fn(con, rid)
                return self.reply(200, page, "text/html; charset=utf-8")
            if parts[:1] != ["api"]:
                return self.reply(404, {"error": "not found"})
            if not me:
                return self.reply(401, {"error": "login"})
            name = parts[1] if len(parts) > 1 else ""
            if not can(me["role"], name, method):
                return self.reply(403, {"error": "مش مسموح لك بالعملية دي"})
            role = me["role"]
            if name == "dashboard":
                m = q.get("month", [datetime.date.today().strftime("%Y-%m")])[0]
                return self.reply(200, dashboard(con, m))
            if name == "settings":
                if method == "PUT":
                    for k, v in self.payload().items():
                        if k in SETTING_KEYS:
                            con.execute("INSERT OR REPLACE INTO settings VALUES (?,?)", (k, str(v)))
                    con.commit()
                return self.reply(200, settings(con))
            if name == "backup":
                fd, tmp = tempfile.mkstemp(suffix=".db"); os.close(fd)
                dst = sqlite3.connect(tmp); con.backup(dst); dst.close()
                data = open(tmp, "rb").read(); os.remove(tmp)
                fn = "press-backup-%s.db" % datetime.date.today().isoformat()
                return self.reply(200, data, "application/octet-stream",
                                  {"Content-Disposition": f'attachment; filename="{fn}"'})
            if name == "restore" and method == "POST":
                return self.restore_backup(con)
            if name == "users":
                return self.users_routes(con, method, parts, me)
            if name == "invoice_data" and method == "GET":
                return self.reply(200, invoice_data(con, int(q.get("id", [0])[0]), role))
            if name == "statement_text" and method == "GET":
                return self.reply(200, statement_text(con, int(q.get("id", [0])[0])))
            if name not in TABLES:
                return self.reply(404, {"error": "not found"})
            rid = int(parts[2]) if len(parts) > 2 else None
            cols = [c for c, _ in TABLES[name]]

            if method == "GET":
                data = orders_list(con) if name == "orders" else rows(con, LIST_SQL[name])
                return self.reply(200, scrub(role, name, data))

            # اعتماد عرض السعر
            if method == "POST" and name == "orders" and len(parts) > 3 and parts[3] == "approve":
                con.execute("UPDATE orders SET status='جديد' WHERE id=? AND status='عرض سعر'", (rid,))
                warns = sync_order_stock(con, rid)
                con.commit()
                return self.reply(200, {"ok": True, "warnings": warns})

            if name == "stock_moves" and rid and method in ("PUT", "DELETE"):
                r0 = con.execute("SELECT auto FROM stock_moves WHERE id=?", (rid,)).fetchone()
                if r0 and r0["auto"]:
                    return self.reply(400, {"error": "دي حركة تلقائية، عدّلها من الأوردر نفسه."})

            if method in ("POST", "PUT"):
                body = self.payload()
                d = coerce(name, body)
                mats = body.get("materials") if name == "orders" else None
                if name == "orders" and role == "staff":
                    old = con.execute("SELECT * FROM orders WHERE id=?", (rid,)).fetchone() if method == "PUT" else None
                    for c in COST_COLS:
                        d[c] = old[c] if old else 0.0
                if name == "customers" and role == "staff":
                    old = con.execute("SELECT opening_balance FROM customers WHERE id=?", (rid,)).fetchone() if method == "PUT" else None
                    d["opening_balance"] = (old["opening_balance"] or 0) if old else 0.0
                if method == "POST":
                    cur = con.execute(f"INSERT INTO {name} ({','.join(cols)}) VALUES ({','.join('?' * len(cols))})",
                                      [d[c] for c in cols])
                    rid = cur.lastrowid
                else:
                    con.execute(f"UPDATE {name} SET {','.join(c + '=?' for c in cols)} WHERE id=?",
                                [d[c] for c in cols] + [rid])
                warns = []
                if name == "orders":
                    if mats is not None:
                        t = save_materials(con, rid, mats)
                        if t is not None:
                            con.execute("UPDATE orders SET material_cost=? WHERE id=?", (t, rid))
                    warns = sync_order_stock(con, rid)
                con.commit()
                return self.reply(200, {"id": rid, "warnings": warns})

            if method == "DELETE":
                for sql, msg in DELETE_GUARD.get(name, []):
                    if con.execute(sql, (rid,)).fetchone()[0]:
                        return self.reply(400, {"error": msg})
                if name == "orders":
                    con.execute("DELETE FROM stock_moves WHERE order_id=? AND auto=1", (rid,))
                    con.execute("DELETE FROM order_materials WHERE order_id=?", (rid,))
                con.execute(f"DELETE FROM {name} WHERE id=?", (rid,))
                con.commit()
                return self.reply(200, {"ok": True})
        except ValueError as ex:
            self.reply(400, {"error": str(ex)})
        except Exception as ex:  # noqa
            self.reply(500, {"error": "خطأ: %s" % ex})
        finally:
            con.close()

    def restore_backup(self, con):
        """استعادة نسخة احتياطية (ملف press.db) - للمدير فقط. بتستبدل كل البيانات الحالية."""
        n = int(self.headers.get("Content-Length") or 0)
        if n < 100 or n > 200 * 1024 * 1024:
            raise ValueError("الملف غير صالح")
        data = self.rfile.read(n)
        if not data.startswith(b"SQLite format 3\x00"):
            raise ValueError("الملف ده مش نسخة احتياطية صحيحة")
        fd, tmp = tempfile.mkstemp(suffix=".db")
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(data)
            src = sqlite3.connect(tmp)
            try:
                names = {r[0] for r in src.execute("SELECT name FROM sqlite_master WHERE type='table'")}
                if not {"customers", "orders", "payments", "users"} <= names:
                    raise ValueError("الملف ده مش نسخة احتياطية من البرنامج ده")
                if src.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
                    raise ValueError("الملف تالف")
                if not src.execute("SELECT COUNT(*) FROM users WHERE role='admin' AND active=1").fetchone()[0]:
                    raise ValueError("النسخة دي مفيهاش مدير نشط، مش هينفع تدخل بعد الاستعادة")
                con.rollback()
                src.backup(con)
            finally:
                src.close()
        finally:
            os.remove(tmp)
        SESSIONS.clear()
        init_db()                                   # ترقية شكل الجداول لو النسخة قديمة
        return self.reply(200, {"ok": True})

    def auth_routes(self, con, method, what):
        if what == "me":
            me = self.current_user(con)
            n = con.execute("SELECT COUNT(*) FROM users").fetchone()[0]
            return self.reply(200, {"user": me, "needs_setup": n == 0})
        if what == "logout":
            ck = self.headers.get("Cookie") or ""
            for part in ck.split(";"):
                k, _, v = part.strip().partition("=")
                if k == "sid":
                    SESSIONS.pop(v, None)
            return self.reply(200, {"ok": True}, headers={"Set-Cookie": "sid=; Max-Age=0; Path=/"})
        if method != "POST":
            return self.reply(405, {"error": "method"})
        d = self.payload()
        un, pw = str(d.get("username", "")).strip(), str(d.get("password", ""))
        if what == "setup":
            if con.execute("SELECT COUNT(*) FROM users").fetchone()[0]:
                return self.reply(400, {"error": "تم الإعداد قبل كده"})
            if not un or len(pw) < 6:
                return self.reply(400, {"error": "اسم المستخدم مطلوب وكلمة المرور 6 حروف على الأقل"})
            cur = con.execute("INSERT INTO users (username,password_hash,full_name,role,active) VALUES (?,?,?,?,1)",
                              (un, hash_pw(pw), str(d.get("full_name", "")).strip(), "admin"))
            con.commit()
            return self.reply(200, {"ok": True}, headers=self.start_session(cur.lastrowid))
        # login
        ip = self.client_address[0]
        if PROXY:
            ip = (self.headers.get("Fly-Client-IP") or (self.headers.get("X-Forwarded-For") or "").split(",")[0].strip() or ip)
        cnt, until = FAILS.get(ip, (0, 0))
        if until > time.time():
            return self.reply(429, {"error": "محاولات كتير غلط، استنى دقيقة وحاول تاني"})
        u = con.execute("SELECT * FROM users WHERE username=?", (un,)).fetchone()
        if not u or not u["active"] or not check_pw(pw, u["password_hash"]):
            cnt += 1
            FAILS[ip] = (cnt, time.time() + 60 if cnt >= 5 else 0)
            if cnt >= 5:
                FAILS[ip] = (0, time.time() + 60)
            return self.reply(401, {"error": "اسم المستخدم أو كلمة المرور غلط"})
        FAILS.pop(ip, None)
        return self.reply(200, {"ok": True}, headers=self.start_session(u["id"]))

    def users_routes(self, con, method, parts, me):
        rid = int(parts[2]) if len(parts) > 2 else None
        if method == "GET":
            return self.reply(200, rows(con, "SELECT id,username,full_name,role,active FROM users ORDER BY id"))
        if method == "DELETE":
            if rid == me["id"]:
                return self.reply(400, {"error": "مينفعش تحذف حسابك."})
            self.ensure_admin_left(con, rid, None, 0)
            con.execute("DELETE FROM users WHERE id=?", (rid,))
            con.commit()
            return self.reply(200, {"ok": True})
        d = self.payload()
        un, pw = str(d.get("username", "")).strip(), str(d.get("password", ""))
        role = d.get("role")
        active = 1 if str(d.get("active", "1")) == "1" else 0
        if not un or role not in ROLES:
            raise ValueError("اسم المستخدم والصلاحية مطلوبين")
        if method == "POST":
            if len(pw) < 6:
                raise ValueError("كلمة المرور 6 حروف على الأقل")
            if con.execute("SELECT 1 FROM users WHERE username=?", (un,)).fetchone():
                raise ValueError("اسم المستخدم موجود قبل كده")
            cur = con.execute("INSERT INTO users (username,password_hash,full_name,role,active) VALUES (?,?,?,?,?)",
                              (un, hash_pw(pw), str(d.get("full_name", "")).strip(), role, active))
            con.commit()
            return self.reply(200, {"id": cur.lastrowid})
        if con.execute("SELECT 1 FROM users WHERE username=? AND id!=?", (un, rid)).fetchone():
            raise ValueError("اسم المستخدم موجود قبل كده")
        self.ensure_admin_left(con, rid, role, active)
        con.execute("UPDATE users SET username=?, full_name=?, role=?, active=? WHERE id=?",
                    (un, str(d.get("full_name", "")).strip(), role, active, rid))
        if pw:
            if len(pw) < 6:
                raise ValueError("كلمة المرور 6 حروف على الأقل")
            con.execute("UPDATE users SET password_hash=? WHERE id=?", (hash_pw(pw), rid))
        con.commit()
        for tok in [t for t, s_ in SESSIONS.items() if s_["uid"] == rid and (pw or not active)]:
            SESSIONS.pop(tok, None)
        return self.reply(200, {"ok": True})

    def ensure_admin_left(self, con, rid, new_role, new_active):
        """لازم يفضل مدير نشط واحد على الأقل"""
        u = con.execute("SELECT role FROM users WHERE id=?", (rid,)).fetchone()
        if u and u["role"] == "admin" and (new_role != "admin" or not new_active):
            n = con.execute("SELECT COUNT(*) FROM users WHERE role='admin' AND active=1 AND id!=?", (rid,)).fetchone()[0]
            if n == 0:
                raise ValueError("لازم يفضل مدير نشط واحد على الأقل.")

    def do_GET(self): self.handle_any("GET")
    def do_POST(self): self.handle_any("POST")
    def do_PUT(self): self.handle_any("PUT")
    def do_DELETE(self): self.handle_any("DELETE")


INDEX_HTML = r"""<!doctype html>
<html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="المطبعة">
<meta name="theme-color" content="#22553F">
<title>حسابات المطبعة</title>
<style>
:root{--g:#22553F;--bg:#f4f6f5;--bd:#d5dbd8}
*{box-sizing:border-box}
body{margin:0;font-family:Tahoma,"Segoe UI",Arial,sans-serif;background:var(--bg);color:#1c1c1c}
header{background:var(--g);color:#fff;padding:12px 20px;display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap}
header h1{margin:0;font-size:20px}
header .u{display:flex;gap:10px;align-items:center;font-size:14px}
header button{background:#ffffff22;color:#fff;border:1px solid #ffffff55;border-radius:6px;padding:4px 10px;cursor:pointer;font:inherit}
nav{display:flex;flex-wrap:wrap;gap:6px;padding:10px 20px;background:#fff;border-bottom:1px solid var(--bd)}
nav button{border:1px solid var(--bd);background:#fff;padding:8px 14px;border-radius:8px;cursor:pointer;font:inherit}
nav button.on{background:var(--g);color:#fff;border-color:var(--g)}
main{padding:18px 20px;max-width:1300px;margin:auto}
.bar{display:flex;gap:10px;align-items:center;margin-bottom:12px;flex-wrap:wrap}
.bar h2{margin:0;flex:1}
input,select,textarea{font:inherit;padding:7px 9px;border:1px solid var(--bd);border-radius:7px;width:100%;background:#fff}
input[readonly]{background:#eef2f0}
.bar input{width:220px}
button.p{background:var(--g);color:#fff;border:0;padding:8px 16px;border-radius:8px;cursor:pointer;font:inherit}
button.s{background:#fff;border:1px solid var(--bd);padding:4px 9px;border-radius:6px;cursor:pointer;font:inherit;font-size:13px}
button.d{color:#b00020}
.wrap{overflow:auto;background:#fff;border:1px solid var(--bd);border-radius:10px}
table{border-collapse:collapse;width:100%;font-size:14px}
th,td{padding:8px 10px;border-bottom:1px solid #eceeed;text-align:right;white-space:nowrap}
th{background:#eef2f0;position:sticky;top:0}
td.num{direction:ltr;text-align:left}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:12px;margin-bottom:16px}
.card{background:#fff;border:1px solid var(--bd);border-radius:10px;padding:14px}
.card small{color:#666}.card b{display:block;font-size:22px;margin-top:4px;direction:ltr;text-align:right}
.neg{color:#b00020}.pos{color:#1b7a3e}
.grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:14px}
.box{background:#fff;border:1px solid var(--bd);border-radius:10px;padding:12px}
.box h3{margin:0 0 8px;font-size:16px}
.badge{padding:2px 8px;border-radius:10px;background:#e9eeec;font-size:12px}
.badge.q{background:#fff3cd}
.modal{position:fixed;inset:0;background:#0006;display:flex;align-items:center;justify-content:center;padding:14px;z-index:5}
.modal form{background:#fff;border-radius:12px;padding:18px;width:min(720px,100%);max-height:92vh;overflow:auto}
.fields{display:grid;grid-template-columns:1fr 1fr;gap:10px}
.fields .full{grid-column:1/-1}
label{font-size:13px;color:#444;display:block;margin-bottom:3px}
.hint{background:#eef7f1;border-radius:8px;padding:8px 10px;font-size:14px;margin-top:10px}
.calc{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.calc input{width:90px}
.mrow{display:grid;grid-template-columns:1fr 110px 36px;gap:6px;margin-bottom:6px}
.mrow.ext{grid-template-columns:1fr 78px 92px 92px 36px}
.mrow.ext .mn{min-width:0}
@media(max-width:620px){.mrow.ext{grid-template-columns:1fr 1fr 1fr}.mrow.ext .mn{grid-column:1/-1}}
.mbox{border:1px dashed var(--bd);border-radius:8px;padding:10px}
.actions{display:flex;gap:8px;margin-top:14px;justify-content:flex-start}
.auth{background:var(--bg)}
.auth form{width:min(380px,100%)}
.err{color:#b00020;min-height:20px;font-size:14px}
</style></head><body>
<header><h1 id="pname">حسابات المطبعة</h1><div class="u" id="userbox"></div></header>
<nav id="nav"></nav>
<main id="main"></main>
<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const money=v=>(+v||0).toLocaleString('en-US',{minimumFractionDigits:2,maximumFractionDigits:2});
const todayStr=()=>new Date().toISOString().slice(0,10);
let ME=null,ST={};
async function api(m,u,b){
  const r=await fetch(u,{method:m,headers:{'Content-Type':'application/json'},body:b?JSON.stringify(b):undefined});
  const j=await r.json().catch(()=>({}));
  if(r.status===401&&!u.startsWith('/api/login')){authScreen('login');throw new Error('سجّل دخول الأول');}
  if(!r.ok) throw new Error(j.error||'حصل خطأ');
  return j;
}
const STATUS=['عرض سعر','جديد','تحت التنفيذ','جاهز','تم التسليم','ملغي'];
const CATS=['مرتبات','إيجار','كهرباء ومياه','صيانة ماكينات','خامات','نقل','أخرى'];
const METHODS=['كاش','تحويل بنكي','شيك','فودافون كاش'];
const ROLEN={admin:'مدير',accountant:'محاسب',staff:'موظف'};
const REF={customers:[],orders:[],items:[]};
const refOpts={
  customers:()=>REF.customers.map(c=>[c.id,c.name]),
  orders:()=>REF.orders.map(o=>[o.id,'#'+o.id+' - '+o.title+' - '+(o.customer_name||'')]),
  items:()=>REF.items.map(i=>[i.id,i.name])
};
const sel=a=>()=>a.map(x=>[x,x]);
const isStaff=()=>ME&&ME.role==='staff';
const PERM_STAFF={customers:'cu',orders:'cu',items:'',stock_moves:'c'};
const can=(t,a)=>!isStaff()||(PERM_STAFF[t]||'').includes(a);

const ENT={
 customers:{title:'العملاء',search:1,
  fields:[{k:'name',l:'الاسم',req:1},{k:'phone',l:'التليفون'},{k:'address',l:'العنوان'},{k:'opening_balance',l:'حساب سابق (رصيد أول المدة)',t:'number',fin:1},{k:'notes',l:'ملاحظات',t:'textarea',full:1}],
  cols:[['الاسم',r=>esc(r.name)],['التليفون',r=>esc(r.phone)],['حساب سابق',r=>money(r.opening_balance),'num',0,1],['إجمالي الأوردرات',r=>money(r.total),'num',0,1],['المدفوع',r=>money(r.paid),'num',0,1],
        ['المتبقي',r=>`<span class="${r.balance>0?'neg':'pos'}">${money(r.balance)}</span>`,'num',1,1]],
  extra:r=>isStaff()?'':`<button class="s" onclick="payForCustomer(${r.id})">+ دفعة</button> <button class="s" onclick="window.open('/statement?id=${r.id}')">كشف حساب</button> <button class="s" onclick="sendWA(${r.id})">واتساب</button>`},
 orders:{title:'أوامر الشغل',search:1,
  fields:[{k:'customer_id',l:'العميل',t:'select',opts:refOpts.customers,req:1},{k:'title',l:'وصف الشغل',req:1},
   {k:'qty',l:'الكمية',t:'number',def:1},{k:'status',l:'الحالة',t:'select',opts:sel(STATUS),def:'جديد'},
   {k:'order_date',l:'تاريخ الأوردر',t:'date',def:'today'},{k:'due_date',l:'تاريخ التسليم',t:'date'},
   {k:'material_cost',l:'تكلفة الخامات',t:'number',fin:1},{k:'labor_cost',l:'تكلفة التشغيل',t:'number',fin:1},
   {k:'finishing_cost',l:'تكلفة التشطيب',t:'number',fin:1},{k:'other_cost',l:'تكاليف أخرى',t:'number',fin:1},
   {k:'price',l:'سعر البيع',t:'number'},{k:'notes',l:'ملاحظات',t:'textarea',full:1}],
  cols:[['#',r=>r.id],['العميل',r=>esc(r.customer_name)],['الشغل',r=>esc(r.title)],['الكمية',r=>r.qty,'num'],
   ['الحالة',r=>`<span class="badge ${r.status==='عرض سعر'?'q':''}">${esc(r.status)}</span>`],['التسليم',r=>r.due_date],
   ['السعر',r=>money(r.price),'num'],
   ['الربح',r=>money(r.price-(r.material_cost+r.labor_cost+r.finishing_cost+r.other_cost)),'num',0,1]],
  extra:r=>`<button class="s" onclick="window.open('/quote?id=${r.id}')">عرض سعر</button> `+
    (r.status==='عرض سعر'?`<button class="s" onclick="approve(${r.id})">اعتماد</button>`:
     `<button class="s" onclick="window.open('/invoice?id=${r.id}')">فاتورة</button> <button class="s" onclick="sendInvoiceWA(${r.id})">واتساب</button>`)},
 payments:{title:'الدفعات',search:1,
  fields:[{k:'customer_id',l:'العميل',t:'select',opts:refOpts.customers,req:1},{k:'pay_date',l:'التاريخ',t:'date',def:'today'},
   {k:'amount',l:'المبلغ',t:'number',req:1},{k:'method',l:'الطريقة',t:'select',opts:sel(METHODS)},
   {k:'notes',l:'ملاحظات',t:'textarea',full:1}],
  cols:[['التاريخ',r=>r.pay_date],['العميل',r=>esc(r.customer_name)],
   ['الطريقة',r=>esc(r.method)],['المبلغ',r=>money(r.amount),'num'],['ملاحظات',r=>esc(r.notes)]]},
 expenses:{title:'المصروفات',search:1,
  fields:[{k:'exp_date',l:'التاريخ',t:'date',def:'today'},{k:'category',l:'النوع',t:'select',opts:sel(CATS)},
   {k:'description',l:'البيان',full:1},{k:'amount',l:'المبلغ',t:'number',req:1}],
  cols:[['التاريخ',r=>r.exp_date],['النوع',r=>esc(r.category)],['البيان',r=>esc(r.description)],['المبلغ',r=>money(r.amount),'num']]},
 items:{title:'المخزون - الأصناف',search:1,
  fields:[{k:'name',l:'اسم الصنف (ورق/حبر/...)',req:1},{k:'unit',l:'الوحدة (فرخ/كيلو/علبة)'},
   {k:'min_qty',l:'حد التنبيه',t:'number'},{k:'unit_cost',l:'سعر الشراء',t:'number',fin:1},{k:'sell_price',l:'سعر البيع',t:'number'},{k:'notes',l:'ملاحظات',t:'textarea',full:1}],
  cols:[['الصنف',r=>esc(r.name)],['الوحدة',r=>esc(r.unit)],['الرصيد',r=>`<span class="${r.min_qty>0&&r.qty<=r.min_qty?'neg':''}">${r.qty}</span>`,'num',1],
   ['حد التنبيه',r=>r.min_qty,'num'],['سعر الشراء',r=>money(r.unit_cost),'num',0,1],['سعر البيع',r=>money(r.sell_price),'num']],
  extra:r=>`<button class="s" onclick="moveFor(${r.id})">حركة</button>`},
 stock_moves:{title:'حركة المخزون',search:1,
  fields:[{k:'item_id',l:'الصنف',t:'select',opts:refOpts.items,req:1},{k:'dir',l:'نوع الحركة',t:'select',opts:()=>[['in','وارد (شراء)'],['out','صرف (استهلاك)']]},
   {k:'qty',l:'الكمية',t:'number',req:1},{k:'move_date',l:'التاريخ',t:'date',def:'today'},
   {k:'order_id',l:'الأوردر (اختياري)',t:'select',opts:()=>[['','—'],...refOpts.orders()]},{k:'notes',l:'ملاحظات',t:'textarea',full:1}],
  cols:[['التاريخ',r=>r.move_date],['الصنف',r=>esc(r.item_name)],['الحركة',r=>r.auto?'صرف تلقائي':(r.qty>=0?'وارد':'صرف')],
   ['الكمية',r=>Math.abs(r.qty)+' '+esc(r.unit),'num'],['أوردر',r=>r.order_id?'#'+r.order_id:''],['ملاحظات',r=>esc(r.notes)]]},
 users:{title:'المستخدمين',
  fields:[{k:'username',l:'اسم المستخدم',req:1},{k:'full_name',l:'الاسم بالكامل'},
   {k:'role',l:'الصلاحية',t:'select',opts:()=>Object.entries(ROLEN)},{k:'active',l:'الحالة',t:'select',opts:()=>[['1','نشط'],['0','موقوف']]},
   {k:'password',l:'كلمة المرور (6 حروف على الأقل - سيبها فاضية في التعديل لو مش هتغيّرها)',t:'password',full:1,pw:1}],
  cols:[['المستخدم',r=>esc(r.username)],['الاسم',r=>esc(r.full_name)],['الصلاحية',r=>ROLEN[r.role]],['الحالة',r=>r.active?'نشط':'موقوف']]}
};
const ALLTABS=[['dash','الرئيسية','admin,accountant'],['orders','أوامر الشغل','admin,accountant,staff'],
 ['customers','العملاء','admin,accountant,staff'],['payments','الدفعات','admin,accountant'],['expenses','المصروفات','admin,accountant'],
 ['items','المخزون','admin,accountant,staff'],['stock_moves','حركة المخزون','admin,accountant,staff'],
 ['users','المستخدمين','admin'],['settings','الإعدادات','admin']];
let cur='dash';
function nav(){
  $('#nav').innerHTML=ALLTABS.filter(t=>t[2].split(',').includes(ME.role)).map(([k,l])=>`<button class="${k===cur?'on':''}" onclick="go('${k}')">${l}</button>`).join('');
}
function authScreen(mode){
  document.getElementById('auth')?.remove();
  const setup=mode==='setup';
  const m=document.createElement('div');m.className='modal auth';m.id='auth';
  m.innerHTML=`<form><h3>${setup?'إعداد أول مدير للبرنامج':'تسجيل الدخول'}</h3>
   ${setup?'<label>الاسم</label><input name="full_name"><br><br>':''}
   <label>اسم المستخدم</label><input name="username" required autofocus><br><br>
   <label>كلمة المرور${setup?' (6 حروف على الأقل)':''}</label><input name="password" type="password" required><br>
   <div class="err" id="aerr"></div><div class="actions"><button class="p" type="submit">${setup?'إنشاء الحساب':'دخول'}</button></div></form>`;
  document.body.appendChild(m);
  m.querySelector('form').onsubmit=async e=>{
    e.preventDefault();const d={};new FormData(e.target).forEach((v,k)=>d[k]=v);
    try{await api('POST',setup?'/api/setup':'/api/login',d);boot();}catch(err){$('#aerr').textContent=err.message;}
  };
}
async function logout(){await api('POST','/api/logout',{});location.reload();}
async function boot(){
  const me=await fetch('/api/me').then(r=>r.json());
  if(me.needs_setup) return authScreen('setup');
  if(!me.user) return authScreen('login');
  ME=me.user;document.getElementById('auth')?.remove();
  ST=await api('GET','/api/settings');
  $('#pname').textContent=ST.press_name;document.title=ST.press_name;
  $('#userbox').innerHTML=`<span>${esc(ME.full_name||ME.username)} (${ROLEN[ME.role]})</span><button onclick="logout()">خروج</button>`;
  cur=ME.role==='staff'?'orders':'dash';nav();go(cur);
}
async function loadRefs(){
  const [c,o,i]=await Promise.all([api('GET','/api/customers'),api('GET','/api/orders'),api('GET','/api/items')]);
  REF.customers=c;REF.orders=o;REF.items=i;
}
async function go(k){cur=k;nav();$('#main').innerHTML='...';
  try{ if(k==='dash') await dash(); else if(k==='settings') await settingsPage(); else await list(k);}catch(e){$('#main').innerHTML='<p class="neg">'+esc(e.message)+'</p>';}
}
let DATA=[];
async function list(t){
  await loadRefs();
  DATA=await api('GET','/api/'+t);
  const E=ENT[t];
  $('#main').innerHTML=`<div class="bar"><h2>${E.title}</h2>${E.search?'<input id="q" placeholder="بحث..." oninput="draw(\''+t+'\')">':''}
   ${can(t,'c')?`<button class="p" onclick="openForm('${t}')">+ إضافة</button>`:''}</div><div class="wrap"><table id="tbl"></table></div>`;
  draw(t);
}
function draw(t){
  const E=ENT[t];const q=($('#q')?.value||'').trim().toLowerCase();
  const cols=E.cols.filter(c=>!(isStaff()&&c[4]));
  const rows=DATA.filter(r=>!q||JSON.stringify(Object.values(r)).toLowerCase().includes(q));
  $('#tbl').innerHTML='<tr>'+cols.map(c=>`<th>${c[0]}</th>`).join('')+'<th></th></tr>'+
   rows.map(r=>'<tr>'+cols.map(c=>`<td class="${c[2]||''}">${c[1](r)}</td>`).join('')+
   `<td>${E.extra?E.extra(r)+' ':''}${can(t,'u')&&!r.auto?`<button class="s" onclick="openForm('${t}',${r.id})">تعديل</button> `:''}${can(t,'d')&&!r.auto?`<button class="s d" onclick="del('${t}',${r.id})">حذف</button>`:''}</td></tr>`).join('')
   +(rows.length?'':`<tr><td colspan="${cols.length+1}" style="text-align:center;color:#777">لا توجد بيانات</td></tr>`);
}
async function del(t,id){
  if(!confirm('متأكد من الحذف؟'))return;
  try{await api('DELETE',`/api/${t}/${id}`);go(t);}catch(e){alert(e.message);}
}
async function approve(id){
  if(!confirm('اعتماد عرض السعر وتحويله لأوردر؟ (هيتخصم الخامات من المخزون)'))return;
  try{const j=await api('POST',`/api/orders/${id}/approve`,{});if(j.warnings&&j.warnings.length)alert('تنبيه:\n'+j.warnings.join('\n'));go('orders');}catch(e){alert(e.message);}
}
function openForm(t,id,pre){
  const E=ENT[t];let r=id?DATA.find(x=>x.id===id):{};
  r={...r,...(pre||{})};
  if(t==='stock_moves'&&id){r.dir=r.qty<0?'out':'in';r.qty=Math.abs(r.qty);}
  const fields=E.fields.filter(F=>!(isStaff()&&F.fin));
  const f=fields.map(F=>{
    let v=r[F.k]; if(F.pw)v=''; if(v==null||v===''){v=F.def==='today'?todayStr():(F.def??'');}
    let inp;
    if(F.t==='select'){inp=`<select name="${F.k}">${F.opts().map(([a,b])=>`<option value="${esc(a)}" ${String(a)===String(v)?'selected':''}>${esc(b)}</option>`).join('')}</select>`;}
    else if(F.t==='textarea'){inp=`<textarea name="${F.k}" rows="2">${esc(v)}</textarea>`;}
    else inp=`<input name="${F.k}" type="${F.t||'text'}" ${F.t==='number'?'step="any"':''} value="${esc(v)}" ${F.req&&!(F.pw&&id)?'required':''} ${F.pw?'autocomplete="new-password"':''}>`;
    return `<div class="${F.full?'full':''}"><label>${F.l}${F.req?' *':''}</label>${inp}</div>`;
  }).join('');
  const isOrd=t==='orders';
  const matBox=isOrd?`<div class="full mbox"><label>الخامات المستخدمة (أصناف المخزن بتتخصم تلقائي، والبنود اللي من برة المخزن بتدخل في التكلفة بس)</label><div id="mats"></div><div class="muted" style="font-size:12px;margin:2px 0 6px">البند من برة المخزن: الاسم ← الكمية ← سعر الشراء ← سعر البيع (للوحدة)</div><button type="button" class="s" id="addmat">+ صنف من المخزن</button> <button type="button" class="s" id="addext">+ بند من برة المخزن</button></div>`:'';
  const calc=isOrd?`<div class="hint calc" id="calc"><button type="button" class="s" id="applysp">احسب السعر من أسعار بيع الخامات</button><span id="unitp"></span></div>`+(isStaff()?'':'<div class="hint" id="hint"></div>'):'';
  const m=document.createElement('div');m.className='modal';
  m.innerHTML=`<form><h3>${id?'تعديل':'إضافة'} - ${E.title}</h3><div class="fields">${f}${matBox}</div>${calc}
   <div class="actions"><button class="p" type="submit">حفظ</button><button class="s" type="button" id="cancel">إلغاء</button></div></form>`;
  document.body.appendChild(m);
  const form=m.querySelector('form');
  const g=n=>+(form.elements[n]?.value)||0;
  function addRow(item_id,qty,uc){
    const d=document.createElement('div');d.className='mrow';
    d.innerHTML=`<select class="mi">${REF.items.map(i=>`<option value="${i.id}" data-uc="${i.unit_cost}" data-sp="${i.sell_price||0}" ${String(i.id)===String(item_id)?'selected':''}>${esc(i.name)} (رصيد ${i.qty})</option>`).join('')}</select>
     <input class="mq" type="number" step="any" min="0" placeholder="الكمية" value="${qty??''}"><button type="button" class="s d">×</button>`;
    const s=d.querySelector('.mi');
    d.dataset.uc=(uc!=null?uc:(s.selectedOptions[0]?.dataset.uc||0));
    d.dataset.sp=s.selectedOptions[0]?.dataset.sp||0;
    s.onchange=()=>{d.dataset.uc=s.selectedOptions[0].dataset.uc;d.dataset.sp=s.selectedOptions[0].dataset.sp;upd();};
    d.querySelector('button').onclick=()=>{d.remove();upd();};
    $('#mats').appendChild(d);
  }
  function addExt(x){
    x=x||{};const d=document.createElement('div');d.className='mrow ext';d.dataset.ext='1';
    d.innerHTML=`<input class="mn" placeholder="اسم البند (مش في المخزن)" value="${esc(x.name||'')}">
     <input class="mq" title="الكمية" type="number" step="any" min="0" placeholder="الكمية" value="${x.qty??''}">
     <input class="mc" title="سعر الشراء للوحدة" type="number" step="any" min="0" placeholder="سعر الشراء" value="${x.unit_cost??''}">
     <input class="ms" title="سعر البيع للوحدة" type="number" step="any" min="0" placeholder="سعر البيع" value="${x.sell_price??''}"><button type="button" class="s d">×</button>`;
    d.querySelector('button').onclick=()=>{d.remove();upd();};
    $('#mats').appendChild(d);
  }
  function rowVals(d){const q=+d.querySelector('.mq').value||0;
    return d.dataset.ext?{q,uc:+d.querySelector('.mc').value||0,sp:+d.querySelector('.ms').value||0}:{q,uc:+d.dataset.uc||0,sp:+d.dataset.sp||0};}
  function matCost(){let t=0,any=false;document.querySelectorAll('#mats .mrow').forEach(d=>{const v=rowVals(d);if(v.q>0){any=true;t+=v.q*v.uc;}});return any?t:null;}
  function sellTotal(){let t=0,any=false;document.querySelectorAll('#mats .mrow').forEach(d=>{const v=rowVals(d);if(v.q>0){any=true;t+=v.q*v.sp;}});return any?t:null;}
  function upd(){
    if(!isOrd)return;
    const mc=matCost(),mi=form.elements.material_cost;
    if(mi){mi.readOnly=mc!==null;if(mc!==null)mi.value=mc.toFixed(2);}
    const cost=g('material_cost')+g('labor_cost')+g('finishing_cost')+g('other_cost'),p=g('price'),q=g('qty');
    if($('#hint'))$('#hint').innerHTML=`إجمالي التكلفة: <b>${money(cost)}</b> &nbsp;|&nbsp; الربح: <b class="${p-cost<0?'neg':'pos'}">${money(p-cost)}</b> (${p?((p-cost)/p*100).toFixed(1):0}%)`;
    if($('#unitp'))$('#unitp').innerHTML=q?`سعر الوحدة: <b>${money(p/q)}</b>`:'';
  }
  if(isOrd){
    (r.materials||[]).forEach(x=>x.item_id?addRow(x.item_id,x.qty,x.unit_cost):addExt(x));
    $('#addmat').onclick=()=>{if(!REF.items.length){alert('مفيش أصناف في المخزون، استخدم "بند من برة المخزن"');return;}addRow();upd();};
    $('#addext').onclick=()=>{addExt();upd();};
    $('#applysp').onclick=()=>{const t=sellTotal();if(t===null){alert('ضيف خامات الأول');return;}
      if(!t&&!confirm('أسعار بيع الخامات دي صفر، هتحط السعر صفر؟'))return;
      form.elements.price.value=t.toFixed(2);upd();};
  }
  form.addEventListener('input',upd);upd();
  m.querySelector('#cancel').onclick=()=>m.remove();
  form.onsubmit=async e=>{
    e.preventDefault();const d={};
    new FormData(form).forEach((v,k)=>d[k]=v);
    if(t==='stock_moves'){d.qty=(d.dir==='out'?-1:1)*Math.abs(+d.qty);delete d.dir;}
    if(isOrd){d.materials=[...document.querySelectorAll('#mats .mrow')].map(x=>x.dataset.ext
      ?{item_id:'',name:x.querySelector('.mn').value,qty:x.querySelector('.mq').value,unit_cost:x.querySelector('.mc').value,sell_price:x.querySelector('.ms').value}
      :{item_id:x.querySelector('.mi').value,qty:x.querySelector('.mq').value});}
    try{ const j=id?await api('PUT',`/api/${t}/${id}`,d):await api('POST','/api/'+t,d);
      m.remove(); if(j.warnings&&j.warnings.length)alert('تنبيه:\n'+j.warnings.join('\n')); go(cur);
      if(isOrd&&!id&&d.status!=='عرض سعر')afterOrderSaved(j.id,d.title);}
    catch(err){alert(err.message);}
  };
}
function statementImage(j){
  const MAXR=40, rows=j.rows.slice(-MAXR), hidden=j.rows.length-rows.length;
  const first=[];
  if(hidden>0){const r0=j.rows[hidden-1];first.push({note:'الرصيد قبل آخر '+MAXR+' حركة',bal:r0.bal});}
  else if(+j.opening){first.push({note:'حساب سابق (رصيد أول المدة)',bal:+j.opening});}
  const body=[...first,...rows];
  const S=2,W=900,RH=40,HEAD=190,FOOT=130,H=HEAD+(body.length+1)*RH+FOOT;
  const cv=document.createElement('canvas');cv.width=W*S;cv.height=H*S;
  const x=cv.getContext('2d');x.scale(S,S);x.direction='rtl';
  const F=(sz,b)=>`${b?'bold ':''}${sz}px Tahoma,"Segoe UI",Arial,sans-serif`;
  x.fillStyle='#fff';x.fillRect(0,0,W,H);
  x.fillStyle='#22553F';x.fillRect(0,0,W,12);
  x.textAlign='right';x.fillStyle='#111';x.font=F(30,1);x.fillText(j.press_name,W-30,62);
  x.font=F(16);x.fillStyle='#555';x.fillText(j.press_phone||'',W-30,90);
  x.textAlign='left';x.font=F(26,1);x.fillStyle='#22553F';x.fillText('كشف حساب',30,62);
  x.font=F(16);x.fillStyle='#555';x.fillText(j.date,30,90);
  x.textAlign='right';x.fillStyle='#111';x.font=F(22,1);x.fillText('العميل: '+j.name,W-30,140);
  const col={date:W-30,desc:W-165,debit:405,credit:285,bal:150};
  const cut=(t,mw)=>{t=String(t??'');if(x.measureText(t).width<=mw)return t;while(t.length>1&&x.measureText(t+'…').width>mw)t=t.slice(0,-1);return t+'…';};
  let y=HEAD-10;
  x.fillStyle='#22553F';x.fillRect(20,y,W-40,RH);
  x.fillStyle='#fff';x.font=F(16,1);x.textAlign='right';
  x.fillText('التاريخ',col.date,y+26);x.fillText('البيان',col.desc,y+26);
  x.textAlign='center';x.fillText('مدين',col.debit,y+26);x.fillText('دائن',col.credit,y+26);x.fillText('الرصيد',col.bal,y+26);
  y+=RH;
  body.forEach((r,i)=>{
    x.fillStyle=i%2?'#f4f6f5':'#fff';x.fillRect(20,y,W-40,RH);
    x.fillStyle='#111';x.font=F(15);
    if(r.note){x.textAlign='right';x.fillText(r.note,col.date,y+26);}
    else{
      x.textAlign='right';x.fillText(r.date,col.date,y+26);x.fillText(cut(r.desc,300),col.desc,y+26);
      x.textAlign='center';
      if(r.debit)x.fillText(money(r.debit),col.debit,y+26);
      if(r.credit){x.fillStyle='#1b7a3e';x.fillText(money(r.credit),col.credit,y+26);}
    }
    x.textAlign='center';x.font=F(15,1);x.fillStyle=r.bal>0?'#b00020':'#1b7a3e';x.fillText(money(r.bal),col.bal,y+26);
    y+=RH;
  });
  x.strokeStyle='#22553F';x.lineWidth=2;x.beginPath();x.moveTo(20,y);x.lineTo(W-20,y);x.stroke();
  y+=22;
  x.fillStyle=j.balance>0?'#fdecea':'#e8f5ec';x.fillRect(20,y,W-40,64);
  x.textAlign='right';x.fillStyle='#111';x.font=F(24,1);x.fillText('المتبقي على العميل',W-40,y+41);
  x.textAlign='left';x.fillStyle=j.balance>0?'#b00020':'#1b7a3e';x.font=F(28,1);x.fillText(money(j.balance)+' جنيه',40,y+43);
  return new Promise(res=>cv.toBlob(res,'image/png'));
}
function showStatementImg(url,phone){
  const m=document.createElement('div');m.className='modal';
  m.innerHTML=`<form style="text-align:center"><p>اضغط مطوّلًا على الصورة واختار <b>نسخ</b> أو <b>مشاركة / حفظ في الصور</b>، وبعدها افتح المحادثة والصق أو أرفق الصورة.</p>
   <img src="${url}" style="max-width:100%;border:1px solid #ddd;border-radius:8px">
   <div class="actions" style="justify-content:center"><button class="p" type="button" id="wab">فتح محادثة واتساب</button><button class="s" type="button" id="wac">إغلاق</button></div></form>`;
  document.body.appendChild(m);
  m.querySelector('#wab').onclick=()=>{location.href='https://wa.me/'+phone;};
  m.querySelector('#wac').onclick=()=>m.remove();
}
async function waSend(apiUrl,makeImage,fname){
  const mobile=/Android|iPhone|iPad|iPod/i.test(navigator.userAgent);
  const w=mobile?null:window.open('','_blank');
  try{
    const j=await api('GET',apiUrl);
    if(!j.phone){if(w)w.close();alert('سجّل رقم تليفون للعميل '+j.name+' الأول (من تعديل العميل).');return;}
    const blob=await makeImage(j);
    const file=new File([blob],fname(j),{type:'image/png'});
    if(mobile&&navigator.canShare&&navigator.canShare({files:[file]})){
      await navigator.share({files:[file]});return;     // اختار واتساب والعميل من قايمة المشاركة
    }
    if(mobile){showStatementImg(URL.createObjectURL(blob),j.phone);return;}
    let copied=false;
    try{await navigator.clipboard.write([new ClipboardItem({'image/png':blob})]);copied=true;}catch(_){}
    const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=file.name;document.body.appendChild(a);a.click();a.remove();
    const url='https://wa.me/'+j.phone;
    if(w)w.location=url;else location=url;
    alert(copied?'الصورة اتنسخت واتحفظت كملف.\nفي المحادثة اضغط Ctrl+V (أو الصق) ثم إرسال.'
                :'الصورة اتحفظت كملف في التنزيلات.\nفي المحادثة اضغط إرفاق (📎) واختار الصورة ثم إرسال.');
  }catch(e){if(w)w.close();if(e&&e.name!=='AbortError')alert(e.message||'حصل خطأ');}
}
function sendWA(cid){return waSend('/api/statement_text?id='+cid,statementImage,j=>'كشف-حساب-'+j.name+'.png');}
function sendInvoiceWA(oid){return waSend('/api/invoice_data?id='+oid,invoiceImage,j=>'فاتورة-'+j.id+'-'+j.name+'.png');}
function afterOrderSaved(oid,title){
  const m=document.createElement('div');m.className='modal';
  m.innerHTML=`<form style="text-align:center"><h3>اتحفظ الأوردر #${oid}</h3><p>${esc(title||'')}</p>
   <div class="actions" style="justify-content:center;flex-wrap:wrap">
   <button class="p" type="button" id="aw">إرسال الفاتورة للعميل على واتساب</button>
   <button class="s" type="button" id="ap">عرض / طباعة الفاتورة</button>
   <button class="s" type="button" id="ac">إغلاق</button></div></form>`;
  document.body.appendChild(m);
  m.querySelector('#aw').onclick=()=>{m.remove();sendInvoiceWA(oid);};
  m.querySelector('#ap').onclick=()=>window.open('/invoice?id='+oid);
  m.querySelector('#ac').onclick=()=>m.remove();
}
function invoiceImage(j){
  const S=2,W=900,RH=44,acc=j.show_account;
  const H=250+RH*2+(acc?60+RH*3+30:90)+(j.notes?60:0);
  const cv=document.createElement('canvas');cv.width=W*S;cv.height=H*S;
  const x=cv.getContext('2d');x.scale(S,S);x.direction='rtl';
  const F=(sz,b)=>`${b?'bold ':''}${sz}px Tahoma,"Segoe UI",Arial,sans-serif`;
  const cut=(t,mw)=>{t=String(t??'');if(x.measureText(t).width<=mw)return t;while(t.length>1&&x.measureText(t+'…').width>mw)t=t.slice(0,-1);return t+'…';};
  x.fillStyle='#fff';x.fillRect(0,0,W,H);x.fillStyle='#22553F';x.fillRect(0,0,W,12);
  x.textAlign='right';x.fillStyle='#111';x.font=F(30,1);x.fillText(j.press_name,W-30,62);
  x.font=F(16);x.fillStyle='#555';x.fillText([j.press_phone,j.press_address].filter(Boolean).join('  -  '),W-30,90);
  x.textAlign='left';x.font=F(26,1);x.fillStyle='#22553F';x.fillText('فاتورة رقم '+j.id,30,62);
  x.font=F(16);x.fillStyle='#555';x.fillText(j.order_date||'',30,90);
  x.textAlign='right';x.fillStyle='#111';x.font=F(22,1);x.fillText('العميل: '+j.name,W-30,142);
  let y=175;
  const col={desc:W-30,qty:380,due:255,price:115};
  x.fillStyle='#22553F';x.fillRect(20,y,W-40,RH);x.fillStyle='#fff';x.font=F(16,1);
  x.textAlign='right';x.fillText('البيان',col.desc,y+28);
  x.textAlign='center';x.fillText('الكمية',col.qty,y+28);x.fillText('التسليم',col.due,y+28);x.fillText('السعر',col.price,y+28);
  y+=RH;x.fillStyle='#f4f6f5';x.fillRect(20,y,W-40,RH);x.fillStyle='#111';x.font=F(16);
  x.textAlign='right';x.fillText(cut(j.title,400),col.desc,y+28);
  x.textAlign='center';x.fillText(String(+j.qty),col.qty,y+28);x.fillText(j.due_date||'',col.due,y+28);
  x.font=F(16,1);x.fillText(money(j.price),col.price,y+28);
  y+=RH;x.strokeStyle='#22553F';x.lineWidth=2;x.beginPath();x.moveTo(20,y);x.lineTo(W-20,y);x.stroke();
  y+=26;
  const line=(label,val,hl,big)=>{
    if(hl){x.fillStyle='#e8f5ec';x.fillRect(20,y,W-40,RH+(big?14:0));}
    x.textAlign='right';x.fillStyle='#111';x.font=F(big?24:18,hl);x.fillText(label,W-40,y+(big?40:29));
    x.textAlign='left';x.fillStyle=hl?'#22553F':'#111';x.font=F(big?28:18,1);x.fillText(money(val)+(big?' جنيه':''),40,y+(big?42:29));
    y+=RH+(big?14:0);
  };
  if(acc){line('الحساب السابق',j.previous);line('قيمة هذه الفاتورة',j.price);line('إجمالي المستحق',j.due,true,true);}
  else line('إجمالي الفاتورة',j.price,true,true);
  if(j.notes){y+=22;x.textAlign='right';x.fillStyle='#555';x.font=F(15);x.fillText('ملاحظات: '+cut(j.notes,780),W-30,y);}
  return new Promise(res=>cv.toBlob(res,'image/png'));
}
function payForCustomer(cid){const c=DATA.find(x=>x.id===cid);cur='payments';DATA=[];
  openForm('payments',null,{customer_id:cid,amount:c?Math.max(0,c.balance):''});}
function moveFor(iid){cur='stock_moves';DATA=[];openForm('stock_moves',null,{item_id:iid});}

async function dash(){
  const month=window._m||todayStr().slice(0,7);
  const d=await api('GET','/api/dashboard?month='+month);
  const C=(l,v,cls='')=>`<div class="card"><small>${l}</small><b class="${cls}">${money(v)}</b></div>`;
  const tbl=(rows,cols)=>rows.length?`<table>${rows.map(r=>'<tr>'+cols.map(c=>`<td>${c(r)}</td>`).join('')+'</tr>').join('')}</table>`:'<small>لا يوجد</small>';
  $('#main').innerHTML=`<div class="bar"><h2>ملخص شهر</h2><input type="month" id="mm" value="${month}" style="width:170px"></div>
  <div class="cards">${C('المبيعات ('+d.orders_count+' أوردر)',d.sales)}${C('تكلفة الأوردرات',d.orders_cost)}${C('إجمالي الربح',d.gross_profit,d.gross_profit<0?'neg':'pos')}
  ${C('المصروفات',d.expenses)}${C('صافي الربح',d.net_profit,d.net_profit<0?'neg':'pos')}${C('المحصّل خلال الشهر',d.collected)}${C('إجمالي المتبقي عند العملاء',d.outstanding,'neg')}
  ${C('عروض أسعار معلقة ('+d.quotes_count+')',d.quotes_total)}</div>
  <div class="grid2">
   <div class="box"><h3>أوردرات متأخرة</h3>${tbl(d.late,[r=>'#'+r.id,r=>esc(r.customer_name),r=>esc(r.title),r=>r.due_date])}</div>
   <div class="box"><h3>أصناف تحت حد التنبيه</h3>${tbl(d.low_stock,[r=>esc(r.name),r=>r.qty+' '+esc(r.unit)])}</div>
   <div class="box"><h3>أكبر العملاء</h3>${tbl(d.top_customers,[r=>esc(r.name),r=>money(r.total)])}</div>
   <div class="box"><h3>المصروفات حسب النوع</h3>${tbl(d.expenses_by_category,[r=>esc(r.category),r=>money(r.total)])}</div>
  </div>`;
  $('#mm').onchange=e=>{window._m=e.target.value;dash();};
}
async function settingsPage(){
  const s=await api('GET','/api/settings');
  const I=(id,l,v,t='text')=>`<label>${l}</label><input id="${id}" type="${t}" value="${esc(v)}"><br><br>`;
  $('#main').innerHTML=`<div class="bar"><h2>الإعدادات</h2></div><div class="box" style="max-width:560px">
   ${I('s1','اسم المطبعة (يظهر في الفواتير وعروض الأسعار)',s.press_name)}${I('s2','التليفون',s.press_phone)}${I('s3','العنوان',s.press_address)}
   ${I('s5','مدة سريان عرض السعر (أيام)',s.quote_days,'number')}
   ${I('s7','كود الدولة لواتساب (مصر 20)',s.country_code||'20')}
   <label>شروط عرض السعر</label><textarea id="s6" rows="3">${esc(s.quote_terms)}</textarea><br><br>
   <button class="p" onclick="saveSettings()">حفظ</button>
   <hr><p>نسخة احتياطية من كل البيانات:</p><button class="s" onclick="location='/api/backup'">تحميل نسخة احتياطية</button>
   <hr><p>استعادة نسخة احتياطية (بتستبدل كل البيانات الحالية، وبعدها لازم تسجّل دخول تاني):</p>
   <input type="file" id="rf" accept=".db"><br><br><button class="s d" onclick="restoreBackup()">استعادة</button></div>`;
}
async function restoreBackup(){
  const f=$('#rf').files[0];if(!f){alert('اختار ملف النسخة الاحتياطية الأول');return;}
  if(!confirm('هتتمسح كل البيانات الحالية وتتبدل بالنسخة دي. متأكد؟'))return;
  try{const r=await fetch('/api/restore',{method:'POST',headers:{'Content-Type':'application/octet-stream'},body:f});
    const j=await r.json().catch(()=>({}));if(!r.ok)throw new Error(j.error||'حصل خطأ');
    alert('تمت الاستعادة. سجّل دخول تاني.');location.reload();}catch(e){alert(e.message);}
}
async function saveSettings(){
  await api('PUT','/api/settings',{press_name:$('#s1').value,press_phone:$('#s2').value,press_address:$('#s3').value,
    quote_days:$('#s5').value,quote_terms:$('#s6').value,country_code:$('#s7').value});
  ST=await api('GET','/api/settings');$('#pname').textContent=ST.press_name;document.title=ST.press_name;alert('تم الحفظ');
}
boot();
</script></body></html>
"""


def free_port(host, start):
    for p in range(start, start + 20):
        with socket.socket() as s:
            if s.connect_ex((host if host != "0.0.0.0" else "127.0.0.1", p)) != 0:
                return p
    return start


def bootstrap_admin():
    """على السيرفر: لو مفيش مستخدمين، أنشئ المدير من متغيرات البيئة (بدل ما أول واحد يفتح الصفحة يبقى هو المدير)"""
    un, pw = os.environ.get("PRESS_ADMIN_USER", "").strip(), os.environ.get("PRESS_ADMIN_PASS", "")
    if not un or len(pw) < 6:
        return
    con = db()
    if not con.execute("SELECT COUNT(*) FROM users").fetchone()[0]:
        con.execute("INSERT INTO users (username,password_hash,full_name,role,active) VALUES (?,?,?,?,1)",
                    (un, hash_pw(pw), "", "admin"))
        con.commit()
        print("Admin user created:", un)
    con.close()


def lan_ip():
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s_:
            s_.connect(("10.255.255.255", 1))
            return s_.getsockname()[0]
    except OSError:
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default=os.environ.get("HOST", "127.0.0.1"), help="استخدم 0.0.0.0 لو عايز أجهزة تانية في نفس الشبكة تدخل")
    ap.add_argument("--port", type=int, default=int(os.environ.get("PORT", 8000)))
    ap.add_argument("--no-browser", action="store_true")
    a = ap.parse_args()
    init_db()
    bootstrap_admin()
    port = free_port(a.host, a.port)
    srv = ThreadingHTTPServer((a.host, port), Handler)
    url = "http://127.0.0.1:%d" % port
    print("Press accounting is running at:", url, " (Ctrl+C to stop)")
    if a.host == "0.0.0.0":
        ip = lan_ip()
        print("\n>>> Open this address on your iPhone (same Wi-Fi):  http://%s:%d\n" % (ip or "<PC-IP>", port))
    if not a.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
