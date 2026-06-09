#!/usr/bin/env python3
"""
EDL Arbitrage Scanner - v12 (cloud-ready; Chinese Gem Pack CASES, looser match)

v12 changes vs v11:
  - Gem Pack case match = "gem pack" + volume + "case". Volume matches "vol 5",
    "vol. 5", "volume 5", "vol5", OR a standalone whole-word "5" (won't fire on
    "$545" or "15"). "20"/"booster box" no longer required.
  - Vol 5 reverted to auto ask-median (prices move fast); $300 floor retained to
    gate out single booster boxes / accessory-case singles.

Run locally (double-run) or on Render (env vars EBAY_APP_ID/EBAY_CERT_ID/POKEDATA_KEY, EDL_DIR=/tmp/edl).
"""

import os, sys, json, csv, time, base64, re, unicodedata, webbrowser, subprocess, threading, http.server
from collections import defaultdict, Counter
from datetime import datetime, timezone, timedelta

try:
    import requests
except ImportError:
    print("MISSING DEPENDENCY: run  pip install requests  then re-run.")
    sys.exit(1)

# ============================== CONFIG ==============================
IS_CLOUD      = bool(os.environ.get("RENDER") or os.environ.get("EDL_CLOUD"))
PROJECT_DIR   = os.environ.get("EDL_DIR", r"D:\Arbitrage Scanner")
os.makedirs(PROJECT_DIR, exist_ok=True)
ALL_SETS_JSON = r"C:\Users\adam.george\Documents\Price Scraper\Data\Pokedata Cache\all_sets.json"
EBAY_KEYS     = os.path.join(PROJECT_DIR, "eBay Keys.txt")
POKEDATA_KEYS = os.path.join(PROJECT_DIR, "Pokedata Keys.txt")
MARKET_CACHE  = os.path.join(PROJECT_DIR, "market_cache.json")
OPPS_PATH     = os.path.join(PROJECT_DIR, "opps.json")
DASHBOARD     = os.path.join(PROJECT_DIR, "dashboard.html")
UNIVERSE_CSV  = os.path.join(PROJECT_DIR, "universe_market.csv")
CATALOG_DUMP  = os.path.join(PROJECT_DIR, "catalog_dump.csv")
DASH_PORT     = int(os.environ.get("PORT", "8787"))
DASH_HOST     = "0.0.0.0" if IS_CLOUD else "127.0.0.1"

PRIORITY_SETS = ["Ascended Heroes", "Destined Rivals", "Prismatic Evolutions", "Black Bolt",
                 "White Flare", "Journey Together", "Surging Sparks", "Silver Tempest",
                 "Crown Zenith", "Twilight Masquerade"]
ENABLED_TYPES = ["ETB", "PC_ETB", "BB", "BUNDLE", "UPC", "SPC",
                 "ETB_CASE", "PC_ETB_CASE", "BB_CASE", "BUNDLE_CASE", "MINI_TIN_DISPLAY"]

BIN_MAX_RATIO, AUCTION_MAX_RATIO, AUCTION_MAX_HOURS = 0.80, 0.70, 24
SHIP_UNKNOWN_MAX_RATIO = 0.65
BIN_MIN_RATIO, AUCTION_MIN_RATIO = 0.20, 0.10
MARKET_REFRESH_HOURS, CYCLE_MINUTES = 6, 60
EBAY_MARKETPLACE = "EBAY_US"
BIN_LIMIT, AUCTION_LIMIT, MAX_PER_SECTION, POLITE_SLEEP = 50, 100, 80, 0.2
GEM_ASK_SAMPLE, GEM_ASK_MIN = 100, 4

SETID_FALLBACK = {"ascended heroes": 3591, "destined rivals": 567, "prismatic evolutions": 557,
                  "black bolt": 570, "white flare": 571, "journey together": 562,
                  "surging sparks": 555, "silver tempest": 503, "crown zenith": 506,
                  "twilight masquerade": 545}

JUNK_BASE = ["accessories", "accessory", "sleeve", "empty", "opened", "open box", "code", "lot",
             "proxy", "loose", "magnetic", "protector", "acrylic", "sticker", "divider", "playmat",
             "binder", "repack", "read description", "damaged", "single pack", "1 pack", "dice",
             "hit point", "damage counter", "players guide", "player s guide", "guide booklet",
             "booklet", "instruction", "rulebook", "rule book", "spinner", "coin", "2x", "3x", "x2", "x3",
             "no packs", "no pack", "no booster", "without pack", "without booster", "packs removed",
             "no promo", "box only", "empty box", "missing packs"]
LANGS = ["japanese", "japan", "korean", "chinese", "french", "german", "spanish", "italian",
         "portuguese", "dutch", "polish", "russian", "thai", "indonesian", "vietnamese",
         "francais", "deutsch", "espanol", "italiano", "portugues", "nederlands",
         "traditional chinese", "simplified chinese"]
CHINESE = {"chinese", "traditional chinese", "simplified chinese"}
JUNK = JUNK_BASE + LANGS
GEM_EXCLUDE = JUNK_BASE + [l for l in LANGS if l not in CHINESE] + ["pokemon go", "digital", "online", "app", "ios", "android"]
LANG_REJECT = ["japanese", "japan", "korean", "chinese", "french", "german", "spanish", "italian",
               "portuguese", "dutch", "polish", "russian", "thai", "indonesian", "vietnamese"]

# ---- Chinese Gem Pack CASES (20-box sealed cases; NOT on Pokedata) -------------
# match = "gem pack" + volume + "case"; volume via vol_re (vol N / standalone N).
# market None -> floored ask-median (estimate, flagged). min_total floor gates single boxes.
GEM_REQUIRE = [["gem pack"], ["case"]]
GEM_PACKS = [
  {"label": "Gem Pack Vol. 1 Case", "vol": "1", "query": "gem pack 1 case", "market": None, "min_total": 300, "is_case": True, "img": ""},
  {"label": "Gem Pack Vol. 2 Case", "vol": "2", "query": "gem pack 2 case", "market": None, "min_total": 300, "is_case": True, "img": ""},
  {"label": "Gem Pack Vol. 3 Case", "vol": "3", "query": "gem pack 3 case", "market": None, "min_total": 300, "is_case": True, "img": ""},
  {"label": "Gem Pack Vol. 4 Case", "vol": "4", "query": "gem pack 4 case", "market": None, "min_total": 300, "is_case": True, "img": ""},
  {"label": "Gem Pack Vol. 5 Case", "vol": "5", "query": "gem pack 5 case", "market": None, "min_total": 300, "is_case": True, "img": ""},
]

_ACC = re.compile(r"\b(?:with|w|in|inc|incl|includes|including|included|and|plus|free|bonus|complete with|comes with|comes in|ships in)\b"
                  r"(?:\s+(?:a|an|the))?(?:\s+(?:protective|acrylic|magnetic|hard|plastic|uv|storage|display|clear|soft|custom|fitted))*"
                  r"\s+(?:case|cases|sleeve|sleeves)\b")
_ACC2 = re.compile(r"\b(?:case|cases)\s+(?:included|incl|inc|ready)\b")
_ACC3 = re.compile(r"\b(?:protective|acrylic|magnetic|hard|plastic|uv|storage|display|clear|soft|custom|fitted)\s+(?:case|cases|sleeve|sleeves)\b")
TRUE_CASE = re.compile(
    r"(?:elite trainer box|etb|booster box|booster bundle|pokemon center elite trainer box|pc etb|pcetb|mini tins?|booster)"
    r"(?:\s+\w+){0,2}\s+(?:case|cases|carton|displays?)\b"
    r"|\bcase\s+of\b|\b(?:sealed|factory|master|full)\s+case\b|\bcarton\b|\bdisplay\s+box\b"
    r"|\b(?:6|8|10|12|16|18|24|36)\s*(?:ct|count|boxes|box|bundles|etb|etbs|tins)\b"
    r"|\bcase\s*\(?\s*(?:of\s*)?\d+\b")

def gem_vol_re(vol):
    v = re.escape(str(vol))
    return re.compile(r"\bvol(?:ume)?\.?\s*%s\b|\b%s\b" % (v, v))

def _t(label, name_has, name_not, is_case, require, exclude_extra):
    return {"label": label, "name_has": name_has, "name_not": name_not, "is_case": is_case,
            "require": require, "exclude": JUNK + exclude_extra}

PC_REQ = [["pokemon center", "pcetb", "pc etb"], ["elite trainer box", "etb", "pcetb", "pc etb"]]
TYPES = {
  "ETB":    _t("ETB", ["elite trainer box"], ["pokemon center", "plus", "ultra premium", "super premium"], False,
               [["elite trainer box", "etb"]],
               ["pokemon center", "pcetb", "pc etb", "plus", "ultra premium", "super premium", "booster box", "booster bundle", "blister", "collection", "tin"]),
  "PC_ETB": _t("PC ETB", ["pokemon center elite trainer box"], ["plus"], False, PC_REQ,
               ["booster box", "booster bundle", "blister", "collection", "tin", "ultra premium", "super premium", "plus"]),
  "BB":     _t("Booster Box", ["booster box"], [], False,
               [["booster box"]],
               ["elite trainer", "booster bundle", "blister", "collection", "tin"]),
  "BUNDLE": _t("Booster Bundle", ["booster bundle"], [], False,
               [["booster bundle"]],
               ["booster box", "elite trainer", "blister", "collection", "tin", "ultra premium", "super premium"]),
  "UPC":    _t("Ultra Premium Collection", ["ultra premium"], ["super premium"], False,
               [["ultra premium"]],
               ["elite trainer", "booster box", "booster bundle", "blister", "tin", "super premium"]),
  "SPC":    _t("Super Premium Collection", ["super premium"], [], False,
               [["super premium"]],
               ["elite trainer", "booster box", "booster bundle", "blister", "tin", "ultra premium"]),
  "ETB_CASE":    _t("ETB Case", ["elite trainer box"], ["pokemon center", "plus", "ultra premium", "super premium"], True,
                    [["elite trainer box", "etb"]],
                    ["pokemon center", "pcetb", "pc etb", "ultra premium", "super premium", "booster box", "booster bundle", "blister", "collection", "tin", "mini tin"]),
  "PC_ETB_CASE": _t("PC ETB Case", ["pokemon center elite trainer box"], [], True, PC_REQ,
                    ["booster box", "booster bundle", "blister", "collection", "tin", "ultra premium", "super premium"]),
  "BB_CASE":     _t("Booster Box Case", ["booster box"], [], True,
                    [["booster box"]],
                    ["elite trainer", "booster bundle", "blister", "collection", "tin"]),
  "BUNDLE_CASE": _t("Booster Bundle Case", ["booster bundle"], [], True,
                    [["booster bundle"]],
                    ["booster box", "elite trainer", "blister", "collection", "tin"]),
  "MINI_TIN_DISPLAY": _t("Mini Tin Display", ["mini tin"], [], True,
                    [["mini tin"]],
                    ["elite trainer", "booster box", "booster bundle", "blister", "collection", "ultra premium", "super premium"]),
}
CASE_TYPES = {"ETB_CASE", "PC_ETB_CASE", "BB_CASE", "BUNDLE_CASE", "MINI_TIN_DISPLAY"}
STOP = {"pokemon", "the", "tcg", "trading", "card", "game", "and", "of"}
# ===================================================================


def log(m): print(f"[{datetime.now().strftime('%H:%M:%S')}] {m}", flush=True)
def load_json(p, d):
    try:
        with open(p, encoding="utf-8") as f: return json.load(f)
    except Exception: return d
def save_json(p, o):
    with open(p, "w", encoding="utf-8") as f: json.dump(o, f)
def now_utc(): return datetime.now(timezone.utc)
def norm(s):
    s = unicodedata.normalize("NFKD", (s or "").lower())
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"[^0-9a-z]+", " ", s).strip()
def is_true_case(text):
    n = norm(text)
    n = _ACC.sub(" ", n); n = _ACC2.sub(" ", n); n = _ACC3.sub(" ", n)
    return bool(TRUE_CASE.search(n))
def median(xs):
    s = sorted(xs); n = len(s)
    if n == 0: return None
    return s[n // 2] if n % 2 else (s[n // 2 - 1] + s[n // 2]) / 2.0


# ----------------------------- keys -----------------------------
def grab_after_colon(path, label):
    try:
        with open(path, encoding="utf-8-sig") as f:
            for ln in f.read().splitlines():
                if label.lower() in ln.lower() and ":" in ln:
                    return ln.split(":", 1)[1].strip()
    except Exception:
        return None
    return None

class Keys:
    def __init__(self):
        self.app_id  = os.environ.get("EBAY_APP_ID")  or grab_after_colon(EBAY_KEYS, "App ID")
        self.cert_id = os.environ.get("EBAY_CERT_ID") or grab_after_colon(EBAY_KEYS, "Cert ID")
        self.pokedata = (os.environ.get("POKEDATA_KEY")
                         or grab_after_colon(POKEDATA_KEYS, "Private API Key")
                         or grab_after_colon(POKEDATA_KEYS, "API Key"))
        self._tok, self._exp = None, 0
        if not (self.app_id and self.cert_id and self.pokedata):
            log("ERROR: missing keys. Set EBAY_APP_ID / EBAY_CERT_ID / POKEDATA_KEY env vars "
                "(cloud) or the *.txt key files (local)."); sys.exit(1)
    def ebay_token(self):
        if self._tok and time.time() < self._exp - 300: return self._tok
        cred = base64.b64encode(f"{self.app_id}:{self.cert_id}".encode()).decode()
        r = requests.post("https://api.ebay.com/identity/v1/oauth2/token",
                          headers={"Content-Type": "application/x-www-form-urlencoded", "Authorization": f"Basic {cred}"},
                          data={"grant_type": "client_credentials", "scope": "https://api.ebay.com/oauth/api_scope"}, timeout=20)
        r.raise_for_status(); j = r.json()
        self._tok, self._exp = j["access_token"], time.time() + int(j.get("expires_in", 7000))
        return self._tok


# --------------------------- helpers ---------------------------
def money(d):
    try: return float(d.get("value")) if isinstance(d, dict) else (float(d) if d is not None else None)
    except Exception: return None
def parse_iso_z(s):
    if not s: return None
    for fmt in ("%Y-%m-%dT%H:%M:%S.%fZ", "%Y-%m-%dT%H:%M:%SZ"):
        try: return datetime.strptime(s, fmt).replace(tzinfo=timezone.utc)
        except Exception: pass
    return None
def set_tokens(set_name):
    toks = [t for t in norm(set_name).split() if t and t not in STOP]
    strong = sorted([t for t in toks if len(t) >= 4 or t.isdigit()], key=len, reverse=True)
    return strong[:2] if len(strong) > 2 else strong


# --------------------------- name -> set_id ---------------------------
def build_setid_map():
    m = {}
    sets = load_json(ALL_SETS_JSON, None)
    if isinstance(sets, list):
        for s in sets:
            if isinstance(s, dict) and s.get("name") and s.get("id") is not None and s.get("language", "ENGLISH") == "ENGLISH":
                m[norm(s["name"])] = s["id"]
    for k, v in SETID_FALLBACK.items():
        m.setdefault(norm(k), v)
    return m


# --------------------------- pokedata catalog ---------------------------
def get_catalog(keys, sid):
    cache = get_catalog._cache
    c = cache.get(str(sid))
    if c and (time.time() - c["ts"]) < MARKET_REFRESH_HOURS * 3600:
        return c["products"]
    try:
        r = requests.get("https://www.pokedata.io/api/products",
                         headers={"Authorization": f"Bearer {keys.pokedata}"}, params={"set_id": sid}, timeout=40)
        if r.status_code != 200 or not isinstance(r.json(), list):
            return c["products"] if c else []
        prods = r.json()
        cache[str(sid)] = {"ts": time.time(), "products": prods}
        save_json(MARKET_CACHE, cache); time.sleep(POLITE_SLEEP)
        return prods
    except Exception as e:
        log(f"catalog set_id={sid} error: {e}")
        return c["products"] if c else []
get_catalog._cache = load_json(MARKET_CACHE, {})

def select_type(name):
    n = norm(name)
    caseflag = is_true_case(name)
    for key in ENABLED_TYPES:
        t = TYPES[key]
        if all(h in n for h in t["name_has"]) and not any(x in n for x in t["name_not"]) and t["is_case"] == caseflag:
            return key
    return None

def pick_base(plist):
    good = [p for p in plist if not any(rv in norm(p.get("name", "")) for rv in LANG_REJECT)]
    pool = good or plist
    pool.sort(key=lambda p: (len(p.get("name", "")), int(p["id"]) if str(p.get("id", "")).isdigit() else 0))
    return pool[0]

def build_universe(keys, setid_map, dump=False):
    uni, dump_rows = [], []
    for sn in PRIORITY_SETS:
        sid = setid_map.get(norm(sn))
        if sid is None:
            log(f"skip {sn!r}: no set_id found"); continue
        cand = defaultdict(list)
        for p in get_catalog(keys, sid):
            key = select_type(p.get("name", ""))
            if key: cand[key].append(p)
            if dump:
                dump_rows.append([sn, p.get("id"), p.get("name"), p.get("market_value"), key or ""])
        for key, plist in cand.items():
            base = pick_base(plist)
            mv = base.get("market_value")
            if not mv or float(mv) <= 0:
                continue
            t, name = TYPES[key], (base.get("name") or "").strip()
            q = name if "pokemon" in name.lower() else "Pokemon " + name
            uni.append({"product_id": str(base.get("id")), "set_name": sn, "type_key": key,
                        "type_label": t["label"], "is_case": key in CASE_TYPES, "name": name,
                        "market": round(float(mv), 2), "img": base.get("img_url"), "query": q,
                        "require": [[s] for s in set_tokens(sn)] + t["require"], "exclude": t["exclude"]})
    uni.sort(key=lambda x: (x["set_name"], x["is_case"], x["type_label"]))
    if dump:
        try:
            with open(CATALOG_DUMP, "w", newline="", encoding="utf-8") as f:
                wr = csv.writer(f); wr.writerow(["set_name", "product_id", "name", "market_value", "matched_type"])
                wr.writerows(dump_rows)
        except Exception: pass
    return uni


# --------------------------- guardrails ---------------------------
def title_ok(title, require_groups, exclude):
    t = norm(title)
    for grp in require_groups:
        if not any(alt in t for alt in grp): return False
    for bad in exclude:
        if norm(bad) and norm(bad) in t: return False
    return True

def match_title(title, prod):
    """title_ok plus an optional whole-word volume regex (for gem packs)."""
    if not title_ok(title, prod["require"], prod["exclude"]): return False
    vr = prod.get("vol_re")
    if vr is not None and not vr.search(norm(title)): return False
    return True


# --------------------------- eBay ---------------------------
def ebay_search(token, q, filt, sort=None, limit=50):
    params = {"q": q, "limit": limit, "filter": filt}
    if sort: params["sort"] = sort
    r = requests.get("https://api.ebay.com/buy/browse/v1/item_summary/search",
                     headers={"Authorization": f"Bearer {token}", "X-EBAY-C-MARKETPLACE-ID": EBAY_MARKETPLACE},
                     params=params, timeout=25)
    return (r.json().get("itemSummaries") or []) if r.status_code == 200 else []

def ebay_get_item(token, item_id):
    try:
        r = requests.get(f"https://api.ebay.com/buy/browse/v1/item/{item_id}",
                         headers={"Authorization": f"Bearer {token}", "X-EBAY-C-MARKETPLACE-ID": EBAY_MARKETPLACE},
                         params={"fieldgroups": "COMPACT"}, timeout=20)
        return r.json() if r.status_code == 200 else None
    except Exception:
        return None

def shipping_from(item):
    so = item.get("shippingOptions") or []
    if so and so[0].get("shippingCostType") == "FIXED":
        return money(so[0].get("shippingCost")), True
    return None, False
def img_of(item, fb):
    return (item.get("image") or {}).get("imageUrl") or ((item.get("thumbnailImages") or [{}])[0].get("imageUrl")) or fb
def base_opp(item, prod):
    return {"item_id": item.get("itemId"), "title": item.get("title"), "url": item.get("itemWebUrl"),
            "image": img_of(item, prod.get("img")), "set_name": prod["set_name"], "type": prod["type_label"],
            "is_case": prod.get("is_case", False), "product_id": prod["product_id"], "market": prod["market"],
            "mkt_est": prod.get("market_src", "set") == "ask-median",
            "seller": (item.get("seller") or {}).get("username"),
            "feedback_pct": (item.get("seller") or {}).get("feedbackPercentage"),
            "feedback_score": (item.get("seller") or {}).get("feedbackScore"), "condition": item.get("condition")}

def eval_bin(item, prod):
    market, price = prod["market"], money(item.get("price"))
    if price is None: return None
    bmax = prod.get("bin_ratio", BIN_MAX_RATIO); mn = prod.get("min_total", 0)
    ship, known = shipping_from(item)
    if known:
        total = price + (ship or 0)
        if total > market * bmax: return None
        ratio = total / market
    else:
        if price > market * min(SHIP_UNKNOWN_MAX_RATIO, bmax): return None
        total, ratio = price, price / market
    if ratio < BIN_MIN_RATIO or total < mn: return None
    o = base_opp(item, prod)
    o.update({"kind": "BIN", "item_price": round(price, 2),
              "shipping": (round(ship, 2) if known and ship is not None else None),
              "shipping_known": known, "total": round(total, 2), "ratio": round(ratio, 3)})
    return o

def eval_auction(item, prod, token):
    market, bid = prod["market"], money(item.get("currentBidPrice"))
    end = parse_iso_z(item.get("itemEndDate"))
    if bid is None or end is None: return None
    amax = prod.get("auc_ratio", AUCTION_MAX_RATIO); mn = prod.get("min_total", 0)
    hours = (end - now_utc()).total_seconds() / 3600.0
    if hours <= 0 or hours > AUCTION_MAX_HOURS: return None
    ship, known = shipping_from(item)
    cost = bid + ((ship or 0) if known else 0)
    ratio = cost / market
    if cost > market * amax or ratio < AUCTION_MIN_RATIO or cost < mn: return None
    o = base_opp(item, prod)
    o.update({"kind": "AUCTION", "current_bid": round(bid, 2),
              "shipping": (round(ship, 2) if known and ship is not None else None),
              "shipping_known": known, "bids": item.get("bidCount"), "end_date": item.get("itemEndDate"),
              "ratio": round(ratio, 3), "min_next_bid": None})
    d = ebay_get_item(token, o["item_id"])
    if d:
        o["min_next_bid"] = money(d.get("minimumPriceToBid"))
        if d.get("bidCount") is not None: o["bids"] = d.get("bidCount")
    return o


# --------------------------- gem packs (CASES; not on Pokedata) ---------------------------
def gem_market(token, gp, key, vr):
    """Manual market if set; else median of current eBay CASE asking prices >= min_total."""
    if gp.get("market"):
        return float(gp["market"]), "set"
    cache = get_catalog._cache
    c = cache.get(key)
    if c and (time.time() - c["ts"]) < MARKET_REFRESH_HOURS * 3600:
        return c.get("market"), c.get("src", "ask-median")
    mn = gp.get("min_total", 0)
    asks = []
    for it in ebay_search(token, gp["query"], "buyingOptions:{FIXED_PRICE},conditionIds:{1000}", limit=GEM_ASK_SAMPLE):
        t = it.get("title", "")
        if not title_ok(t, GEM_REQUIRE, GEM_EXCLUDE): continue
        if not vr.search(norm(t)): continue
        p = money(it.get("price"))
        if p is None: continue
        s, known = shipping_from(it)
        tot = p + (s or 0)
        if tot < mn: continue                      # ignore single packs/boxes, only real cases
        asks.append(tot)
    if len(asks) < GEM_ASK_MIN:
        cache[key] = {"ts": time.time(), "market": None, "src": "insufficient"}
        save_json(MARKET_CACHE, cache); time.sleep(POLITE_SLEEP)
        return None, "insufficient"
    med = round(median(asks), 2)
    cache[key] = {"ts": time.time(), "market": med, "src": "ask-median", "n": len(asks)}
    save_json(MARKET_CACHE, cache); time.sleep(POLITE_SLEEP)
    return med, "ask-median"

def gem_universe(token):
    out = []
    for i, gp in enumerate(GEM_PACKS):
        vr = gem_vol_re(gp["vol"])
        mkt, src = gem_market(token, gp, f"gem:{i}", vr)
        if not mkt:
            log(f"gem '{gp['label']}': no market ({src}) — check listings or set a 'market' value")
            continue
        binr = 0.70 if src == "ask-median" else BIN_MAX_RATIO
        aucr = 0.60 if src == "ask-median" else AUCTION_MAX_RATIO
        out.append({"product_id": f"GEM-{i}", "set_name": "Chinese Gem Pack", "type_key": "GEM",
                    "type_label": gp["label"], "is_case": gp.get("is_case", True), "name": gp["label"],
                    "market": float(mkt), "market_src": src, "img": gp.get("img"), "query": gp["query"],
                    "require": GEM_REQUIRE, "exclude": GEM_EXCLUDE, "vol_re": vr,
                    "bin_ratio": binr, "auc_ratio": aucr, "min_total": gp.get("min_total", 0), "skip_case_gate": True})
    return out


# --------------------------- scan / validate ---------------------------
def scan(token, universe, existing_ids, cycle_iso):
    new, seen = [], set(existing_ids)
    for prod in universe:
        market = prod["market"]
        ceil = round(market * prod.get("bin_ratio", BIN_MAX_RATIO), 2)
        bin_filt = f"buyingOptions:{{FIXED_PRICE}},conditionIds:{{1000}},price:[..{ceil}],priceCurrency:USD"
        for it in ebay_search(token, prod["query"], bin_filt, sort="price", limit=BIN_LIMIT):
            iid, title = it.get("itemId"), it.get("title", "")
            if not iid or iid in seen or not match_title(title, prod): continue
            if not prod.get("skip_case_gate") and is_true_case(title) != prod["is_case"]: continue
            o = eval_bin(it, prod)
            if o:
                o["first_seen"] = o["last_validated"] = cycle_iso; new.append(o); seen.add(iid)
        time.sleep(POLITE_SLEEP)
        lo = now_utc().strftime("%Y-%m-%dT%H:%M:%S.000Z")
        hi = (now_utc() + timedelta(hours=AUCTION_MAX_HOURS)).strftime("%Y-%m-%dT%H:%M:%S.000Z")
        auc_filt = f"buyingOptions:{{AUCTION}},conditionIds:{{1000}},itemEndDate:[{lo}..{hi}]"
        for it in ebay_search(token, prod["query"], auc_filt, limit=AUCTION_LIMIT):
            iid, title = it.get("itemId"), it.get("title", "")
            if not iid or iid in seen or not match_title(title, prod): continue
            if not prod.get("skip_case_gate") and is_true_case(title) != prod["is_case"]: continue
            o = eval_auction(it, prod, token)
            if o:
                o["first_seen"] = o["last_validated"] = cycle_iso; new.append(o); seen.add(iid)
        time.sleep(POLITE_SLEEP)
    return new

def validate(token, opps, uni_by_pid, cycle_iso):
    kept = []
    for o in opps:
        prod = uni_by_pid.get(o["product_id"])
        if not prod: continue
        title = o.get("title", "")
        if not match_title(title, prod): continue
        if not prod.get("skip_case_gate") and is_true_case(title) != prod["is_case"]: continue
        d = ebay_get_item(token, o["item_id"])
        if not d: continue
        end = parse_iso_z(d.get("itemEndDate"))
        if end and end <= now_utc(): continue
        market = prod["market"]; mn = prod.get("min_total", 0)
        if o["kind"] == "BIN":
            price = money(d.get("price"))
            if price is None: continue
            bmax = prod.get("bin_ratio", BIN_MAX_RATIO)
            ship, known = shipping_from(d)
            total = price + (ship or 0) if known else price
            ratio = total / market if known else price / market
            ok = (total <= market * bmax) if known else (price <= market * min(SHIP_UNKNOWN_MAX_RATIO, bmax))
            if not ok or ratio < BIN_MIN_RATIO or total < mn: continue
            o.update({"item_price": round(price, 2), "shipping": (round(ship, 2) if known and ship is not None else None),
                      "shipping_known": known, "total": round(total, 2), "ratio": round(ratio, 3),
                      "market": market, "mkt_est": prod.get("market_src", "set") == "ask-median", "last_validated": cycle_iso})
        else:
            bid = money(d.get("currentBidPrice"))
            if bid is None: continue
            amax = prod.get("auc_ratio", AUCTION_MAX_RATIO)
            ship, known = shipping_from(d)
            cost = bid + ((ship or 0) if known else 0)
            ratio = cost / market
            hours = (end - now_utc()).total_seconds() / 3600.0 if end else None
            if cost > market * amax or ratio < AUCTION_MIN_RATIO or cost < mn or \
               (hours is not None and (hours <= 0 or hours > AUCTION_MAX_HOURS)): continue
            o.update({"current_bid": round(bid, 2), "min_next_bid": money(d.get("minimumPriceToBid")),
                      "bids": d.get("bidCount"), "end_date": d.get("itemEndDate"),
                      "shipping": (round(ship, 2) if known and ship is not None else None),
                      "shipping_known": known, "ratio": round(ratio, 3), "market": market,
                      "mkt_est": prod.get("market_src", "set") == "ask-median", "last_validated": cycle_iso})
        kept.append(o); time.sleep(POLITE_SLEEP)
    return kept


# --------------------------- dashboard (EDL brand, responsive) ---------------------------
DASH = r"""<!DOCTYPE html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta http-equiv="refresh" content="60">
<title>EDL Arbitrage Scanner</title>
<link href="https://fonts.googleapis.com/css2?family=Bebas+Neue&family=DM+Mono:wght@400;500&family=DM+Sans:wght@300;400;500;600;700&display=swap" rel="stylesheet">
<style>
:root{--black:#0a0a0a;--card:#181a1d;--line:#2a2d32;--gold:#f5c842;--red:#e8505b;--green:#4ecb71;--text:#e8e8e8;--muted:#7a7f88;
--sans:'DM Sans',sans-serif;--mono:'DM Mono',monospace;--display:'Bebas Neue',sans-serif}
*{box-sizing:border-box;margin:0;padding:0}
body{background:var(--black);color:var(--text);font-family:var(--sans);font-size:14px;line-height:1.45;
background-image:radial-gradient(circle at 12% -10%,rgba(245,200,66,.06),transparent 40%);min-height:100vh;-webkit-text-size-adjust:100%}
header{position:sticky;top:0;z-index:5;background:rgba(10,10,10,.9);backdrop-filter:blur(8px);border-bottom:1px solid var(--line);
padding:14px 22px;display:flex;align-items:baseline;gap:14px 18px;flex-wrap:wrap}
.brand{font-family:var(--display);font-size:30px;letter-spacing:2px;color:var(--gold);line-height:1}.brand span{color:var(--text)}
.sub{font-family:var(--mono);font-size:11px;letter-spacing:2px;text-transform:uppercase;color:var(--muted)}
.meta{font-family:var(--mono);font-size:11px;color:var(--muted)}
.toggle{margin-left:auto;font-family:var(--mono);font-size:11px;color:var(--gold);cursor:pointer;letter-spacing:1px;text-transform:uppercase}
.sec{padding:18px 22px}
.sec h2{font-family:var(--display);font-size:20px;letter-spacing:2px;margin-bottom:12px;display:flex;align-items:center;gap:10px}
.sec h2:before{content:"";width:8px;height:8px;border-radius:99px}
.bin h2{color:var(--green)}.bin h2:before{background:var(--green);box-shadow:0 0 8px var(--green)}
.auc h2{color:var(--gold)}.auc h2:before{background:var(--gold);box-shadow:0 0 8px var(--gold)}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(min(100%,320px),1fr));gap:14px}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;overflow:hidden;display:flex;flex-direction:column;
opacity:0;transform:translateY(8px);animation:rise .4s ease forwards;transition:border-color .15s,transform .15s,box-shadow .15s;position:relative}
.card:hover{border-color:var(--gold);transform:translateY(-3px);box-shadow:0 10px 30px rgba(0,0,0,.5)}
@keyframes rise{to{opacity:1;transform:translateY(0)}}
.thumb{height:150px;background:#0b0e12 center/contain no-repeat;border-bottom:1px solid var(--line)}
.badge{position:absolute;top:10px;left:10px;font-family:var(--mono);font-size:10px;letter-spacing:1px;text-transform:uppercase;
padding:3px 8px;border-radius:99px;background:rgba(10,10,10,.78);border:1px solid var(--gold);color:var(--gold)}
.badge.case{border-color:var(--red);color:var(--red)}
.newb{position:absolute;top:10px;right:10px;font-family:var(--mono);font-size:10px;letter-spacing:1px;padding:3px 8px;border-radius:99px;
background:var(--green);color:#06210f;font-weight:600}
.body{padding:12px 13px;display:flex;flex-direction:column;gap:8px;flex:1}
.t{font-size:13px;line-height:1.35;max-height:3.5em;overflow:hidden;color:var(--text)}
.set{font-family:var(--mono);font-size:11px;color:var(--muted);text-transform:uppercase;letter-spacing:.5px}
.row{display:flex;justify-content:space-between;align-items:baseline;gap:8px;font-family:var(--mono);font-variant-numeric:tabular-nums}
.k{color:var(--muted);font-size:11px}.big{font-size:20px;font-weight:500}
.disc{font-family:var(--display);font-size:26px;letter-spacing:1px;line-height:1}.ends{color:var(--gold);font-weight:500}
.flags{display:flex;gap:6px;flex-wrap:wrap;margin-top:2px}
.flag{font-family:var(--mono);font-size:10px;padding:2px 7px;border-radius:99px;border:1px solid var(--line);color:var(--muted)}
.flag.warn{color:var(--gold);border-color:var(--gold)}
.actions{display:flex;gap:8px;margin-top:auto;padding-top:6px}
a.open,button.dq{flex:1;text-align:center;font-family:var(--sans);font-size:12px;font-weight:600;padding:10px;border-radius:8px;cursor:pointer;text-decoration:none}
a.open{background:var(--gold);color:#1a1500;border:1px solid var(--gold)}a.open:hover{filter:brightness(1.08)}
button.dq{background:transparent;color:var(--muted);border:1px solid var(--line)}button.dq:hover{border-color:var(--red);color:var(--red)}
.empty{color:var(--muted);font-family:var(--mono);font-size:12px;padding:6px 0}
@media (max-width:560px){
  header{padding:11px 14px;gap:8px 12px}
  .brand{font-size:23px}.sub{display:none}
  .sec{padding:14px}
  .grid{gap:11px}
  .thumb{height:200px}
  a.open,button.dq{padding:13px;font-size:14px}
  .disc{font-size:24px}
  .toggle{margin-left:auto}
}
</style></head><body>
<header>
  <div class="brand">ELITE DECK<span>LAB</span></div><div class="sub">Arbitrage Scanner</div>
  <div class="meta">updated __UPDATED__</div><div class="meta" id="counts"></div><div class="toggle" id="toggle"></div>
</header>
<div class="sec bin"><h2>Buy It Now</h2><div class="grid" id="bin"></div></div>
<div class="sec auc"><h2>Auctions · Ending Soon</h2><div class="grid" id="auc"></div></div>
<script>
const OPPS=__OPPS_JSON__, CAP=__CAP__, DQKEY="arb_disq"; let showDq=false;
function dq(){try{return JSON.parse(localStorage.getItem(DQKEY)||"[]")}catch(e){return[]}}
function setDq(a){localStorage.setItem(DQKEY,JSON.stringify(a))}
function fmt(n){return n==null?"—":"$"+Number(n).toFixed(2)}
function hrs(iso){return (new Date(iso)-new Date())/3600000}
function tleft(iso){let h=hrs(iso);if(h<=0)return"ended";if(h<1)return Math.round(h*60)+"m";return Math.floor(h)+"h "+Math.round((h%1)*60)+"m"}
function dcolor(r){if(r<=0.6)return"var(--green)";if(r<=0.72)return"#9ee6b0";return"var(--gold)"}
function card(o,isDq,i){
  const d=document.createElement("div");d.className="card";d.style.animationDelay=(i*22)+"ms";
  const off=Math.round((1-o.ratio)*100), flags=[];
  if(o.mkt_est)flags.push('<span class="flag warn">mkt est (asks)</span>');
  if(!o.shipping_known)flags.push('<span class="flag warn">ship: calc — verify</span>');
  if(o.feedback_score!=null)flags.push('<span class="flag">'+o.feedback_pct+'% · '+o.feedback_score+'</span>');
  let mid;
  if(o.kind==="BIN"){
    mid=`<div class="row"><span class="k">item + ship</span><span class="big">${fmt(o.total)}</span></div>
         <div class="row"><span class="k">item ${fmt(o.item_price)} · ship ${o.shipping_known?fmt(o.shipping):"calc"}</span>
         <span class="disc" style="color:${dcolor(o.ratio)}">${off}%</span></div>`;
  }else{
    mid=`<div class="row"><span class="k">current bid</span><span class="big">${fmt(o.current_bid)}</span></div>
         <div class="row"><span class="k">min next ${fmt(o.min_next_bid)} · ${o.bids||0} bids</span>
         <span class="disc" style="color:${dcolor(o.ratio)}">${off}%</span></div>
         <div class="row"><span class="k">ends in</span><span class="ends">${tleft(o.end_date)}</span></div>`;
  }
  d.innerHTML=`<div class="thumb" style="background-image:url('${o.image||""}')"></div>
    <div class="badge${o.is_case?' case':''}">${o.type}</div>${(o.is_new&&!isDq)?'<div class="newb">NEW</div>':''}
    <div class="body"><div class="t">${o.title||""}</div><div class="set">${o.set_name} · mkt ${fmt(o.market)}</div>
      ${mid}<div class="flags">${flags.join("")}</div>
      <div class="actions"><a class="open" href="${o.url}" target="_blank" rel="noopener">Open listing</a>
      <button class="dq">${isDq?"Restore":"Disqualify"}</button></div></div>`;
  d.querySelector(".dq").onclick=()=>{let a=dq();isDq?a=a.filter(x=>x!==o.item_id):a.push(o.item_id);setDq(a);render();};
  return d;
}
function render(){
  const dd=dq(),B=document.getElementById("bin"),A=document.getElementById("auc");B.innerHTML="";A.innerHTML="";
  let act=OPPS.filter(o=>o.kind!=="AUCTION"||hrs(o.end_date)>0);
  let vis=act.filter(o=>showDq?dd.includes(o.item_id):!dd.includes(o.item_id));
  let bins=vis.filter(o=>o.kind==="BIN").sort((a,b)=>a.ratio-b.ratio).slice(0,CAP);
  let aucs=vis.filter(o=>o.kind==="AUCTION").sort((a,b)=>hrs(a.end_date)-hrs(b.end_date)).slice(0,CAP);
  bins.forEach((o,i)=>B.appendChild(card(o,showDq,i)));aucs.forEach((o,i)=>A.appendChild(card(o,showDq,i)));
  if(!bins.length)B.innerHTML='<div class="empty">none</div>';if(!aucs.length)A.innerHTML='<div class="empty">none</div>';
  const nd=act.filter(o=>dd.includes(o.item_id)).length;
  document.getElementById("counts").textContent=bins.length+" BIN · "+aucs.length+" auction"+(showDq?" (disqualified)":"");
  document.getElementById("toggle").textContent=showDq?"← active":"disqualified ("+nd+")";
}
document.getElementById("toggle").onclick=()=>{showDq=!showDq;render();};
render();setInterval(render,30000);
</script></body></html>"""

def render_dashboard(opps, cycle_iso):
    slim = [dict(o, is_new=(o.get("first_seen") == cycle_iso)) for o in opps]
    out = (DASH.replace("__OPPS_JSON__", json.dumps(slim)).replace("__CAP__", str(MAX_PER_SECTION))
               .replace("__UPDATED__", datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    with open(DASHBOARD, "w", encoding="utf-8") as f: f.write(out)


# --------------------------- local web server (also serves on Render) ---------------------------
class DashHandler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *a, **k): super().__init__(*a, directory=PROJECT_DIR, **k)
    def do_GET(self):
        if self.path in ("/", "/index.html"): self.path = "/dashboard.html"
        return super().do_GET()
    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()
    def log_message(self, *a): pass

def serve_dashboard():
    try:
        http.server.ThreadingHTTPServer((DASH_HOST, DASH_PORT), DashHandler).serve_forever()
    except Exception as e:
        log(f"dashboard server error: {e}")

def open_dashboard():
    if IS_CLOUD: return
    url = f"http://localhost:{DASH_PORT}/"
    for ch in [r"C:\Program Files\Google\Chrome\Application\chrome.exe",
               r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
               os.path.expandvars(r"%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe")]:
        try:
            if os.path.exists(ch):
                subprocess.Popen([ch, "--new-window", url]); return
        except Exception: pass
    try: webbrowser.open(url, new=1)
    except Exception: pass


# --------------------------- main ---------------------------
def write_universe_report(universe):
    try:
        with open(UNIVERSE_CSV, "w", newline="", encoding="utf-8") as f:
            wr = csv.writer(f); wr.writerow(["set_name", "type", "product_id", "market", "name", "query"])
            for p in universe:
                wr.writerow([p["set_name"], p["type_label"], p["product_id"], p["market"], p["name"], p["query"]])
    except Exception: pass

def main():
    keys = Keys()
    opps = load_json(OPPS_PATH, [])
    render_dashboard(opps, now_utc().isoformat())
    threading.Thread(target=serve_dashboard, daemon=True).start()
    time.sleep(0.5)
    log(f"dashboard serving on {DASH_HOST}:{DASH_PORT}" + ("" if IS_CLOUD else "  (open http://localhost:%d/)" % DASH_PORT))
    open_dashboard()
    setid_map = build_setid_map()
    tok = keys.ebay_token()
    universe = build_universe(keys, setid_map, dump=True) + gem_universe(tok)
    write_universe_report(universe)
    by_t = Counter(p["type_label"] for p in universe)
    log(f"universe: {len(universe)} products ({len(PRIORITY_SETS)} sets + {len(GEM_PACKS)} gem cases)")
    log("  " + ", ".join(f"{k}:{v}" for k, v in sorted(by_t.items())))
    while True:
        cstart = now_utc(); cycle_iso = cstart.isoformat()
        try:
            tok = keys.ebay_token()
            universe = build_universe(keys, setid_map) + gem_universe(tok)
            uni_by_pid = {p["product_id"]: p for p in universe}
            opps = validate(tok, opps, uni_by_pid, cycle_iso)
            added = scan(tok, universe, {o["item_id"] for o in opps}, cycle_iso)
            opps.extend(added); save_json(OPPS_PATH, opps)
            render_dashboard(opps, cycle_iso)
            log(f"cycle done: {len(opps)} active opps (+{len(added)} new)")
            if added and not IS_CLOUD: print("\a", end="", flush=True)
        except Exception as e:
            log(f"cycle error: {e}")
        time.sleep(CYCLE_MINUTES * 60)

if __name__ == "__main__":
    main()
