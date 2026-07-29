#!/usr/bin/env python3
"""
EDL Arbitrage Scanner - v16 (Mega Evolution + earlier Scarlet & Violet sets added)

v16 changes vs v15:
  - PRIORITY_SETS expanded: added Mega Evolution, Perfect Order, Chaos Rising
    (Mega Evolution era) and Scarlet & Violet, Paldea Evolved, Obsidian Flames,
    151, Paradox Rift, Paldean Fates, Temporal Forces, Shrouded Fable,
    Stellar Crown (earlier Scarlet & Violet era).
  - SETID_FALLBACK: added corresponding set_ids resolved via Pokedata /api/sets.
  - No product-type logic changed. BB/ETB/ETB_CASE/BUNDLE_CASE/etc. detection
    already runs per-catalog per-set, so new sets get full type coverage
    automatically once their catalog is pulled.
  - Pitch Black (5th ME set, releases 2026-07-17) intentionally NOT added yet —
    not in Pokedata's catalog until it releases. Re-run find_set_ids.py after
    release to grab its set_id.

v15 changes vs v14:
  - dashboard order flipped: Auctions (Ending Soon) shown first, Buy It Now below.

v14: seller-feedback gate (0-feedback sellers excluded; env EDL_MIN_FEEDBACK, default 1).

Run only ONE instance (local OR Render); eBay's 5,000 Browse calls/day cap is per app key.
"""

import os, sys, json, csv, time, base64, re, unicodedata, webbrowser, subprocess, threading, http.server
from collections import defaultdict, Counter
from datetime import datetime, timezone, timedelta

try:
    import requests
except ImportError:
    print("MISSING DEPENDENCY: run  pip install requests  then re-run.")
    sys.exit(1)

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import edl_price_guard as price_guard
except Exception as _e:                                    # scanner must run regardless
    price_guard = None
    print(f"[warn] price guard unavailable ({_e}); arbitrage scanning unaffected.")

# ============================== CONFIG ==============================
IS_CLOUD      = bool(os.environ.get("RENDER") or os.environ.get("EDL_CLOUD"))
PROJECT_DIR   = os.environ.get("EDL_DIR", r"D:\Arbitrage Scanner")
os.makedirs(PROJECT_DIR, exist_ok=True)
ALL_SETS_JSON = r"C:\Users\adam.george\Documents\Price Scraper\Data\Pokedata Cache\all_sets.json"
EBAY_KEYS     = os.path.join(PROJECT_DIR, "eBay Keys.txt")
POKEDATA_KEYS = os.path.join(PROJECT_DIR, "Pokedata Keys.txt")
MARKET_CACHE  = os.path.join(PROJECT_DIR, "market_cache.json")
PRICE_ALERTS_PATH = os.path.join(PROJECT_DIR, "price_alerts.json")
# Flag our own listings priced below this share of market value. Overpricing is
# deliberate on our side and is never flagged.
PRICE_UNDER_RATIO = float(os.environ.get("EDL_UNDER_RATIO", "0.90"))
OPPS_PATH     = os.path.join(PROJECT_DIR, "opps.json")
DASHBOARD     = os.path.join(PROJECT_DIR, "dashboard.html")
UNIVERSE_CSV  = os.path.join(PROJECT_DIR, "universe_market.csv")
CATALOG_DUMP  = os.path.join(PROJECT_DIR, "catalog_dump.csv")
DASH_PORT     = int(os.environ.get("PORT", "8787"))
DASH_HOST     = "0.0.0.0" if IS_CLOUD else "127.0.0.1"

PRIORITY_SETS = ["Ascended Heroes", "Destined Rivals", "Prismatic Evolutions", "Black Bolt",
                 "White Flare", "Journey Together", "Surging Sparks", "Silver Tempest",
                 "Crown Zenith", "Twilight Masquerade",
                 # Mega Evolution era additions
                 "Mega Evolution", "Phantasmal Flames", "Pitch Black",
                 "Perfect Order", "Chaos Rising",
                 # Earlier Scarlet & Violet era additions
                 "Scarlet & Violet", "Paldea Evolved", "Obsidian Flames", "151",
                 "Paradox Rift", "Paldean Fates", "Temporal Forces", "Shrouded Fable",
                 "Stellar Crown",
                 # 2026-07-27: Sword & Shield era backfill. The scanner previously
                 # covered only Silver Tempest and Crown Zenith out of 18 S&S sets.
                 "Sword & Shield", "Rebel Clash", "Darkness Ablaze", "Champion's Path",
                 "Vivid Voltage", "Shining Fates", "Battle Styles", "Chilling Reign",
                 "Evolving Skies", "Celebrations", "Fusion Strike", "Brilliant Stars",
                 "Astral Radiance", "Pokemon GO", "Lost Origin",
                 "Trading Card Game Classic",
                 # 2026-07-27: promo / collab sets across all three eras
                 "Sword & Shield Promo", "Celebrations: Classic Collection",
                 "Trick or Trade 2022", "Mcdonald's 25th Anniversary",
                 "Mcdonald's Promos 2022", "Scarlet & Violet Promos",
                 "Trick or Trade 2023", "Trick or Trade 2024",
                 "McDonald's Promos 2023", "Mcdonald's Dragon Discovery",
                 "Mega Evolution Promos"]
# Per-set narrowing of ENABLED_TYPES. A set listed here is scanned on eBay ONLY
# for the type keys given; everything else in that set is skipped. Sets absent
# from this map are scanned for all ENABLED_TYPES as usual.
# 2026-07-26: we have enough Perfect Order / Chaos Rising sealed singles, so eBay
# scanning for them is narrowed to case-sized buys only. This does NOT affect the
# storefront price guard, which still checks every product in both sets.
SET_TYPE_LIMITS = {
    "perfect order": {"BB_CASE", "ETB_CASE"},
    "chaos rising":  {"BB_CASE", "ETB_CASE"},
}

# "Mega Evolution" and "Scarlet & Violet" are BASE set names AND the era prefix
# printed on every later set in their era ("Mega Evolution-Phantasmal Flames").
# set_tokens() therefore reduces the base sets to {mega, evolution} / {scarlet,
# violet}, which every era listing also satisfies — so an Ascended Heroes ETB
# would match the base Mega Evolution ETB and get valued at the wrong market.
# Each base set must exclude its siblings' names. Keep these lists updated as
# new sets in either era release.
ERA_SIBLING_EXCLUDES = {
    "mega evolution": ["phantasmal flames", "ascended heroes", "perfect order",
                       "chaos rising", "pitch black", "mega rising"],
    "scarlet violet": ["paldea evolved", "obsidian flames", "151", "paradox rift",
                       "paldean fates", "temporal forces", "twilight masquerade",
                       "shrouded fable", "stellar crown", "surging sparks",
                       "prismatic evolutions", "journey together", "destined rivals",
                       "white flare", "black bolt"],
    # Note: "151" is matched as a plain substring, so a base Scarlet & Violet
    # listing containing those digits for another reason is skipped. Losing an
    # occasional base-set hit beats valuing a 151 product at base-set market.
}

ENABLED_TYPES = ["ETB", "PC_ETB", "BB", "BUNDLE", "UPC", "SPC",
                 "ETB_CASE", "PC_ETB_CASE", "BB_CASE", "BUNDLE_CASE", "MINI_TIN_DISPLAY"]

# ============ ONE PIECE (booster boxes only) ============
# Added 2026-07-29. Booster boxes are the only One Piece sealed format with a
# record worth acting on: measured from a near-launch buy the median box did
# 2.5x, and every box in ~3 years of history that was bought and held is up.
# Cases, starter decks and loose packs all underperformed the market, and the
# loose Double Pack price data is too noisy to trade on -- so none are included.
#
# Market values come from the same pokedata /api/products endpoint the Pokemon
# path uses, so this works unchanged on Render.
ONE_PIECE_SETS = [
    (3202, "Romance Dawn", "OP01"),
    (3198, "Paramount War", "OP02"),
    (3195, "Pillars of Strength", "OP03"),
    (3191, "Kingdoms of Intrigue", "OP04"),
    (3188, "Awakening of the New Era", "OP05"),
    (3185, "Wings of the Captain", "OP06"),
    (3180, "500 Years in the Future", "OP07"),
    (3177, "Two Legends", "OP08"),
    (3166, "Emperors in the New World", "OP09"),
    (3163, "Royal Blood", "OP10"),
    (3154, "A Fist of Divine Speed", "OP11"),
    (3152, "Legacy of the Master", "OP12"),
    (3631, "Carrying On His Will", "OP13"),
    (3629, "The Azure Sea's Seven", "OP14"),
    (3182, "Extra Booster Memorial Collection", "EB01"),
    (3627, "Extra Booster One Piece Heroines Edition", "EB03"),
    (3170, "Premium Booster The Best", "PRB01"),
    (3150, "Premium Booster The Best Vol 2", "PRB02"),
]

# pokedata carries no sealed PRODUCTS for the newest sets yet -- verified
# 2026-07-29: /api/products returns 0 rows for OP15, OP16 and ST-30 (cards only).
# These are exactly the sets with the most active listings, so they get a manual
# market value sourced from PriceCharting.
#
# THESE GO STALE. The scanner logs a warning every cycle it uses one, and logs
# when pokedata starts carrying the product so the entry can be deleted. Review
# whenever you see that message.
OP_MANUAL_MARKET = {
    # set_id: (set name, set code, booster box market value, as-of date)
    3875: ("The Time of Battle", "OP16", 202.50, "2026-07-29"),
    3836: ("Adventure on Kami's Island", "OP15", 240.22, "2026-07-29"),
}

# One Piece booster boxes must never match Pokemon listings, or a $200 One Piece
# box gets valued against a Pokemon set's market. "one piece" is required on
# every title and "pokemon" is excluded.
OP_BOX_REQUIRE = [["one piece"], ["booster box", "booster display"]]

BIN_MAX_RATIO, AUCTION_MAX_RATIO, AUCTION_MAX_HOURS = 0.80, 0.70, 24
SHIP_UNKNOWN_MAX_RATIO = 0.65
BIN_MIN_RATIO, AUCTION_MIN_RATIO = 0.20, 0.10
MARKET_REFRESH_HOURS = 6
# eBay's Browse API allows 5,000 calls/day per app key. MAX_CALLS_PER_CYCLE is
# OUR budget, sized so (calls per sweep x cycles per day) stays under that cap.
#
# A full sweep costs roughly: 2 calls per universe product (one BIN search, one
# auction search) + 1 call per active opp during validate(). Note build_universe
# emits ONE row per (set, type) via pick_base, not one per raw product.
#
# 2026-07-27: the S&S + promo backfill took the universe from 156 to 233 products
# (measured), so a sweep is ~466 scan + ~50 validate = ~516 calls. At the old
# 90-minute cycle that would be ~8,250 calls/day -- well over the cap. A 4-hour
# cycle gives 6 sweeps/day at ~516 calls = ~3,100/day, comfortably inside 5,000.
#
# The old 280 budget was ALREADY too small before this change: 156 products cost
# ~362 calls, so scan() hit the ceiling and stopped partway. It restarts at index
# 0 every cycle with no resume offset, so the alphabetical tail of the universe
# (Stellar Crown through White Flare) was reached only in cycles where few opps
# needed validating. If the universe ever outgrows the budget again, that silent
# blind spot returns -- raise MAX_CALLS_PER_CYCLE rather than letting it truncate.
#
# Sealed prices don't move on a 90-minute timescale, and AUCTION_MAX_HOURS is 24,
# so a 4-hour cycle still sees every ending auction with hours of lead time.
#
# If you change one of these, recheck the other: cycles_per_day = 1440/CYCLE_MINUTES
# and cycles_per_day * MAX_CALLS_PER_CYCLE must stay under 5,000.
CYCLE_MINUTES = int(os.environ.get("EDL_CYCLE_MIN", "480"))
MAX_CALLS_PER_CYCLE = int(os.environ.get("EDL_MAX_CALLS", "600"))
MIN_FEEDBACK_SCORE = int(os.environ.get("EDL_MIN_FEEDBACK", "1"))     # 0-feedback sellers excluded
RATE_LIMIT_PAUSE_MIN = 60
EBAY_MARKETPLACE = "EBAY_US"
BIN_LIMIT, AUCTION_LIMIT, MAX_PER_SECTION, POLITE_SLEEP = 50, 100, 80, 0.2
GEM_ASK_SAMPLE, GEM_ASK_MIN = 100, 4
EBAY_BROWSE = "https://api.ebay.com/buy/browse/v1/item_summary/search"
EBAY_ITEM   = "https://api.ebay.com/buy/browse/v1/item/"

SETID_FALLBACK = {"ascended heroes": 3591, "destined rivals": 567, "prismatic evolutions": 557,
                  "black bolt": 570, "white flare": 571, "journey together": 562,
                  "surging sparks": 555, "silver tempest": 503, "crown zenith": 506,
                  "twilight masquerade": 545,
                  # Mega Evolution era (perfect order / chaos rising kept here so the
                  # price guard can resolve them and they're one edit from returning)
                  "mega evolution": 574, "phantasmal flames": 3589, "pitch black": 3859,
                  "perfect order": 3665, "chaos rising": 3850,
                  # Earlier Scarlet & Violet era
                  "scarlet & violet": 510, "paldea evolved": 513, "obsidian flames": 517,
                  "151": 532, "paradox rift": 536, "paldean fates": 539,
                  "temporal forces": 542, "shrouded fable": 548, "stellar crown": 549,
                  # Sword & Shield era (added 2026-07-27)
                  "sword & shield": 6, "rebel clash": 5, "darkness ablaze": 4,
                  "champion's path": 2, "vivid voltage": 3, "shining fates": 21,
                  "battle styles": 20, "chilling reign": 26, "evolving skies": 108,
                  "celebrations": 112, "fusion strike": 172, "brilliant stars": 178,
                  "astral radiance": 182, "pokemon go": 387, "lost origin": 400,
                  "trading card game classic": 561,
                  # Promo / collab sets (added 2026-07-27)
                  "sword & shield promo": 109, "celebrations: classic collection": 111,
                  "trick or trade 2022": 504, "mcdonald's 25th anniversary": 171,
                  "mcdonald's promos 2022": 399, "scarlet & violet promos": 515,
                  "trick or trade 2023": 531, "trick or trade 2024": 554,
                  "mcdonald's promos 2023": 530, "mcdonald's dragon discovery": 559,
                  "mega evolution promos": 575}

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

# One Piece box exclusions: the usual junk, every non-English language, anything
# case-sized, and Pokemon itself (a cross-match would value a One Piece box
# against a Pokemon market).
OP_BOX_EXCLUDE = JUNK + ["pokemon", "case", "carton", "starter deck", "ultra deck",
                         "double pack", "sleeved", "single pack", "tin", "deck box"]

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
def feedback_int(v):
    try: return int(v)
    except (TypeError, ValueError): return None


# --------------------------- eBay request gate (rate-limit aware) ---------------------------
class RateLimit(Exception):
    pass
_calls = {"n": 0, "remaining": None}

def _ebay_get(url, headers, params):
    _calls["n"] += 1
    r = requests.get(url, headers=headers, params=params, timeout=25)
    rem = r.headers.get("X-EBAY-C-RateLimit-Remaining") or r.headers.get("x-ebay-c-ratelimit-remaining")
    if rem is not None:
        _calls["remaining"] = rem
    if r.status_code == 429:
        raise RateLimit()
    return r


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


# --------------------------- pokedata catalog (not eBay; no rate limit) ---------------------------
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

def op_box_variant_filters(name):
    """Distinguish One Piece print waves so a box isn't valued at the wrong market.

    OP01 exists as Wave 1 (blue bottom, ~$6.3k) and Wave 2 (white bottom, ~$1.6k)
    with identical cards. Valuing a white-bottom box against the blue market would
    make an ordinary listing look like a 4x steal, so each wave carries its own
    require/exclude terms.
    """
    n = norm(name)
    if "wave 1" in n or "blue" in n:
        return [["blue"]], []                    # only match explicit blue-bottom
    if "wave 2" in n or "white" in n:
        return [], ["blue"]                      # default box; never match blue
    return [], []


def op_identifier_group(sname, code):
    """Accept EITHER the set code or a distinctive set word.

    Sellers often title a box "One Piece OP-16 Booster Box" with no set name at
    all. Requiring every set-name token would silently miss those. Short tokens
    are dropped so a generic word can't create a false match; "one piece" and
    "booster box" are required separately, so this group only has to identify
    WHICH set.
    """
    # norm() converts hyphens to SPACES, so "OP-16" in a title becomes "op 16".
    # Cover the joined and spaced spellings; the hyphenated form never survives norm.
    letters = code.rstrip("0123456789").lower()
    digits = code[len(letters):]
    alts = [f"{letters}{digits}", f"{letters} {digits}"]
    alts += [t for t in set_tokens(sname) if len(t) >= 6]
    seen, out = set(), []
    for a in alts:
        if a and a not in seen:
            seen.add(a); out.append(a)
    return out


def build_op_universe(keys, dump_rows=None):
    """One Piece booster boxes. One universe entry per box SKU (waves kept apart)."""
    uni = []
    sets = [(sid, nm, cd) for sid, nm, cd in ONE_PIECE_SETS]
    sets += [(sid, meta[0], meta[1]) for sid, meta in OP_MANUAL_MARKET.items()]
    for sid, sname, scode in sets:
        products = get_catalog(keys, sid)
        boxes = []
        for p in products:
            nm = norm(p.get("name", ""))
            if (p.get("type") or "").upper() != "BOOSTERBOX":
                continue
            if "case" in nm or "carton" in nm:
                continue
            mv = p.get("market_value")
            if mv and float(mv) > 0:
                boxes.append(p)
            if dump_rows is not None:
                dump_rows.append([f"[OP] {sname}", p.get("id"), p.get("name"), mv, "OP_BB"])

        if not boxes and sid in OP_MANUAL_MARKET:
            nm, cd, mv, asof = OP_MANUAL_MARKET[sid]
            log(f"[OP] {nm}: pokedata has no sealed product; using MANUAL market "
                f"${mv:.2f} (as of {asof}) -- review this entry")
            uni.append({"product_id": f"opman-{sid}", "set_name": f"[OP] {nm}",
                        "tcg": "One Piece", "type_key": "OP_BB",
                        "type_label": "OP Booster Box", "is_case": False,
                        "name": f"{nm} Booster Box", "market": round(float(mv), 2),
                        "img": "", "query": f"One Piece {nm} Booster Box",
                        "require": OP_BOX_REQUIRE + [op_identifier_group(nm, cd)],
                        "exclude": OP_BOX_EXCLUDE, "market_src": "manual"})
            continue

        if boxes and sid in OP_MANUAL_MARKET:
            log(f"[OP] {sname}: pokedata now carries a booster box -- "
                f"remove it from OP_MANUAL_MARKET")

        for p in boxes:
            name = (p.get("name") or "").strip()
            req_extra, exc_extra = op_box_variant_filters(name)
            uni.append({
                "product_id": str(p.get("id")), "set_name": f"[OP] {sname}",
                "tcg": "One Piece", "type_key": "OP_BB",
                "type_label": "OP Booster Box", "is_case": False, "name": name,
                "market": round(float(p["market_value"]), 2), "img": p.get("img_url"),
                "query": f"One Piece {sname} Booster Box",
                "require": OP_BOX_REQUIRE + [op_identifier_group(sname, scode)] + req_extra,
                "exclude": OP_BOX_EXCLUDE + exc_extra,
            })
    uni.sort(key=lambda x: (x["set_name"], x["name"]))
    return uni


def build_universe(keys, setid_map, dump=False):
    uni, dump_rows = [], []
    for sn in PRIORITY_SETS:
        sid = setid_map.get(norm(sn))
        if sid is None:
            log(f"skip {sn!r}: no set_id found"); continue
        allowed = SET_TYPE_LIMITS.get(norm(sn))       # None = scan every enabled type
        cand = defaultdict(list)
        for p in get_catalog(keys, sid):
            key = select_type(p.get("name", ""))
            if key: cand[key].append(p)
            if dump:
                dump_rows.append([sn, p.get("id"), p.get("name"), p.get("market_value"), key or ""])
        if allowed is not None:
            cand = defaultdict(list, {k: v for k, v in cand.items() if k in allowed})
        for key, plist in cand.items():
            base = pick_base(plist)
            mv = base.get("market_value")
            if not mv or float(mv) <= 0:
                continue
            t, name = TYPES[key], (base.get("name") or "").strip()
            q = name if "pokemon" in name.lower() else "Pokemon " + name
            # A base era set must not swallow listings from its own era's sets.
            excl = t["exclude"] + ERA_SIBLING_EXCLUDES.get(norm(sn), [])
            uni.append({"product_id": str(base.get("id")), "set_name": sn,
                        "tcg": "Pokemon", "type_key": key,
                        "type_label": t["label"], "is_case": key in CASE_TYPES, "name": name,
                        "market": round(float(mv), 2), "img": base.get("img_url"), "query": q,
                        "require": [[s] for s in set_tokens(sn)] + t["require"], "exclude": excl})
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
    if not title_ok(title, prod["require"], prod["exclude"]): return False
    vr = prod.get("vol_re")
    if vr is not None and not vr.search(norm(title)): return False
    return True

def seller_ok(item):
    """Exclude sellers with 0 feedback (or no feedback score)."""
    fb = feedback_int((item.get("seller") or {}).get("feedbackScore"))
    return fb is not None and fb >= MIN_FEEDBACK_SCORE


# --------------------------- eBay ---------------------------
def ebay_search(token, q, filt, sort=None, limit=50):
    params = {"q": q, "limit": limit, "filter": filt}
    if sort: params["sort"] = sort
    r = _ebay_get(EBAY_BROWSE, {"Authorization": f"Bearer {token}", "X-EBAY-C-MARKETPLACE-ID": EBAY_MARKETPLACE}, params)
    return (r.json().get("itemSummaries") or []) if r.status_code == 200 else []

def ebay_get_item(token, item_id):
    r = _ebay_get(EBAY_ITEM + str(item_id),
                  {"Authorization": f"Bearer {token}", "X-EBAY-C-MARKETPLACE-ID": EBAY_MARKETPLACE},
                  {"fieldgroups": "COMPACT"})
    return r.json() if r.status_code == 200 else None

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

def eval_auction(item, prod):
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
    return o


# --------------------------- gem packs (CASES; not on Pokedata) ---------------------------
def gem_market(token, gp, key, vr):
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
        if not seller_ok(it): continue
        p = money(it.get("price"))
        if p is None: continue
        s, known = shipping_from(it)
        tot = p + (s or 0)
        if tot < mn: continue
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
            log(f"gem '{gp['label']}': no market ({src})")
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
        if _calls["n"] >= MAX_CALLS_PER_CYCLE:
            log(f"per-cycle call budget ({MAX_CALLS_PER_CYCLE}) reached — deferring remaining products to next cycle")
            break
        market = prod["market"]
        # 2026-07-29: fixed-price (Buy It Now) scanning removed entirely. That
        # side of eBay is dominated by mispriced, mislabelled and outright scam
        # listings for sealed TCG product, so the hit rate never justified the
        # calls. Dropping it also halves the per-product cost from 2 calls to 1,
        # which is what pays for the One Piece additions.
        lo = now_utc().strftime("%Y-%m-%dT%H:%M:%S.000Z")
        hi = (now_utc() + timedelta(hours=AUCTION_MAX_HOURS)).strftime("%Y-%m-%dT%H:%M:%S.000Z")
        auc_filt = f"buyingOptions:{{AUCTION}},conditionIds:{{1000}},itemEndDate:[{lo}..{hi}]"
        for it in ebay_search(token, prod["query"], auc_filt, limit=AUCTION_LIMIT):
            iid, title = it.get("itemId"), it.get("title", "")
            if not iid or iid in seen or not match_title(title, prod): continue
            if not seller_ok(it): continue
            if not prod.get("skip_case_gate") and is_true_case(title) != prod["is_case"]: continue
            o = eval_auction(it, prod)
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
        fb = feedback_int(o.get("feedback_score"))            # drop now-gated 0-feedback opps (no extra call)
        if fb is None or fb < MIN_FEEDBACK_SCORE: continue
        d = ebay_get_item(token, o["item_id"])
        if not d: continue
        end = parse_iso_z(d.get("itemEndDate"))
        if end and end <= now_utc(): continue
        market = prod["market"]; mn = prod.get("min_total", 0)
        if o["kind"] == "BIN":
            continue          # BIN retired 2026-07-29; drop any stale BIN opps
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
.pg h2{color:var(--red)}.pg h2:before{background:var(--red);box-shadow:0 0 8px var(--red)}
.pg .note{font-family:var(--mono);font-size:11px;color:var(--muted);margin:-6px 0 10px}
.pgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(min(100%,340px),1fr));gap:12px}
.pc{background:var(--card);border:1px solid var(--line);border-left:3px solid var(--red);border-radius:10px;
padding:11px 13px;display:flex;flex-direction:column;gap:7px}
.pc.oos{border-left-color:var(--muted);opacity:.72}
.pc .ttl{font-size:13px;line-height:1.35;color:var(--text)}
.pc .mrow{display:flex;justify-content:space-between;align-items:baseline;font-family:var(--mono);
font-variant-numeric:tabular-nums;gap:8px}
.pc .ours{font-size:19px;font-weight:500;color:var(--red)}
.pc .mkt{font-size:12px;color:var(--muted)}
.pc .pct{font-family:var(--display);font-size:24px;letter-spacing:1px;line-height:1;color:var(--red)}
.pc.oos .pct,.pc.oos .ours{color:var(--muted)}
.pc .stock{font-family:var(--mono);font-size:10px;letter-spacing:1px;text-transform:uppercase;
padding:2px 7px;border-radius:99px;border:1px solid var(--line);color:var(--muted);align-self:flex-start}
.pc .stock.live{border-color:var(--red);color:var(--red)}
.pc a{color:var(--gold);font-family:var(--mono);font-size:11px;text-decoration:none}
.pc a:hover{text-decoration:underline}
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
<div class="sec pg" id="pgsec"><h2>Our Pricing · Below Market</h2>
  <div class="note" id="pgnote"></div><div class="pgrid" id="pg"></div></div>
<div class="sec auc"><h2>Auctions · Ending Soon</h2><div class="grid" id="auc"></div></div>
<script>
const OPPS=__OPPS_JSON__, CAP=__CAP__, DQKEY="arb_disq"; let showDq=false;
const PRICE_ALERTS=__PRICE_ALERTS__, PRICE_STATS=__PRICE_STATS__;
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
  const dd=dq(),A=document.getElementById("auc");A.innerHTML="";
  let act=OPPS.filter(o=>o.kind==="AUCTION"&&hrs(o.end_date)>0);
  let vis=act.filter(o=>showDq?dd.includes(o.item_id):!dd.includes(o.item_id));
  let aucs=vis.sort((a,b)=>hrs(a.end_date)-hrs(b.end_date)).slice(0,CAP);
  aucs.forEach((o,i)=>A.appendChild(card(o,showDq,i)));
  if(!aucs.length)A.innerHTML='<div class="empty">none</div>';
  const nd=act.filter(o=>dd.includes(o.item_id)).length;
  document.getElementById("counts").textContent=aucs.length+" auction"+(showDq?" (disqualified)":"");
  document.getElementById("toggle").textContent=showDq?"← active":"disqualified ("+nd+")";
}
function renderPrice(){
  const P=document.getElementById("pg"),N=document.getElementById("pgnote");
  P.innerHTML="";
  const live=PRICE_ALERTS.filter(a=>a.available).length;
  N.textContent=PRICE_STATS.error
    ? "price check unavailable: "+PRICE_STATS.error
    : PRICE_ALERTS.length+" under "+Math.round(PRICE_STATS.under_ratio*100)+"% of market ("
      +live+" in stock) · "+PRICE_STATS.matched+" of "+PRICE_STATS.site_variants
      +" listings priced against market · "+PRICE_STATS.unmatched+" not covered";
  if(!PRICE_ALERTS.length){
    P.innerHTML='<div class="empty">'+(PRICE_STATS.error?"—":"nothing underpriced — all good")+'</div>';
    return;
  }
  PRICE_ALERTS.forEach(a=>{
    const d=document.createElement("div");
    d.className="pc"+(a.available?"":" oos");
    d.innerHTML=`<div class="ttl">${a.title}</div>
      <span class="stock${a.available?' live':''}">${a.available?'in stock':'sold out'}</span>
      <div class="mrow"><span class="ours">${fmt(a.price)}</span>
        <span class="pct">${a.under_pct}% under</span></div>
      <div class="mrow"><span class="mkt">market ${fmt(a.market)} · gap ${fmt(a.gap)}</span>
        <a href="${a.url}" target="_blank" rel="noopener">open ›</a></div>
      <div class="mkt" style="font-size:10px;opacity:.75">${a.set_name} · vs ${a.market_name}</div>`;
    P.appendChild(d);
  });
}
document.getElementById("toggle").onclick=()=>{showDq=!showDq;render();};
render();renderPrice();setInterval(render,30000);
</script></body></html>"""

def render_dashboard(opps, cycle_iso, price_alerts=None, price_stats=None):
    slim = [dict(o, is_new=(o.get("first_seen") == cycle_iso)) for o in opps]
    stats = dict(price_stats or {"error": "not run yet"})
    stats.setdefault("under_ratio", PRICE_UNDER_RATIO)
    stats.setdefault("site_variants", 0); stats.setdefault("matched", 0); stats.setdefault("unmatched", 0)
    out = (DASH.replace("__OPPS_JSON__", json.dumps(slim)).replace("__CAP__", str(MAX_PER_SECTION))
               .replace("__PRICE_ALERTS__", json.dumps(price_alerts or []))
               .replace("__PRICE_STATS__", json.dumps(stats))
               .replace("__UPDATED__", datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    with open(DASHBOARD, "w", encoding="utf-8") as f: f.write(out)


# --------------------------- storefront price guard ---------------------------
def run_price_guard(keys, setid_map):
    """Compare our storefront prices to market. Never raises; never uses eBay quota."""
    if price_guard is None:
        return [], {"error": "edl_price_guard.py not found"}
    try:
        rows = price_guard.market_rows_from_scanner(get_catalog, keys, setid_map, PRIORITY_SETS)
        if not rows:
            return [], {"error": "no market data yet"}
        alerts, stats, _matched, _unmatched = price_guard.build_alerts(rows, PRICE_UNDER_RATIO)
        stats["under_ratio"] = PRICE_UNDER_RATIO
        save_json(PRICE_ALERTS_PATH, {"stats": stats, "alerts": alerts})
        live = sum(1 for a in alerts if a["available"])
        log(f"price guard: {len(alerts)} under {PRICE_UNDER_RATIO:.0%} of market "
            f"({live} in stock) | {stats['matched']}/{stats['site_variants']} listings checked")
        return alerts, stats
    except Exception as e:
        log(f"price guard error: {e}")
        return [], {"error": str(e)[:120]}


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
    # Show last run's price alerts immediately so the page is never empty on open.
    cached = load_json(PRICE_ALERTS_PATH, {})
    price_alerts, price_stats = cached.get("alerts", []), cached.get("stats", {})
    render_dashboard(opps, now_utc().isoformat(), price_alerts, price_stats)
    threading.Thread(target=serve_dashboard, daemon=True).start()
    time.sleep(0.5)
    log(f"dashboard serving on {DASH_HOST}:{DASH_PORT}" + ("" if IS_CLOUD else "  (open http://localhost:%d/)" % DASH_PORT))
    open_dashboard()
    setid_map = build_setid_map()
    # Price guard runs on open, before the (slower) eBay work.
    price_alerts, price_stats = run_price_guard(keys, setid_map)
    render_dashboard(opps, now_utc().isoformat(), price_alerts, price_stats)
    try:
        tok = keys.ebay_token()
        universe = build_universe(keys, setid_map, dump=True) + build_op_universe(keys) + gem_universe(tok)
        write_universe_report(universe)
        by_t = Counter(p["type_label"] for p in universe)
        log(f"universe: {len(universe)} products ({len(PRIORITY_SETS)} sets + {len(GEM_PACKS)} gem cases)")
        log("  " + ", ".join(f"{k}:{v}" for k, v in sorted(by_t.items())))
    except RateLimit:
        log("eBay rate-limited at startup (daily 5,000 cap). Will keep retrying; quota resets 07:00 UTC.")
    except Exception as e:
        log(f"startup build error: {e}")
    while True:
        cycle_iso = now_utc().isoformat()
        _calls["n"] = 0
        try:
            tok = keys.ebay_token()
            universe = build_universe(keys, setid_map) + build_op_universe(keys) + gem_universe(tok)
            uni_by_pid = {p["product_id"]: p for p in universe}
            opps = validate(tok, opps, uni_by_pid, cycle_iso)
            added = scan(tok, universe, {o["item_id"] for o in opps}, cycle_iso)
            opps.extend(added); save_json(OPPS_PATH, opps)
            price_alerts, price_stats = run_price_guard(keys, setid_map)
            render_dashboard(opps, cycle_iso, price_alerts, price_stats)
            log(f"cycle done: {len(opps)} active opps (+{len(added)} new) | eBay calls {_calls['n']}, remaining {_calls['remaining']}")
            if added and not IS_CLOUD: print("\a", end="", flush=True)
        except RateLimit:
            log(f"eBay daily call cap (5,000) hit after {_calls['n']} calls — pausing {RATE_LIMIT_PAUSE_MIN} min (resets 07:00 UTC)")
            time.sleep(RATE_LIMIT_PAUSE_MIN * 60); continue
        except Exception as e:
            log(f"cycle error: {e}")
        time.sleep(CYCLE_MINUTES * 60)

if __name__ == "__main__":
    main()
