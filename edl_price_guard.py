"""
EDL Price Guard — flags storefront prices that sit below market value.

Compares live elitedecklab.com prices against Pokedata market values and
reports anything priced under a threshold (default 90%) of market. Overpricing
is never flagged; that's intentional on our side.

Matching is deliberately conservative: a product only matches when the SET and
a canonical PRODUCT TYPE both agree exactly, then name similarity breaks ties.
An unmatched product is reported as unmatched rather than guessed at, because a
wrong match (e.g. Booster Pack -> Booster Box) would produce a false alarm on a
correctly priced item.

Used as a library by arb_scanner (build_alerts) and runnable standalone:
    python edl_price_guard.py            # report from catalog_dump.csv
    python edl_price_guard.py --json     # machine-readable
"""

import csv
import json
import os
import re
import sys
import urllib.request
from datetime import datetime, timezone

STORE = "https://elitedecklab.com"
PROJECT_DIR = os.environ.get("EDL_DIR", r"D:\Arbitrage Scanner")
CATALOG_DUMP = os.path.join(PROJECT_DIR, "catalog_dump.csv")
ALERTS_PATH = os.path.join(PROJECT_DIR, "price_alerts.json")

UNDER_RATIO = float(os.environ.get("EDL_UNDER_RATIO", "0.90"))   # flag below 90% of market
MIN_MARKET = float(os.environ.get("EDL_MIN_MARKET", "5"))        # ignore trivial market values
NAME_SIM_MIN = 0.75    # market name's words that must appear in our title

# "Scarlet & Violet" and "Mega Evolution" name real base sets, but they are also
# the ERA prefix on nearly every later set's title ("Scarlet & Violet—Surging
# Sparks ..."). They must therefore only be considered when no specific set in
# the title matches, or every product collapses onto the base set's market value.
ERA_SETS = {"Scarlet & Violet", "Mega Evolution"}

# --- set aliases: how a set appears on our site vs in Pokedata ---------------
SET_ALIASES = {
    "151": ["151"],
    "Ascended Heroes": ["ascended heroes"],
    "Black Bolt": ["black bolt"],
    "Chaos Rising": ["chaos rising"],
    "Crown Zenith": ["crown zenith"],
    "Destined Rivals": ["destined rivals"],
    "Journey Together": ["journey together"],
    "Mega Evolution": ["mega evolution"],
    "Obsidian Flames": ["obsidian flames"],
    "Paldea Evolved": ["paldea evolved"],
    "Paldean Fates": ["paldean fates"],
    "Paradox Rift": ["paradox rift"],
    "Perfect Order": ["perfect order"],
    "Phantasmal Flames": ["phantasmal flames"],
    "Pitch Black": ["pitch black"],
    "Prismatic Evolutions": ["prismatic evolutions"],
    "Scarlet & Violet": ["scarlet & violet", "scarlet and violet"],
    "Shrouded Fable": ["shrouded fable"],
    "Silver Tempest": ["silver tempest"],
    "Stellar Crown": ["stellar crown"],
    "Surging Sparks": ["surging sparks"],
    "Temporal Forces": ["temporal forces"],
    "Twilight Masquerade": ["twilight masquerade"],
    "White Flare": ["white flare"],
}

# --- canonical product types. ORDER MATTERS: most specific first. ------------
# (canonical, [patterns]) — a name's type is the FIRST pattern that matches.
TYPE_RULES = [
    ("PC_ETB_CASE",   [r"pokemon center elite trainer box.*\bcase\b", r"pc etb.*\bcase\b"]),
    ("ETB_CASE",      [r"elite trainer box.*\bcase\b", r"\betb\b.*\bcase\b"]),
    ("BB_CASE",       [r"booster box.*\bcase\b"]),
    ("BUNDLE_CASE",   [r"booster bundle.*(?:\bcase\b|bulk case)"]),
    ("MINI_TIN_5PK",  [r"mini tins? 5-?pack", r"mini tins? five pack"]),
    ("MINI_TIN_DISP", [r"mini tin display"]),
    ("UPC",           [r"ultra-?premium collection"]),
    ("SPC",           [r"super-?premium collection"]),
    ("PC_ETB",        [r"pokemon center elite trainer box", r"\bpc etb\b"]),
    ("ETB",           [r"elite trainer box", r"\betb\b"]),
    ("BB",            [r"booster box"]),
    ("BUNDLE",        [r"booster bundle"]),
    ("SLEEVED_PACK",  [r"sleeved booster pack"]),
    ("PACK",          [r"booster pack", r"\bbooster\b(?!\s*(?:box|bundle))"]),
    ("BLISTER_3",     [r"3-?pack blister", r"three pack blister"]),
    ("BLISTER_2",     [r"2-?pack blister", r"two pack blister", r"enhanced 2-?pack"]),
    ("BLISTER",       [r"blister"]),
    ("MINI_TIN",      [r"mini tin"]),
    ("TIN",           [r"\btin\b"]),
    ("PIN_COLLECTION", [r"pin collection"]),
    ("POSTER_COLL",   [r"poster collection"]),
    ("PREMIUM_COLL",  [r"premium collection"]),
    ("SURPRISE_BOX",  [r"surprise box"]),
    ("PORTFOLIO",     [r"portfolio"]),
    ("EX_BOX",        [r"\bex box\b", r"ex premium", r"\bshowcase\b"]),
    ("COLLECTION",    [r"collection"]),
]


def norm(s):
    s = (s or "").lower()
    s = s.replace("\u2014", " ").replace("\u2013", " ").replace("&", " and ")
    s = re.sub(r"pok[e\u00e9]mon", "pokemon", s)
    s = re.sub(r"[^a-z0-9 ]+", " ", s)
    return re.sub(r"\s+", " ", s).strip()


# A case/display/carton must never match a single unit, whatever its base type.
CASEISH = re.compile(r"\bcase\b|\bcarton\b|\bdisplay\b")


def canon_type(name):
    n = norm(name)
    for canonical, pats in TYPE_RULES:
        for p in pats:
            if re.search(p.replace("&", "and"), n):
                if (CASEISH.search(n) and not canonical.endswith("_CASE")
                        and canonical != "MINI_TIN_DISP"):
                    return canonical + "_CASE"
                return canonical
    return None


def detect_set(name):
    """Return the set this product belongs to, or None.

    Specific sets always win over era names; among equals, the longest alias
    wins. Era names are used only as a fallback (a true base-set product).
    """
    n = norm(name)
    specific, specific_len = None, 0
    era, era_len = None, 0
    for set_name, aliases in SET_ALIASES.items():
        for a in aliases:
            an = norm(a)
            if not an or an not in n:
                continue
            if set_name in ERA_SETS:
                if len(an) > era_len:
                    era, era_len = set_name, len(an)
            elif len(an) > specific_len:
                specific, specific_len = set_name, len(an)
    return specific or era


NOISE = {"pokemon", "tcg", "the", "and", "scarlet", "violet", "mega", "evolution",
         "packs", "pack", "s"}


def coverage(site_title, market_name):
    """Share of the market name's meaningful words present in our title.

    Our storefront titles are verbose ("Pokemon TCG: Scarlet & Violet-Destined
    Rivals Booster Pack") while Pokedata's are terse ("Destined Rivals Booster
    Pack"), so symmetric measures like Jaccard unfairly punish a correct match.
    What matters is whether the market product's words all appear in ours.
    """
    ta = set(norm(site_title).split())
    tb = set(norm(market_name).split())
    core = tb - NOISE or tb
    if not core:
        return 0.0
    return len(ta & core) / len(core)


def fetch_site_products():
    """All storefront products with their price and stock state."""
    out, page = [], 1
    while True:
        url = f"{STORE}/products.json?limit=250&page={page}"
        with urllib.request.urlopen(url, timeout=45) as r:
            batch = json.load(r)["products"]
        for p in batch:
            for v in p["variants"]:
                try:
                    price = float(v["price"])
                except (TypeError, ValueError):
                    continue
                out.append({
                    "handle": p["handle"],
                    "title": p["title"],
                    "variant_title": v.get("title") or "",
                    "price": price,
                    "available": bool(v.get("available")),
                    "image": (p["images"][0]["src"] if p.get("images") else ""),
                    "url": f"{STORE}/products/{p['handle']}",
                })
        if len(batch) < 250:
            return out
        page += 1


def load_market_from_dump(path=CATALOG_DUMP):
    """Market rows from the scanner's catalog dump: set, name, market_value."""
    rows = []
    if not os.path.exists(path):
        return rows
    with open(path, newline="", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            try:
                mv = float(r["market_value"])
            except (TypeError, ValueError, KeyError):
                continue
            if mv <= 0:
                continue
            rows.append({"set_name": r["set_name"], "name": r["name"], "market": mv,
                         "product_id": r.get("product_id", "")})
    return rows


# Sets we price-check regardless of whether the scanner is eBay-scanning them.
# Pokedata lookups cost nothing against the eBay quota, so watching our own
# prices here is free even for sets we've dropped from arbitrage scanning.
# Perfect Order and Chaos Rising were dropped from PRIORITY_SETS on 2026-07-26
# but we still sell them, so their prices must still be checked.
EXTRA_SETS = {"Phantasmal Flames": 3589, "Pitch Black": 3859,
              "Perfect Order": 3665, "Chaos Rising": 3850}


def market_rows_from_scanner(get_catalog, keys, setid_map, priority_sets):
    """Build market rows from the scanner's own Pokedata catalog.

    Reuses the scanner's cached get_catalog(), so this costs no extra API calls
    and never touches the eBay quota.
    """
    rows = []
    wanted = {sn: setid_map.get(norm(sn)) for sn in priority_sets}
    for sn, sid in EXTRA_SETS.items():
        wanted.setdefault(sn, sid)
        if wanted.get(sn) is None:
            wanted[sn] = sid
    for sn, sid in wanted.items():
        if sid is None:
            continue
        for p in get_catalog(keys, sid):
            try:
                mv = float(p.get("market_value") or 0)
            except (TypeError, ValueError):
                continue
            if mv > 0:
                rows.append({"set_name": sn, "name": p.get("name") or "",
                             "market": mv, "product_id": str(p.get("id", ""))})
    return rows


def market_from_catalog(catalog_rows):
    """Index market rows by (set, canonical type) -> list of candidates."""
    idx = {}
    for r in catalog_rows:
        ct = canon_type(r["name"])
        if not ct:
            continue
        # Pokedata rows carry their set in a column; trust it, fall back to name.
        sn = r.get("set_name") or detect_set(r["name"])
        if not sn:
            continue
        idx.setdefault((norm(sn), ct), []).append(r)
    return idx


def match_product(sp, idx):
    """Find the market row for one site product. Conservative: set+type must agree."""
    sn = detect_set(sp["title"])
    ct = canon_type(sp["title"])
    if not sn or not ct:
        return None, ("no set" if not sn else "no type")
    cands = idx.get((norm(sn), ct))
    if not cands:
        return None, f"no market row for {sn} / {ct}"
    # Best = most of the market name covered; ties go to the more specific name.
    scored = sorted(
        cands,
        key=lambda c: (coverage(sp["title"], c["name"]), len(norm(c["name"]).split())),
        reverse=True,
    )
    best = scored[0]
    best_score = coverage(sp["title"], best["name"])
    if best_score < NAME_SIM_MIN:
        return None, "ambiguous name"
    # A genuine tie between differently-priced products is not safe to guess at.
    if len(scored) > 1:
        second = scored[1]
        if (abs(coverage(sp["title"], second["name"]) - best_score) < 1e-9
                and abs(second["market"] - best["market"]) > 0.01):
            return None, "ambiguous (tied candidates)"
    return best, None


def build_alerts(catalog_rows, under_ratio=UNDER_RATIO):
    """Return (alerts, stats). Alerts = our price below `under_ratio` of market."""
    idx = market_from_catalog(catalog_rows)
    site = fetch_site_products()
    alerts, matched, unmatched = [], [], []
    for sp in site:
        if sp["price"] <= 0:
            continue
        m, why = match_product(sp, idx)
        if not m:
            unmatched.append({**sp, "reason": why})
            continue
        if m["market"] < MIN_MARKET:
            continue
        ratio = sp["price"] / m["market"]
        rec = {**sp, "market": round(m["market"], 2), "market_name": m["name"],
               "set_name": m["set_name"], "ratio": round(ratio, 4),
               "under_pct": round((1 - ratio) * 100, 1),
               "gap": round(m["market"] - sp["price"], 2)}
        matched.append(rec)
        if ratio < under_ratio:
            alerts.append(rec)
    # In-stock first (those are losing margin right now), then worst ratio.
    alerts.sort(key=lambda a: (not a["available"], a["ratio"]))
    stats = {"site_variants": len(site), "matched": len(matched),
             "unmatched": len(unmatched), "alerts": len(alerts),
             "checked_at": datetime.now(timezone.utc).isoformat()}
    return alerts, stats, matched, unmatched


def main():
    catalog = load_market_from_dump()
    if not catalog:
        print(f"No market data at {CATALOG_DUMP}. Run the arb scanner once first.")
        return
    alerts, stats, matched, unmatched = build_alerts(catalog)
    if "--json" in sys.argv:
        print(json.dumps({"stats": stats, "alerts": alerts}, indent=1))
        return
    print(f"site variants: {stats['site_variants']} | matched: {stats['matched']} "
          f"| unmatched: {stats['unmatched']} | ALERTS: {stats['alerts']}\n")
    print(f"{'ratio':>6} {'ours':>9} {'market':>9}  {'stock':<9} title")
    print("-" * 110)
    for a in matched[:200]:
        flag = "!!" if a["ratio"] < UNDER_RATIO else "  "
        print(f"{flag}{a['ratio']*100:5.0f}% {a['price']:9.2f} {a['market']:9.2f}  "
              f"{'in stock' if a['available'] else 'sold out':<9} {a['title'][:60]}")
        print(f"{'':>7}{'':>9} {'':>9}  {'':<9} vs {a['market_name'][:60]}")
    print(f"\n--- unmatched ({len(unmatched)}) ---")
    for u in unmatched[:40]:
        print(f"  {u['reason']:<34} {u['title'][:64]}")


if __name__ == "__main__":
    main()
