"""
wc_logic.py — data + logic layer for the WC2026 dynasty-pool Streamlit app.

No streamlit imports here: everything in this module is pure and unit-testable
offline. app.py owns caching, layout, and HTML.

Key ideas
- Round classification is done by *date* (converted to US-Eastern so late west
  coast kickoffs stay on their local calendar day), with keyword override. This
  avoids depending on ESPN's round labels.
- Group games are also verified structurally (both teams in the same group).
- Scoring is split into `banked` (completed results / finalized groups) and
  `live` (provisional: in-progress scores + if-the-table-ended-today bonuses).
- The knockout bracket resolves from finalized group tables, then prefers
  ESPN's actual fixtures once they exist (which makes FIFA's official
  third-place allocation authoritative rather than our projection).
"""
from __future__ import annotations
import json
import re
import datetime as dt
import unicodedata
import urllib.request
from zoneinfo import ZoneInfo

# ---------------------------------------------------------------- constants
ET = ZoneInfo("America/New_York")
START = dt.date(2026, 6, 11)
END = dt.date(2026, 7, 19)
ESPN = "https://site.api.espn.com/apis/site/v2/sports/soccer/fifa.world/scoreboard"

GROUPS = {
    "A": ["Mexico", "South Africa", "South Korea", "Czechia"],
    "B": ["Canada", "Bosnia", "Qatar", "Switzerland"],
    "C": ["Brazil", "Morocco", "Haiti", "Scotland"],
    "D": ["USA", "Paraguay", "Australia", "Turkiye"],
    "E": ["Germany", "Curacao", "Cote d'Ivoire", "Ecuador"],
    "F": ["Netherlands", "Japan", "Sweden", "Tunisia"],
    "G": ["Belgium", "Egypt", "Iran", "New Zealand"],
    "H": ["Spain", "Cape Verde", "Saudi Arabia", "Uruguay"],
    "I": ["France", "Senegal", "Iraq", "Norway"],
    "J": ["Argentina", "Algeria", "Austria", "Jordan"],
    "K": ["Portugal", "DR Congo", "Uzbekistan", "Colombia"],
    "L": ["England", "Croatia", "Ghana", "Panama"],
}
team_group = {t: g for g, ts in GROUPS.items() for t in ts}
ALL_TEAMS = list(team_group)

DRAFT = {
    "Alex D": ["France", "USA", "Colombia", "South Korea", "Egypt", "New Zealand"],
    "Nathan": ["Spain", "Switzerland", "Croatia", "Cote d'Ivoire", "Algeria", "Uzbekistan"],
    "Zack": ["England", "Morocco", "Mexico", "Czechia", "Paraguay", "Cape Verde"],
    "Kyle": ["Argentina", "Norway", "Japan", "Canada", "Ghana", "South Africa"],
    "Nathaniel": ["Portugal", "Belgium", "Turkiye", "Scotland", "Australia", "Tunisia"],
    "Jack": ["Brazil", "Uruguay", "Austria", "Sweden", "DR Congo", "Curacao"],
    "Alex B": ["Germany", "Netherlands", "Ecuador", "Senegal", "Iran", "Bosnia"],
}
team_owner = {t: o for o, ts in DRAFT.items() for t in ts}

SCORE = {"GW": 2, "GD": 1, "ADV": 5, "WGRP": 3,
         "R32": 6, "R16": 8, "QF": 10, "SF": 12, "F": 25, "3P": 0}
ROUND_NAMES = {"GROUP": "Group Stage", "R32": "Round of 32", "R16": "Round of 16",
               "QF": "Quarterfinal", "SF": "Semifinal", "3P": "Third Place", "F": "Final"}

DISPLAY = {"Cote d'Ivoire": "Côte d'Ivoire", "Turkiye": "Türkiye", "Curacao": "Curaçao"}
def disp(t): return DISPLAY.get(t, t)

# official 2026 R32 slot map (matches 73-88); ("W",g)/("RU",g)/("T",slot)
SLOT_ALLOWED = {74: set("ABCDF"), 77: set("CDFGH"), 79: set("CEFHI"), 80: set("EHIJK"),
                81: set("BEFIJ"), 82: set("AEHIJ"), 85: set("EFGIJ"), 87: set("DEIJL")}
R32_DEF = [
    (73, ("RU", "A"), ("RU", "B")), (74, ("W", "E"), ("T", 74)),
    (75, ("W", "F"), ("RU", "C")), (76, ("W", "C"), ("RU", "F")),
    (77, ("W", "I"), ("T", 77)), (78, ("RU", "E"), ("RU", "I")),
    (79, ("W", "A"), ("T", 79)), (80, ("W", "L"), ("T", 80)),
    (81, ("W", "D"), ("T", 81)), (82, ("W", "G"), ("T", 82)),
    (83, ("RU", "K"), ("RU", "L")), (84, ("W", "H"), ("RU", "J")),
    (85, ("W", "B"), ("T", 85)), (86, ("W", "J"), ("RU", "H")),
    (87, ("W", "K"), ("T", 87)), (88, ("RU", "D"), ("RU", "G")),
]
R16_DEF = [(89, 74, 77), (90, 73, 75), (91, 76, 78), (92, 79, 80),
           (93, 83, 84), (94, 81, 82), (95, 86, 88), (96, 85, 87)]
QF_DEF = [(97, 89, 90), (98, 93, 94), (99, 91, 92), (100, 95, 96)]
SF_DEF = [(101, 97, 98), (102, 99, 100)]

# round date windows (US-Eastern calendar dates)
ROUND_WINDOWS = [
    ("GROUP", dt.date(2026, 6, 11), dt.date(2026, 6, 27)),
    ("R32", dt.date(2026, 6, 28), dt.date(2026, 7, 3)),
    ("R16", dt.date(2026, 7, 4), dt.date(2026, 7, 8)),
    ("QF", dt.date(2026, 7, 9), dt.date(2026, 7, 13)),
    ("SF", dt.date(2026, 7, 14), dt.date(2026, 7, 17)),
    ("3P", dt.date(2026, 7, 18), dt.date(2026, 7, 18)),
    ("F", dt.date(2026, 7, 19), dt.date(2026, 7, 19)),
]

# ---------------------------------------------------------------- name canon
ALIAS = {
    "united states": "USA", "usa": "USA", "ivory coast": "Cote d'Ivoire",
    "cote divoire": "Cote d'Ivoire", "turkey": "Turkiye", "turkiye": "Turkiye",
    "czech republic": "Czechia", "czechia": "Czechia", "congo dr": "DR Congo",
    "dr congo": "DR Congo", "democratic republic of the congo": "DR Congo",
    "curacao": "Curacao", "cabo verde": "Cape Verde", "cape verde": "Cape Verde",
    "bosnia and herzegovina": "Bosnia", "bosnia": "Bosnia",
    "bosnia herzegovina": "Bosnia",
    "korea republic": "South Korea", "south korea": "South Korea",
    "ir iran": "Iran", "iran": "Iran", "new zealand": "New Zealand",
}
def _strip(s):
    return "".join(c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c))

def _norm(s):
    k = _strip(s).lower().replace("'", "").replace("-", " ")
    return " ".join(k.split())

_CANON = {_norm(t): t for t in ALL_TEAMS}

def canon(name):
    if not name:
        return None
    k = _norm(name)
    if k in ALIAS:
        return ALIAS[k]
    return _CANON.get(k)

# ---------------------------------------------------------------- fetch/parse
def http_get_scoreboard(dates_str, limit=400):
    """dates_str: 'YYYYMMDD' or 'YYYYMMDD-YYYYMMDD'. Raises on failure."""
    url = f"{ESPN}?dates={dates_str}&limit={limit}"
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (wc-pool-tracker)"})
    with urllib.request.urlopen(req, timeout=20) as r:
        return json.loads(r.read().decode())

def classify_round(local_date, text=""):
    s = (text or "").lower()
    if "third place" in s or "3rd place" in s:
        return "3P"
    if "round of 32" in s:
        return "R32"
    if "round of 16" in s:
        return "R16"
    if "quarter" in s:
        return "QF"
    if "semi" in s:
        return "SF"
    for r, a, b in ROUND_WINDOWS:
        if a <= local_date <= b:
            return r
    return "GROUP" if local_date < dt.date(2026, 6, 28) else "F"

def parse_event(ev):
    """ESPN event -> normalized match dict (or None if unparseable)."""
    try:
        comp = ev["competitions"][0]
        status = comp.get("status") or ev.get("status") or {}
        stype = status.get("type", {}) or {}
        state = stype.get("state", "pre")            # pre | in | post
        completed = bool(stype.get("completed"))
        iso = (ev.get("date") or comp.get("date") or "").replace("Z", "+00:00")
        utc = dt.datetime.fromisoformat(iso)
        local_date = utc.astimezone(ET).date()
        cs = comp["competitors"]
        home = next((c for c in cs if c.get("homeAway") == "home"), cs[0])
        away = next((c for c in cs if c.get("homeAway") == "away"), cs[-1])
        raw_a = home.get("team", {}).get("displayName", "?")
        raw_b = away.get("team", {}).get("displayName", "?")
        a, b = canon(raw_a), canon(raw_b)
        known = bool(a and b)
        sa = int(home.get("score") or 0)
        sb = int(away.get("score") or 0)
        notes = ""
        try:
            notes = (comp.get("notes") or [{}])[0].get("headline", "") or ""
        except Exception:
            pass
        rnd = classify_round(local_date, f"{notes} {ev.get('name','')}")
        winner = None
        if completed and known:
            if home.get("winner") is True:
                winner = a
            elif away.get("winner") is True:
                winner = b
            elif sa > sb:
                winner = a
            elif sb > sa:
                winner = b
        group = None
        if known and rnd == "GROUP" and team_group.get(a) == team_group.get(b):
            group = team_group[a]
        return {
            "id": str(ev.get("id") or f"{raw_a}|{raw_b}|{iso}"),
            "utc": utc, "local_date": local_date,
            "a": a, "b": b, "raw_a": raw_a, "raw_b": raw_b, "known": known,
            "sa": sa, "sb": sb, "state": state, "completed": completed,
            "clock": stype.get("shortDetail") or stype.get("detail") or "",
            "round": rnd, "group": group, "winner": winner,
            "venue": (comp.get("venue") or {}).get("fullName", ""),
        }
    except Exception:
        return None

_PLACEHOLDER = re.compile(r"winner|loser|2nd place|third place|tbd|play.?off", re.I)

def collect(raw_payloads):
    """List of ESPN scoreboard payloads -> (sorted matches, unknown team names)."""
    seen, unknown = {}, set()
    for data in raw_payloads:
        for ev in (data or {}).get("events", []):
            m = parse_event(ev)
            if not m:
                continue
            if not m["known"]:
                for nm, c in ((m["raw_a"], m["a"]), (m["raw_b"], m["b"])):
                    if c is None and not _PLACEHOLDER.search(nm):
                        unknown.add(nm)
            seen[m["id"]] = m
    return sorted(seen.values(), key=lambda m: m["utc"]), sorted(unknown)

# ---------------------------------------------------------------- scoring
def _new_row():
    return {"P": 0, "W": 0, "D": 0, "L": 0, "GF": 0, "GA": 0, "Pts": 0, "live": False}

def build_state(matches):
    banked = {t: 0.0 for t in ALL_TEAMS}
    live = {t: 0.0 for t in ALL_TEAMS}
    status = {t: "alive" for t in ALL_TEAMS}
    tbl = {g: {t: _new_row() for t in GROUPS[g]} for g in GROUPS}
    done = {g: 0 for g in GROUPS}

    def feed(g, t, gf, ga, is_live):
        row = tbl[g][t]
        row["P"] += 1
        row["GF"] += gf
        row["GA"] += ga
        if is_live:
            row["live"] = True
        if gf > ga:
            row["W"] += 1
            row["Pts"] += 3
        elif gf == ga:
            row["D"] += 1
            row["Pts"] += 1
        else:
            row["L"] += 1

    for m in matches:
        if m["round"] != "GROUP" or not m.get("group"):
            continue
        g, a, b, sa, sb = m["group"], m["a"], m["b"], m["sa"], m["sb"]
        if m["completed"]:
            done[g] += 1
            feed(g, a, sa, sb, False)
            feed(g, b, sb, sa, False)
            if sa > sb:
                banked[a] += SCORE["GW"]
            elif sb > sa:
                banked[b] += SCORE["GW"]
            else:
                banked[a] += SCORE["GD"]
                banked[b] += SCORE["GD"]
        elif m["state"] == "in":
            feed(g, a, sa, sb, True)
            feed(g, b, sb, sa, True)
            if sa > sb:
                live[a] += SCORE["GW"]
            elif sb > sa:
                live[b] += SCORE["GW"]
            else:
                live[a] += SCORE["GD"]
                live[b] += SCORE["GD"]

    # rank groups: real Pts, GD, GF, name (FIFA tiebreakers approximated)
    group_rank, group_final = {}, {}
    for g in GROUPS:
        order = sorted(GROUPS[g],
                       key=lambda t: (-tbl[g][t]["Pts"],
                                      -(tbl[g][t]["GF"] - tbl[g][t]["GA"]),
                                      -tbl[g][t]["GF"], t))
        group_rank[g] = order
        final = done[g] == 6
        group_final[g] = final
        tgt = banked if final else live
        tgt[order[0]] += SCORE["WGRP"]
        tgt[order[0]] += SCORE["ADV"]
        tgt[order[1]] += SCORE["ADV"]
        if final:
            status[order[3]] = "eliminated"

    all_final = all(group_final.values())
    thirds = []
    for g in GROUPS:
        t = group_rank[g][2]
        r = tbl[g][t]
        thirds.append({"g": g, "t": t, "Pts": r["Pts"], "GD": r["GF"] - r["GA"],
                       "GF": r["GF"], "live": r["live"], "final": group_final[g]})
    thirds.sort(key=lambda x: (-x["Pts"], -x["GD"], -x["GF"], x["t"]))
    top8 = {x["t"] for x in thirds[:8]}
    top8_groups = [x["g"] for x in thirds[:8]]
    for i, x in enumerate(thirds):
        if i < 8:
            (banked if all_final else live)[x["t"]] += SCORE["ADV"]
        elif all_final:
            status[x["t"]] = "eliminated"

    champion = None
    for m in matches:
        rnd = m["round"]
        if rnd not in ("R32", "R16", "QF", "SF", "3P", "F") or not m["known"]:
            continue
        pts = SCORE[rnd]
        if m["completed"] and m["winner"]:
            banked[m["winner"]] += pts
            loser = m["b"] if m["winner"] == m["a"] else m["a"]
            if rnd != "3P":
                status[loser] = "eliminated"
            if rnd == "F":
                champion = m["winner"]
        elif m["state"] == "in":
            if m["sa"] > m["sb"]:
                live[m["a"]] += pts
            elif m["sb"] > m["sa"]:
                live[m["b"]] += pts
    if champion:
        status[champion] = "champion"

    owner_banked = {o: sum(banked[t] for t in ts) for o, ts in DRAFT.items()}
    owner_live = {o: sum(live[t] for t in ts) for o, ts in DRAFT.items()}
    owner_total = {o: owner_banked[o] + owner_live[o] for o in DRAFT}
    return {
        "banked": banked, "live": live,
        "total": {t: banked[t] + live[t] for t in ALL_TEAMS},
        "status": status, "tbl": tbl, "done": done,
        "group_rank": group_rank, "group_final": group_final, "all_final": all_final,
        "thirds": thirds, "third_top8": top8, "top8_groups": top8_groups,
        "owner_banked": owner_banked, "owner_live": owner_live, "owner_total": owner_total,
        "champion": champion,
    }

# ---------------------------------------------------------------- bracket
def assign_thirds(qual_groups):
    """Valid slot->group assignment under FIFA group-eligibility constraints."""
    qs = set(qual_groups)
    slots = sorted(SLOT_ALLOWED, key=lambda s: len(SLOT_ALLOWED[s] & qs))
    res = {}

    def bt(i, used):
        if i == len(slots):
            return True
        s = slots[i]
        for g in sorted(SLOT_ALLOWED[s] & qs):
            if g not in used:
                res[s] = g
                used.add(g)
                if bt(i + 1, used):
                    return True
                used.discard(g)
                del res[s]
        return False

    bt(0, set())
    return res

def _mk_card(slot):
    return {"slot": slot, "a": None, "b": None, "albl": "", "blbl": "",
            "sa": None, "sb": None, "state": "pre", "clock": "", "winner": None}

def _attach(card, pool):
    """Bind an actual ESPN match to a card when a known side appears in it."""
    for i, m in enumerate(pool):
        names = {m["a"], m["b"]}
        if (card["a"] in names) or (card["b"] in names):
            if card["a"] in names and not card["b"]:
                card["b"] = m["b"] if m["a"] == card["a"] else m["a"]
            if card["b"] in names and not card["a"]:
                card["a"] = m["b"] if m["a"] == card["b"] else m["a"]
            flip = (m["a"] == card["b"]) or (m["b"] == card["a"])
            card["sa"], card["sb"] = (m["sb"], m["sa"]) if flip else (m["sa"], m["sb"])
            card["state"] = "post" if m["completed"] else m["state"]
            card["clock"] = m["clock"]
            card["winner"] = m["winner"]
            pool.pop(i)
            return
    # no actual fixture yet

def resolve_bracket(matches, state):
    gr, gf = state["group_rank"], state["group_final"]
    third_assign = assign_thirds(state["top8_groups"]) if state["all_final"] else {}
    pools = {r: [m for m in matches if m["round"] == r and m["known"]]
             for r in ("R32", "R16", "QF", "SF", "3P", "F")}

    def side(spec):
        kind = spec[0]
        if kind == "W":
            g = spec[1]
            return (gr[g][0], "") if gf[g] else (None, f"Winner {g}")
        if kind == "RU":
            g = spec[1]
            return (gr[g][1], "") if gf[g] else (None, f"2nd {g}")
        slot = spec[1]
        g = third_assign.get(slot)
        if g:
            return (gr[g][2], "")
        return (None, "3rd " + "/".join(sorted(SLOT_ALLOWED[slot])))

    cards = {}
    for slot, sa_, sb_ in R32_DEF:
        c = _mk_card(slot)
        c["a"], c["albl"] = side(sa_)
        c["b"], c["blbl"] = side(sb_)
        _attach(c, pools["R32"])
        cards[slot] = c

    def feed_round(defs, rnd):
        for entry in defs:
            slot, fa, fb = entry
            c = _mk_card(slot)
            for key, f in (("a", fa), ("b", fb)):
                w = cards[f]["winner"]
                if w:
                    c[key] = w
                else:
                    c[key + "lbl"] = f"Winner M{f}"
            _attach(c, pools[rnd])
            cards[slot] = c

    feed_round(R16_DEF, "R16")
    feed_round(QF_DEF, "QF")
    feed_round(SF_DEF, "SF")
    feed_round([(104, 101, 102)], "F")
    # third place: SF losers
    c3 = _mk_card(103)
    for key, f in (("a", 101), ("b", 102)):
        cd = cards[f]
        if cd["winner"] and cd["a"] and cd["b"]:
            c3[key] = cd["b"] if cd["winner"] == cd["a"] else cd["a"]
        else:
            c3[key + "lbl"] = f"Loser M{f}"
    _attach(c3, pools["3P"])
    cards[103] = c3

    # display in tree order so each round's adjacent winners feed the same
    # next-round card (fixes the "winners side-by-side but play different
    # teams" look). Walk the feeder graph from the final downward.
    r16_feed = {s: (a, b) for s, a, b in R16_DEF}
    qf_feed = {s: (a, b) for s, a, b in QF_DEF}
    sf_feed = {s: (a, b) for s, a, b in SF_DEF}
    sf_disp = [101, 102]
    qf_disp = [m for s in sf_disp for m in sf_feed[s]]
    r16_disp = [m for s in qf_disp for m in qf_feed[s]]
    r32_disp = [m for s in r16_disp for m in r16_feed[s]]
    return {
        "R32": [cards[s] for s in r32_disp],
        "R16": [cards[s] for s in r16_disp],
        "QF": [cards[s] for s in qf_disp],
        "SF": [cards[s] for s in sf_disp],
        "F": [cards[104], cards[103]],
    }

# ---------------------------------------------------------------- demo data
ELO = {
    "Mexico": 1880, "South Africa": 1710, "South Korea": 1815, "Czechia": 1800,
    "Canada": 1850, "Bosnia": 1815, "Qatar": 1700, "Switzerland": 1880,
    "Brazil": 2060, "Morocco": 1925, "Haiti": 1580, "Scotland": 1775,
    "USA": 1905, "Paraguay": 1775, "Australia": 1760, "Turkiye": 1835,
    "Germany": 2010, "Curacao": 1600, "Cote d'Ivoire": 1805, "Ecuador": 1835,
    "Netherlands": 2000, "Japan": 1865, "Sweden": 1820, "Tunisia": 1750,
    "Belgium": 1955, "Egypt": 1785, "Iran": 1795, "New Zealand": 1605,
    "Spain": 2110, "Cape Verde": 1640, "Saudi Arabia": 1695, "Uruguay": 1945,
    "France": 2085, "Senegal": 1885, "Iraq": 1655, "Norway": 1865,
    "Argentina": 2080, "Algeria": 1795, "Austria": 1850, "Jordan": 1685,
    "Portugal": 2030, "DR Congo": 1735, "Uzbekistan": 1690, "Colombia": 1930,
    "England": 2055, "Croatia": 1925, "Ghana": 1760, "Panama": 1690,
}

def demo_matches(seed=26):
    """Demo mode: one full Elo-driven simulation of all 104 matches, so every
    tab renders a completed tournament (groups, bracket, champion, standings).
    Deterministic for a given seed."""
    import random as _r
    rng = _r.Random(seed)
    out = []

    def _exp(a, b):
        return 1 / (1 + 10 ** ((ELO[b] - ELO[a]) / 400))

    def mk(a, b, sa, sb, day, hour, rnd, group=None):
        utc = dt.datetime(day.year, day.month, day.day, hour, 0, tzinfo=dt.timezone.utc)
        return {"id": f"demo-{rnd}-{a}-{b}", "utc": utc,
                "local_date": utc.astimezone(ET).date(),
                "a": a, "b": b, "raw_a": a, "raw_b": b, "known": True,
                "sa": sa, "sb": sb, "state": "post", "completed": True,
                "clock": "FT", "round": rnd, "group": group,
                "winner": a if sa > sb else (b if sb > sa else None),
                "venue": "Demo Stadium"}

    def group_score(a, b):
        ea = _exp(a, b)
        d = abs(ELO[a] - ELO[b])
        pdraw = 0.27 * (2.718281828 ** (-(d / 220) ** 2))
        if rng.random() < pdraw:
            g = rng.choice([0, 1, 1, 2])
            return g, g
        win_a = rng.random() < ea
        wg = rng.choice([1, 1, 2, 2, 2, 3, 3, 4])
        lg = rng.randint(0, min(wg - 1, 2))
        return (wg, lg) if win_a else (lg, wg)

    # group stage: 72 games across June 11-27
    for gi, (g, tm) in enumerate(GROUPS.items()):
        t1, t2, t3, t4 = tm
        mds = [[(t1, t2), (t3, t4)], [(t1, t3), (t2, t4)], [(t1, t4), (t2, t3)]]
        days = [gi % 6, 6 + gi % 6, 12 + gi % 5]
        for pairs, dy in zip(mds, days):
            for k, (a, b) in enumerate(pairs):
                sa, sb = group_score(a, b)
                out.append(mk(a, b, sa, sb, START + dt.timedelta(days=dy),
                              16 + 3 * k, "GROUP", g))

    # finalize groups exactly the way the live app would, then play the bracket
    st = build_state(out)
    gr = st["group_rank"]
    amap = assign_thirds(st["top8_groups"])

    def resolve(spec):
        if spec[0] == "W":
            return gr[spec[1]][0]
        if spec[0] == "RU":
            return gr[spec[1]][1]
        return gr[amap[spec[1]]][2]

    def ko(a, b, rnd, day, hour):
        win = a if rng.random() < _exp(a, b) else b
        wg = rng.choice([1, 2, 2, 3])
        lg = rng.randint(0, wg - 1)
        sa, sb = (wg, lg) if win == a else (lg, wg)
        out.append(mk(a, b, sa, sb, day, hour, rnd))
        return win

    w = {}
    for i, (slot, A, B) in enumerate(R32_DEF):
        day = dt.date(2026, 6, 28) + dt.timedelta(days=(i * 6) // 16)
        w[slot] = ko(resolve(A), resolve(B), "R32", day, 16 + 3 * (i % 3))
    for i, (slot, fa, fb) in enumerate(R16_DEF):
        w[slot] = ko(w[fa], w[fb], "R16",
                     dt.date(2026, 7, 4) + dt.timedelta(days=i // 2), 17 + 3 * (i % 2))
    for i, (slot, fa, fb) in enumerate(QF_DEF):
        w[slot] = ko(w[fa], w[fb], "QF",
                     dt.date(2026, 7, 9) + dt.timedelta(days=(i * 3) // 4), 18 + 2 * (i % 2))
    losers = {}
    for i, (slot, fa, fb) in enumerate(SF_DEF):
        a, b = w[fa], w[fb]
        w[slot] = ko(a, b, "SF", dt.date(2026, 7, 14) + dt.timedelta(days=i), 19)
        losers[slot] = b if w[slot] == a else a
    ko(losers[101], losers[102], "3P", dt.date(2026, 7, 18), 19)
    ko(w[101], w[102], "F", dt.date(2026, 7, 19), 19)
    return sorted(out, key=lambda m: m["utc"])


# ---- single-file bridge: the app section below refers to this module as `wc`
import sys as _sys
wc = _sys.modules[__name__]

import datetime as dt
from zoneinfo import ZoneInfo

import streamlit as st

try:
    from streamlit_autorefresh import st_autorefresh
    HAS_AR = True
except Exception:
    HAS_AR = False

st.set_page_config(page_title="WC26 Pool", page_icon="⚽", layout="wide")

COLORS = {"Nathan": "#ffc83d", "Alex B": "#38bdf8", "Alex D": "#fb7185",
          "Zack": "#c084fc", "Kyle": "#34d399", "Nathaniel": "#fb923c", "Jack": "#60a5fa"}
ME = "Nathan"
TZ = ZoneInfo("America/Los_Angeles")  # all times shown in Pacific

CSS = """
<style>
.stApp{background:#070b09}
header[data-testid="stHeader"]{background:rgba(0,0,0,0)}
.stApp, .stMarkdown, .stCaption, p, li, td, th{color:#eef3f0}

:root{--panel:#0e1512;--panel2:#121d18;--line:#22332b;--ink:#eef3f0;--mut:#7d9388;
--pitch:#16d97e;--gold:#ffc83d;--rose:#fb7185;--liveC:#ff5d5d}
.block-container{padding-top:2.4rem;max-width:1150px}
h1,h2,h3{letter-spacing:-.01em}
.hdr{font-family:Impact,'Arial Narrow Bold','Arial Narrow',sans-serif;text-transform:uppercase;
font-size:clamp(34px,6vw,54px);line-height:.95;margin:0 0 2px}
.hdr span{color:var(--gold)}
.eyebrow{text-transform:uppercase;letter-spacing:.28em;font-size:11px;color:var(--pitch);font-weight:700}
.upd{color:var(--mut);font-size:12px;margin-bottom:4px}
.chip{font-size:10px;font-weight:700;border:1px solid;border-radius:5px;padding:1px 6px;
margin-left:7px;letter-spacing:.04em;white-space:nowrap;vertical-align:1px}
.lvp{color:var(--liveC);font-weight:700}
.lv{display:inline-block;width:7px;height:7px;border-radius:50%;background:var(--liveC);
margin-left:6px;animation:pulse 1.4s infinite;vertical-align:1px}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.35}}
/* schedule */
.mcard{display:grid;grid-template-columns:120px 1fr 86px;gap:14px;align-items:center;
background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:12px 16px;margin-bottom:10px}
.mwhen{font-size:13px;color:var(--ink);font-weight:700}
.mwhen small{display:block;color:var(--mut);font-weight:600;font-size:10.5px;
text-transform:uppercase;letter-spacing:.06em;margin-top:2px}
.trow{display:flex;align-items:center;gap:8px;padding:3px 0;font-size:15px}
.tname{font-weight:700}
.tsc{margin-left:auto;font-family:Impact,'Arial Narrow',sans-serif;font-size:19px;min-width:20px;text-align:right}
.trow.w .tname,.trow.w .tsc{color:var(--pitch)}
.mstat{text-align:center;font-weight:800;font-size:12px;border-radius:8px;padding:7px 4px}
.mstat.in{background:rgba(255,93,93,.14);color:var(--liveC)}
.mstat.post{background:var(--panel2);color:var(--mut)}
.mstat.pre{background:rgba(22,217,126,.1);color:var(--pitch)}
/* group tables */
.gt{width:100%;border-collapse:collapse;background:var(--panel);border:1px solid var(--line);
border-radius:12px;overflow:hidden;margin-bottom:14px}
.gt th{background:var(--panel2);color:var(--mut);font-size:10px;text-transform:uppercase;
letter-spacing:.08em;padding:8px 8px;text-align:left}
.gt td{padding:8px 8px;border-top:1px solid rgba(34,51,43,.55);font-size:13px}
.gt .num{text-align:right}
.gt tr.q1 td:first-child{box-shadow:inset 3px 0 0 var(--pitch)}
.gt tr.q3 td:first-child{box-shadow:inset 3px 0 0 var(--gold)}
.gt .fp{font-weight:800;text-align:right}
.gname{font-weight:800;font-size:15px;margin:2px 0 6px}
.gname .fin{color:var(--pitch);font-size:10px;letter-spacing:.1em;margin-left:8px}
.gname .liv{color:var(--liveC);font-size:10px;letter-spacing:.1em;margin-left:8px}
/* bracket */
.bwrap{overflow-x:auto;padding-bottom:10px}
.bcols{display:flex;gap:18px;min-width:1180px}
.bcol{flex:1;display:flex;flex-direction:column;justify-content:space-around;min-width:212px}
.bhead{color:var(--mut);font-size:11px;text-transform:uppercase;letter-spacing:.16em;
font-weight:700;text-align:center;margin-bottom:8px}
.bk{background:var(--panel);border:1px solid var(--line);border-radius:10px;
padding:7px 10px;margin:5px 0}
.bks{display:flex;align-items:center;gap:6px;padding:3px 0;font-size:13px}
.bknm{font-weight:700}
.bksc{margin-left:auto;font-family:Impact,'Arial Narrow',sans-serif;font-size:15px}
.bks.win .bknm,.bks.win .bksc{color:var(--pitch)}
.ph{color:var(--mut);font-weight:600;font-style:italic;font-size:12px}
.bclock{font-size:10px;color:var(--liveC);font-weight:800;text-align:right}
/* owners */
.orow{display:grid;grid-template-columns:38px 1fr 90px 70px 96px;gap:12px;align-items:center;
background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:13px 16px;margin-bottom:9px}
.orow.me{border-color:var(--gold)}
.ork{font-family:Impact,'Arial Narrow',sans-serif;font-size:26px;color:var(--mut);text-align:center}
.orow:first-child .ork{color:var(--gold)}
.oname{font-weight:800;font-size:16px}
.dot{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:8px}
.you{font-size:8px;letter-spacing:.1em;background:var(--gold);color:#1a1403;
padding:2px 5px;border-radius:4px;font-weight:800;margin-left:7px;vertical-align:2px}
.ostat{font-family:Impact,'Arial Narrow',sans-serif;font-size:20px;text-align:right}
.ostat small{display:block;font-family:system-ui;font-size:9px;color:var(--mut);
font-weight:700;letter-spacing:.06em;text-transform:uppercase}
.osub{display:none;font-size:11px;color:var(--mut);font-weight:600;margin-top:3px}
.obar{height:12px;background:#0a120e;border:1px solid var(--line);border-radius:6px;overflow:hidden}
.obar i{display:block;height:100%;border-radius:6px}
.badge{font-size:9px;font-weight:800;letter-spacing:.08em;padding:2px 7px;border-radius:5px}
.badge.out{background:rgba(125,147,136,.16);color:var(--mut)}
.badge.alive{background:rgba(22,217,126,.14);color:var(--pitch)}
.badge.champ{background:rgba(255,200,61,.2);color:var(--gold)}
/* native widget fixes for the dark look */
.stButton > button{background:#121d18 !important;color:#eef3f0 !important;
border:1px solid #2e4438 !important;font-weight:700 !important;border-radius:9px !important}
.stButton > button:hover{border-color:#16d97e !important;color:#16d97e !important}
.stButton > button p{color:inherit !important}
[data-testid="stExpander"] details{background:#0e1512 !important;border:1px solid #22332b !important;border-radius:10px !important}
[data-testid="stExpander"] summary,[data-testid="stExpander"] summary p,
[data-testid="stExpander"] summary span,[data-testid="stExpander"] svg{color:#eef3f0 !important;fill:#eef3f0 !important}
label, label p, [data-testid="stWidgetLabel"] p{color:#eef3f0 !important}
.gt{max-width:860px}
/* settings + debug expanders: make them obvious and tappable on mobile */
[data-testid="stExpander"] summary{font-weight:800 !important;font-size:15px !important}
[data-testid="stExpander"] summary:hover{color:#16d97e !important}
/* mobile: owners rows collapse to rank · name · total (banked/live move under name) */
@media(max-width:560px){
  .orow{grid-template-columns:30px 1fr auto !important;gap:9px !important;padding:12px 13px !important}
  .colhide{display:none !important}
  .osub{display:block !important}
  .ork{font-size:22px !important}
  .otot{font-size:21px !important}
}
</style>
"""
st.markdown(CSS, unsafe_allow_html=True)

if "demo_seed" not in st.session_state:
    st.session_state.demo_seed = 26

# ------------------------------------------------------------- data loading
@st.cache_data(ttl=6 * 3600, show_spinner=False)
def fetch_archive(ds):
    return wc.http_get_scoreboard(ds)

@st.cache_data(ttl=60, show_spinner=False)
def fetch_live(ds):
    return wc.http_get_scoreboard(ds)

@st.cache_data(ttl=3600, show_spinner=False)
def fetch_future(ds):
    return wc.http_get_scoreboard(ds)

def _rng(a, b):
    return f"{a:%Y%m%d}" if a == b else f"{a:%Y%m%d}-{b:%Y%m%d}"

def load_matches(demo):
    if demo:
        return wc.demo_matches(st.session_state.demo_seed), [], []
    payloads, errors = [], []
    today = dt.date.today()
    arch_end = min(today - dt.timedelta(days=2), wc.END)
    if arch_end >= wc.START:
        try:
            payloads.append(fetch_archive(_rng(wc.START, arch_end)))
        except Exception as e:
            errors.append(f"archive fetch: {e}")
    la, lb = max(wc.START, today - dt.timedelta(days=1)), min(wc.END, today + dt.timedelta(days=1))
    if la <= lb:
        try:
            payloads.append(fetch_live(_rng(la, lb)))
        except Exception as e:
            errors.append(f"live fetch: {e}")
    fa = max(wc.START, today + dt.timedelta(days=2))
    if fa <= wc.END:
        try:
            payloads.append(fetch_future(_rng(fa, wc.END)))
        except Exception as e:
            errors.append(f"future fetch: {e}")
    matches, unknown = wc.collect(payloads)
    return matches, unknown, errors

# ------------------------------------------------------------- sidebar
with st.expander("⚙️  Settings & controls", expanded=False):
    cset = st.columns([1.4, 1.4, 1.2])
    with cset[0]:
        demo = st.toggle("Demo mode (sample data)", value=False,
                         help="Plays one full Elo-simulated tournament (all 104 matches) so every tab is filled out end to end.")
    with cset[1]:
        if HAS_AR:
            auto = st.toggle("Auto-refresh", value=True)
            secs = st.select_slider("Refresh every", options=[30, 60, 120], value=60,
                                    format_func=lambda s: f"{s}s")
            if auto and not demo:
                st_autorefresh(interval=secs * 1000, key="ar")
        else:
            auto = False
    with cset[2]:
        btn_label = "🎲 New simulation" if demo else "↻ Refresh data now"
        st.write("")
        if st.button(btn_label, use_container_width=True):
            if demo:
                import random as _rnd
                st.session_state.demo_seed = _rnd.randrange(1, 1_000_000)
            else:
                fetch_live.clear()
                fetch_future.clear()
            st.rerun()

matches, unknown_names, fetch_errors = load_matches(demo)
state = wc.build_state(matches)
bracket = wc.resolve_bracket(matches, state)
n_live = sum(1 for m in matches if m["state"] == "in")

# ------------------------------------------------------------- header
st.markdown('<div class="eyebrow">World Cup 2026 · Dynasty Pool</div>', unsafe_allow_html=True)
st.markdown('<div class="hdr">Live <span>Tracker</span></div>', unsafe_allow_html=True)
mode = "DEMO DATA" if demo else "LIVE · ESPN"
now = dt.datetime.now(TZ).strftime("%b %d, %I:%M %p").replace(" 0", " ")
live_note = f' · <span class="lvp">{n_live} match{"es" if n_live != 1 else ""} live</span>' if n_live else ""
st.markdown(f'<div class="upd">{mode} · {len(matches)} fixtures loaded · updated {now} PT{live_note}</div>',
            unsafe_allow_html=True)

if fetch_errors and not matches:
    st.error("Couldn't reach ESPN. Hit refresh in a minute — or flip on Demo mode to preview the app.")
elif fetch_errors:
    st.warning("Some data ranges failed to load; standings may be partial. Try a manual refresh.")

# ------------------------------------------------------------- shared helpers
def chip(team):
    o = wc.team_owner.get(team)
    if not o:
        return ""
    return f'<span class="chip" style="border-color:{COLORS[o]};color:{COLORS[o]}">{o}</span>'

def fpts_html(t):
    b, l = state["banked"][t], state["live"][t]
    s = f"{b:g}"
    if l:
        s += f'<span class="lvp"> +{l:g}</span>'
    return s

def status_badge(t):
    s = state["status"][t]
    if s == "eliminated":
        return '<span class="badge out">OUT</span>'
    if s == "champion":
        return '<span class="badge champ">🏆 CHAMPION</span>'
    return '<span class="badge alive">ALIVE</span>'

tab1, tab2, tab3, tab4 = st.tabs(["📅 Schedule", "📊 Groups", "🪜 Bracket", "🏆 Pool Standings"])

# ------------------------------------------------------------- TAB 1 schedule
with tab1:
    default_day = dt.date(2026, 6, 18) if demo else min(max(dt.date.today(), wc.START), wc.END)
    c1, c2 = st.columns([2, 5])
    with c1:
        day = st.date_input("Matchday", value=default_day, min_value=wc.START, max_value=wc.END)
    todays = [m for m in matches if m["utc"].astimezone(TZ).date() == day]
    todays.sort(key=lambda m: m["utc"])
    if not todays:
        st.info("No matches on this date (or fixtures not posted yet). Try another day.")
    for m in todays:
        ta = wc.disp(m["a"]) if m["known"] else m["raw_a"]
        tb = wc.disp(m["b"]) if m["known"] else m["raw_b"]
        local = m["utc"].astimezone(TZ)
        when = local.strftime("%I:%M %p").lstrip("0")
        rnd = wc.ROUND_NAMES[m["round"]] + (f" · Group {m['group']}" if m["group"] else "")
        if m["state"] == "in":
            stat = f'<div class="mstat in">● {m["clock"] or "LIVE"}</div>'
        elif m["completed"]:
            stat = '<div class="mstat post">FT</div>'
        else:
            stat = f'<div class="mstat pre">{when}</div>'
        sa = "" if m["state"] == "pre" else m["sa"]
        sb = "" if m["state"] == "pre" else m["sb"]
        wa = " w" if (m["state"] != "pre" and m["sa"] > m["sb"]) else ""
        wb = " w" if (m["state"] != "pre" and m["sb"] > m["sa"]) else ""
        venue = f"<small>{m['venue']}</small>" if m["venue"] else "<small></small>"
        st.markdown(f"""
<div class="mcard">
  <div class="mwhen">{when}<small>{rnd}</small>{venue}</div>
  <div>
    <div class="trow{wa}"><span class="tname">{ta}</span>{chip(m["a"])}<span class="tsc">{sa}</span></div>
    <div class="trow{wb}"><span class="tname">{tb}</span>{chip(m["b"])}<span class="tsc">{sb}</span></div>
  </div>
  {stat}
</div>""", unsafe_allow_html=True)

# ------------------------------------------------------------- TAB 2 groups
with tab2:
    st.caption("Fantasy **Pts** = banked, with provisional points in red (live scores + "
               "if-the-group-ended-today bonuses: +3 win group, +5 advance, +5 best-8 thirds). "
               "Table tiebreakers approximated as points → GD → GF.")
    letters = list(wc.GROUPS)
    for g in letters:
        if True:
            if True:
                fin = state["group_final"][g]
                live_g = any(state["tbl"][g][t]["live"] for t in wc.GROUPS[g])
                badge = '<span class="fin">✓ FINAL</span>' if fin else ('<span class="liv">● LIVE</span>' if live_g else "")
                rows = ""
                for pos, t in enumerate(state["group_rank"][g]):
                    r = state["tbl"][g][t]
                    cls = "q1" if pos < 2 else ("q3" if pos == 2 else "")
                    lv = '<span class="lv"></span>' if r["live"] else ""
                    gd = r["GF"] - r["GA"]
                    rows += (f'<tr class="{cls}"><td>{pos + 1}</td>'
                             f'<td><b>{wc.disp(t)}</b>{lv}{chip(t)}</td>'
                             f'<td class="num">{r["P"]}</td><td class="num">{r["W"]}-{r["D"]}-{r["L"]}</td>'
                             f'<td class="num">{gd:+d}</td><td class="num">{r["Pts"]}</td>'
                             f'<td class="fp">{fpts_html(t)}</td></tr>')
                st.markdown(f'<div class="gname">Group {g} {badge}</div>'
                            f'<table class="gt"><tr><th>#</th><th>Team</th><th>P</th>'
                            f'<th>W-D-L</th><th>GD</th><th>Pts</th><th>Fantasy</th></tr>{rows}</table>',
                            unsafe_allow_html=True)
    st.markdown("#### Best third-place race")
    st.caption("Top 8 qualify for the Round of 32." +
               (" Standings final." if state["all_final"] else " Provisional until all groups finish."))
    rows = ""
    for i, x in enumerate(state["thirds"]):
        inout = ('<span class="badge alive">IN</span>' if i < 8 else '<span class="badge out">OUT</span>')
        lv = '<span class="lv"></span>' if x["live"] else ""
        style = ' style="border-top:2px solid var(--gold)"' if i == 8 else ""
        rows += (f'<tr{style}><td>{i + 1}</td><td><b>{wc.disp(x["t"])}</b>{lv}{chip(x["t"])} '
                 f'<span style="color:var(--mut)">· {x["g"]}</span></td>'
                 f'<td class="num">{x["Pts"]}</td><td class="num">{x["GD"]:+d}</td>'
                 f'<td class="num">{x["GF"]}</td><td>{inout}</td></tr>')
    st.markdown(f'<table class="gt"><tr><th>#</th><th>Team · Group</th><th>Pts</th>'
                f'<th>GD</th><th>GF</th><th></th></tr>{rows}</table>', unsafe_allow_html=True)

# ------------------------------------------------------------- TAB 3 bracket
with tab3:
    if not state["all_final"]:
        st.caption("Slots fill in as groups finish. Third-place lines show *eligible* groups; "
                   "exact allocation follows FIFA's table — once ESPN posts the real Round-of-32 "
                   "fixtures, those take over automatically.")
    def bk_card(c):
        def side(team, lbl, sc, is_w):
            nm = f"<b>{wc.disp(team)}</b>{chip(team)}" if team else f'<span class="ph">{lbl}</span>'
            scs = "" if sc is None else sc
            return f'<div class="bks{" win" if is_w else ""}"><span class="bknm">{nm}</span><span class="bksc">{scs}</span></div>'
        wa = c["winner"] is not None and c["winner"] == c["a"]
        wb = c["winner"] is not None and c["winner"] == c["b"]
        clock = f'<div class="bclock">● {c["clock"]}</div>' if c["state"] == "in" else ""
        return f'<div class="bk">{side(c["a"], c["albl"], c["sa"], wa)}{side(c["b"], c["blbl"], c["sb"], wb)}{clock}</div>'

    cols_html = ""
    for rnd, label in (("R32", "Round of 32"), ("R16", "Round of 16"),
                       ("QF", "Quarterfinals"), ("SF", "Semifinals")):
        cards = "".join(bk_card(c) for c in bracket[rnd])
        cols_html += f'<div class="bcol"><div class="bhead">{label}</div>{cards}</div>'
    fin, third = bracket["F"]
    cols_html += (f'<div class="bcol"><div class="bhead">Final · July 19</div>{bk_card(fin)}'
                  f'<div class="bhead" style="margin-top:18px">Third Place</div>{bk_card(third)}</div>')
    st.markdown(f'<div class="bwrap"><div class="bcols">{cols_html}</div></div>', unsafe_allow_html=True)
    if state["champion"]:
        o = wc.team_owner.get(state["champion"], "—")
        st.success(f"🏆 **{wc.disp(state['champion'])}** are world champions — {o} banks the 25.")

# ------------------------------------------------------------- TAB 4 owners
with tab4:
    ranked = sorted(wc.DRAFT, key=lambda o: -state["owner_total"][o])
    mx = max(state["owner_total"][o] for o in ranked) or 1
    html = ""
    for i, o in enumerate(ranked):
        c = COLORS[o]
        you = '<span class="you">YOU</span>' if o == ME else ""
        b, l, t = state["owner_banked"][o], state["owner_live"][o], state["owner_total"][o]
        lhtml = f'<div class="ostat lvp">+{l:g}<small>live</small></div>' if l else '<div class="ostat" style="color:var(--mut)">—<small>live</small></div>'
        sub = f'<div class="osub">{b:g} banked' + (f' · <span class="lvp">+{l:g} live</span>' if l else '') + '</div>'
        html += (f'<div class="orow{" me" if o == ME else ""}">'
                 f'<div class="ork">{i + 1}</div>'
                 f'<div class="oname"><span class="dot" style="background:{c}"></span>{o}{you}'
                 f'{sub}'
                 f'<div class="obar" style="margin-top:7px"><i style="background:{c};width:{t / mx * 100:.1f}%"></i></div></div>'
                 f'<div class="ostat colhide">{b:g}<small>banked</small></div>'
                 f'{lhtml.replace("ostat", "ostat colhide", 1)}'
                 f'<div class="ostat otot" style="color:{c};font-size:24px">{t:g}<small>total</small></div>'
                 f'</div>')
    st.markdown(html, unsafe_allow_html=True)
    st.caption("Banked = locked in from finished results and finalized groups. "
               "Live = provisional points that can still swing (in-progress scores + current group positions).")
    st.markdown("#### Rosters")
    for o in ranked:
        alive = sum(1 for t in wc.DRAFT[o] if state["status"][t] != "eliminated")
        with st.expander(f"{o} — {state['owner_total'][o]:g} pts · {alive}/6 teams alive"):
            rows = ""
            for t in sorted(wc.DRAFT[o], key=lambda t: -state["total"][t]):
                rows += (f'<tr><td><b>{wc.disp(t)}</b> <span style="color:var(--mut)">'
                         f'· Group {wc.team_group[t]}</span></td>'
                         f'<td>{status_badge(t)}</td>'
                         f'<td class="num">{state["banked"][t]:g}</td>'
                         f'<td class="num lvp">{("+" + format(state["live"][t], "g")) if state["live"][t] else "—"}</td>'
                         f'<td class="fp">{state["total"][t]:g}</td></tr>')
            st.markdown(f'<table class="gt"><tr><th>Team</th><th>Status</th><th>Banked</th>'
                        f'<th>Live</th><th>Total</th></tr>{rows}</table>', unsafe_allow_html=True)

# ------------------------------------------------------------- debug
with st.expander("🔧 Data debug"):
    st.write(f"Fixtures parsed: **{len(matches)}**")
    st.write(f"Completed: **{sum(1 for m in matches if m['completed'])}** · "
             f"Live: **{n_live}**")
    if unknown_names:
        st.warning("Unmatched team names from ESPN (add to the ALIAS map at the top of this file): "
                   + ", ".join(unknown_names))
    if fetch_errors:
        st.error("\n".join(fetch_errors))
    if not unknown_names and not fetch_errors:
        st.write("No name mismatches, no fetch errors. ✓")