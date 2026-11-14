#!/usr/bin/env python3
"""Build the stock data warehouse layers from stock.db into warehouse.db.

Source tables (stock.db)
    opening(sku, qty)                  -- opening balance, no warehouse
    movements(mid, sku, wh, biz_time, insert_time, type, qty)
                                       -- type in (IN, OUT, ADJUST)
                                       -- biz_time = business time
                                       -- insert_time = time the row hit the DB
                                       -- a late document has insert_time days after biz_time
    stocktake(sku, take_day, qty_found) -- physical count after the close of take_day
                                       -- NOTE: sku-level only, there is no warehouse column

Target tables (warehouse.db)
    dwd_balance(wh, sku, day, in_qty, out_qty, adj_qty, close_qty, take_diff)
    dws_day(day, in_qty, out_qty, adj_qty, close_qty, sku_count)
    stocktake_audit(...)                -- audit trail for the stocktake reset (the "交代")
    layer_notes(k, v)                   -- machine-readable statement of the conventions

Output
    layer_check.txt   -- three-way reconciliation dwd <-> movements <-> dws;
                         every row that does not tie out is printed as a DIFF line.

Conventions implemented here (also stored in warehouse.db.layer_notes)
--------------------------------------------------------------------
1. Grain of dwd_balance is (wh, sku, day).  Every (wh, sku) combination that
   appears in movements gets exactly one row per day from the date of its
   first movement (by biz_time) through the last business day in the data.
   Days without movements still get a row; in_qty/out_qty/adj_qty are 0 and
   close_qty carries forward.

2. Opening has no warehouse.  The opening qty of a sku is credited, once, to
   the warehouse of that sku's earliest movement (biz_time, then mid as
   tie-break).  It is a carried-in balance, not an inflow: it never appears in
   in_qty.  Other warehouses of the same sku start from 0 on their own first
   movement date.

3. Cumulative-flow basis: close_qty = previous close + in_qty - out_qty + adj_qty
   (+ take_diff on a stocktake day).  in_qty/out_qty/adj_qty are the sums of the
   day's movement quantities per type, so negative quantities are kept in place:
   a red reversal is a negative IN and lands in in_qty as a negative number,
   a negative ADJUST lands in adj_qty as a negative number.

4. Late documents are replayed on their business day (biz_time), never on
   insert_time.  A late document therefore restates its business day and every
   later day of the same (wh, sku) chain.  insert_time is used only to decide
   the calendar end and to report lateness in layer_check.txt.

5. Stocktake is sku-level.  On take_day, after that day's flows are applied:
       book_qty   = close_qty computed from the cumulative-flow chain
       take_diff  = qty_found - book_qty
       close_qty  = qty_found            (the counted value becomes the new
                                          baseline; all later days continue
                                          from it)
   take_diff is NULL on every non-stocktake day and is filled on the stocktake
   day (0 is stored as 0, not NULL, when book and physical agree).

6. Stocktake on a day that also has flows ("盘点日当天仍有流水进出"):
   the day's in_qty/out_qty/adj_qty keep recording the raw same-day flows;
   the book balance is formed from them and then compared with the physical
   count.  The whole gap, including any effect of same-day flows and of late
   documents replayed onto that day, is isolated in take_diff, so the identity
       close_qty = prev_close_qty + in_qty - out_qty + adj_qty + take_diff
   holds on the stocktake day, and
       close_qty = prev_close_qty + in_qty - out_qty + adj_qty
   holds on every other day.  The stocktake never rewrites the movement columns.
   stocktake_audit records, per (sku, take_day), the same-day flow totals,
   the book balance before the reset, the physical count and the resulting
   take_diff, so the presentation is explicit and auditable.

7. If a sku with a stocktake spans several warehouses (not present in the
   sample), qty_found is read as the sku total.  The reset is applied at sku
   level and the whole take_diff is absorbed by the sku's home warehouse
   (rule 2), leaving other warehouses' rows untouched with take_diff NULL.

8. dws_day aggregates dwd_balance by day: sums of the three flow columns and
   of close_qty.  sku_count is the number of dwd_balance detail rows on that
   day (row count, not distinct sku count).
"""

from __future__ import annotations

import argparse
import os
import sqlite3
import sys
from collections import defaultdict
from datetime import date, datetime, timedelta, timezone

ZERO3 = ("in_qty", "out_qty", "adj_qty")
TYPE_COL = {"IN": "in_qty", "OUT": "out_qty", "ADJUST": "adj_qty"}


# --------------------------------------------------------------------------- #
# small helpers
# --------------------------------------------------------------------------- #
def d(s: str) -> date:
    """Parse the date part of a TEXT timestamp."""
    return date.fromisoformat(s[:10])


def day_str(dd: date) -> str:
    return dd.isoformat()


def daterange(start: date, end: date):
    cur = start
    while cur <= end:
        yield cur
        cur += timedelta(days=1)


def coalesce(v, default=0):
    return default if v is None else v


def warn(msg: str) -> None:
    print("WARNING:", msg, file=sys.stderr)


# --------------------------------------------------------------------------- #
# source loading
# --------------------------------------------------------------------------- #
def load_source(path: str):
    con = sqlite3.connect(path)
    con.row_factory = sqlite3.Row

    opening = {}
    dup_opening = []
    for r in con.execute("SELECT sku, qty FROM opening"):
        if r["sku"] in opening:
            dup_opening.append(r["sku"])
        opening[r["sku"]] = opening.get(r["sku"], 0) + int(r["qty"])
    if dup_opening:
        warn(f"opening has duplicate sku rows, summed: {sorted(set(dup_opening))}")

    movs = [dict(r) for r in con.execute(
        "SELECT mid, sku, wh, biz_time, insert_time, type, qty FROM movements")]
    for m in movs:
        m["qty"] = int(m["qty"])
        m["day"] = day_str(d(m["biz_time"]))
        m["insert_day"] = day_str(d(m["insert_time"]))
        if m["type"] not in TYPE_COL:
            warn(f"movement {m['mid']} has unknown type {m['type']!r}; treated as ADJUST")
        if m["wh"] in (None, "") or m["sku"] in (None, ""):
            warn(f"movement {m['mid']} has no wh/sku")

    takes = defaultdict(dict)          # sku -> {day: qty_found}
    take_dups = []
    for r in con.execute("SELECT sku, take_day, qty_found FROM stocktake"):
        dd = day_str(d(r["take_day"]))
        sku = r["sku"]
        if dd in takes[sku]:
            take_dups.append((sku, dd))
        takes[sku][dd] = int(r["qty_found"])
    if take_dups:
        warn(f"duplicate stocktake (sku, day) rows, last wins: {take_dups}")

    con.close()
    return opening, movs, takes


# --------------------------------------------------------------------------- #
# layer construction
# --------------------------------------------------------------------------- #
def build_layer(opening, movs, takes):
    """Return (dwd_rows, dws_rows, audit_rows, notes)."""
    # Home warehouse per sku: warehouse of the earliest movement (biz_time, mid).
    home_wh = {}
    for m in sorted(movs, key=lambda x: (x["biz_time"], x["mid"])):
        home_wh.setdefault(m["sku"], m["wh"])

    # First business day of every (wh, sku) combination.
    combo_start = {}
    for m in movs:
        key = (m["wh"], m["sku"])
        dd = d(m["day"])
        if key not in combo_start or dd < combo_start[key]:
            combo_start[key] = dd

    # Daily movement totals per (wh, sku, day).
    flows = defaultdict(lambda: {"in_qty": 0, "out_qty": 0, "adj_qty": 0})
    for m in movs:
        col = TYPE_COL.get(m["type"], "adj_qty")
        flows[(m["wh"], m["sku"], m["day"])][col] += m["qty"]

    # Calendar end: last business day, also allowing for insert dates and take days
    # so nothing that exists in the sources falls outside the grid.
    ends = [d(m["day"]) for m in movs] + [d(m["insert_day"]) for m in movs]
    ends += [d(dd) for per in takes.values() for dd in per]
    if not ends:
        return [], [], [], {}
    cal_end = max(ends)

    # Skus to place: every sku seen anywhere.
    all_skus = sorted(set(opening) | {m["sku"] for m in movs} | set(takes))

    dwd = []
    audit = []
    unplaced = []

    for sku in all_skus:
        whs = sorted({wh for (wh, s) in combo_start if s == sku})
        if not whs:
            # In opening / stocktake but no movement: no warehouse can be inferred.
            unplaced.append(sku)
            warn(f"sku {sku} has no movement, so it cannot be assigned to a warehouse; "
                 f"its opening/count is omitted from dwd_balance")
            continue
        home = home_wh.get(sku, whs[0])
        start = {wh: combo_start[(wh, sku)] for wh in whs}
        first_day = min(start.values())

        close = {}                      # wh -> current close balance
        for dd in daterange(first_day, cal_end):
            day = day_str(dd)
            active = [wh for wh in whs if dd >= start[wh]]

            # 1) open the combination (opening qty is a carried balance, not a flow)
            #    and apply the day's flows.
            for wh in active:
                if wh not in close:
                    close[wh] = opening.get(sku, 0) if wh == home else 0
                f = flows.get((wh, sku, day), {"in_qty": 0, "out_qty": 0, "adj_qty": 0})
                close[wh] += f["in_qty"] - f["out_qty"] + f["adj_qty"]

            # 2) stocktake reset, after same-day flows.
            take_diff_row = {wh: None for wh in active}
            if day in takes.get(sku, {}):
                physical = takes[sku][day]
                book_total = sum(close[wh] for wh in active)
                diff = physical - book_total
                absorb = home if home in active else (active[0] if active else None)
                if absorb is None:
                    warn(f"stocktake {sku} {day} falls before the first movement; ignored")
                else:
                    close[absorb] += diff
                    take_diff_row[absorb] = diff
                    audit.append({
                        "day": day, "sku": sku, "wh": absorb,
                        "in_qty": sum(flows.get((w, sku, day), {}).get("in_qty", 0) for w in active),
                        "out_qty": sum(flows.get((w, sku, day), {}).get("out_qty", 0) for w in active),
                        "adj_qty": sum(flows.get((w, sku, day), {}).get("adj_qty", 0) for w in active),
                        "book_qty": book_total, "take_qty": physical, "take_diff": diff,
                    })

            # 3) emit one dwd row per active warehouse, every day.
            for wh in active:
                f = flows.get((wh, sku, day), {"in_qty": 0, "out_qty": 0, "adj_qty": 0})
                dwd.append({
                    "wh": wh, "sku": sku, "day": day,
                    "in_qty": f["in_qty"], "out_qty": f["out_qty"], "adj_qty": f["adj_qty"],
                    "close_qty": close[wh], "take_diff": take_diff_row[wh],
                })

    dwd.sort(key=lambda r: (r["day"], r["wh"], r["sku"]))
    audit.sort(key=lambda r: (r["day"], r["sku"], r["wh"]))

    # dws_day: aggregate the detail by day.
    agg = defaultdict(lambda: {"in_qty": 0, "out_qty": 0, "adj_qty": 0, "close_qty": 0, "sku_count": 0})
    for r in dwd:
        a = agg[r["day"]]
        a["in_qty"] += r["in_qty"]
        a["out_qty"] += r["out_qty"]
        a["adj_qty"] += r["adj_qty"]
        a["close_qty"] += r["close_qty"]
        a["sku_count"] += 1
    dws = [{"day": k, **v} for k, v in sorted(agg.items())]

    notes = make_notes(opening, movs, takes, home_wh, cal_end, unplaced)
    return dwd, dws, audit, notes


def make_notes(opening, movs, takes, home_wh, cal_end, unplaced) -> list[tuple[str, str]]:
    late = [m for m in movs if m["insert_day"] > m["day"]]
    firsts = sorted({m["day"] for m in movs})
    notes = [
        ("layer", "dwd_balance -> dws_day; source stock.db, target warehouse.db"),
        ("grain_dwd", "one row per (wh, sku, day); each wh+sku combination runs daily "
                      "from its first movement biz date through the last date in the data"),
        ("calendar", f"business dates {firsts[0]}..{day_str(cal_end)} inclusive; "
                     f"first date is per combination, end date is global"),
        ("flow_basis", "cumulative flows: close = prev_close + in - out + adj (+ take_diff on a stocktake day)"),
        ("opening", "opening has no warehouse: credited once to the sku's earliest-movement "
                    "warehouse (biz_time, mid tie-break); it is a carried balance and is never "
                    "counted in in_qty; other warehouses of the same sku start at 0"),
        ("red_reversal", "a red reversal is a negative-qty IN and stays in in_qty as a negative "
                         "amount; negative ADJUST stays in adj_qty as a negative amount"),
        ("late_docs", "movements are replayed on biz_time, never insert_time; a late doc restates "
                      "its business day and all later days of the same wh+sku chain; "
                      f"{len(late)} of {len(movs)} movements are late in this dataset"),
        ("stocktake_reset", "on take_day, after that day's flows: take_diff = qty_found - book_qty; "
                            "close_qty = qty_found (the counted value is the new baseline); later days "
                            "continue from the counted value"),
        ("take_diff_null", "take_diff is NULL on non-stocktake days and stores the difference "
                           "(0 included) on the stocktake day"),
        ("stocktake_day_flows",
         "same-day flows are NOT suppressed on a stocktake day: in/out/adj keep the raw day's movements, "
         "book_qty is built from them, and the entire gap -- including any same-day flow and any late "
         "document replayed onto that day -- is isolated in take_diff; identity on a stocktake day: "
         "close = prev_close + in - out + adj + take_diff; stocktake_audit records book_qty, "
         "take_qty and take_diff per (sku, take_day)"),
        ("stocktake_multi_wh",
         "stocktake is sku-level (no wh column); qty_found is read as the sku total. If a sku spans "
         "several warehouses, the reset is applied at sku level and the whole take_diff is absorbed "
         "by the sku's home warehouse; the other warehouse rows keep take_diff NULL. All stocktake "
         "skus in this sample are single-warehouse"),
        ("dws_day", "sums of in/out/adj/close across dwd_balance rows for the day; sku_count is the "
                    "number of detail rows on that day (row count, not distinct skus)"),
        ("no_flow_days", "a wh+sku day with no movement still gets a dwd row: in/out/adj = 0, close carries"),
        ("checks", "layer_check.txt reconciles dwd_balance <-> movements <-> dws_day; "
                   "every non-tying row is printed as a DIFF line"),
    ]
    if unplaced:
        notes.append(("unplaced_skus", "skus with no movement could not be placed in a warehouse: "
                                       + ", ".join(unplaced)))
    return notes


# --------------------------------------------------------------------------- #
# writing
# --------------------------------------------------------------------------- #
DDL = """
DROP TABLE IF EXISTS dwd_balance;
DROP TABLE IF EXISTS dws_day;
DROP TABLE IF EXISTS stocktake_audit;
DROP TABLE IF EXISTS layer_notes;

CREATE TABLE dwd_balance (
    wh        TEXT    NOT NULL,
    sku       TEXT    NOT NULL,
    day       TEXT    NOT NULL,
    in_qty    INTEGER NOT NULL,
    out_qty   INTEGER NOT NULL,
    adj_qty   INTEGER NOT NULL,
    close_qty INTEGER NOT NULL,
    take_diff INTEGER,
    PRIMARY KEY (wh, sku, day)
);

CREATE TABLE dws_day (
    day        TEXT    PRIMARY KEY,
    in_qty     INTEGER NOT NULL,
    out_qty    INTEGER NOT NULL,
    adj_qty    INTEGER NOT NULL,
    close_qty  INTEGER NOT NULL,
    sku_count  INTEGER NOT NULL
);

CREATE TABLE stocktake_audit (
    day        TEXT    NOT NULL,   -- take_day
    sku        TEXT    NOT NULL,
    wh         TEXT    NOT NULL,   -- warehouse that absorbs the reset
    in_qty     INTEGER NOT NULL,   -- same-day flows across the sku's active warehouses
    out_qty    INTEGER NOT NULL,
    adj_qty    INTEGER NOT NULL,
    book_qty   INTEGER NOT NULL,   -- cumulative-flow book balance before the reset
    take_qty   INTEGER NOT NULL,   -- qty_found
    take_diff  INTEGER NOT NULL,   -- take_qty - book_qty
    PRIMARY KEY (sku, day)
);

CREATE TABLE layer_notes (
    k TEXT PRIMARY KEY,
    v TEXT NOT NULL
);
"""


def write_layer(dst_path, dwd, dws, audit, notes):
    con = sqlite3.connect(dst_path)
    con.executescript(DDL)
    con.executemany(
        "INSERT INTO dwd_balance VALUES (?,?,?,?,?,?,?,?)",
        [(r["wh"], r["sku"], r["day"], r["in_qty"], r["out_qty"], r["adj_qty"],
         r["close_qty"], r["take_diff"]) for r in dwd])
    con.executemany(
        "INSERT INTO dws_day VALUES (?,?,?,?,?,?)",
        [(r["day"], r["in_qty"], r["out_qty"], r["adj_qty"], r["close_qty"], r["sku_count"])
         for r in dws])
    con.executemany(
        "INSERT INTO stocktake_audit VALUES (?,?,?,?,?,?,?,?,?)",
        [(r["day"], r["sku"], r["wh"], r["in_qty"], r["out_qty"], r["adj_qty"],
         r["book_qty"], r["take_qty"], r["take_diff"]) for r in audit])
    con.executemany("INSERT INTO layer_notes VALUES (?,?)", notes)
    con.commit()
    con.close()


# --------------------------------------------------------------------------- #
# reconciliation: dwd_balance <-> movements <-> dws_day
# --------------------------------------------------------------------------- #
def run_checks(src_path, dst_path, out_path):
    src = sqlite3.connect(src_path)
    src.row_factory = sqlite3.Row
    dst = sqlite3.connect(dst_path)
    dst.row_factory = sqlite3.Row

    diffs = []      # (check, key, field, dwd_value, ref_value)
    infos = []
    warns = []

    def add(check, key, field, left, right):
        diffs.append((check, key, field, left, right))

    movements = [dict(r) for r in src.execute(
        "SELECT mid, sku, wh, biz_time, insert_time, type, qty FROM movements")]
    for m in movements:
        m["qty"] = int(m["qty"])
        m["day"] = m["biz_time"][:10]
        m["insert_day"] = m["insert_time"][:10]

    dwd = [dict(r) for r in dst.execute("SELECT * FROM dwd_balance ORDER BY day, wh, sku")]
    dws = [dict(r) for r in dst.execute("SELECT * FROM dws_day ORDER BY day")]

    if not dwd:
        diffs.append(("layer", "dwd_balance", "rows", 0, 1))

    # ---- expected daily flows from movements, per (wh, sku, day) --------------
    exp = defaultdict(lambda: {"in_qty": 0, "out_qty": 0, "adj_qty": 0})
    for m in movements:
        key = (m["wh"], m["sku"], m["day"])
        if m["type"] == "IN":
            exp[key]["in_qty"] += m["qty"]
        elif m["type"] == "OUT":
            exp[key]["out_qty"] += m["qty"]
        elif m["type"] == "ADJUST":
            exp[key]["adj_qty"] += m["qty"]
        else:
            exp[key]["adj_qty"] += m["qty"]   # build used the same fallback

    # check 1: dwd_balance flow columns vs movements
    seen_keys = set()
    for r in dwd:
        key = (r["wh"], r["sku"], r["day"])
        seen_keys.add(key)
        e = exp.get(key, {"in_qty": 0, "out_qty": 0, "adj_qty": 0})
        for f in ZERO3:
            if r[f] != e[f]:
                add("dwd<>movements", key, f, r[f], e[f])
    for key, e in exp.items():
        if key not in seen_keys:
            add("dwd<>movements", key, "row", None, sum(e.values()) or 0)

    # check 2: closing chain inside each (wh, sku) chain
    home = {}
    for m in sorted(movements, key=lambda x: (x["biz_time"], x["mid"])):
        home.setdefault(m["sku"], m["wh"])
    opening = defaultdict(int)
    for r in src.execute("SELECT sku, qty FROM opening"):
        opening[r["sku"]] += int(r["qty"])
    opening = dict(opening)
    chains = defaultdict(list)
    for r in dwd:
        chains[(r["wh"], r["sku"])].append(r)
    for (wh, sku), rows in chains.items():
        rows.sort(key=lambda r: r["day"])
        prev = None
        for i, r in enumerate(rows):
            base = opening.get(sku, 0) if (prev is None and wh == home.get(sku)) else prev
            base = coalesce(base, 0)
            expected = base + r["in_qty"] - r["out_qty"] + r["adj_qty"] + coalesce(r["take_diff"], 0)
            if r["close_qty"] != expected:
                add("close-chain", (wh, sku, r["day"]), "close_qty", r["close_qty"], expected)
            prev = r["close_qty"]
        # first row must be the combination's first movement date (grid completeness)
        if rows and rows[0]["day"] != min(m["day"] for m in movements
                                          if m["wh"] == wh and m["sku"] == sku):
            add("grid", (wh, sku), "first_day", rows[0]["day"],
                min(m["day"] for m in movements if m["wh"] == wh and m["sku"] == sku))
        # every day to the global end must exist
        if rows:
            end = max(r["day"] for r in dwd)
            days = [r["day"] for r in rows]
            want = [day_str(d) for d in daterange(d(rows[0]["day"]), d(end))]
            if days != want:
                miss = sorted(set(want) - set(days))
                add("grid", (wh, sku), "missing_days", len(days), len(want))
                infos.append(f"grid gap {wh}/{sku}: missing {miss}")

    # check 3: dws_day vs dwd_balance per day
    agg = defaultdict(lambda: {"in_qty": 0, "out_qty": 0, "adj_qty": 0, "close_qty": 0, "sku_count": 0})
    for r in dwd:
        a = agg[r["day"]]
        for f in ("in_qty", "out_qty", "adj_qty", "close_qty"):
            a[f] += r[f]
        a["sku_count"] += 1
    dws_by_day = {r["day"]: r for r in dws}
    for day, a in agg.items():
        r = dws_by_day.get(day)
        if r is None:
            add("dws<>dwd", day, "row", None, 1)
            continue
        for f in ("in_qty", "out_qty", "adj_qty", "close_qty", "sku_count"):
            if r[f] != a[f]:
                add("dws<>dwd", day, f, r[f], a[f])
    for day in set(dws_by_day) - set(agg):
        add("dws<>dwd", day, "row", 1, None)

    # check 4: dws_day flow columns vs movements, per day
    day_exp = defaultdict(lambda: {"in_qty": 0, "out_qty": 0, "adj_qty": 0})
    for m in movements:
        f = {"IN": "in_qty", "OUT": "out_qty"}.get(m["type"], "adj_qty")
        day_exp[m["day"]][f] += m["qty"]
    for day, r in dws_by_day.items():
        e = day_exp.get(day, {"in_qty": 0, "out_qty": 0, "adj_qty": 0})
        for f in ZERO3:
            if r[f] != e[f]:
                add("dws<>movements", day, f, r[f], e[f])
    for day in set(day_exp) - set(dws_by_day):
        add("dws<>movements", day, "row", None, 1)

    # check 5: global totals (three-way, end of window)
    m_tot = {"in_qty": 0, "out_qty": 0, "adj_qty": 0}
    for m in movements:
        f = {"IN": "in_qty", "OUT": "out_qty"}.get(m["type"], "adj_qty")
        m_tot[f] += m["qty"]
    dwd_tot = {f: sum(r[f] for r in dwd) for f in ZERO3}
    dws_tot = {f: sum(r[f] for r in dws) for f in ZERO3}
    for f in ZERO3:
        if dwd_tot[f] != m_tot[f]:
            add("total<>movements", "dwd", f, dwd_tot[f], m_tot[f])
        if dws_tot[f] != m_tot[f]:
            add("total<>movements", "dws", f, dws_tot[f], m_tot[f])

    # end-of-window balance: opening placed + net movements + take_diff
    placed_opening = sum(v for s, v in opening.items()
                         if any(m["sku"] == s for m in movements))
    take_total = sum(int(r["take_diff"]) for r in dst.execute(
        "SELECT take_diff FROM dwd_balance WHERE take_diff IS NOT NULL"))
    net = m_tot["in_qty"] - m_tot["out_qty"] + m_tot["adj_qty"]
    end_expected = placed_opening + net + take_total
    end_dwd = sum(r["close_qty"] for r in dwd if r["day"] == max(x["day"] for x in dwd))
    end_dws = dws[-1]["close_qty"] if dws else 0
    if end_dwd != end_expected:
        add("total", "dwd", "end_close", end_dwd, end_expected)
    if end_dws != end_expected:
        add("total", "dws", "end_close", end_dws, end_expected)
    placed_skus = {s for s, v in opening.items() if any(m["sku"] == s for m in movements)}
    if set(opening) - placed_skus:
        warns.append("opening skus with no movements (not placed): " + str(sorted(set(opening) - placed_skus)))

    # check 6: stocktake audit vs the two layers
    for r in dst.execute("SELECT * FROM stocktake_audit ORDER BY day, sku"):
        r = dict(r)
        actual = dst.execute(
            "SELECT COALESCE(SUM(close_qty),0), COUNT(*) FROM dwd_balance WHERE sku=? AND day=?",
            (r["sku"], r["day"])).fetchone()
        if actual[0] != r["take_qty"]:
            add("stocktake", (r["sku"], r["day"]), "close_qty", actual[0], r["take_qty"])
        if actual[1] == 0:
            add("stocktake", (r["sku"], r["day"]), "row", 0, 1)
    # take_diff present exactly on stocktake days (once per stocktake)
    take_keys = {(r["sku"], r["day"]) for r in dst.execute("SELECT sku, day FROM stocktake_audit")}
    observed_td = defaultdict(int)
    for r in dwd:
        if r["take_diff"] is not None:
            observed_td[(r["sku"], r["day"])] += 1
    for key in take_keys:
        if observed_td.get(key, 0) != 1:
            add("stocktake", key, "take_diff_rows", observed_td.get(key, 0), 1)
    for key in set(observed_td) - take_keys:
        add("stocktake", key, "unexpected_take_diff", observed_td[key], 0)
    # the stored diff must equal count - book
    for r in dst.execute("SELECT * FROM stocktake_audit"):
        if r["take_diff"] != r["take_qty"] - r["book_qty"]:
            add("stocktake", (r["sku"], r["day"]), "take_diff", r["take_diff"],
                r["take_qty"] - r["book_qty"])

    # non-diff observations
    neg = [r for r in dwd if r["close_qty"] < 0]
    if neg:
        warns.append(f"{len(neg)} dwd rows with negative close_qty: "
                     + str([(r["wh"], r["sku"], r["day"], r["close_qty"]) for r in neg][:10]))
    late = [m for m in movements if m["insert_day"] > m["day"]]
    infos.append(f"late movements (biz day < insert day): {len(late)} of {len(movements)}")
    for m in sorted(late, key=lambda x: (x["day"], x["mid"])):
        infos.append(f"  late {m['mid']} {m['sku']}/{m['wh']} type={m['type']} qty={m['qty']} "
                     f"biz={m['day']} inserted={m['insert_day']}")
    skus = sorted({r["sku"] for r in dwd})
    wh_sku = sorted({(r["wh"], r["sku"]) for r in dwd})
    infos.append(f"dwd_balance: {len(dwd)} rows, {len(wh_sku)} (wh,sku) combinations, "
                 f"{len(dws)} days, skus={', '.join(skus)}")
    infos.append(f"dwd sums in/out/adj = {dwd_tot['in_qty']}/{dwd_tot['out_qty']}/{dwd_tot['adj_qty']}; "
                 f"movements sums = {m_tot['in_qty']}/{m_tot['out_qty']}/{m_tot['adj_qty']}")
    infos.append(f"opening placed = {placed_opening}; net movement = {net}; take_diff total = {take_total}; "
                 f"end close expected = {end_expected}; dwd = {end_dwd}; dws = {end_dws}")

    # ---- write layer_check.txt ------------------------------------------------
    lines = []
    lines.append("layer_check.txt -- three-way reconciliation: dwd_balance <-> movements <-> dws_day")
    lines.append(f"source: {src_path}")
    lines.append(f"layer : {dst_path}")
    if dwd:
        days = sorted({r["day"] for r in dwd})
        lines.append(f"window: {days[0]} .. {days[-1]}  ({len(days)} days)")
    lines.append(f"generated_at: {datetime.now(timezone.utc).isoformat(timespec='seconds')}")
    lines.append("")
    lines.append("checks")
    lines.append("  [1] dwd_balance flow columns vs movements, grain (wh, sku, day)")
    lines.append("  [2] close chain within each (wh, sku): close = prev + in - out + adj + take_diff")
    lines.append("  [3] dws_day vs dwd_balance, grain (day): sums and sku_count")
    lines.append("  [4] dws_day flow columns vs movements, grain (day)")
    lines.append("  [5] global totals: dwd / dws / movements agree, end close reconciles")
    lines.append("  [6] stocktake: reset applied, take_diff exactly on stocktake days")
    lines.append("")
    if diffs:
        lines.append(f"diff rows: {len(diffs)}")
        lines.append("format: DIFF | check | key | field | layer_value | reference_value | delta")
        for check, key, field, left, right in diffs:
            delta = None
            if isinstance(left, (int, float)) and isinstance(right, (int, float)):
                delta = left - right
            lines.append(f"DIFF | {check} | {key} | {field} | {left} | {right} | {delta}")
    else:
        lines.append("diff rows: 0 -- every dwd / dws / movement row ties out")
    lines.append("")
    lines.append("info")
    for s in infos:
        lines.append("  " + s)
    if warns:
        lines.append("")
        lines.append("warnings")
        for s in warns:
            lines.append("  WARN " + s)
    lines.append("")
    lines.append("RESULT: " + ("PASS -- 0 diff rows" if not diffs else f"FAIL -- {len(diffs)} diff rows"))
    text = "\n".join(lines) + "\n"
    with open(out_path, "w", encoding="utf-8") as fh:
        fh.write(text)

    src.close()
    dst.close()
    return diffs


# --------------------------------------------------------------------------- #
def main(argv=None):
    ap = argparse.ArgumentParser(description="Build dwd_balance / dws_day from stock.db")
    ap.add_argument("src", nargs="?", default="stock.db", help="source sqlite db")
    ap.add_argument("dst", nargs="?", default="warehouse.db", help="target sqlite db")
    ap.add_argument("check", nargs="?", default="layer_check.txt", help="reconciliation report")
    args = ap.parse_args(argv)

    for p in (args.src,):
        if not os.path.exists(p):
            sys.exit(f"source db not found: {p}")

    opening, movs, takes = load_source(args.src)
    dwd, dws, audit, notes = build_layer(opening, movs, takes)
    write_layer(args.dst, dwd, dws, audit, notes)
    diffs = run_checks(args.src, args.dst, args.check)

    print(f"dwd_balance: {len(dwd)} rows | dws_day: {len(dws)} rows | "
          f"stocktake_audit: {len(audit)} rows -> {args.dst}")
    print(f"checks: {'PASS' if not diffs else 'FAIL'} ({len(diffs)} diff rows) -> {args.check}")
    return 0 if not diffs else 1


if __name__ == "__main__":
    sys.exit(main())
