#!/usr/bin/env python3
"""Depth-2 continuation-persistence census on the frozen 8-vs-5 residual.

Candidate admission is exactly the validated normalized raw-size residual:
raw_size(candidate) <= size(rescued_parent)+1.  No prover policy is changed.
For each admitted candidate we enumerate its one-step children, then ask whether
those children themselves preserve the previously validated moderate-contraction
corridor.  This tests persistence of future-action structure rather than another
local clause score.
"""
from __future__ import annotations

import json
import statistics
import time
from pathlib import Path

import run_residual3_lookahead_separator as base

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "experiments/mathgraph/results/residual3-depth2-persistence.json"
THRESHOLD = 0.5347
MAX_FRONTIER_CHILDREN = 12


def raw_gate(qraw, qred, parent):
    return base.size(qraw) <= base.size(parent) + 1


def enumerate_children(m, search, active, parent):
    """Unique legal one-step children with reduced-size deltas and raw-gate flag."""
    rules = [q for x in active if (q := search.orient(x)) is not None]
    pr = search.orient(parent)
    rules2 = rules + ([pr] if pr is not None else [])
    seen = set()
    out = []
    psize = base.size(parent)
    pscore = base.score0(search, parent)
    for oi, other in enumerate(active + [parent]):
        for bo, bi, a, b in ((parent, other, 9999, oi), (other, parent, oi, 9999)):
            for oside, outer in enumerate(base.fp.oriented_variants(m, bo)):
                for iside, inner in enumerate(base.fp.oriented_variants(m, bi)):
                    for path in m.nonvariable_positions(
                        outer.lhs,
                        maximum_depth=search.limits["maximum_depth"],
                        include_root=True,
                    ):
                        if search.expired():
                            return out
                        q = search.critical_pair(outer, inner, a * 2 + oside, b * 2 + iside, path)
                        if q is None:
                            continue
                        qr = search.interreduce(q, rules2)
                        k = base.fp.clause_key(qr)
                        if k in seen:
                            continue
                        seen.add(k)
                        out.append(
                            {
                                "clause": qr,
                                "key": k,
                                "delta": float(base.size(qr) - psize),
                                "target_delta": float(base.score0(search, qr) - pscore),
                                "rawgate": bool(raw_gate(q, qr, parent)),
                            }
                        )
    return out


def moderate_fraction(children):
    if not children:
        return 0.0
    return sum(-6 <= x["delta"] <= 0 for x in children) / len(children)


def depth2_stats(m, search, active, candidate):
    first = enumerate_children(m, search, active, candidate)
    one_corridor = moderate_fraction(first)

    # The second level follows only first-level children that remain inside the
    # same normalized raw-size residual.  Bound width deterministically by the
    # most target-relevant children to keep this a small, reproducible test.
    frontier = [x for x in first if x["rawgate"]]
    frontier.sort(key=lambda x: (x["target_delta"], x["delta"], str(x["key"])))
    frontier = frontier[:MAX_FRONTIER_CHILDREN]

    child_corridors = []
    child_legal = []
    pooled_grandchildren = []
    for x in frontier:
        if search.expired():
            break
        second = enumerate_children(m, search, active + [candidate], x["clause"])
        child_corridors.append(moderate_fraction(second))
        child_legal.append(len(second))
        pooled_grandchildren.extend(second)

    assessed = len(child_corridors)
    persistent = sum(v > THRESHOLD for v in child_corridors)
    return {
        "one_step_corridor": one_corridor,
        "first_legal_children": len(first),
        "first_rawgate_children": sum(int(x["rawgate"]) for x in first),
        "depth2_assessed_children": assessed,
        "depth2_persistent_children": persistent,
        "depth2_persistent_fraction": persistent / assessed if assessed else 0.0,
        "depth2_mean_child_corridor": statistics.fmean(child_corridors) if child_corridors else 0.0,
        "depth2_median_child_corridor": float(statistics.median(child_corridors)) if child_corridors else 0.0,
        "depth2_min_child_corridor": min(child_corridors) if child_corridors else 0.0,
        "depth2_max_child_corridor": max(child_corridors) if child_corridors else 0.0,
        "depth2_mean_child_branching": statistics.fmean(child_legal) if child_legal else 0.0,
        "depth2_pooled_moderate_fraction": moderate_fraction(pooled_grandchildren),
        "depth2_grandchildren": len(pooled_grandchildren),
    }


def census_one(m, r):
    state, err = base.prepare(m, r)
    if err:
        return err
    eng, search, active, rescued, given, later, vpath, first_i = state

    # prepare() uses a proof-search deadline.  This is a measurement-only
    # continuation census, so give the bounded depth-2 probe its own fixed
    # deadline while leaving every inference rule and normalization unchanged.
    local_deadline = time.monotonic() + 150.0
    search.expired = lambda: time.monotonic() >= local_deadline

    rules = [q for x in active if (q := search.orient(x)) is not None]
    later_set = set(later)
    rows = []
    seen = set()
    for oi, other in enumerate(active):
        for parent_outer, bo, bi, a, b in (
            (True, rescued, other, given, oi),
            (False, other, rescued, oi, given),
        ):
            for oside, outer in enumerate(base.fp.oriented_variants(m, bo)):
                for iside, inner in enumerate(base.fp.oriented_variants(m, bi)):
                    for path in m.nonvariable_positions(
                        outer.lhs,
                        maximum_depth=search.limits["maximum_depth"],
                        include_root=True,
                    ):
                        if search.expired():
                            break
                        q = search.critical_pair(outer, inner, a * 2 + oside, b * 2 + iside, path)
                        if q is None:
                            continue
                        qr = search.interreduce(q, rules)
                        k = base.fp.clause_key(qr)
                        sig = (k, parent_outer, oside, iside, tuple(path))
                        if sig in seen:
                            continue
                        seen.add(sig)
                        if not raw_gate(q, qr, rescued):
                            continue
                        rows.append(
                            {
                                "positive": k in later_set,
                                "formula_key": str(k),
                                "local": {
                                    "raw_size": base.size(q),
                                    "reduced_size": base.size(qr),
                                    "distinct_vars": base.distinct_vars(qr),
                                },
                                "lookahead": depth2_stats(m, search, active, qr),
                            }
                        )

    keys = [
        "one_step_corridor",
        "first_legal_children",
        "first_rawgate_children",
        "depth2_assessed_children",
        "depth2_persistent_children",
        "depth2_persistent_fraction",
        "depth2_mean_child_corridor",
        "depth2_median_child_corridor",
        "depth2_min_child_corridor",
        "depth2_max_child_corridor",
        "depth2_mean_child_branching",
        "depth2_pooled_moderate_fraction",
        "depth2_grandchildren",
    ]
    seps = [base.best_numeric(rows, k) for k in keys]
    seps = [x for x in seps if x]
    seps.sort(
        key=lambda z: (z["balanced_accuracy"], z["precision"], z["recall"], -z["fp"]),
        reverse=True,
    )
    return {
        "id": r["id"],
        "status": "COMPLETE",
        "first_vampire_path_index": first_i,
        "rescue_formula": vpath[first_i]["formula"],
        "candidates": len(rows),
        "positives": sum(x["positive"] for x in rows),
        "negatives": sum(not x["positive"] for x in rows),
        "best_depth2_separators": seps[:16],
        "rows": rows,
    }


def main():
    td, m = base.fp.load_solver()
    byid = {r["id"]: r for r in base.fp.rows()}
    out = []
    try:
        for rid in base.IDS:
            rec = census_one(m, byid[rid])
            out.append(rec)
            print("DEPTH2_PERSISTENCE", json.dumps(rec, sort_keys=True), flush=True)
    finally:
        td.cleanup()

    pooled = [x for rec in out if rec.get("status") == "COMPLETE" for x in rec["rows"]]
    keys = [
        "one_step_corridor",
        "first_legal_children",
        "first_rawgate_children",
        "depth2_assessed_children",
        "depth2_persistent_children",
        "depth2_persistent_fraction",
        "depth2_mean_child_corridor",
        "depth2_median_child_corridor",
        "depth2_min_child_corridor",
        "depth2_max_child_corridor",
        "depth2_mean_child_branching",
        "depth2_pooled_moderate_fraction",
        "depth2_grandchildren",
    ]
    seps = [base.best_numeric(pooled, k) for k in keys] if pooled else []
    seps = [x for x in seps if x]
    seps.sort(
        key=lambda z: (z["balanced_accuracy"], z["precision"], z["recall"], -z["fp"]),
        reverse=True,
    )
    pool = {
        "candidates": len(pooled),
        "positives": sum(x["positive"] for x in pooled),
        "negatives": sum(not x["positive"] for x in pooled),
        "threshold": THRESHOLD,
        "max_frontier_children": MAX_FRONTIER_CHILDREN,
        "best_depth2_separators": seps[:20],
    }
    result = {"rows": out, "pooled": pool}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("DEPTH2_PERSISTENCE_POOLED", json.dumps(pool, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
