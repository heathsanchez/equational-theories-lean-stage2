#!/usr/bin/env python3
"""Fast, target-independent collapse capability probe over a stress corpus.

For each row we discard the real target and ask whether the source theory alone
can derive the synthetic universal equality x = y under a tiny fixed budget.
Any positive must replay internally.  The experiment is intentionally blind to
problem ids and real targets; ids are logged only after the search result exists.
"""

import argparse
import importlib.util
import json
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("mathgraph_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_text(row):
    for key in ("equation1", "source", "eq1"):
        if isinstance(row.get(key), str):
            return row[key]
    raise KeyError("source equation not found")


def truth_label(row):
    for key in ("answer", "label", "truth", "is_true"):
        if key in row:
            value = row[key]
            if isinstance(value, bool):
                return value
            if isinstance(value, str):
                low = value.strip().lower()
                if low in ("true", "1", "yes"):
                    return True
                if low in ("false", "0", "no"):
                    return False
            if isinstance(value, (int, float)):
                return bool(value)
    return None


def unpack_result(search, raw):
    if raw is None or raw is False:
        return None
    if isinstance(raw, int):
        return search.nodes, raw
    if isinstance(raw, tuple) and len(raw) == 2:
        a, b = raw
        if isinstance(a, list) and isinstance(b, int):
            return a, b
        if isinstance(a, int) and isinstance(b, list):
            return b, a
    if hasattr(raw, "lhs") and raw in search.nodes:
        return search.nodes, search.nodes.index(raw)
    return None


def run_search(module, source, seconds):
    x = ("var", "x")
    y = ("var", "y")
    synthetic = (x, y, ("x", "y"))

    direct = module.variable_omission_collapse(source, synthetic)
    if direct is not None:
        nodes, root = direct
        return {
            "collapsed": bool(module.replay_dag(source, nodes, root)),
            "constructor": "variable_omission_collapse",
            "proof_nodes": len(nodes),
            "graph_edges": 0,
            "exhaustion": None,
        }

    limits = {
        "max_term_size": 11,
        "max_pool_terms": 22,
        "max_core_terms": 6,
        "max_source_attempts": 30000,
        "max_source_edges": 700,
        "max_derivation_nodes": 2200,
        "max_graph_edges": 1800,
        "max_congruence_rounds": 2,
    }
    search = module.EqualitySearch(
        source, synthetic, time.monotonic() + seconds, limits
    )
    method_name = next(
        (name for name in ("solve", "run", "search")
         if callable(getattr(search, name, None))),
        None,
    )
    if method_name is None:
        raise RuntimeError("EqualitySearch has no executable entrypoint")
    raw = getattr(search, method_name)()
    unpacked = unpack_result(search, raw)
    collapsed = False
    proof_nodes = 0
    if unpacked is not None:
        nodes, root = unpacked
        collapsed = bool(module.replay_dag(source, nodes, root))
        proof_nodes = len(nodes) if collapsed else 0
    return {
        "collapsed": collapsed,
        "constructor": "equality_search" if collapsed else None,
        "proof_nodes": proof_nodes,
        "graph_edges": getattr(search, "graph_edges", None),
        "exhaustion": getattr(search, "exhaustion", None),
        "entrypoint": method_name,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus", type=Path)
    ap.add_argument("--seconds", type=float, default=1.0)
    args = ap.parse_args()

    module = load_solver()
    rows = [
        json.loads(line) for line in args.corpus.read_text().splitlines()
        if line.strip()
    ]
    results = []
    started = time.monotonic()
    for index, row in enumerate(rows):
        source = module.parse_equation(source_text(row))
        t0 = time.monotonic()
        probe = run_search(module, source, args.seconds)
        rec = {
            "index": index,
            "id": row.get("id"),
            "label": truth_label(row),
            "elapsed_seconds": round(time.monotonic() - t0, 4),
            **probe,
        }
        results.append(rec)
        if rec["collapsed"]:
            print("SOURCE_COLLAPSE_POSITIVE " + json.dumps(rec, sort_keys=True), flush=True)

    positives = [r for r in results if r["collapsed"]]
    by_label = {}
    for label in (True, False, None):
        subset = [r for r in results if r["label"] is label]
        if subset:
            by_label[str(label)] = {
                "rows": len(subset),
                "collapsed": sum(r["collapsed"] for r in subset),
            }
    wanted = {
        r["id"]: r for r in results
        if r["id"] in {"order5_normal_0030", "order5_normal_0036"}
    }
    summary = {
        "rows": len(results),
        "seconds_per_row": args.seconds,
        "wall_seconds": round(time.monotonic() - started, 3),
        "positives": len(positives),
        "by_label": by_label,
        "focus": wanted,
        "positive_ids": [r["id"] for r in positives],
    }
    print("SOURCE_COLLAPSE_SUMMARY " + json.dumps(summary, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
