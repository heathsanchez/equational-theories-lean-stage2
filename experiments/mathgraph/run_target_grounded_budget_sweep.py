#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("mathgraph_solver_budget_sweep", SOLVER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    m = load_solver()
    rows = json.loads(args.input.read_text())
    if isinstance(rows, dict):
        rows = rows.get("rows", [])

    base = dict(m.COMPACT_SUPERPOSITION_PROBE)
    conditions = [
        ("P05", 0.5, {}),
        ("P1", 1.0, {}),
        ("P2", 2.0, {}),
        ("P5", 5.0, {}),
        ("P10", 10.0, {}),
        ("W5", 5.0, {"maximum_rules":384,"maximum_rounds":32,"new_clauses_per_round":256,"maximum_clauses":4000,"normalization_steps":160,"maximum_term_size":55,"maximum_replay_term_size":220,"maximum_proof_nodes":30000}),
        ("W10", 10.0, {"maximum_rules":512,"maximum_rounds":48,"new_clauses_per_round":384,"maximum_clauses":8000,"normalization_steps":192,"maximum_term_size":65,"maximum_replay_term_size":260,"maximum_proof_nodes":40000}),
    ]
    out = {"conditions": {}, "summary": {}}
    for name, seconds, overrides in conditions:
        results = []
        for row in rows:
            source = m.parse_equation(row["equation1"])
            target = m.parse_equation(row["equation2"])
            limits = dict(base)
            limits.update({
                "seconds": seconds,
                "maximum_term_size":45,
                "maximum_replay_term_size":160,
                "maximum_depth":10,
                "maximum_rules":192,
                "maximum_rounds":16,
                "new_clauses_per_round":128,
                "maximum_clauses":2000,
                "normalization_steps":96,
                "maximum_proof_nodes":20000,
            })
            limits.update(overrides)
            started = time.monotonic()
            engine = m.TargetGroundedRefutation(source, target, time.monotonic()+seconds, limits)
            found = engine.solve()
            elapsed = time.monotonic()-started
            proof_nodes = None
            replay_ok = False
            if found is not None:
                nodes, root = found
                proof_nodes = len(m.proof_node_ids(nodes, root))
                replay_ok = m.replay_dag(source, nodes, root, maximum_term_size=limits["maximum_replay_term_size"], maximum_nodes=limits["maximum_proof_nodes"]) and (nodes[root].lhs, nodes[root].rhs) == target[:2]
            rec = {
                "id": row["id"], "found": bool(found), "replay_ok": bool(replay_ok),
                "elapsed": round(elapsed,6), "clauses": len(engine.search.clauses),
                "rounds": engine.search.rounds, "superpositions": engine.search.superpositions,
                "reductions": engine.search.reductions, "proof_nodes": proof_nodes,
                "generated": engine.search.generated, "max_recipe_cost": engine.search.maximum_recipe_cost,
            }
            print(name, json.dumps(rec, sort_keys=True), flush=True)
            results.append(rec)
        out["conditions"][name] = results
        hits = [r["id"] for r in results if r["found"] and r["replay_ok"]]
        out["summary"][name] = {"count": len(hits), "hits": hits}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True))
    print(json.dumps(out["summary"], indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
