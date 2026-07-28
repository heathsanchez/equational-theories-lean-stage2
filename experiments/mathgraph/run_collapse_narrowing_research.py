#!/usr/bin/env python3
"""Diagnostic bounded narrowing on the current recursive-collapse residuals."""

import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("mathgraph_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def current_residuals():
    rows = json.loads((ROOT / "examples/problems/sample_200.json").read_text())
    accepted = set(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "normalization_baseline_manifest.json").read_text()
        )["sample_200_accepted"]
    )
    accepted.update(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "quotient_matcher_promotion_summary.json").read_text()
        )["public_hits"]
    )
    accepted.update(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "variable_omission_collapse_summary.json").read_text()
        )["sample_200"]["new_hits"]
    )
    return [
        row for row in rows
        if row["id"].startswith("true_") and row["id"] not in accepted
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=10.0)
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--branching", type=int, default=256)
    parser.add_argument("--terms", type=int, default=4096)
    parser.add_argument("--context-depth", type=int, default=8)
    parser.add_argument("--term-size", type=int, default=21)
    parser.add_argument("--id")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    module = load_solver()
    output = []
    rows = [r for r in current_residuals() if not args.id or r["id"] == args.id]
    for index, row in enumerate(rows, 1):
        print(f"[{index}/{len(rows)}] {row['id']}", flush=True)
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        started = time.monotonic()
        limits = {
            "max_term_size": max(
                args.term_size, module.term_size(target[0]) + 10,
                module.term_size(target[1]) + 10,
            ),
            "max_derivation_nodes": 12000,
            "max_graph_edges": 10000,
            "max_source_edges": 10000,
            "max_source_attempts": 100000,
            "max_congruence_rounds": 0,
        }
        search = module.ContextualSearch(
            source, target, started + args.seconds, limits
        )
        found = search.solve_target_narrowing(
            args.depth, args.branching, args.terms, args.context_depth
        )
        record = {
            "id": row["id"],
            "found": found is not None,
            "seconds": round(time.monotonic() - started, 6),
            "successors": search.narrowing_successors,
            "term_size_rejections": search.term_size_rejections,
        }
        if found:
            nodes, root = found
            replay = module.replay_dag(
                source, nodes, root, maximum_term_size=limits["max_term_size"]
            )
            code, proof_nodes = module.make_dag_certificate(target, nodes, root)
            record.update(
                replay=replay,
                proof_nodes=proof_nodes,
                certificate_bytes=len(code.encode()),
                code=code,
            )
        output.append(record)
        print(json.dumps({k: v for k, v in record.items() if k != "code"}))
    if args.output:
        args.output.write_text(json.dumps({"diagnostic_only": True, "rows": output}, indent=2))


if __name__ == "__main__":
    main()
