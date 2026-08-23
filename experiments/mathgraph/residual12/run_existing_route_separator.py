#!/usr/bin/env python3
"""Run the frozen existing given-clause route on the 12 unlabelled residuals."""

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = Path(__file__).with_name("released_residuals_unlabelled.json")
EXPECTED_COLUMNS = {
    "id", "index", "difficulty", "eq1_id", "eq2_id",
    "equation1", "equation2",
}


def load_solver(path):
    spec = importlib.util.spec_from_file_location(
        "mathgraph_residual12_frozen_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def size(term):
    if term[0] == "var":
        return 1
    return 1 + size(term[1]) + size(term[2])


def depth(term):
    if term[0] == "var":
        return 0
    return 1 + max(depth(term[1]), depth(term[2]))


def limits_for(solver, seconds):
    limits = dict(solver.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds": seconds,
        "maximum_term_size": 65,
        "maximum_replay_term_size": 260,
        "maximum_depth": 12,
        "maximum_rules": 768,
        "maximum_rounds": 64,
        "new_clauses_per_round": 512,
        "maximum_clauses": 12000,
        "normalization_steps": 256,
        "maximum_proof_nodes": 50000,
    })
    return limits


def run_one(solver, row, seconds):
    source = solver.parse_equation(row["equation1"])
    target = solver.parse_equation(row["equation2"])
    limits = limits_for(solver, seconds)
    started = time.monotonic()
    engine = solver.TargetGroundedRefutation(
        source, target, started + seconds, limits
    )
    error = None
    try:
        found = engine.solve_given_clause(
            maximum_given=512,
            focus_per_age=4,
        )
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError,
        ValueError,
    ) as exc:
        found = None
        error = type(exc).__name__
    elapsed = time.monotonic() - started
    result = {
        "seconds_budget": seconds,
        "elapsed_seconds": round(elapsed, 6),
        "found": found is not None,
        "error": error,
        "clauses": len(engine.search.clauses),
        "rounds": engine.search.rounds,
        "superpositions": engine.search.superpositions,
        "exhaustion": getattr(engine.search, "exhaustion", None),
        "root_matches": False,
        "replayed": False,
        "proof_nodes": 0,
        "certificate_bytes": 0,
        "certificate_sha256": None,
        "bare_untyped_rfl": 0,
    }
    if found is None:
        return result
    nodes, root = found
    result["root_matches"] = (
        (nodes[root].lhs, nodes[root].rhs) == target[:2]
    )
    result["replayed"] = solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )
    code, proof_nodes = solver.make_dag_certificate(target, nodes, root)
    if len(code.encode("utf-8")) > solver.EqualitySearch.MAX_CERTIFICATE_BYTES:
        code = solver.compact_lean_have_bindings(code)
    encoded = code.encode("utf-8")
    result["proof_nodes"] = proof_nodes
    result["certificate_bytes"] = len(encoded)
    result["certificate_sha256"] = hashlib.sha256(encoded).hexdigest()
    result["bare_untyped_rfl"] = sum(
        1 for line in code.splitlines()
        if line.lstrip().startswith("have ")
        and line.rstrip().endswith(" := rfl")
        and " : " not in line
    )
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--budgets", default="30,60")
    args = parser.parse_args()
    rows = json.loads(args.input.read_text(encoding="utf-8"))
    if (
        not isinstance(rows, list)
        or len(rows) != 12
        or any(set(row) != EXPECTED_COLUMNS for row in rows)
    ):
        raise SystemExit("unexpected unlabelled residual schema")
    budgets = tuple(int(value) for value in args.budgets.split(","))
    if not budgets or any(value <= 0 or value > 60 for value in budgets):
        raise SystemExit("budgets must be in 1..60")
    solver = load_solver(args.solver)
    output_rows = []
    started = time.monotonic()
    for row in rows:
        source = solver.parse_equation(row["equation1"])
        target = solver.parse_equation(row["equation2"])
        record = {
            "id": row["id"],
            "difficulty": row["difficulty"],
            "structure": {
                "source_variables": len(source[2]),
                "target_variables": len(target[2]),
                "source_lhs_size": size(source[0]),
                "source_rhs_size": size(source[1]),
                "target_lhs_size": size(target[0]),
                "target_rhs_size": size(target[1]),
                "source_lhs_depth": depth(source[0]),
                "source_rhs_depth": depth(source[1]),
                "target_lhs_depth": depth(target[0]),
                "target_rhs_depth": depth(target[1]),
            },
            "attempts": [],
        }
        for seconds in budgets:
            attempt = run_one(solver, row, seconds)
            record["attempts"].append(attempt)
            print(json.dumps({"id": row["id"], **attempt}), flush=True)
            if (
                attempt["found"]
                and attempt["root_matches"]
                and attempt["replayed"]
                and attempt["certificate_bytes"] <= 100000
                and attempt["bare_untyped_rfl"] == 0
            ):
                break
        output_rows.append(record)
    output = {
        "schema": "mathgraph.verified-residual-12-existing-route.v1",
        "solver_sha256": hashlib.sha256(args.solver.read_bytes()).hexdigest(),
        "input_sha256": hashlib.sha256(args.input.read_bytes()).hexdigest(),
        "budgets_seconds": list(budgets),
        "label_fields_available_to_runner": [],
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "rows": output_rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "rows": len(output_rows),
        "internal_successes": sum(
            any(a["found"] and a["root_matches"] and a["replayed"]
                and a["certificate_bytes"] <= 100000
                and a["bare_untyped_rfl"] == 0
                for a in row["attempts"])
            for row in output_rows
        ),
        "elapsed_seconds": output["elapsed_seconds"],
    }), flush=True)


if __name__ == "__main__":
    main()
