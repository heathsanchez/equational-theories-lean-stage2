#!/usr/bin/env python3
"""Push the three expanding grounded frontiers to the full 120-second bound."""

import argparse
import hashlib
import json
import time
from pathlib import Path

from run_closure_hit_attack import officially_verify
from run_existing_route_separator import limits_for, load_solver


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = Path(__file__).with_name("released_residuals_unlabelled.json")
EXPECTED_SOLVER_SHA256 = "652fba6799e9066368f135319023865a4a58399f7a7228f20b31ea59bdc8f39c"
EXPECTED_INPUT_SHA256 = "6039b4deac53bf290389180c7b688448311e5fde3fd78e083b56147a7eeb6b24"
SELECTED_IDS = (
    "evaluation_normal_0036",
    "evaluation_order5_0006",
    "evaluation_order5_0042",
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
        found = engine.solve_given_clause(maximum_given=512, focus_per_age=4)
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError
    ) as exc:
        found = None
        error = type(exc).__name__
    record = {
        "seconds_budget": seconds,
        "elapsed_seconds": round(time.monotonic() - started, 6),
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
        "judge_status": None,
    }
    if found is None:
        return record
    nodes, root = found
    record["root_matches"] = (nodes[root].lhs, nodes[root].rhs) == target[:2]
    record["replayed"] = solver.replay_dag(
        source, nodes, root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )
    code, proof_nodes = solver.make_dag_certificate(target, nodes, root)
    if len(code.encode("utf-8")) > solver.EqualitySearch.MAX_CERTIFICATE_BYTES:
        code = solver.compact_lean_have_bindings(code)
    encoded = code.encode("utf-8")
    record["proof_nodes"] = proof_nodes
    record["certificate_bytes"] = len(encoded)
    record["certificate_sha256"] = hashlib.sha256(encoded).hexdigest()
    record["bare_untyped_rfl"] = sum(
        1 for line in code.splitlines()
        if line.lstrip().startswith("have ")
        and line.rstrip().endswith(" := rfl")
        and " : " not in line
    )
    if (
        record["root_matches"] and record["replayed"]
        and record["certificate_bytes"] <= 100000
        and record["bare_untyped_rfl"] == 0
    ):
        record["judge_status"] = officially_verify(row, code)
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if digest(args.solver) != EXPECTED_SOLVER_SHA256:
        raise SystemExit("solver hash differs from frozen separator")
    if digest(args.input) != EXPECTED_INPUT_SHA256:
        raise SystemExit("input hash differs from frozen separator")
    payload = json.loads(args.input.read_text(encoding="utf-8"))
    assert all("answer" not in row and "label" not in row for row in payload)
    by_id = {row["id"]: row for row in payload}
    if not set(SELECTED_IDS) <= set(by_id):
        raise SystemExit("selected expanding rows are absent")
    solver = load_solver(args.solver)
    output_rows = []
    started = time.monotonic()
    for problem_id in SELECTED_IDS:
        row = by_id[problem_id]
        attempts = []
        for seconds in (60, 120):
            attempt = run_one(solver, row, seconds)
            attempts.append(attempt)
            print(json.dumps({"id": problem_id, **attempt}), flush=True)
            if attempt.get("judge_status") == "accepted":
                break
        output_rows.append({"id": problem_id, "attempts": attempts})
    result = {
        "schema": "mathgraph.residual12-expanding-three-120-results.v1",
        "solver_sha256": EXPECTED_SOLVER_SHA256,
        "input_sha256": EXPECTED_INPUT_SHA256,
        "label_fields_available_to_runner": [],
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "rows": output_rows,
    }
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    invalid = [
        row["id"] for row in output_rows for attempt in row["attempts"]
        if attempt["found"] and not (
            attempt["root_matches"] and attempt["replayed"]
            and attempt["certificate_bytes"] <= 100000
            and attempt["bare_untyped_rfl"] == 0
            and attempt["judge_status"] == "accepted"
        )
    ]
    print(json.dumps({
        "rows": len(output_rows),
        "official_hits": sum(
            any(a.get("judge_status") == "accepted" for a in row["attempts"])
            for row in output_rows
        ),
        "invalid_internal_hits": invalid,
        "elapsed_seconds": result["elapsed_seconds"],
    }, sort_keys=True), flush=True)
    if invalid:
        raise SystemExit("internal hit failed the frozen verifier boundary")


if __name__ == "__main__":
    main()
