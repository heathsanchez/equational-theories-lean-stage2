#!/usr/bin/env python3
"""Run the frozen compact route on a label-blind independent-family audit."""

import argparse
import hashlib
import json
from pathlib import Path

from run_closure_hit_attack import load_solver, run_once


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = Path(__file__).with_name("independent_family_audit_inputs.json")
EXPECTED_SOLVER_SHA256 = "a92eae8cce4fdf7c787c3218fa4f7eb1158c92a6b57f2920199ddbe6e7726a08"
EXPECTED_INPUT_SHA256 = "075f7a3b8d0dd389c2d2a12d444af435eb921f622954185cb3d0f867d7cdb503"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if digest(args.solver) != EXPECTED_SOLVER_SHA256:
        raise SystemExit("solver hash differs from frozen transfer audit")
    if digest(args.input) != EXPECTED_INPUT_SHA256:
        raise SystemExit("input hash differs from frozen transfer audit")
    payload = json.loads(args.input.read_text(encoding="utf-8"))
    rows = payload["rows"]
    assert len(rows) == 156
    assert all("answer" not in row and "label" not in row for row in rows)
    solver = load_solver(args.solver)
    output = []
    for index, row in enumerate(rows):
        source = solver.parse_equation(row["equation1"])
        target = solver.parse_equation(row["equation2"])
        attempts = {}
        for seconds in (3.0, 5.0):
            attempts[str(int(seconds))] = run_once(
                solver, source, target, seconds,
                f"{row['id']}_compact_{int(seconds)}_{index}",
            )
        output.append({
            "id": row["id"],
            "content_sha256": row["content_sha256"],
            "source_family": row["source_family"],
            "source_law_id": row.get("eq1_id"),
            "attempts": attempts,
        })
    result = {
        "schema": "mathgraph.residual12-independent-family-raw-results.v1",
        "solver_sha256": EXPECTED_SOLVER_SHA256,
        "inputs_sha256": EXPECTED_INPUT_SHA256,
        "label_fields_available_to_runner": [],
        "rows": output,
    }
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "rows": len(output),
        "attempts": 2 * len(output),
        "internal_hits": sum(
            attempt["found"] for row in output
            for attempt in row["attempts"].values()
        ),
        "lean_acceptances": sum(
            attempt.get("judge_status") == "accepted" for row in output
            for attempt in row["attempts"].values()
        ),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
