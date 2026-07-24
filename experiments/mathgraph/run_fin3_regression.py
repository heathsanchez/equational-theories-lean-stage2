#!/usr/bin/env python3
"""Official Fin 3 proxy suite plus independent semantic/replay audits."""

import argparse
import importlib.util
import json
import subprocess
import sys
import tempfile
import time
from itertools import product
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
CASES = ROOT / "experiments" / "mathgraph" / "regressions" / "fin3_cases.json"
SOLVER_DIR = ROOT / "submissions" / "mathgraph"
SOLVER_FILE = SOLVER_DIR / "solver.py"
FIN3_FALSE_CASES = {
    "fin3_no_fin2_countermodel",
    "fin3_requires_three_elements",
    "fin3_noncommutative_model",
    "fin3_nonassociative_model",
    "fin3_no_idempotent_diagonal",
    "fin3_target_witness_one_element",
    "fin3_target_witness_two_elements",
    "fin3_target_witness_three_elements",
    "fin3_source_one_variable",
    "fin3_source_several_variables",
    "fin3_complete_prefix_after_deadline",
    "fin3_corrupted_replay_control",
}
TRUE_CASES = {"fin3_true_control_one", "fin3_true_control_several"}


def load_solver():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("mathgraph_fin3_solver", SOLVER_FILE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def metrics(row):
    records = []
    for event in row.get("log", []):
        if event.get("type") != "solver_stderr":
            continue
        for line in event.get("tail", "").splitlines():
            prefix = "MATHGRAPH_METRICS "
            if line.startswith(prefix):
                records.append(json.loads(line[len(prefix):]))
    return records


def direct_search(solver, problem, configuration):
    source = solver.parse_equation(problem["equation1"])
    target = solver.parse_equation(problem["equation2"])
    search = solver.Fin3Search(
        source,
        target,
        time.monotonic() + configuration["seconds"],
        configuration["maximum_states"],
        configuration["maximum_models"],
    )
    if configuration["kind"] == "target-guided":
        found = search.search_target_guided()
    elif configuration["kind"] == "partial-source":
        found = search.search_partial_source_models()
    else:
        found = search.search_complete_enumeration()
    return source, target, search, found


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    problems = json.loads(CASES.read_text(encoding="utf-8"))
    by_problem = {problem["id"]: problem for problem in problems}

    with tempfile.TemporaryDirectory(prefix="mathgraph-fin3-") as tmp:
        output = Path(tmp) / "results.json"
        subprocess.run(
            [
                sys.executable,
                "-m",
                "pipeline.runner",
                "--submission",
                str(SOLVER_DIR),
                "--problems",
                str(CASES),
                "--output",
                str(output),
            ],
            cwd=ROOT,
            check=True,
        )
        rows = json.loads(output.read_text(encoding="utf-8"))
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(output.read_bytes())

    by_id = {row["id"]: row for row in rows}
    assert len(by_id) == len(problems) == 16
    old = by_id["fin3_old_fin2_route"]
    assert old.get("solved") and old.get("verdict") == "false"
    assert not any(
        item["portfolio"].startswith("fin3-") for item in metrics(old)
    )
    for problem_id in FIN3_FALSE_CASES:
        row = by_id[problem_id]
        assert row.get("solved") and row.get("verdict") == "false", problem_id
        assert row.get("judge_calls") == 1 and row.get("llm_calls") == 0
        assert any(
            item["portfolio"] == "fin3-fast" and item["found"]
            for item in metrics(row)
        ), problem_id
    for problem_id in TRUE_CASES:
        row = by_id[problem_id]
        assert row.get("solved") and row.get("verdict") == "true", problem_id
        assert row.get("judge_calls") == 1 and row.get("llm_calls") == 0
    growth = by_id["fin3_growth_pathological_abstain"]
    assert not growth.get("solved") and growth.get("judge_calls") == 0
    rejected = [
        (row["id"], event.get("response", {}).get("status"))
        for row in rows
        for event in row.get("log", [])
        if event.get("type") == "judge"
        and event.get("response", {}).get("status") != "accepted"
    ]
    assert not rejected, rejected

    solver = load_solver()
    fast = solver.FIN3_PORTFOLIO[0]
    audited = {}
    for problem_id in sorted(FIN3_FALSE_CASES):
        source, target, search, found = direct_search(
            solver, by_problem[problem_id], fast
        )
        assert found is not None, problem_id
        table, witness = found
        serialized = solver.serialize_flat_table(table, 3)
        assert solver.replay_countermodel(
            source, target, table, 3, witness, serialized
        )
        assert solver.find_fin2_countermodel(
            source, target, time.monotonic() + 0.2
        ) is None
        audited[problem_id] = (source, target, search, table, witness)

    table = audited["fin3_noncommutative_model"][3]
    assert any(
        table[3 * left + right] != table[3 * right + left]
        for left in range(3) for right in range(3)
    )
    source, target, _, table, witness = audited["fin3_nonassociative_model"]
    assert solver.replay_countermodel(
        source, target, table, 3, witness,
        solver.serialize_flat_table(table, 3),
    )
    table = audited["fin3_no_idempotent_diagonal"][3]
    assert all(table[3 * value + value] != value for value in range(3))
    assert len(set(audited["fin3_target_witness_one_element"][4])) == 1
    assert len(set(audited["fin3_target_witness_two_elements"][4])) == 2

    source, target, _, table, _ = audited[
        "fin3_target_witness_three_elements"
    ]
    all_three = next(
        assignment
        for assignment in product(range(3), repeat=len(target[2]))
        if len(set(assignment)) == 3
        and solver.evaluate_compiled(
            solver.compile_equation(target), assignment, table
        )[0]
        != solver.evaluate_compiled(
            solver.compile_equation(target), assignment, table
        )[1]
    )
    assert solver.replay_countermodel(
        source, target, table, 3, all_three,
        solver.serialize_flat_table(table, 3),
    )

    reference = by_problem["fin3_no_fin2_countermodel"]
    for configuration in solver.FIN3_PORTFOLIO[1:]:
        source, target, search, found = direct_search(
            solver, reference, configuration
        )
        assert found is not None, configuration["name"]
        table, witness = found
        assert solver.replay_countermodel(
            source, target, table, 3, witness,
            solver.serialize_flat_table(table, 3),
        )

    source, target, search, table, witness = audited[
        "fin3_complete_prefix_after_deadline"
    ]
    search.deadline = time.monotonic() - 1.0
    assert solver.replay_countermodel(
        source, target, table, 3, witness,
        solver.serialize_flat_table(table, 3),
    )

    source, target, _, table, witness = audited[
        "fin3_corrupted_replay_control"
    ]
    corrupted = list(table)
    corrupted[0] = (corrupted[0] + 1) % 3
    assert not solver.replay_countermodel(
        source, target, corrupted, 3, witness,
        solver.serialize_flat_table(table, 3),
    )
    assert not solver.replay_countermodel(
        source, target, table, 3, witness,
        solver.serialize_flat_table(table, 3) + " ",
    )

    complete_config = solver.FIN3_PORTFOLIO[2]
    true_control = by_problem["fin3_true_control_one"]
    source, target, complete, found = direct_search(
        solver, true_control, complete_config
    )
    assert found is None and complete.complete
    assert complete.complete_tables == 3330
    assert complete.symmetry_duplicates == 16353

    largest_certificate = max(
        len((row.get("code") or "").encode("utf-8")) for row in rows
    )
    print(
        "Fin 3 regression: 13 accepted FALSE, 2 accepted TRUE, "
        "1 bounded abstention, zero rejected judge calls; "
        f"largest certificate {largest_certificate} bytes"
    )


if __name__ == "__main__":
    main()
