#!/usr/bin/env python3
"""Official source-reentry proxy/judge regression and partial-prefix audit."""

import argparse
import importlib.util
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
CASES = ROOT / "experiments" / "mathgraph" / "regressions" / "source_reentry_cases.json"
SOLVER_DIR = ROOT / "submissions" / "mathgraph"
SOLVER_FILE = SOLVER_DIR / "solver.py"
TRUE_GENERATIONS = {
    "reentry_one_generation": 1,
    "reentry_two_generations": 2,
    "reentry_after_congruence": 1,
    "reentry_reversed_source_orientation": 1,
    "reentry_convergent_intermediate": 1,
    "reentry_collapse_law": 1,
    "reentry_projection_absorption": 1,
    "reentry_complete_prefix_before_timeout": 1,
}
FALSE_CASES = {
    "reentry_false_control_one",
    "reentry_false_control_two",
}


def metrics(row):
    found = []
    for event in row.get("log", []):
        if event.get("type") != "solver_stderr":
            continue
        for line in event.get("tail", "").splitlines():
            prefix = "MATHGRAPH_METRICS "
            if line.startswith(prefix):
                found.append(json.loads(line[len(prefix):]))
    return found


def load_solver():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("mathgraph_solver", SOLVER_FILE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def partial_prefix_audit(problem):
    solver = load_solver()
    source = solver.parse_equation(problem["equation1"])
    target = solver.parse_equation(problem["equation2"])
    configuration = solver.REENTRY_PORTFOLIO[1]
    search = solver.EqualitySearch(
        source,
        target,
        time.monotonic() + configuration["seconds"],
        configuration["limits"],
    )
    assert search.solve() is None
    search.max_term_size = configuration["reentry_term_size"]
    search.max_derivation_nodes = configuration["reentry_nodes"]
    search.max_graph_edges = configuration["reentry_edges"]
    found = search.solve_reentry(
        configuration["generations"],
        configuration["new_terms"],
        configuration["instances"],
        configuration["targeted"],
    )
    assert found is not None
    search.deadline = time.monotonic() - 1.0
    expired_root = search.shortest_path()
    assert expired_root is not None, "expired complete prefix was discarded"
    assert solver.replay_dag(source, search.nodes, expired_root)
    code, _ = solver.make_dag_certificate(target, search.nodes, expired_root)

    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    answer = json.dumps({"verdict": "true", "code": code})
    result = verify_answer(_to_judge_problem(problem), answer)
    assert result["status"] == "accepted", result
    return len(code.encode("utf-8"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    problems = json.loads(CASES.read_text(encoding="utf-8"))

    with tempfile.TemporaryDirectory(prefix="mathgraph-source-reentry-") as tmp:
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
    assert len(by_id) == len(problems) == 11
    for problem_id, generation in TRUE_GENERATIONS.items():
        row = by_id[problem_id]
        assert row.get("solved") and row.get("verdict") == "true", problem_id
        marker = f"source-reentry generation {generation}"
        assert marker in row.get("code", ""), (problem_id, marker)
        assert row.get("judge_calls") == 1 and row.get("llm_calls") == 0
    for problem_id in FALSE_CASES:
        row = by_id[problem_id]
        assert row.get("solved") and row.get("verdict") == "false", problem_id
        assert "source-reentry" not in (row.get("code") or "")
        assert row.get("judge_calls") == 1 and row.get("llm_calls") == 0

    growth = by_id["reentry_growth_pathological_abstain"]
    assert not growth.get("solved") and growth.get("judge_calls") == 0
    assert any(
        item["portfolio"] == "initial-chain"
        and item.get("exhaustion") == "timeout"
        for item in metrics(growth)
    )
    rejected = [
        (row["id"], event.get("response", {}).get("status"))
        for row in rows
        for event in row.get("log", [])
        if event.get("type") == "judge"
        and event.get("response", {}).get("status") != "accepted"
    ]
    assert not rejected, rejected

    prefix_problem = next(
        problem
        for problem in problems
        if problem["id"] == "reentry_complete_prefix_before_timeout"
    )
    prefix_bytes = partial_prefix_audit(prefix_problem)
    print(
        "source-reentry regression: 8 accepted TRUE, 2 accepted FALSE, "
        "1 bounded timeout abstention, zero rejected judge calls; "
        f"expired-prefix certificate {prefix_bytes} bytes accepted"
    )


if __name__ == "__main__":
    main()
