#!/usr/bin/env python3
"""Official contextual-overlap proxy suite and independent provenance audits."""

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
CASES = (
    ROOT / "experiments" / "mathgraph" / "regressions"
    / "contextual_overlap_cases.json"
)
SOLVER_DIR = ROOT / "submissions" / "mathgraph"
SOLVER_FILE = SOLVER_DIR / "solver.py"
OVERLAP_CASES = {
    "overlap_source_lhs_left_child",
    "overlap_source_lhs_right_child",
    "overlap_source_rhs",
    "overlap_reversed_inner",
    "overlap_reversed_outer",
    "overlap_nested_context",
    "overlap_self_different_substitutions",
    "critical_pair_trans_after_congruence",
    "contextual_complete_prefix_before_timeout",
}
NARROWING_CASES = {
    "target_side_narrowing",
    "bidirectional_narrowing_meet",
    "narrowing_expand_then_contract",
}
FALSE_CASES = {
    "contextual_false_control_commutativity",
    "contextual_false_control_associativity",
    "variable_position_overlap_suppressed",
}


def load_solver():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("mathgraph_solver", SOLVER_FILE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def officially_verify(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    answer = json.dumps({"verdict": "true", "code": code})
    result = verify_answer(_to_judge_problem(problem), answer)
    assert result["status"] == "accepted", (problem["id"], result)


def direct_constructor_audit(problem, kind, expire_after=False):
    solver = load_solver()
    source = solver.parse_equation(problem["equation1"])
    target = solver.parse_equation(problem["equation2"])
    configuration = (
        solver.CONTEXTUAL_PORTFOLIO[0]
        if kind == "target-narrowing"
        else solver.CONTEXTUAL_PORTFOLIO[2]
    )
    search = solver.ContextualSearch(
        source,
        target,
        time.monotonic() + configuration["seconds"],
        configuration["limits"],
    )
    if kind == "target-narrowing":
        found = search.solve_target_narrowing(
            configuration["maximum_depth"],
            configuration["branching"],
            configuration["maximum_terms"],
            configuration["maximum_context_depth"],
        )
    else:
        found = search.solve_contextual_overlap(
            configuration["maximum_overlap_depth"],
            configuration["maximum_context_depth"],
            configuration["maximum_source_instances"],
            configuration["maximum_candidates"],
            configuration["maximum_new_nodes"],
        )
    assert found is not None, problem["id"]
    nodes, root = found
    if expire_after:
        search.deadline = time.monotonic() - 1.0
        root = search.shortest_path()
        assert root is not None, "complete prefix was discarded at deadline"
    used = solver.proof_node_ids(nodes, root)
    assert any(nodes[node_id].constructor == kind for node_id in used)
    assert solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=configuration["limits"]["max_term_size"],
        maximum_nodes=configuration["limits"]["max_derivation_nodes"],
    )
    code, _ = solver.make_dag_certificate(target, nodes, root)
    assert len(code.encode("utf-8")) <= solver.EqualitySearch.MAX_CERTIFICATE_BYTES
    officially_verify(problem, code)
    return search, nodes, used, len(code.encode("utf-8"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    problems = json.loads(CASES.read_text(encoding="utf-8"))
    by_problem = {problem["id"]: problem for problem in problems}

    with tempfile.TemporaryDirectory(prefix="mathgraph-contextual-") as tmp:
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
    positives = OVERLAP_CASES | NARROWING_CASES
    for problem_id in positives:
        row = by_id[problem_id]
        assert row.get("solved") and row.get("verdict") == "true", problem_id
        assert row.get("judge_calls") == 1 and row.get("llm_calls") == 0
    for problem_id in FALSE_CASES:
        row = by_id[problem_id]
        assert row.get("solved") and row.get("verdict") == "false", problem_id
        assert row.get("judge_calls") == 1 and row.get("llm_calls") == 0
    growth = by_id["contextual_growth_pathological_abstain"]
    assert not growth.get("solved") and growth.get("judge_calls") == 0
    rejected = [
        (row["id"], event.get("response", {}).get("status"))
        for row in rows
        for event in row.get("log", [])
        if event.get("type") == "judge"
        and event.get("response", {}).get("status") != "accepted"
    ]
    assert not rejected, rejected

    audits = {}
    for problem_id in sorted(OVERLAP_CASES):
        audits[problem_id] = direct_constructor_audit(
            by_problem[problem_id],
            "contextual-overlap",
            expire_after=problem_id == "contextual_complete_prefix_before_timeout",
        )
    for problem_id in sorted(NARROWING_CASES):
        audits[problem_id] = direct_constructor_audit(
            by_problem[problem_id], "target-narrowing"
        )

    left = audits["overlap_source_lhs_left_child"][0]
    right = audits["overlap_source_lhs_right_child"][0]
    rhs = audits["overlap_source_rhs"][0]
    reversed_inner = audits["overlap_reversed_inner"][0]
    reversed_outer = audits["overlap_reversed_outer"][0]
    nested = audits["overlap_nested_context"][1]
    self_nodes = audits["overlap_self_different_substitutions"][1]
    critical = audits["critical_pair_trans_after_congruence"][1]
    assert any(
        node.overlap_record and node.overlap_record[4][0] == "L"
        for node in left.nodes
    )
    assert any(
        node.overlap_record and node.overlap_record[4][0] == "R"
        for node in right.nodes
    )
    assert any(
        node.overlap_record and node.overlap_record[2] == 1
        for node in rhs.nodes
    )
    assert any(
        node.overlap_record and node.overlap_record[3] == 1
        for node in reversed_inner.nodes
    )
    assert any(
        node.overlap_record and node.overlap_record[2] == 0
        for node in reversed_outer.nodes
    )
    assert any(
        node.context_record and len(node.context_record[1]) >= 2
        for node in nested
    )
    assert any(
        node.overlap_record
        and self_nodes[node.overlap_record[0]].substitution
        != self_nodes[node.overlap_record[1]].substitution
        for node in self_nodes
    )
    assert any(
        node.overlap_record and node.kind == "transitivity"
        for node in critical
    )

    solver = load_solver()
    variable = by_problem["variable_position_overlap_suppressed"]
    source = solver.parse_equation(variable["equation1"])
    target = solver.parse_equation(variable["equation2"])
    config = solver.CONTEXTUAL_PORTFOLIO[1]
    search = solver.ContextualSearch(
        source, target, time.monotonic() + 1.0, config["limits"]
    )
    search.solve_contextual_overlap(
        config["maximum_overlap_depth"],
        config["maximum_context_depth"],
        config["maximum_source_instances"],
        config["maximum_candidates"],
        config["maximum_new_nodes"],
    )
    assert search.variable_overlap_suppressed > 0

    largest_dag = max(len(item[2]) for item in audits.values())
    largest_certificate = max(item[3] for item in audits.values())
    print(
        "contextual regression: 12 accepted TRUE, 3 accepted FALSE, "
        "1 bounded abstention, zero rejected judge calls; "
        f"largest proof DAG {largest_dag}, certificate {largest_certificate} bytes"
    )


if __name__ == "__main__":
    main()
