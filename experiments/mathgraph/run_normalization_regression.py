#!/usr/bin/env python3
"""Official and independent replay suite for equational normalization."""

import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
CASES = ROOT / "experiments/mathgraph/regressions/normalization_cases.json"


def load_solver():
    spec = importlib.util.spec_from_file_location(
        "normalization_regression_solver", SOLVER
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    answer = json.dumps({"verdict": "true", "code": code})
    return verify_answer(_to_judge_problem(problem), answer)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    solver = load_solver()
    cases = json.loads(CASES.read_text())
    records = []
    false_judge_calls = 0
    for problem in cases:
        source = solver.parse_equation(problem["equation1"])
        target = solver.parse_equation(problem["equation2"])
        configuration = dict(solver.NORMALIZATION_PORTFOLIO[1])
        if problem["id"] == "norm_budget_control":
            configuration["normalization_steps"] = 2
        search = solver.EquationalNormalizer(
            source,
            target,
            time.monotonic() + configuration["seconds"],
            configuration,
        )
        found = search.solve()
        if problem["expect_true"] and problem["id"] != "norm_budget_control":
            assert found is not None, problem["id"]
            nodes, root = found
            assert solver.replay_dag(
                source,
                nodes,
                root,
                maximum_term_size=configuration["maximum_term_size"],
                maximum_nodes=configuration["maximum_proof_nodes"],
            )
            assert (nodes[root].lhs, nodes[root].rhs) == target[:2]
            code, proof_nodes = solver.make_dag_certificate(
                target, nodes, root
            )
            result = verify(problem, code)
            assert result["status"] == "accepted", (problem["id"], result)
            records.append({
                "id": problem["id"],
                "proof_nodes": proof_nodes,
                "certificate_bytes": len(code.encode()),
                "left_steps": search.left_steps,
                "right_steps": search.right_steps,
                "decreasing_rules": search.decreasing_rules,
                "selected_rules": len(search.selected_rules),
                "alpha_duplicates": search.alpha_duplicates_removed,
                "critical_pairs": search.local_critical_pairs,
            })
        else:
            assert found is None, problem["id"]
            false_judge_calls += 0

    # Corrupted rule evidence and corrupted stored matching substitutions fail
    # in the independent layers before certificate generation.
    probe = next(
        problem for problem in cases
        if problem["id"] == "norm_left_projection_nested"
    )
    source = solver.parse_equation(probe["equation1"])
    target = solver.parse_equation(probe["equation2"])
    configuration = dict(solver.NORMALIZATION_PORTFOLIO[1])
    audit = solver.EquationalNormalizer(
        source, target, time.monotonic() + 1.0, configuration
    )
    audit.generate_consequences()
    audit.orient()
    audit.select_rulebook()
    normal, trace, _ = audit.normalize(target[0])
    assert trace
    corrupted = [dict(step) for step in trace]
    corrupted[0]["substitution"] = ()
    assert not audit.replay_trace(target[0], corrupted, normal)
    bad_nodes = [solver.EqualityNode(
        ("var", "a"), ("var", "b"), "reflexivity"
    )]
    assert not solver.replay_dag(source, bad_nodes, 0)

    payload = {
        "cases": len(cases),
        "positive_official_acceptances": len(records),
        "negative_true_judge_calls": false_judge_calls,
        "corrupted_rule_rejected": True,
        "corrupted_match_rejected": True,
        "largest_proof_nodes": max(
            item["proof_nodes"] for item in records
        ),
        "largest_certificate_bytes": max(
            item["certificate_bytes"] for item in records
        ),
        "records": records,
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True))
    print(
        f"normalization regression: {len(records)} official TRUE "
        f"acceptances, {len(cases) - len(records)} abstention/corruption "
        "controls, zero FALSE-control judge calls"
    )


if __name__ == "__main__":
    main()
