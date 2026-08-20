#!/usr/bin/env python3
"""Label-blind normalization grid on the fixed content-hash development half."""

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
PROBLEMS = ROOT / "examples/problems/sample_200.json"


def load_solver():
    spec = importlib.util.spec_from_file_location(
        "normalization_development_solver", SOLVER
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def digest(row):
    return hashlib.sha256(
        (row["equation1"].strip() + "\0" + row["equation2"].strip()).encode()
    ).hexdigest()


def verify(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    started = time.monotonic()
    answer = json.dumps({"verdict": "true", "code": code})
    result = verify_answer(_to_judge_problem(problem), answer)
    return result.get("status", "unparsed"), time.monotonic() - started


def run(module, problem, base, ordering, selector):
    configuration = {
        **base,
        "ordering": ordering,
        "selector": selector,
    }
    source = module.parse_equation(problem["equation1"])
    target = module.parse_equation(problem["equation2"])
    started = time.monotonic()
    search = module.EquationalNormalizer(
        source,
        target,
        started + configuration["seconds"],
        configuration,
    )
    found = search.solve()
    row = {
        "configuration": base["name"],
        "ordering": ordering,
        "selector": selector,
        "found": found is not None,
        "engine_seconds": round(time.monotonic() - started, 6),
        "source_instances": search.source_instances_generated,
        "composed_consequences": search.composed_consequences,
        "replayed_candidates": search.replayed_candidates,
        "replay_failures": search.replay_failures,
        "decreasing_rules": search.decreasing_rules,
        "nonorientable": search.nonorientable_equalities,
        "alpha_duplicates": search.alpha_duplicates_removed,
        "selected_rules": len(search.selected_rules),
        "critical_pairs": search.local_critical_pairs,
        "joined_critical_pairs": search.joined_critical_pairs,
        "unresolved_critical_pairs": search.unresolved_critical_pairs,
        "left_steps": search.left_steps,
        "right_steps": search.right_steps,
        "distinct_normal_forms": search.distinct_normal_forms,
        "normalization_budget_exits": search.normalization_budget_exits,
        "consequence_budget_exits": search.consequence_budget_exits,
        "exhaustion": search.exhaustion,
    }
    if found is not None:
        nodes, root = found
        replay_started = time.monotonic()
        row["replay_ok"] = module.replay_dag(
            source,
            nodes,
            root,
            maximum_term_size=configuration["maximum_term_size"],
            maximum_nodes=configuration["maximum_proof_nodes"],
        )
        row["replay_seconds"] = round(
            time.monotonic() - replay_started, 6
        )
        code, proof_nodes = module.make_dag_certificate(
            target, nodes, root
        )
        row["proof_nodes"] = proof_nodes
        row["certificate_bytes"] = len(code.encode())
        status, judge_seconds = verify(problem, code)
        row["judge_status"] = status
        row["judge_seconds"] = round(judge_seconds, 6)
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--combination", choices=(
        "size-coverage", "size-reduction",
        "depth-coverage", "depth-reduction",
    ))
    parser.add_argument(
        "--scope", choices=("development", "holdout", "sample200"),
        default="development",
    )
    args = parser.parse_args()
    module = load_solver()
    problems = json.loads(PROBLEMS.read_text())
    ordered = sorted(
        problems, key=lambda row: (digest(row), row["equation1"],
                                   row["equation2"])
    )
    development = {
        "development": ordered[:100],
        "holdout": ordered[100:],
        "sample200": problems,
    }[args.scope]
    baseline = {
        row["id"]: row
        for row in json.loads(args.baseline.read_text())
    }
    unresolved = [
        row for row in development if not baseline[row["id"]].get("solved")
    ]
    rows = []
    combinations = [
        (ordering, selector)
        for ordering in ("size", "depth")
        for selector in ("coverage", "reduction")
    ]
    if args.combination:
        combinations = [tuple(args.combination.split("-", 1))]
    for index, problem in enumerate(unresolved, 1):
        print(f"[{index}/{len(unresolved)}] {problem['id']}", flush=True)
        portfolios = {}
        for ordering, selector in combinations:
            attempts = []
            for configuration in module.NORMALIZATION_PORTFOLIO[:3]:
                attempt = run(
                    module, problem, configuration, ordering, selector
                )
                attempts.append(attempt)
                if attempt["found"]:
                    break
            portfolios[ordering + "-" + selector] = attempts
        rows.append({
            "id": problem["id"],
            "content_sha256": digest(problem),
            "portfolios": portfolios,
        })
    args.output.write_text(json.dumps({
        "solver_sha256": hashlib.sha256(SOLVER.read_bytes()).hexdigest(),
        "baseline_sha256": hashlib.sha256(
            args.baseline.read_bytes()
        ).hexdigest(),
        "development_unresolved": len(unresolved),
        "rows": rows,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
