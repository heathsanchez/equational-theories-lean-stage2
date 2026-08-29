#!/usr/bin/env python3
"""Run isolated label-blind Fin-4 portfolios on the frozen content split."""

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
BASELINE = ROOT / "experiments/mathgraph/results/fin3_final/sample_200.json"


def load_solver():
    spec = importlib.util.spec_from_file_location("fin4_split_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def content_digest(problem):
    payload = (
        problem["equation1"].strip()
        + "\0"
        + problem["equation2"].strip()
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def content_split(problems):
    ordered = sorted(
        problems,
        key=lambda row: (
            content_digest(row),
            row["equation1"],
            row["equation2"],
        ),
    )
    midpoint = len(ordered) // 2
    return ordered[:midpoint], ordered[midpoint:]


def verify(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    answer = json.dumps({"verdict": "false", "code": code})
    started = time.monotonic()
    result = verify_answer(_to_judge_problem(problem), answer)
    elapsed = time.monotonic() - started
    assert result["status"] == "accepted", (problem["id"], result)
    return elapsed


def run_configuration(module, problem, configuration):
    source = module.parse_equation(problem["equation1"])
    target = module.parse_equation(problem["equation2"])
    started = time.monotonic()
    engine = module.FiniteModelEngine(
        4,
        source,
        target,
        started + configuration["seconds"],
        configuration["maximum_states"],
        configuration["maximum_models"],
        options=configuration["options"],
    )
    found = engine.search_target_guided()
    elapsed = time.monotonic() - started
    row = {
        "configuration": configuration["name"],
        "found": found is not None,
        "engine_seconds": round(elapsed, 6),
        "target_witnesses_considered": engine.target_witnesses_tested,
        "target_witnesses_fully_searched":
            engine.target_witnesses_fully_searched,
        "partial_states": engine.partial_states,
        "propagation_rounds": engine.propagation_rounds,
        "constraint_evaluations": engine.constraint_evaluations,
        "term_support_evaluations": engine.term_support_evaluations,
        "support_cache_hits": engine.support_cache_hits,
        "domain_reductions": engine.domain_reductions,
        "forced_assignments": engine.forced_assignments,
        "support_disjoint_contradictions":
            engine.support_disjoint_contradictions,
        "source_contradictions": engine.source_contradictions,
        "target_contradictions": engine.target_contradictions,
        "branch_choices": engine.branch_choices,
        "branch_values": engine.branch_values,
        "maximum_depth": engine.maximum_depth,
        "nogoods_learned": engine.nogoods_learned,
        "nogoods_minimized": engine.nogoods_minimized,
        "nogoods_reused": engine.nogoods_reused,
        "symmetry_permutations_tested":
            engine.symmetry_permutations_tested,
        "symmetry_prunes": engine.symmetry_branch_prunes,
        "source_models": engine.source_models,
        "target_falsifying_models": engine.target_falsifying_models,
        "first_source_model_seconds": engine.first_source_model_seconds,
        "propagation_seconds": round(engine.propagation_seconds, 6),
        "activity_seconds": round(engine.activity_seconds, 6),
        "nogood_seconds": round(engine.nogood_seconds, 6),
        "symmetry_seconds": round(engine.symmetry_seconds, 6),
        "exhaustion": engine.exhaustion,
    }
    if found is not None:
        table, witness = found
        replay_started = time.monotonic()
        assert engine.replay(table, witness)
        row["replay_seconds"] = round(
            time.monotonic() - replay_started, 6
        )
        code = engine.emit_certificate(table)
        row["certificate_bytes"] = len(code.encode("utf-8"))
        row["judge_seconds"] = round(verify(problem, code), 6)
        row["witness_cardinality"] = len(set(witness))
        row["canonical_table"] = list(engine.canonicalize(table))
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--split", choices=("development", "holdout"), required=True
    )
    parser.add_argument("--include-medium", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-solver-sha256")
    args = parser.parse_args()
    solver_hash = hashlib.sha256(SOLVER.read_bytes()).hexdigest()
    if args.expected_solver_sha256:
        assert solver_hash == args.expected_solver_sha256, (
            "solver changed after Fin-4 freeze"
        )
    module = load_solver()
    problems = json.loads(PROBLEMS.read_text(encoding="utf-8"))
    development, holdout = content_split(problems)
    selected = development if args.split == "development" else holdout
    baseline_rows = {
        row["id"]: row
        for row in json.loads(BASELINE.read_text(encoding="utf-8"))
    }
    unresolved = [
        problem for problem in selected
        if not baseline_rows[problem["id"]].get("solved")
    ]
    portfolio = list(module.FIN4_PORTFOLIO[:2])
    if args.include_medium:
        portfolio.append(module.FIN4_PORTFOLIO[2])
    rows = []
    for index, problem in enumerate(unresolved, 1):
        print(
            f"[{index}/{len(unresolved)}] {problem['id']}", flush=True
        )
        attempts = []
        for configuration in portfolio:
            attempt = run_configuration(module, problem, configuration)
            attempts.append(attempt)
            if attempt["found"]:
                break
        rows.append({
            "id": problem["id"],
            "content_sha256": content_digest(problem),
            "attempts": attempts,
            "found": any(item["found"] for item in attempts),
        })
    baseline_true = sum(
        baseline_rows[problem["id"]].get("solved")
        and baseline_rows[problem["id"]].get("verdict") == "true"
        for problem in selected
    )
    baseline_false = sum(
        baseline_rows[problem["id"]].get("solved")
        and baseline_rows[problem["id"]].get("verdict") == "false"
        for problem in selected
    )
    gains = sum(row["found"] for row in rows)
    payload = {
        "split": args.split,
        "solver_sha256": solver_hash,
        "problem_count": len(selected),
        "unresolved_attempted": len(unresolved),
        "baseline_true": baseline_true,
        "baseline_false": baseline_false,
        "fin4_false_gain": gains,
        "final_true": baseline_true,
        "final_false": baseline_false + gains,
        "invalid_outcomes": 0,
        "rows": rows,
    }
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(
        f"{args.split}: TRUE {baseline_true}, FALSE "
        f"{baseline_false + gains}, Fin-4 gain {gains}"
    )


if __name__ == "__main__":
    main()
