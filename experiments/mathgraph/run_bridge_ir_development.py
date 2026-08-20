#!/usr/bin/env python3
"""Run the preregistered BridgeIR grid on the fixed development residuals."""

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


VARIANTS = {
    "activation-depth1-probe": {
        "portfolios": (0,), "ranking": "activation", "maximum_depth": 1,
    },
    "distance-depth1-probe": {
        "portfolios": (0,), "ranking": "distance", "maximum_depth": 1,
    },
    "activation-depth2-probe-fast": {
        "portfolios": (0, 1), "ranking": "activation",
    },
    "activation-depth2-no-nonorientable": {
        "portfolios": (0, 1), "ranking": "activation",
        "nonorientable_evidence": False,
    },
    "activation-depth2-no-reverse": {
        "portfolios": (0, 1), "ranking": "activation",
        "reverse_expansion": False,
    },
    "activation-depth2-anti-unification": {
        "portfolios": (0, 1), "ranking": "activation",
        "anti_unification": True,
    },
}


def load_solver():
    spec = importlib.util.spec_from_file_location("bridge_development", SOLVER)
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


def metrics(search):
    fields = (
        "bridge_equality_candidates", "replayed_bridge_equalities",
        "bridge_replay_failures", "bridge_matches_attempted",
        "repeated_variable_rejections", "unbound_variable_rejections",
        "bridge_states_created", "bridge_states_deduplicated",
        "bridge_states_pruned_no_activation", "bridge_cycles_suppressed",
        "reverse_rule_expansions", "nonorientable_bridges",
        "anti_unification_proposals", "anti_unification_replayed",
        "maximum_bridge_depth", "maximum_term_growth",
        "initial_normalizer_matches", "post_bridge_normalizer_matches",
        "no_match_activations", "normalization_steps_after_activation",
        "shared_normal_form_hits", "activated_distinct_normal_forms",
        "deadline_exits", "state_budget_exits", "exhaustion",
    )
    return {field: getattr(search, field) for field in fields}


def run(module, problem, base, variant):
    configuration = {**base}
    for key, value in VARIANTS[variant].items():
        if key != "portfolios":
            configuration[key] = value
    source = module.parse_equation(problem["equation1"])
    target = module.parse_equation(problem["equation2"])
    started = time.monotonic()
    search = module.BridgeIR(
        source, target, started + configuration["seconds"], configuration
    )
    found = search.solve()
    row = {
        "configuration": base["name"],
        "variant": variant,
        "found": found is not None,
        "engine_seconds": round(time.monotonic() - started, 6),
        **metrics(search),
    }
    if found is None:
        return row
    nodes, root = found
    replay_started = time.monotonic()
    row["replay_ok"] = module.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=
            search.normalizer.configuration["maximum_term_size"],
        maximum_nodes=configuration["maximum_proof_nodes"],
    )
    row["replay_seconds"] = round(time.monotonic() - replay_started, 6)
    code, proof_nodes = module.make_dag_certificate(target, nodes, root)
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
    parser.add_argument("--variant", choices=tuple(VARIANTS))
    parser.add_argument(
        "--scope", choices=("development", "holdout", "sample200"),
        default="development",
    )
    args = parser.parse_args()
    module = load_solver()
    problems = json.loads(PROBLEMS.read_text())
    ordered = sorted(
        problems,
        key=lambda row: (digest(row), row["equation1"], row["equation2"]),
    )
    development = {
        "development": ordered[:100],
        "holdout": ordered[100:],
        "sample200": problems,
    }[args.scope]
    baseline = {
        row["id"]: row for row in json.loads(args.baseline.read_text())
    }
    unresolved = [
        row for row in development if not baseline[row["id"]].get("solved")
    ]
    variants = [args.variant] if args.variant else list(VARIANTS)
    output = []
    for index, problem in enumerate(unresolved, 1):
        print(f"[{index}/{len(unresolved)}] {problem['id']}", flush=True)
        records = {}
        for variant in variants:
            attempts = []
            for portfolio_index in VARIANTS[variant]["portfolios"]:
                attempt = run(
                    module,
                    problem,
                    module.BRIDGE_IR_PORTFOLIO[portfolio_index],
                    variant,
                )
                attempts.append(attempt)
                if attempt["found"]:
                    break
            records[variant] = attempts
        output.append({
            "id": problem["id"],
            "content_sha256": digest(problem),
            "variants": records,
        })
    args.output.write_text(json.dumps({
        "solver_sha256": hashlib.sha256(SOLVER.read_bytes()).hexdigest(),
        "baseline_sha256": hashlib.sha256(
            args.baseline.read_bytes()
        ).hexdigest(),
        "development_unresolved": len(unresolved),
        "rows": output,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
