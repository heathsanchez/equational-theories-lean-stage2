#!/usr/bin/env python3
"""Run frozen BridgeIR comparators without access to sealed labels."""

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
EXPECTED_SOLVER = "68729dde1e27c544e5d3e12504ea5878d57ad0af70cf16c80bb238433976dcf8"
EXPECTED_INPUTS = "c9422887172d2f2f7f4620001cb92ecc0f669b96fda44193feff13050ac273fd"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def load_solver():
    assert sha256(SOLVER) == EXPECTED_SOLVER
    spec = importlib.util.spec_from_file_location("sealed_bridge_ir", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def judge(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    started = time.monotonic()
    result = verify_answer(
        _to_judge_problem(problem),
        json.dumps({"verdict": "true", "code": code}),
    )
    return result, time.monotonic() - started


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


def run_configuration(module, problem, base):
    configuration = dict(base)
    source = module.parse_equation(problem["equation1"])
    target = module.parse_equation(problem["equation2"])
    started = time.monotonic()
    search = module.BridgeIR(
        source, target, started + configuration["seconds"], configuration
    )
    found = search.solve()
    attempt = {
        "configuration": base["name"],
        "found": found is not None,
        "engine_seconds": round(time.monotonic() - started, 6),
        **metrics(search),
    }
    if found is None:
        return attempt
    nodes, root = found
    replay_started = time.monotonic()
    replay_ok = module.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=
            search.normalizer.configuration["maximum_term_size"],
        maximum_nodes=configuration["maximum_proof_nodes"],
    )
    attempt["replay_seconds"] = round(
        time.monotonic() - replay_started, 6
    )
    attempt["replay_ok"] = replay_ok
    if not replay_ok:
        attempt["judge_status"] = "not_called_replay_failure"
        return attempt
    code, proof_nodes = module.make_dag_certificate(target, nodes, root)
    attempt["proof_nodes"] = proof_nodes
    attempt["certificate_bytes"] = len(code.encode())
    attempt["certificate_sha256"] = hashlib.sha256(code.encode()).hexdigest()
    result, judge_seconds = judge(problem, code)
    attempt["judge_seconds"] = round(judge_seconds, 6)
    attempt["judge_status"] = result.get("status", "unparsed")
    attempt["judge_message"] = result.get("message")
    return attempt


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--preregistration", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--closure", type=Path, required=True)
    args = parser.parse_args()
    assert sha256(args.inputs) == EXPECTED_INPUTS
    manifest = json.loads(args.manifest.read_text())
    preregistration = json.loads(args.preregistration.read_text())
    assert manifest["inputs_sha256"] == EXPECTED_INPUTS
    assert manifest["solver_sha256"] == EXPECTED_SOLVER
    assert preregistration["authoritative_head"] == manifest["authoritative_head"]
    module = load_solver()
    payload = json.loads(args.inputs.read_text())
    rows = payload["rows"]
    deep_hashes = {
        row["content_sha256"]
        for row in sorted(rows, key=lambda item: item["content_sha256"])[:10]
    }
    output_rows = []
    started_at = now()
    for index, row in enumerate(rows, 1):
        print(f"[{index}/{len(rows)}] {row['id']}", flush=True)
        problem = {
            key: row[key]
            for key in ("id", "eq1_id", "eq2_id", "equation1", "equation2")
        }
        attempts = []
        for configuration in module.BRIDGE_IR_PORTFOLIO[:3]:
            attempt = run_configuration(module, problem, configuration)
            attempts.append(attempt)
            if attempt["found"]:
                break
        if (
            not any(attempt["found"] for attempt in attempts)
            and row["content_sha256"] in deep_hashes
        ):
            attempts.append(
                run_configuration(
                    module, problem, module.BRIDGE_IR_PORTFOLIO[3]
                )
            )
        output_rows.append({
            "id": row["id"],
            "content_sha256": row["content_sha256"],
            "stratum": row["stratum"],
            "baseline": row["baseline"],
            "attempts": attempts,
        })
    result = {
        "audit_version": payload["audit_version"],
        "started_at_utc": started_at,
        "finished_at_utc": now(),
        "inputs_sha256": sha256(args.inputs),
        "manifest_sha256": sha256(args.manifest),
        "preregistration_sha256": sha256(args.preregistration),
        "solver_sha256": sha256(SOLVER),
        "deep_subset_content_hashes": sorted(deep_hashes),
        "labels_loaded_by_runner": False,
        "rows": output_rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True))
    closure = {
        "closed_at_utc": now(),
        "result_sha256": sha256(args.output),
        "inputs_sha256": sha256(args.inputs),
        "sealed_labels_sha256": manifest["labels_sha256"],
        "solver_sha256": sha256(SOLVER),
        "labels_loaded_by_runner": False,
    }
    args.closure.write_text(json.dumps(closure, indent=2, sort_keys=True))
    print(json.dumps({
        "rows": len(rows),
        "result_sha256": sha256(args.output),
        "closure_sha256": sha256(args.closure),
    }, indent=2))


if __name__ == "__main__":
    main()
