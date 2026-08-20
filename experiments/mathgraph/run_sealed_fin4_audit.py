#!/usr/bin/env python3
"""Run frozen production and Fin-4 comparators without access to labels."""

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
SOLVER_FILE = ROOT / "submissions/mathgraph/solver.py"
SUBMISSION = ROOT / "submissions/mathgraph"
EXPECTED_SOLVER_SHA256 = (
    "ddb646624106d143a6b0882b1ec46fa9e047dc40214310010b5dda89f55f2eb7"
)
EXPECTED_INPUT_SHA256 = (
    "42f3680536f5bdcfe0e63b9d4eb977be4515ac978ea49088c86f4011c144c30c"
)


def now():
    return datetime.now(timezone.utc).isoformat()


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_solver():
    assert sha256(SOLVER_FILE) == EXPECTED_SOLVER_SHA256
    spec = importlib.util.spec_from_file_location(
        "sealed_frozen_fin4_solver", SOLVER_FILE
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def judge(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    started = time.monotonic()
    answer = json.dumps({"verdict": "false", "code": code})
    result = verify_answer(_to_judge_problem(problem), answer)
    return result, time.monotonic() - started


def metrics(engine):
    return {
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
        "canonicalization_seconds": round(
            engine.canonicalization_seconds, 6
        ),
        "exhaustion": engine.exhaustion,
    }


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
    attempt = {
        "configuration": configuration["name"],
        "found": found is not None,
        "engine_seconds": round(time.monotonic() - started, 6),
        **metrics(engine),
    }
    if found is None:
        return attempt
    table, witness = found
    replay_started = time.monotonic()
    replay_ok = engine.replay(table, witness)
    attempt["replay_seconds"] = round(
        time.monotonic() - replay_started, 6
    )
    attempt["replay_ok"] = replay_ok
    if not replay_ok:
        attempt["judge_status"] = "not_called_replay_failure"
        return attempt
    code = engine.emit_certificate(table)
    attempt["certificate_bytes"] = len(code.encode("utf-8"))
    result, judge_seconds = judge(problem, code)
    attempt["judge_seconds"] = round(judge_seconds, 6)
    attempt["judge_status"] = result.get("status", "unparsed")
    attempt["judge_message"] = result.get("message")
    attempt["witness_cardinality"] = len(set(witness))
    attempt["witness"] = list(witness)
    attempt["canonical_table"] = list(engine.canonicalize(table))
    attempt["certificate_sha256"] = hashlib.sha256(
        code.encode("utf-8")
    ).hexdigest()
    return attempt


def baseline_result(problem):
    from pipeline.proxy import load_config, run_solver

    started = time.monotonic()
    result = run_solver(str(SUBMISSION), problem, load_config())
    compact = {
        "solved": bool(result.get("solved")),
        "verdict": result.get("verdict"),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "llm_calls": result.get("llm_calls", 0),
        "judge_statuses": [],
    }
    for event in result.get("log", []):
        if event.get("type") == "judge":
            compact["judge_statuses"].append(
                event.get("response", {}).get("status", "unparsed")
            )
    return compact


def official_problem(row):
    return {
        "id": row["id"],
        "eq1_id": row["eq1_id"],
        "eq2_id": row["eq2_id"],
        "equation1": row["equation1"],
        "equation2": row["equation2"],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--preregistration", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--closure", type=Path, required=True)
    args = parser.parse_args()
    assert sha256(args.inputs) == EXPECTED_INPUT_SHA256
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    prereg = json.loads(args.preregistration.read_text(encoding="utf-8"))
    assert manifest["inputs_sha256"] == EXPECTED_INPUT_SHA256
    assert prereg["input_sha256"] == EXPECTED_INPUT_SHA256
    assert prereg["frozen_solver_sha256"] == EXPECTED_SOLVER_SHA256
    module = load_solver()
    payload = json.loads(args.inputs.read_text(encoding="utf-8"))
    rows = payload["rows"]
    deep_hashes = {
        row["content_sha256"]
        for row in sorted(rows, key=lambda item: item["content_sha256"])[:10]
    }
    started_at = now()
    output_rows = []
    for index, row in enumerate(rows, 1):
        problem = official_problem(row)
        print(f"[{index}/{len(rows)}] {row['id']}", flush=True)
        baseline = baseline_result(problem)
        attempts = []
        for configuration in module.FIN4_PORTFOLIO[:3]:
            attempt = run_configuration(module, problem, configuration)
            attempts.append(attempt)
            if attempt["found"]:
                break
        if (
            not any(item["found"] for item in attempts)
            and row["content_sha256"] in deep_hashes
        ):
            attempts.append(
                run_configuration(module, problem, module.FIN4_PORTFOLIO[3])
            )
        output_rows.append({
            "id": row["id"],
            "content_sha256": row["content_sha256"],
            "stratum": row["stratum"],
            "baseline": baseline,
            "attempts": attempts,
        })
    result = {
        "audit_version": payload["audit_version"],
        "started_at_utc": started_at,
        "finished_at_utc": now(),
        "inputs_sha256": sha256(args.inputs),
        "manifest_sha256": sha256(args.manifest),
        "preregistration_sha256": sha256(args.preregistration),
        "solver_sha256": sha256(SOLVER_FILE),
        "deep_subset_content_hashes": sorted(deep_hashes),
        "rows": output_rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True), encoding="utf-8"
    )
    result_hash = sha256(args.output)
    closure = {
        "closed_at_utc": now(),
        "result_path": str(args.output),
        "result_sha256": result_hash,
        "inputs_sha256": sha256(args.inputs),
        "sealed_labels_sha256": manifest["sealed_labels_sha256"],
        "solver_sha256": sha256(SOLVER_FILE),
        "labels_loaded_by_runner": False,
    }
    args.closure.write_text(
        json.dumps(closure, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(json.dumps({
        "rows": len(rows),
        "result_sha256": result_hash,
        "closure_sha256": sha256(args.closure),
    }, indent=2))


if __name__ == "__main__":
    main()
