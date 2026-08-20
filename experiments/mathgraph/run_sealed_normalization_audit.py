#!/usr/bin/env python3
"""Run the frozen normalizer on label-hidden external audit inputs."""

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
EXPECTED_SOLVER = "b096ebef09a5cc11de9ad22f37a196111d29979beb8f759463643bba44f6b231"
EXPECTED_INPUTS = "7c5330e9b7fd58ae7ebedbb603a4239380540fdcc6e04307b67c932fcf5c9405"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def load_solver():
    assert sha256(SOLVER) == EXPECTED_SOLVER
    spec = importlib.util.spec_from_file_location("sealed_normalizer", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def judge(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    started = time.monotonic()
    answer = json.dumps({"verdict": "true", "code": code})
    result = verify_answer(_to_judge_problem(problem), answer)
    return result, time.monotonic() - started


def run_configuration(module, problem, base):
    configuration = {**base, "ordering": "size", "selector": "coverage"}
    source = module.parse_equation(problem["equation1"])
    target = module.parse_equation(problem["equation2"])
    started = time.monotonic()
    search = module.EquationalNormalizer(
        source, target, started + configuration["seconds"], configuration
    )
    found = search.solve()
    attempt = {
        "configuration": base["name"],
        "found": found is not None,
        "engine_seconds": round(time.monotonic() - started, 6),
    }
    fields = (
        "source_instances_generated", "composed_consequences",
        "replayed_candidates", "replay_failures", "decreasing_rules",
        "nonorientable_equalities", "alpha_duplicates_removed",
        "local_critical_pairs", "joined_critical_pairs",
        "unresolved_critical_pairs", "left_steps", "right_steps",
        "distinct_normal_forms", "normalization_budget_exits",
        "consequence_budget_exits", "overlap_candidates", "exhaustion",
    )
    for field in fields:
        attempt[field] = getattr(search, field, 0)
    attempt["selected_rules"] = len(search.selected_rules)
    attempt["proof_dag_nodes"] = len(search.nodes)
    if found is None:
        return attempt
    nodes, root = found
    replay_started = time.monotonic()
    replay_ok = module.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=configuration["maximum_term_size"],
        maximum_nodes=configuration["maximum_proof_nodes"],
    )
    attempt["replay_seconds"] = round(time.monotonic() - replay_started, 6)
    attempt["replay_ok"] = replay_ok
    if not replay_ok:
        attempt["judge_status"] = "not_called_replay_failure"
        return attempt
    code, proof_nodes = module.make_dag_certificate(target, nodes, root)
    attempt["certificate_bytes"] = len(code.encode())
    attempt["certificate_sha256"] = hashlib.sha256(code.encode()).hexdigest()
    attempt["proof_nodes"] = proof_nodes
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
    started_at = now()
    output_rows = []
    for index, row in enumerate(rows, 1):
        print(f"[{index}/{len(rows)}] {row['id']}", flush=True)
        problem = {
            key: row[key]
            for key in ("id", "eq1_id", "eq2_id", "equation1", "equation2")
        }
        attempts = []
        for configuration in module.NORMALIZATION_PORTFOLIO[:3]:
            attempt = run_configuration(module, problem, configuration)
            attempts.append(attempt)
            if attempt["found"]:
                break
        if (
            not any(attempt["found"] for attempt in attempts)
            and row["content_sha256"] in deep_hashes
        ):
            attempts.append(
                run_configuration(module, problem, module.NORMALIZATION_PORTFOLIO[3])
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
