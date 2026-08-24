#!/usr/bin/env python3
"""Recover and localize the previously observed CN1 proof for residual 0036."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PREREG = HERE / "0036_cn1_certificate_recovery_preregistration.json"
RUNNER = (
    ROOT / "experiments/mathgraph/paramodulator_control/"
    "run_forward_demodulation_ablation.py"
)
PRIOR = (
    ROOT / "experiments/mathgraph/paramodulator_control/"
    "six_residual_continuation_novelty_cn1_results.json"
)
INPUT = HERE / "released_residuals_unlabelled.json"
DEFAULT_OUTPUT_DIR = HERE / "0036_cn1_certificate_recovery_artifacts"
EXPECTED_PREREG_SHA256 = (
    "6c58b6ce9075669e09cc1dde856be800eadde1756fb5eb4a74df758135f07465"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_runner():
    spec = importlib.util.spec_from_file_location(
        "mathgraph_0036_cn1_frozen_runner", RUNNER
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def prior_record(payload):
    return next(
        row
        for row in payload["conditions"]["CN1"]
        if row["id"] == "evaluation_normal_0036"
    )


def ancestry_table(proof_text, ancestry_ids, closed_id):
    wanted = set(ancestry_ids) | {str(int(closed_id) + 1)}
    rows = []
    for line in proof_text.splitlines():
        number, _, rest = line.partition(" ")
        if number not in wanted:
            continue
        formula, marker, justification = rest.rpartition(".  [")
        rows.append({
            "id": number,
            "formula": formula if marker else rest,
            "justification": (
                justification[:-2] if marker and justification.endswith("].")
                else justification
            ),
            "closes": number == str(int(closed_id) + 1),
        })
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--official", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    args = parser.parse_args()

    protocol = json.loads(PREREG.read_text(encoding="utf-8"))
    prior_payload = json.loads(PRIOR.read_text(encoding="utf-8"))
    previous = prior_record(prior_payload)
    rows = json.loads(INPUT.read_text(encoding="utf-8"))
    expected_headers = {
        "id", "index", "difficulty", "eq1_id", "eq2_id",
        "equation1", "equation2",
    }
    header_ok = bool(rows) and all(set(row) == expected_headers for row in rows)
    row = next(item for item in rows if item["id"] == "evaluation_normal_0036")
    body_ok = (
        row["equation1"] == protocol["target"]["source"]
        and row["equation2"] == protocol["target"]["goal"]
        and "answer" not in row
    )
    frozen = protocol["frozen_inputs"]
    frozen_hashes_ok = (
        sha256(PREREG) == EXPECTED_PREREG_SHA256
        and sha256(RUNNER) == frozen["runner_sha256"]
        and sha256(PRIOR) == frozen["prior_result_sha256"]
        and sha256(INPUT) == frozen["unlabelled_input_sha256"]
    )
    previous_claim_ok = all((
        previous["status"] == "proved",
        previous["plan_ok"],
        previous["independent_replay"],
        previous["external_plan_replay"],
        previous["lean_status"] == "accepted",
        previous["proof_ancestry_nodes"] == 9,
        previous["proof_ancestry_superpositions"] == 7,
        previous["proof_ancestry_demodulations"] == 0,
    ))

    runner = load_runner()
    solver = runner.load_solver()
    independent = runner.load_independent_replayer()
    engine, external_replay = runner.prepare_engine(solver)
    config = protocol["frozen_configuration"]
    settings = engine["argparse"].Namespace(
        max_clauses=config["maximum_clauses"],
        max_weight=config["maximum_weight"],
        max_term_size=config["maximum_term_size"],
        max_processed=config["maximum_processed"],
        pair_budget=config["pair_budget"],
        timeout=config["timeout_seconds"],
        translate=True,
        unordered=False,
        neg_bias=0,
        old_rules_first=False,
        tautology_prune=False,
        forward_subsumption=False,
    )
    started = time.monotonic()
    result = runner.ForwardDemodulationRun(
        engine,
        row,
        settings,
        forward_demodulation=True,
        scheduler=True,
        local_demodulation=False,
        dual_retention=True,
        per_given_budget=config["dual_retention_per_given"],
        global_budget=config["dual_retention_global"],
        quotient_mode=True,
        expose_all_representatives=False,
        merge_passive_classes=False,
        operation_relative_representatives=True,
        lazy_representative_materialization=False,
        continuation_novelty=True,
        corridor_lookahead=False,
        trace_events=True,
    ).solve()
    wall_seconds = round(time.monotonic() - started, 6)

    independent_ok = False
    external_ok = False
    judge_status = None
    judge_seconds = None
    if result.get("status") == "proved" and result.get("plan_ok"):
        independent_ok = bool(independent.replay_plan(result["spec"]))
        external_ok = bool(external_replay["replay_plan"](result["spec"]))
        if args.official and independent_ok and external_ok:
            judged, elapsed = runner.judge(row, result["code"])
            judge_status = judged.get("status")
            judge_seconds = round(elapsed, 6)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    proof_path = args.output_dir / "0036_cn1_proof.p9p"
    plan_path = args.output_dir / "0036_cn1_plan.json"
    lean_path = args.output_dir / "0036_cn1_certificate.lean"
    ancestry_path = args.output_dir / "0036_cn1_ancestry.json"
    proof_path.write_text(result.get("proof_text", ""), encoding="utf-8")
    plan_path.write_text(
        json.dumps(result.get("spec"), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    lean_path.write_text(result.get("code", ""), encoding="utf-8")
    ancestry = ancestry_table(
        result.get("proof_text", ""),
        result.get("proof_ancestry_ids", []),
        result.get("closed_id", "0"),
    ) if result.get("closed_id") else []
    ancestry_payload = {
        "schema": "mathgraph.0036-cn1-proof-ancestry.v1",
        "proof_ancestry_ids": result.get("proof_ancestry_ids", []),
        "rows": ancestry,
        "selection_events": result.get("selection_events", []),
        "proof_ancestry_demodulation_events": result.get(
            "proof_ancestry_demodulation_events", []
        ),
    }
    ancestry_path.write_text(
        json.dumps(ancestry_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    artifact_paths = [proof_path, plan_path, lean_path, ancestry_path]
    artifacts_ok = all(path.exists() and path.stat().st_size > 0 for path in artifact_paths)

    measurement_ok = all((
        protocol["status"] == "FROZEN_BEFORE_RECOVERY_EXECUTABLE",
        frozen_hashes_ok,
        sha256(ROOT / frozen["solver_path"]) == frozen["solver_sha256"],
        header_ok,
        body_ok,
        previous_claim_ok,
    ))
    gate = protocol["acceptance_gate"]
    shape_ok = all((
        result.get("proof_ancestry_nodes") == gate["proof_ancestry_nodes"],
        result.get("proof_ancestry_superpositions")
        == gate["proof_ancestry_superpositions"],
        result.get("proof_ancestry_demodulations")
        == gate["proof_ancestry_demodulations"],
        result.get("n_lemmas") == gate["expected_lemmas"],
        result.get("total_steps") == gate["expected_total_steps"],
    ))
    accepted = all((
        result.get("status") == gate["status"],
        result.get("plan_ok") is gate["plan_ok"],
        independent_ok is gate["independent_replay"],
        external_ok is gate["external_plan_replay"],
        args.official,
        judge_status == gate["official_lean_status"],
        len(result.get("code", "").encode()) <= gate["maximum_certificate_bytes"],
        artifacts_ok,
    ))
    if not measurement_ok:
        decision = "MEASUREMENT_FAILURE"
    elif accepted and shape_ok:
        decision = "CN1_CERTIFICATE_RECOVERED"
    elif accepted:
        decision = "CN1_PROOF_SHAPE_DRIFT"
    else:
        decision = "CN1_RECOVERY_FAILURE"

    summary = {
        "schema": "mathgraph.0036-cn1-certificate-recovery-results.v1",
        "decision": decision,
        "measurement_ok": measurement_ok,
        "official_enabled": args.official,
        "input_headers_ok": header_ok,
        "equation_bodies_ok": body_ok,
        "frozen_hashes_ok": frozen_hashes_ok,
        "previous_claim_ok": previous_claim_ok,
        "recovery": {
            "status": result.get("status"),
            "wall_seconds": wall_seconds,
            "generated": result.get("generated"),
            "retained": result.get("retained"),
            "processed": result.get("processed"),
            "forward_demodulations": result.get("forward_demodulations"),
            "operationally_novel_materializations": result.get(
                "operationally_novel_materializations"
            ),
            "proof_ancestry_nodes": result.get("proof_ancestry_nodes"),
            "proof_ancestry_superpositions": result.get(
                "proof_ancestry_superpositions"
            ),
            "proof_ancestry_demodulations": result.get(
                "proof_ancestry_demodulations"
            ),
            "proof_ancestry_ids": result.get("proof_ancestry_ids"),
            "closed_id": result.get("closed_id"),
            "plan_ok": result.get("plan_ok"),
            "independent_replay": independent_ok,
            "external_plan_replay": external_ok,
            "lean_status": judge_status,
            "judge_seconds": judge_seconds,
            "n_lemmas": result.get("n_lemmas"),
            "total_steps": result.get("total_steps"),
            "certificate_bytes": len(result.get("code", "").encode()),
            "shape_ok": shape_ok,
        },
        "artifacts": {
            path.name: {
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            }
            for path in artifact_paths
        },
    }
    output = args.output_dir / "0036_cn1_certificate_recovery_results.json"
    output.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(summary, sort_keys=True), flush=True)
    if decision not in {"CN1_CERTIFICATE_RECOVERED", "CN1_PROOF_SHAPE_DRIFT"}:
        raise SystemExit(decision)


if __name__ == "__main__":
    main()
