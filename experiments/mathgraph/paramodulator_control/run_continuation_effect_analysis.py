#!/usr/bin/env python3
"""Paired S/FS traces and single-rewrite counterfactual deletions.

Diagnostic only.  The frozen production solver is loaded but never edited.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

from run_forward_demodulation_ablation import (
    DEFAULT_INPUT,
    EXPECTED_SOLVER_SHA256,
    ForwardDemodulationRun,
    load_independent_replayer,
    load_solver,
    prepare_engine,
    sha256,
)


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_OUTPUT = (
    ROOT
    / "experiments/mathgraph/paramodulator_control/"
    "continuation_effect_analysis.json"
)


def selection_identity(event):
    chosen = event["chosen"]
    return (
        chosen["polarity"],
        chosen["alpha_key"],
        chosen["weight"],
        event["goal_score"],
    )


def align_selection_traces(control, treatment):
    left = control.get("selection_events", [])
    right = treatment.get("selection_events", [])
    common = 0
    for control_event, treatment_event in zip(left, right):
        if selection_identity(control_event) != selection_identity(treatment_event):
            break
        common += 1
    window_start = max(0, common - 2)
    window_end = common + 3
    return {
        "common_prefix_selections": common,
        "earliest_divergence_index": (
            common if common < min(len(left), len(right)) else None
        ),
        "control_selection_count": len(left),
        "treatment_selection_count": len(right),
        "control_window": left[window_start:window_end],
        "treatment_window": right[window_start:window_end],
    }


def make_settings(engine, args):
    return engine["argparse"].Namespace(
        max_clauses=args.max_clauses,
        max_weight=args.max_weight,
        max_term_size=args.max_term_size,
        max_processed=args.max_processed,
        pair_budget=args.pair_budget,
        timeout=args.timeout,
        translate=True,
        unordered=False,
        neg_bias=0,
        old_rules_first=False,
        tautology_prune=False,
        forward_subsumption=False,
    )


def run_condition(engine, row, settings, condition, blocked=()):
    return ForwardDemodulationRun(
        engine,
        row,
        settings,
        forward_demodulation=condition == "FS",
        scheduler=True,
        local_demodulation=condition == "FS",
        trace_events=True,
        blocked_demodulation_signatures=blocked,
    ).solve()


def verified(result, row, independent, external_replay, judge_enabled):
    record = {
        "proved": result.get("status") == "proved",
        "plan_ok": bool(result.get("plan_ok")),
        "independent_replay": False,
        "external_replay": False,
        "lean_status": None,
    }
    if not record["proved"] or not record["plan_ok"]:
        return record
    record["independent_replay"] = bool(independent.replay_plan(result["spec"]))
    record["external_replay"] = bool(external_replay["replay_plan"](result["spec"]))
    if (
        judge_enabled
        and record["independent_replay"]
        and record["external_replay"]
    ):
        from run_forward_demodulation_ablation import judge

        judged, elapsed = judge(row, result["code"])
        record["lean_status"] = judged.get("status")
        record["judge_seconds"] = round(elapsed, 6)
    return record


def compact_run(result):
    keys = (
        "status",
        "exit",
        "generated",
        "retained",
        "processed",
        "seen",
        "elapsed_s",
        "forward_demodulations",
        "demodulation_attempts",
        "superposition_candidates",
        "proof_ancestry_nodes",
        "proof_ancestry_demodulations",
        "proof_ancestry_superpositions",
    )
    return {key: result.get(key) for key in keys}


def ancestry_signature_set(result):
    return {
        event["signature"]
        for event in result.get("proof_ancestry_demodulation_events", [])
    }


def hash_events(events):
    encoded = json.dumps(events, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def run(args):
    module = load_solver()
    independent = load_independent_replayer()
    engine, external_replay = prepare_engine(module)
    payload = json.loads(args.input.read_text())
    rows = payload.get("rows", payload) if isinstance(payload, dict) else payload
    analyses = []
    for row in rows:
        print(json.dumps({"id": row["id"], "phase": "paired"}), flush=True)
        settings = make_settings(engine, args)
        control = run_condition(engine, row, settings, "S")
        treatment = run_condition(engine, row, settings, "FS")
        control_check = verified(
            control, row, independent, external_replay, args.judge
        )
        treatment_check = verified(
            treatment, row, independent, external_replay, args.judge
        )
        ancestry_events = treatment.get(
            "proof_ancestry_demodulation_events", []
        )
        counterfactuals = []
        original_signatures = ancestry_signature_set(treatment)
        for event in ancestry_events:
            signature = event["signature"]
            print(
                json.dumps(
                    {
                        "id": row["id"],
                        "phase": "delete",
                        "signature": signature[:12],
                    }
                ),
                flush=True,
            )
            counterfactual = run_condition(
                engine, row, settings, "FS", blocked=(signature,)
            )
            check = verified(
                counterfactual,
                row,
                independent,
                external_replay,
                args.judge,
            )
            replacement_signatures = ancestry_signature_set(counterfactual)
            accepted = (
                check["proved"]
                and check["plan_ok"]
                and check["independent_replay"]
                and check["external_replay"]
                and (
                    not args.judge
                    or check["lean_status"] in {"accepted", "complete"}
                )
            )
            if not accepted:
                classification = "necessary_under_frozen_search"
            elif replacement_signatures == original_signatures - {signature}:
                classification = "incidental"
            else:
                classification = "replaceable"
            counterfactuals.append(
                {
                    "deleted_signature": signature,
                    "deleted_event": event,
                    "classification": classification,
                    "verification": check,
                    "run": compact_run(counterfactual),
                    "replacement_ancestry_signatures": sorted(
                        replacement_signatures
                    ),
                }
            )
        analyses.append(
            {
                "id": row["id"],
                "equation_content_hash": hashlib.sha256(
                    (
                        row["equation1"].strip()
                        + "\n"
                        + row["equation2"].strip()
                    ).encode()
                ).hexdigest(),
                "control": compact_run(control),
                "treatment": compact_run(treatment),
                "control_verification": control_check,
                "treatment_verification": treatment_check,
                "selection_alignment": align_selection_traces(
                    control, treatment
                ),
                "control_selection_trace_sha256": hash_events(
                    control.get("selection_events", [])
                ),
                "treatment_selection_trace_sha256": hash_events(
                    treatment.get("selection_events", [])
                ),
                "control_raw_children_sha256": hash_events(
                    control.get("raw_child_events", [])
                ),
                "treatment_raw_children_sha256": hash_events(
                    treatment.get("raw_child_events", [])
                ),
                "treatment_demodulation_events": treatment.get(
                    "demodulation_events", []
                ),
                "proof_ancestry_demodulation_events": ancestry_events,
                "counterfactual_deletions": counterfactuals,
            }
        )
    counts = {}
    for analysis in analyses:
        for counterfactual in analysis["counterfactual_deletions"]:
            name = counterfactual["classification"]
            counts[name] = counts.get(name, 0) + 1
    result = {
        "schema": "mathgraph.continuation-effect-analysis.v1",
        "diagnostic_only": True,
        "production_changed": False,
        "solver_sha256": sha256(
            ROOT / "submissions/mathgraph/solver.py"
        ),
        "preregistration_sha256": sha256(
            ROOT
            / "experiments/mathgraph/paramodulator_control/"
            "continuation_effect_preregistration.json"
        ),
        "limits": {
            "max_clauses": args.max_clauses,
            "max_processed": args.max_processed,
            "max_weight": args.max_weight,
            "max_term_size": args.max_term_size,
            "pair_budget": args.pair_budget,
            "timeout_seconds": args.timeout,
        },
        "counterfactual_classification_counts": counts,
        "rows": analyses,
    }
    if result["solver_sha256"] != EXPECTED_SOLVER_SHA256:
        raise RuntimeError("production solver changed during diagnostic")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "counts": counts}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--max-clauses", type=int, default=8000)
    parser.add_argument("--max-processed", type=int, default=8000)
    parser.add_argument("--max-weight", type=int, default=36)
    parser.add_argument("--max-term-size", type=int, default=30)
    parser.add_argument("--pair-budget", type=int, default=300)
    parser.add_argument("--timeout", type=float, default=2.0)
    parser.add_argument("--judge", action="store_true")
    args = parser.parse_args()
    run(args)


if __name__ == "__main__":
    main()
