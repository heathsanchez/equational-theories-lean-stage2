#!/usr/bin/env python3
"""Delete the sole proof-ancestral CN1 materialization and replay officially."""

from __future__ import annotations

import json
from pathlib import Path

from run_continuation_effect_analysis import make_settings, verified
from run_forward_demodulation_ablation import (
    DEFAULT_INPUT,
    ForwardDemodulationRun,
    load_independent_replayer,
    load_solver,
    prepare_engine,
    sha256,
)


ROOT = Path(__file__).resolve().parents[3]
CN1_RESULTS = (
    ROOT
    / "experiments/mathgraph/paramodulator_control/"
    "six_residual_continuation_novelty_cn1_results.json"
)
OUTPUT = (
    ROOT
    / "experiments/mathgraph/paramodulator_control/"
    "continuation_novelty_counterfactual.json"
)


class Settings:
    max_clauses = 8000
    max_processed = 8000
    max_weight = 36
    max_term_size = 30
    pair_budget = 300
    timeout = 2.0


def main():
    previous = json.loads(CN1_RESULTS.read_text())["conditions"]["CN1"]
    target = next(
        row
        for row in previous
        if row.get("proof_ancestry_demodulations", 0) > 0
    )
    event = target["proof_ancestry_demodulation_events"][0]
    rows = json.loads(DEFAULT_INPUT.read_text())
    row = next(item for item in rows if item["id"] == target["id"])
    module = load_solver()
    independent = load_independent_replayer()
    engine, external_replay = prepare_engine(module)
    settings = make_settings(engine, Settings)
    result = ForwardDemodulationRun(
        engine,
        row,
        settings,
        forward_demodulation=True,
        scheduler=True,
        dual_retention=True,
        per_given_budget=1,
        global_budget=256,
        quotient_mode=True,
        operation_relative_representatives=True,
        continuation_novelty=True,
        blocked_demodulation_signatures=(event["signature"],),
    ).solve()
    check = verified(
        result, row, independent, external_replay, judge_enabled=True
    )
    accepted = (
        check["proved"]
        and check["plan_ok"]
        and check["independent_replay"]
        and check["external_replay"]
        and check["lean_status"] in {"accepted", "complete"}
    )
    payload = {
        "schema": "mathgraph.continuation-novelty-counterfactual.v1",
        "diagnostic_only": True,
        "production_changed": False,
        "solver_sha256": sha256(
            ROOT / "submissions/mathgraph/solver.py"
        ),
        "row_id": row["id"],
        "deleted_signature": event["signature"],
        "classification": (
            "replaceable" if accepted else "necessary_under_frozen_search"
        ),
        "verification": check,
        "counterfactual_run": {
            key: result.get(key)
            for key in (
                "status",
                "exit",
                "generated",
                "processed",
                "forward_demodulations",
                "operationally_novel_materializations",
                "proof_ancestry_demodulations",
            )
        },
        "aggregate_causal_precision": {
            "CN1_materializations": sum(
                row.get("operationally_novel_materializations", 0)
                for row in previous
            ),
            "CN1_proof_ancestral_materializations": sum(
                row.get("proof_ancestry_demodulations", 0)
                for row in previous
                if row.get("lean_status") in {"accepted", "complete"}
            ),
        },
    }
    OUTPUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
