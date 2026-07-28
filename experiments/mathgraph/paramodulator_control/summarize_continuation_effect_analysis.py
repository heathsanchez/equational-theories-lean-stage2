#!/usr/bin/env python3
"""Compress a full continuation-effect run into a Git-sized audit summary."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


def accepted(check):
    return (
        check["proved"]
        and check["plan_ok"]
        and check["independent_replay"]
        and check["external_replay"]
        and check.get("lean_status") in {"accepted", "complete"}
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    payload = json.loads(args.input.read_text())
    counts = Counter()
    rows = []
    for row in payload["rows"]:
        original = {
            event["signature"]
            for event in row["proof_ancestry_demodulation_events"]
        }
        deletions = []
        for item in row["counterfactual_deletions"]:
            replacement = set(item["replacement_ancestry_signatures"])
            if not accepted(item["verification"]):
                classification = "necessary_under_frozen_search"
            elif replacement == original - {item["deleted_signature"]}:
                classification = "incidental"
            else:
                classification = "replaceable"
            counts[classification] += 1
            deletions.append(
                {
                    "deleted_signature": item["deleted_signature"],
                    "classification": classification,
                    "verification": item["verification"],
                    "run": item["run"],
                }
            )
        alignment = row["selection_alignment"]
        rows.append(
            {
                "id": row["id"],
                "equation_content_hash": row["equation_content_hash"],
                "control": row["control"],
                "treatment": row["treatment"],
                "control_verification": row["control_verification"],
                "treatment_verification": row["treatment_verification"],
                "selection_alignment": {
                    key: alignment[key]
                    for key in (
                        "common_prefix_selections",
                        "earliest_divergence_index",
                        "control_selection_count",
                        "treatment_selection_count",
                    )
                },
                "trace_hashes": {
                    key: row[key]
                    for key in (
                        "control_selection_trace_sha256",
                        "treatment_selection_trace_sha256",
                        "control_raw_children_sha256",
                        "treatment_raw_children_sha256",
                    )
                },
                "proof_ancestry_demodulation_events": row[
                    "proof_ancestry_demodulation_events"
                ],
                "counterfactual_deletions": deletions,
            }
        )
    output = {
        "schema": "mathgraph.continuation-effect-summary.v1",
        "diagnostic_only": True,
        "production_changed": False,
        "solver_sha256": payload["solver_sha256"],
        "preregistration_sha256": payload["preregistration_sha256"],
        "limits": payload["limits"],
        "counterfactual_classification_counts": dict(counts),
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")


if __name__ == "__main__":
    main()
