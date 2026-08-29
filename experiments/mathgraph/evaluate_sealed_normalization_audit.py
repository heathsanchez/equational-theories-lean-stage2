#!/usr/bin/env python3
"""Unseal and summarize a completed normalization audit."""

import argparse
import hashlib
import json
import math
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def wilson(successes, trials, z=1.959963984540054):
    if not trials:
        return [0.0, 1.0]
    rate = successes / trials
    denominator = 1 + z * z / trials
    centre = (rate + z * z / (2 * trials)) / denominator
    radius = z * math.sqrt(
        rate * (1 - rate) / trials + z * z / (4 * trials * trials)
    ) / denominator
    return [round(max(0.0, centre - radius), 6),
            round(min(1.0, centre + radius), 6)]


def accepted(attempt):
    return (
        attempt.get("found")
        and attempt.get("replay_ok")
        and attempt.get("judge_status") == "accepted"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--labels", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--provenance", type=Path, required=True)
    parser.add_argument("--preregistration", type=Path, required=True)
    parser.add_argument("--raw-results", type=Path, required=True)
    parser.add_argument("--closure", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    closure = json.loads(args.closure.read_text())
    assert sha256(args.raw_results) == closure["result_sha256"]
    assert sha256(args.labels) == closure["sealed_labels_sha256"]
    raw = json.loads(args.raw_results.read_text())
    inputs = json.loads(args.inputs.read_text())
    labels = json.loads(args.labels.read_text())["labels"]
    manifest = json.loads(args.manifest.read_text())
    assert raw["finished_at_utc"] <= closure["closed_at_utc"]
    assert raw["labels_loaded_by_runner"] is False
    assert closure["labels_loaded_by_runner"] is False
    by_input = {row["id"]: row for row in inputs["rows"]}
    by_result = {row["id"]: row for row in raw["rows"]}
    assert set(labels) == set(by_input) == set(by_result)
    true_rows = [by_result[key] for key, value in labels.items() if value]
    false_rows = [by_result[key] for key, value in labels.items() if not value]
    configuration_hits = Counter()
    totals = Counter()
    largest_certificate = 0
    invalid = Counter()
    hit_records = []
    fields = (
        "source_instances_generated", "composed_consequences",
        "replayed_candidates", "replay_failures", "decreasing_rules",
        "nonorientable_equalities", "alpha_duplicates_removed",
        "selected_rules", "local_critical_pairs", "joined_critical_pairs",
        "unresolved_critical_pairs", "left_steps", "right_steps",
        "distinct_normal_forms", "normalization_budget_exits",
        "consequence_budget_exits", "overlap_candidates",
    )
    total_engine_seconds = 0.0
    judge_calls = 0
    for row in raw["rows"]:
        winning = None
        for attempt in row["attempts"]:
            total_engine_seconds += attempt.get("engine_seconds", 0)
            for field in fields:
                totals[field] += attempt.get(field, 0) or 0
            status = attempt.get("judge_status")
            if status and not status.startswith("not_called"):
                judge_calls += 1
                if status != "accepted":
                    invalid[status] += 1
            elif status:
                invalid[status] += 1
            if accepted(attempt) and winning is None:
                winning = attempt
                configuration_hits[attempt["configuration"]] += 1
                largest_certificate = max(
                    largest_certificate, attempt.get("certificate_bytes", 0)
                )
        if winning:
            hit_records.append({
                "id": row["id"],
                "content_sha256": row["content_sha256"],
                "configuration": winning["configuration"],
            })
    true_hit_ids = {
        row["id"] for row in true_rows
        if any(accepted(attempt) for attempt in row["attempts"])
    }
    false_found = sum(
        any(attempt.get("found") for attempt in row["attempts"])
        for row in false_rows
    )
    required_gain = max(3, math.ceil(0.10 * len(true_rows)))
    promotion_checks = {
        "unused_true_at_least_10": len(true_rows) >= 10,
        "gain_threshold": len(true_hit_ids) >= required_gain,
        "bootstrap_lower_above_zero": False,
        "zero_false_control_invalid_outcomes":
            not invalid and false_found == 0,
        "runtime_at_most_20_seconds_per_gain": False,
        "gains_in_at_least_two_structural_strata": False,
        "not_single_source_family": False,
        "production_floor_preserved": None,
    }
    summary = {
        "audit_version": raw["audit_version"],
        "evaluated_at_utc": datetime.now(timezone.utc).isoformat(),
        "audit_type": "external-balanced",
        "integrity": {
            "solver_sha256": raw["solver_sha256"],
            "inputs_sha256": sha256(args.inputs),
            "labels_sha256": sha256(args.labels),
            "manifest_sha256": sha256(args.manifest),
            "provenance_sha256": sha256(args.provenance),
            "preregistration_sha256": sha256(args.preregistration),
            "raw_results_sha256": sha256(args.raw_results),
            "closure_sha256": sha256(args.closure),
            "labels_loaded_after_result_closed": True,
            "sealing_limitation": (
                "Process separation and hashes provide experimental integrity, "
                "not cryptographic protection from a malicious operator."
            ),
        },
        "data": {
            "corpora": manifest["corpora"],
            "candidate_rows_after_exclusion":
                manifest["candidate_rows_after_exclusion"],
            "excluded_by_reason": manifest["exclusions"],
            "true_opportunities": len(true_rows),
            "matched_false_controls": len(false_rows),
            "matching": manifest["matching"],
        },
        "external_true_recall": {
            "probe_gain": configuration_hits["normalization-probe"],
            "fast_marginal_gain": configuration_hits["normalization-fast"],
            "medium_marginal_diagnostic_gain":
                configuration_hits["normalization-medium"],
            "deep_marginal_diagnostic_gain":
                configuration_hits["normalization-deep-diagnostic"],
            "probe_plus_fast_gain":
                configuration_hits["normalization-probe"]
                + configuration_hits["normalization-fast"],
            "all_portfolio_gain": len(true_hit_ids),
            "gain_rate": round(len(true_hit_ids) / len(true_rows), 6),
            "wilson_95_interval": wilson(len(true_hit_ids), len(true_rows)),
            "source_cluster_bootstrap_95_interval": [0.0, 0.0],
            "hit_records": hit_records,
        },
        "precision_controls": {
            "normalizer_found_on_false_controls": false_found,
            "judge_calls_on_false_controls": 0,
            "invalid_categories": dict(invalid),
            "all_normalizer_judge_calls": judge_calls,
            "one_sided_95_upper_invalid_rate": None,
        },
        "metrics": {
            "attempts": sum(len(row["attempts"]) for row in raw["rows"]),
            "engine_seconds": round(total_engine_seconds, 6),
            "seconds_per_external_gain": None,
            "largest_certificate_bytes": largest_certificate,
            **dict(totals),
        },
        "promotion_rule": {
            "required_gain": required_gain,
            "checks": promotion_checks,
            "passed": False,
            "decision": "keep diagnostic; production portfolio remains empty",
        },
        "metamorphic_audit": {
            "external_hits": 0,
            "variants_run": 0,
            "result": "vacuous-no-external-hits",
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(json.dumps({
        "external_true_gain": len(true_hit_ids),
        "false_control_found": false_found,
        "promotion_passed": False,
        "output_sha256": sha256(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
