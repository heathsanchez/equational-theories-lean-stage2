#!/usr/bin/env python3
"""Unseal and evaluate a completed, hashed Fin-4 audit run."""

import argparse
import hashlib
import json
import math
import random
from collections import Counter, defaultdict
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
    radius = (
        z
        * math.sqrt(
            rate * (1 - rate) / trials + z * z / (4 * trials * trials)
        )
        / denominator
    )
    return [round(max(0.0, centre - radius), 6),
            round(min(1.0, centre + radius), 6)]


def attempt_for(row, name):
    return next(
        (item for item in row["attempts"] if item["configuration"] == name),
        None,
    )


def accepted(attempt):
    return bool(
        attempt
        and attempt.get("found")
        and attempt.get("replay_ok")
        and attempt.get("judge_status") == "accepted"
    )


def cumulative_hit(row, names):
    return any(accepted(attempt_for(row, name)) for name in names)


def cluster_bootstrap(rows, successes, seed, replicates=10000):
    clusters = defaultdict(list)
    for row in rows:
        source_hash = hashlib.sha256(
            row["equation1"].encode("utf-8")
        ).hexdigest()
        clusters[source_hash].append(row["id"])
    keys = sorted(clusters)
    rng = random.Random(seed)
    rates = []
    for _ in range(replicates):
        sampled = [rng.choice(keys) for _ in keys]
        numerator = 0
        denominator = 0
        for key in sampled:
            ids = clusters[key]
            denominator += len(ids)
            numerator += sum(item in successes for item in ids)
        rates.append(numerator / denominator if denominator else 0.0)
    rates.sort()
    return {
        "replicates": replicates,
        "source_clusters": len(keys),
        "interval_95": [
            round(rates[int(0.025 * replicates)], 6),
            round(rates[min(replicates - 1, int(0.975 * replicates))], 6),
        ],
    }


def sum_runtime(rows, names):
    total = 0.0
    for row in rows:
        for name in names:
            attempt = attempt_for(row, name)
            if attempt is None:
                continue
            total += attempt.get("engine_seconds", 0.0)
            total += attempt.get("replay_seconds", 0.0)
            total += attempt.get("judge_seconds", 0.0)
            if accepted(attempt):
                break
    return round(total, 6)


def aggregate_attempts(rows, names):
    fields = (
        "target_witnesses_considered",
        "target_witnesses_fully_searched",
        "partial_states",
        "propagation_rounds",
        "constraint_evaluations",
        "term_support_evaluations",
        "support_cache_hits",
        "domain_reductions",
        "forced_assignments",
        "support_disjoint_contradictions",
        "source_contradictions",
        "target_contradictions",
        "branch_choices",
        "branch_values",
        "nogoods_learned",
        "nogoods_minimized",
        "nogoods_reused",
        "symmetry_permutations_tested",
        "symmetry_prunes",
        "source_models",
        "target_falsifying_models",
    )
    totals = Counter()
    maximum_depth = 0
    attempts = 0
    for row in rows:
        for name in names:
            item = attempt_for(row, name)
            if item is None:
                continue
            attempts += 1
            for field in fields:
                totals[field] += item.get(field, 0) or 0
            maximum_depth = max(maximum_depth, item.get("maximum_depth", 0))
            if accepted(item):
                break
    result = {"attempts": attempts, **dict(totals)}
    result["maximum_depth"] = maximum_depth
    result["mean_branch_factor"] = round(
        totals["branch_values"] / totals["branch_choices"], 6
    ) if totals["branch_choices"] else 0.0
    return result


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
    closure = json.loads(args.closure.read_text(encoding="utf-8"))
    assert sha256(args.raw_results) == closure["result_sha256"]
    assert sha256(args.labels) == closure["sealed_labels_sha256"]
    raw = json.loads(args.raw_results.read_text(encoding="utf-8"))
    inputs = json.loads(args.inputs.read_text(encoding="utf-8"))
    labels = json.loads(args.labels.read_text(encoding="utf-8"))["labels"]
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    provenance = json.loads(args.provenance.read_text(encoding="utf-8"))
    assert sha256(args.provenance) == manifest["provenance_sha256"]
    prereg = json.loads(args.preregistration.read_text(encoding="utf-8"))
    assert raw["finished_at_utc"] <= closure["closed_at_utc"]
    by_id = {row["id"]: row for row in raw["rows"]}
    input_by_id = {row["id"]: row for row in inputs["rows"]}
    assert set(by_id) == set(labels) == set(input_by_id)
    false_rows = [by_id[key] for key, value in labels.items() if not value]
    true_rows = [by_id[key] for key, value in labels.items() if value]
    unresolved_false = [
        row for row in false_rows if not (
            row["baseline"]["solved"]
            and row["baseline"]["verdict"] == "false"
        )
    ]
    unresolved_all = [
        row for row in raw["rows"] if not row["baseline"]["solved"]
    ]
    probe_names = ["fin4-probe"]
    fast_names = ["fin4-probe", "fin4-fast"]
    medium_names = fast_names + ["fin4-medium"]
    deep_names = medium_names + ["fin4-deep-diagnostic"]
    probe_ids = {
        row["id"] for row in unresolved_false
        if cumulative_hit(row, probe_names)
    }
    fast_ids = {
        row["id"] for row in unresolved_false
        if cumulative_hit(row, fast_names)
    }
    medium_ids = {
        row["id"] for row in unresolved_false
        if cumulative_hit(row, medium_names)
    }
    deep_ids = {
        row["id"] for row in unresolved_false
        if cumulative_hit(row, deep_names)
    }
    seed = int(manifest["seed_sha256"][:16], 16)
    bootstrap = cluster_bootstrap(
        [input_by_id[row["id"]] for row in unresolved_false],
        fast_ids,
        seed,
    )
    strata = Counter()
    witness_cardinality = Counter()
    source_families = Counter()
    certificate_sizes = []
    hit_records = []
    for row in unresolved_false:
        winning = next(
            (item for item in row["attempts"] if accepted(item)), None
        )
        if winning is None:
            continue
        feature = row["stratum"]
        categories = (
            "source-vars-1-2" if feature["source_variables"] <= 2
            else "source-vars-3-plus",
            "shallow" if max(feature["source_depth"],
                             feature["target_depth"]) <= 2 else "nested",
            feature["fin3_source_phenotype"],
        )
        for category in categories:
            strata[category] += 1
        witness_cardinality[str(winning["witness_cardinality"])] += 1
        source_hash = hashlib.sha256(
            input_by_id[row["id"]]["equation1"].encode("utf-8")
        ).hexdigest()
        source_families[source_hash] += 1
        certificate_sizes.append(winning["certificate_bytes"])
        hit_records.append({
            "id": row["id"],
            "content_sha256": row["content_sha256"],
            "configuration": winning["configuration"],
            "source_family_sha256": source_hash,
            "witness_cardinality": winning["witness_cardinality"],
            "canonical_table": winning["canonical_table"],
            "partial_states": winning["partial_states"],
            "engine_seconds": winning["engine_seconds"],
            "certificate_bytes": winning["certificate_bytes"],
        })
    invalid_categories = Counter()
    true_fin4_judge_calls = 0
    total_fin4_judge_calls = 0
    for row in raw["rows"]:
        for attempt in row["attempts"]:
            status = attempt.get("judge_status")
            if status is None or status.startswith("not_called"):
                if status:
                    invalid_categories[status] += 1
                continue
            total_fin4_judge_calls += 1
            if labels[row["id"]]:
                true_fin4_judge_calls += 1
            if status != "accepted":
                invalid_categories[status] += 1
    baseline_false = sum(
        row["baseline"]["solved"] and row["baseline"]["verdict"] == "false"
        for row in false_rows
    )
    baseline_true = sum(
        row["baseline"]["solved"] and row["baseline"]["verdict"] == "true"
        for row in true_rows
    )
    fast_runtime = sum_runtime(unresolved_all, fast_names)
    fast_gain = len(fast_ids)
    runtime_per_gain = (
        round(fast_runtime / fast_gain, 6) if fast_gain else None
    )
    required_gain = max(2, math.ceil(0.10 * len(unresolved_false)))
    distinct_gain_strata = sum(value > 0 for value in strata.values())
    maximum_source_family = max(source_families.values(), default=0)
    rule_checks = {
        "unused_false_at_least_10": len(false_rows) >= 10,
        "gain_threshold": fast_gain >= required_gain,
        "bootstrap_lower_above_zero": bootstrap["interval_95"][0] > 0,
        "zero_invalid_outcomes": not invalid_categories,
        "runtime_at_most_20_seconds_per_gain":
            runtime_per_gain is not None and runtime_per_gain <= 20,
        "gains_in_at_least_two_structural_strata":
            distinct_gain_strata >= 2,
        "not_single_source_family":
            fast_gain > 0 and maximum_source_family < fast_gain,
        "production_floor_preserved": None,
    }
    summary = {
        "audit_version": raw["audit_version"],
        "evaluated_at_utc": datetime.now(timezone.utc).isoformat(),
        "audit_type": manifest["audit_type_if_valid"],
        "data_source": manifest["corpora"],
        "integrity": {
            "authoritative_head": manifest["authoritative_head"],
            "solver_sha256": raw["solver_sha256"],
            "inputs_sha256": sha256(args.inputs),
            "labels_sha256": sha256(args.labels),
            "manifest_sha256": sha256(args.manifest),
            "preregistration_sha256": sha256(args.preregistration),
            "raw_results_sha256": sha256(args.raw_results),
            "closure_sha256": sha256(args.closure),
            "labels_loaded_after_result_closed": True,
            "sealing_limitation": (
                "Process separation and hashes provide experimental integrity, "
                "not cryptographic protection from a malicious operator."
            ),
        },
        "provenance": {
            "previously_used_pair_count":
                provenance["previously_used_pair_count"],
            "excluded_by_reason": manifest["exclusions"],
            "candidate_rows_after_hash_exclusion":
                manifest["candidate_rows_after_hash_exclusion"],
            "false_no_order_le_3_opportunities":
                manifest["false_no_order_le_3_opportunities"],
        },
        "matching": manifest["matching"],
        "audit_counts": {
            "false_opportunities": len(false_rows),
            "true_controls": len(true_rows),
            "baseline_unresolved_false": len(unresolved_false),
            "baseline_unresolved_all": len(unresolved_all),
        },
        "baseline": {
            "false_accepted_on_false_set": baseline_false,
            "true_accepted_on_true_set": baseline_true,
        },
        "fin4": {
            "probe_gain": len(probe_ids),
            "fast_marginal_gain": len(fast_ids - probe_ids),
            "probe_plus_fast_gain": len(fast_ids),
            "medium_marginal_diagnostic_gain": len(medium_ids - fast_ids),
            "deep_marginal_diagnostic_gain": len(deep_ids - medium_ids),
            "unresolved_false_after_probe_fast":
                len(unresolved_false) - len(fast_ids),
            "gain_rate": round(
                len(fast_ids) / len(unresolved_false), 6
            ) if unresolved_false else 0.0,
            "wilson_95_interval":
                wilson(len(fast_ids), len(unresolved_false)),
            "source_cluster_bootstrap": bootstrap,
            "structural_strata_with_gains": dict(strata),
            "source_families_with_gains": len(source_families),
            "maximum_gain_from_one_source_family": maximum_source_family,
            "witness_cardinality_distribution": dict(witness_cardinality),
            "largest_certificate_bytes": max(certificate_sizes, default=0),
            "hit_records": hit_records,
        },
        "precision": {
            "true_control_fin4_judge_calls": true_fin4_judge_calls,
            "invalid_categories": dict(invalid_categories),
            "all_fin4_judge_calls": total_fin4_judge_calls,
            "one_sided_95_upper_invalid_rate_given_zero":
                round(1 - 0.05 ** (1 / total_fin4_judge_calls), 6)
                if total_fin4_judge_calls and not invalid_categories else None,
        },
        "runtime": {
            "probe_plus_fast_seconds_on_baseline_unresolved_rows":
                fast_runtime,
            "seconds_per_added_false": runtime_per_gain,
        },
        "engine_metrics_probe_plus_fast":
            aggregate_attempts(unresolved_all, fast_names),
        "preregistered_promotion": {
            "required_gain": required_gain,
            "checks": rule_checks,
            "passed_before_production_regression":
                all(value for value in rule_checks.values()
                    if value is not None),
            "final_passed": None,
        },
        "metamorphic": None,
        "production_regression": None,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(json.dumps({
        "false_opportunities": len(false_rows),
        "true_controls": len(true_rows),
        "baseline_false": baseline_false,
        "baseline_true": baseline_true,
        "probe_gain": len(probe_ids),
        "fast_marginal_gain": len(fast_ids - probe_ids),
        "medium_gain": len(medium_ids - fast_ids),
        "deep_gain": len(deep_ids - medium_ids),
        "wilson_95": wilson(len(fast_ids), len(unresolved_false)),
        "bootstrap_95": bootstrap["interval_95"],
        "runtime_per_gain": runtime_per_gain,
        "invalid": dict(invalid_categories),
        "preproduction_rule_pass":
            summary["preregistered_promotion"][
                "passed_before_production_regression"
            ],
    }, indent=2))


if __name__ == "__main__":
    main()
