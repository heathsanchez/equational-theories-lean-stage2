#!/usr/bin/env python3
"""Unseal and evaluate a completed BridgeIR external audit."""

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
    radius = z * math.sqrt(
        rate * (1 - rate) / trials + z * z / (4 * trials * trials)
    ) / denominator
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


def cumulative_activation(row, names):
    return any(
        (attempt_for(row, name) or {}).get("no_match_activations", 0) > 0
        for name in names
    )


def cluster_bootstrap(input_rows, success_ids, seed, replicates=10000):
    clusters = defaultdict(list)
    for row in input_rows:
        source_hash = hashlib.sha256(
            row["equation1"].encode()
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
            numerator += sum(item in success_ids for item in ids)
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


def aggregate(rows, names):
    fields = (
        "bridge_equality_candidates", "replayed_bridge_equalities",
        "bridge_replay_failures", "bridge_matches_attempted",
        "repeated_variable_rejections", "unbound_variable_rejections",
        "bridge_states_created", "bridge_states_deduplicated",
        "bridge_states_pruned_no_activation", "bridge_cycles_suppressed",
        "reverse_rule_expansions", "nonorientable_bridges",
        "anti_unification_proposals", "anti_unification_replayed",
        "initial_normalizer_matches", "post_bridge_normalizer_matches",
        "no_match_activations", "normalization_steps_after_activation",
        "shared_normal_form_hits", "activated_distinct_normal_forms",
        "deadline_exits", "state_budget_exits",
    )
    totals = Counter()
    attempts = 0
    maximum_depth = 0
    maximum_growth = 0
    engine_seconds = 0.0
    replay_seconds = 0.0
    judge_seconds = 0.0
    for row in rows:
        for name in names:
            item = attempt_for(row, name)
            if item is None:
                continue
            attempts += 1
            engine_seconds += item.get("engine_seconds", 0)
            replay_seconds += item.get("replay_seconds", 0)
            judge_seconds += item.get("judge_seconds", 0)
            for field in fields:
                totals[field] += item.get(field, 0) or 0
            maximum_depth = max(
                maximum_depth, item.get("maximum_bridge_depth", 0)
            )
            maximum_growth = max(
                maximum_growth, item.get("maximum_term_growth", 0)
            )
            if accepted(item):
                break
    return {
        "attempts": attempts,
        **dict(totals),
        "maximum_bridge_depth": maximum_depth,
        "maximum_term_growth": maximum_growth,
        "engine_seconds": round(engine_seconds, 6),
        "replay_seconds": round(replay_seconds, 6),
        "judge_seconds": round(judge_seconds, 6),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--labels", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--provenance", type=Path, required=True)
    parser.add_argument("--preregistration", type=Path, required=True)
    parser.add_argument("--raw-results", type=Path, required=True)
    parser.add_argument("--closure", type=Path, required=True)
    parser.add_argument("--metamorphic", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    closure = json.loads(args.closure.read_text())
    assert sha256(args.raw_results) == closure["result_sha256"]
    assert sha256(args.labels) == closure["sealed_labels_sha256"]
    raw = json.loads(args.raw_results.read_text())
    inputs = json.loads(args.inputs.read_text())
    labels = json.loads(args.labels.read_text())["labels"]
    manifest = json.loads(args.manifest.read_text())
    metamorphic = (
        json.loads(args.metamorphic.read_text())
        if args.metamorphic is not None else None
    )
    assert raw["finished_at_utc"] <= closure["closed_at_utc"]
    assert not raw["labels_loaded_by_runner"]
    assert not closure["labels_loaded_by_runner"]
    by_input = {row["id"]: row for row in inputs["rows"]}
    by_result = {row["id"]: row for row in raw["rows"]}
    assert set(labels) == set(by_input) == set(by_result)
    true_rows = [by_result[key] for key, value in labels.items() if value]
    false_rows = [by_result[key] for key, value in labels.items() if not value]
    probe = ["bridge-probe"]
    fast = ["bridge-probe", "bridge-fast"]
    medium = fast + ["bridge-medium"]
    deep = medium + ["bridge-deep-diagnostic"]
    probe_hits = {
        row["id"] for row in true_rows if cumulative_hit(row, probe)
    }
    fast_hits = {
        row["id"] for row in true_rows if cumulative_hit(row, fast)
    }
    medium_hits = {
        row["id"] for row in true_rows if cumulative_hit(row, medium)
    }
    deep_hits = {
        row["id"] for row in true_rows if cumulative_hit(row, deep)
    }
    probe_activations = {
        row["id"] for row in true_rows if cumulative_activation(row, probe)
    }
    fast_activations = {
        row["id"] for row in true_rows if cumulative_activation(row, fast)
    }
    medium_activations = {
        row["id"] for row in true_rows
        if cumulative_activation(row, medium)
    }
    seed = int(manifest["seed_sha256"][:16], 16)
    bootstrap = cluster_bootstrap(
        [by_input[row["id"]] for row in true_rows], fast_hits, seed
    )
    source_families = Counter()
    strata = Counter()
    hit_records = []
    certificate_sizes = []
    proof_sizes = []
    for row in true_rows:
        winning = next(
            (item for item in row["attempts"] if accepted(item)), None
        )
        if winning is None:
            continue
        input_row = by_input[row["id"]]
        source_hash = hashlib.sha256(
            input_row["equation1"].encode()
        ).hexdigest()
        source_families[source_hash] += 1
        feature = row["stratum"]
        for category in (
            "source-vars-1-2" if feature["source_variables"] <= 2
            else "source-vars-3-plus",
            "shallow" if max(
                feature["source_depth"], feature["target_depth"]
            ) <= 2 else "nested",
        ):
            strata[category] += 1
        certificate_sizes.append(winning.get("certificate_bytes", 0))
        proof_sizes.append(winning.get("proof_nodes", 0))
        hit_records.append({
            "id": row["id"],
            "content_sha256": row["content_sha256"],
            "configuration": winning["configuration"],
            "source_family_sha256": source_hash,
            "activations": winning["no_match_activations"],
            "maximum_bridge_depth": winning["maximum_bridge_depth"],
            "bridge_states": winning["bridge_states_created"],
            "engine_seconds": winning["engine_seconds"],
            "proof_nodes": winning.get("proof_nodes", 0),
            "certificate_bytes": winning.get("certificate_bytes", 0),
        })
    invalid = Counter()
    false_judge_calls = 0
    all_judge_calls = 0
    false_found = 0
    for row in raw["rows"]:
        for attempt in row["attempts"]:
            if not labels[row["id"]] and attempt.get("found"):
                false_found += 1
            status = attempt.get("judge_status")
            if status is None:
                continue
            if status.startswith("not_called"):
                invalid[status] += 1
                continue
            all_judge_calls += 1
            if not labels[row["id"]]:
                false_judge_calls += 1
            if status != "accepted":
                invalid[status] += 1
    runtime = aggregate(raw["rows"], fast)
    seconds_per_gain = (
        round(
            (
                runtime["engine_seconds"]
                + runtime["replay_seconds"]
                + runtime["judge_seconds"]
            ) / len(fast_hits),
            6,
        )
        if fast_hits else None
    )
    required_gain = max(3, math.ceil(0.10 * len(true_rows)))
    conversion = (
        len(fast_hits) / len(fast_activations) if fast_activations else 0.0
    )
    maximum_family = max(source_families.values(), default=0)
    checks = {
        "unused_true_at_least_20": len(true_rows) >= 20,
        "gain_threshold": len(fast_hits) >= required_gain,
        "activation_rate_at_least_20_percent":
            len(fast_activations) / len(true_rows) >= 0.20,
        "activation_to_proof_at_least_25_percent": conversion >= 0.25,
        "bootstrap_lower_above_zero":
            bootstrap["interval_95"][0] > 0,
        "at_least_three_source_families": len(source_families) >= 3,
        "no_source_above_one_third":
            bool(fast_hits) and maximum_family / len(fast_hits) <= 1 / 3,
        "zero_invalid_false_controls":
            not invalid and not false_found and not false_judge_calls,
        "all_traces_replay": not invalid.get(
            "not_called_replay_failure", 0
        ),
        "runtime_at_most_20_seconds_per_gain":
            seconds_per_gain is not None and seconds_per_gain <= 20,
        "production_floor_preserved": None,
        "full_sample_true_gain": None,
    }
    summary = {
        "audit_version": raw["audit_version"],
        "evaluated_at_utc": datetime.now(timezone.utc).isoformat(),
        "audit_type": "external-large-balanced",
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
            "initial_no_match_opportunities": len(true_rows),
            "matching": manifest["matching"],
        },
        "activation": {
            "probe_rows": len(probe_activations),
            "fast_marginal_rows":
                len(fast_activations - probe_activations),
            "probe_plus_fast_rows": len(fast_activations),
            "medium_marginal_rows":
                len(medium_activations - fast_activations),
            "probe_plus_fast_rate": round(
                len(fast_activations) / len(true_rows), 6
            ),
            "activation_to_proof_conversion": round(conversion, 6),
        },
        "true_recall": {
            "probe_gain": len(probe_hits),
            "fast_marginal_gain": len(fast_hits - probe_hits),
            "probe_plus_fast_gain": len(fast_hits),
            "medium_marginal_diagnostic_gain":
                len(medium_hits - fast_hits),
            "deep_marginal_diagnostic_gain":
                len(deep_hits - medium_hits),
            "probe_plus_fast_gain_rate": round(
                len(fast_hits) / len(true_rows), 6
            ),
            "wilson_95_interval": wilson(len(fast_hits), len(true_rows)),
            "source_cluster_bootstrap": bootstrap,
            "source_families_with_any_hit": len(source_families),
            "maximum_hits_from_one_family": maximum_family,
            "structural_strata_with_hits": dict(strata),
            "hit_records": hit_records,
        },
        "precision": {
            "false_control_found": false_found,
            "false_control_true_judge_calls": false_judge_calls,
            "invalid_categories": dict(invalid),
            "all_bridge_judge_calls": all_judge_calls,
            "one_sided_95_upper_false_control_event_rate":
                round(1 - 0.05 ** (1 / len(false_rows)), 6),
        },
        "metrics": {
            "probe": aggregate(raw["rows"], probe),
            "probe_plus_fast": runtime,
            "probe_fast_medium": aggregate(raw["rows"], medium),
            "all_diagnostics": aggregate(raw["rows"], deep),
            "seconds_per_probe_fast_gain": seconds_per_gain,
            "largest_proof_nodes": max(proof_sizes, default=0),
            "largest_certificate_bytes": max(certificate_sizes, default=0),
        },
        "promotion_rule": {
            "required_gain": required_gain,
            "checks": checks,
            "passed": False,
            "decision": "keep diagnostic; production portfolio remains empty",
        },
        "metamorphic_audit": {
            "external_hits": len(hit_records),
            "status": (
                "complete" if metamorphic is not None
                else "pending separate post-unseal run"
            ),
            "result": metamorphic,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(json.dumps({
        "probe_gain": len(probe_hits),
        "fast_marginal_gain": len(fast_hits - probe_hits),
        "medium_marginal_gain": len(medium_hits - fast_hits),
        "probe_fast_activations": len(fast_activations),
        "promotion_passed": False,
        "output_sha256": sha256(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
