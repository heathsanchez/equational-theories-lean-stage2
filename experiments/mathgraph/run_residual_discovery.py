#!/usr/bin/env python3
"""Build the discovery-only residual taxonomy and freeze cluster artifacts."""

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from experiments.mathgraph import residual_characterization as rc


def now():
    return datetime.now(timezone.utc).isoformat()


def load_rows():
    rows = []
    seen = set()

    sample = json.loads(
        (ROOT / "examples/problems/sample_200.json").read_text()
    )
    baseline = json.loads(
        (ROOT / "experiments/mathgraph/results/normalization_baseline_manifest.json")
        .read_text()
    )["sample_200_accepted"]
    for row in sample:
        if row["id"].startswith("true_") and row["id"] not in baseline:
            item = dict(row)
            item["origin"] = "sample_200_unresolved_true"
            item["dataset_role"] = "public-discovery"
            rows.append(item)

    for prefix in ("normalization", "bridge_ir"):
        inputs = json.loads(
            (ROOT / f"experiments/mathgraph/audits/{prefix}_audit_inputs.json")
            .read_text()
        )
        labels = json.loads(
            (ROOT / f"experiments/mathgraph/audits/{prefix}_audit_labels.sealed.json")
            .read_text()
        )["labels"]
        for row in inputs["rows"]:
            if not labels[row["id"]]:
                continue
            item = {
                key: row[key]
                for key in (
                    "id", "eq1_id", "eq2_id", "equation1", "equation2"
                )
            }
            item["origin"] = f"{prefix}_external_true_discovery"
            item["dataset_role"] = "external-discovery"
            rows.append(item)

    module = rc.load_solver()
    unique = []
    for row in rows:
        _, _, digest = rc.content_hash(
            module, row["equation1"], row["equation2"]
        )
        if digest not in seen:
            seen.add(digest)
            unique.append(row)
    return unique


def compact_object(item):
    return {
        key: value for key, value in item.items()
        if key not in ("supporting_obstruction_evidence",)
    }


def activation_comparison(records):
    activated = [
        row for row in records
        if row["provenance"]["origin"] == "bridge_ir_external_true_discovery"
        and row["bridge_trace"]["activation_row"]
    ]
    entries = []
    for row in activated:
        bridge = row["bridge_trace"]
        activation = bridge["best_activation"] or {}
        entries.append({
            "content_sha256": row["identity"]["content_sha256"],
            "source_family": row["provenance"]["source_group_sha256"],
            "completed_under_frozen_fast":
                bool(bridge["shared_normal_form_hit"]),
            "bridge_direction": activation.get("direction"),
            "context_path": activation.get("context_path"),
            "context_depth": activation.get("context_depth"),
            "bridge_depth": activation.get("bridge_depth"),
            "introduced_term_shape": activation.get("introduced_term_shape"),
            "term_growth": activation.get("term_growth"),
            "equality_source_type": activation.get("equality_source_type"),
            "activated_rule_families":
                bridge["activated_rule_families"],
            "syntactic_activations": bridge["activation_events"],
            "productive_activations": bridge["productive_activations"],
            "normalization_suffix": activation.get("normalization_suffix", []),
            "final_normal_forms": {
                "left": row["normalization_trace"]["left_terminal"],
                "right": row["normalization_trace"]["right_terminal"],
                "best_activation_terminal": bridge["best_terminal_term"],
            },
            "divergence_frontier": row["divergence_frontier"],
            "candidate_object_kinds": [
                item["kind"] for item in row["counterfactual_objects"]
            ],
            "failure_reason": (
                None if bridge["shared_normal_form_hit"]
                else row["earliest_failure"]["exact_rejection_reason"]
                or "ACTIVATED_DISTINCT_NORMAL_FORMS"
            ),
        })
    success = [row for row in entries if row["completed_under_frozen_fast"]]
    failed = [row for row in entries if not row["completed_under_frozen_fast"]]
    shapes = Counter(
        item["kind"] for row in failed for item in
        next(
            record["counterfactual_objects"]
            for record in records
            if record["identity"]["content_sha256"] == row["content_sha256"]
        )[:1]
    )
    return {
        "schema_version": "mathgraph.bridge-activation-comparison.v1",
        "activated_rows": len(entries),
        "frozen_fast_completions": len(success),
        "frozen_fast_failures": len(failed),
        "records": entries,
        "successful_profile": {
            "directions": Counter(
                row["bridge_direction"] for row in success
            ),
            "depths": Counter(row["bridge_depth"] for row in success),
        },
        "failed_profile": {
            "directions": Counter(
                row["bridge_direction"] for row in failed
            ),
            "depths": Counter(row["bridge_depth"] for row in failed),
        },
        "failed_leading_counterfactual_kinds": shapes,
        "independence_note":
            "Metamorphic presentations are excluded from support counts.",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnostics-dir", type=Path, required=True)
    parser.add_argument("--results-dir", type=Path, required=True)
    args = parser.parse_args()
    args.diagnostics_dir.mkdir(parents=True, exist_ok=True)
    args.results_dir.mkdir(parents=True, exist_ok=True)
    module = rc.load_solver()
    source_rows = load_rows()
    records = []
    for index, row in enumerate(source_rows, 1):
        print(f"[{index}/{len(source_rows)}] {row['origin']} {row['id']}", flush=True)
        record = rc.characterize(module, row)
        if record["diagnostic_seconds"] > 3.5:
            record["limitations"].append("DIAGNOSTIC_WALL_CAP_OVERRUN")
        records.append(record)

    seed = hashlib.sha256(
        b"c1e23ab86f24ed1105b5c3157e7859d77178e298"
        b"residual-characterization-discovery-v1"
    ).hexdigest()
    clusters = rc.cluster_discovery(records, seed, bootstrap_replicates=1000)
    for row in records:
        digest = row["identity"]["content_sha256"]
        row["cluster_assignment"]["hierarchical"] = (
            clusters["hierarchical"]["assignments"][digest]
        )
    objects = [
        {
            "content_sha256": row["identity"]["content_sha256"],
            "source_group_sha256": row["provenance"]["source_group_sha256"],
            "objects": [compact_object(item) for item in
                        row["counterfactual_objects"]],
        }
        for row in records
    ]
    features = [
        {
            "content_sha256": row["identity"]["content_sha256"],
            "source_group_sha256": row["provenance"]["source_group_sha256"],
            "features": row["structural_features"],
            "primary_obstruction": row["primary_obstruction"],
            "cluster_assignment": row["cluster_assignment"],
        }
        for row in records
    ]
    class_summary = rc.summarize_classes(records)
    leading = max(
        class_summary,
        key=lambda key: (
            class_summary[key]["count"], -int(key[1:])
        ),
    )
    clusters["rule_based_distribution"] = class_summary
    clusters["dominant_rule_class"] = leading
    clusters["dominant_family_bootstrap_95"] = rc.family_bootstrap(
        records, leading, seed
    )
    clusters["feature_ablations"] = rc.ablation_stability(records, clusters)
    clusters["source_family_leakage"] = rc.source_family_leakage(records)
    clusters["created_at_utc"] = now()
    clusters["solver_sha256"] = rc.SOLVER_SHA256

    outputs = {
        "residual_discovery_records.json": {
            "schema_version": rc.SCHEMA_VERSION,
            "created_at_utc": now(),
            "solver_sha256": rc.SOLVER_SHA256,
            "rows": records,
        },
        "residual_discovery_candidate_objects.json": {
            "schema_version": "mathgraph.counterfactual-objects.v1",
            "trust_status": "CANDIDATE",
            "rows": objects,
        },
        "residual_discovery_features.json": {
            "schema_version": "mathgraph.residual-features.v1",
            "feature_names": list(rc.FEATURE_NAMES),
            "rows": features,
        },
        "residual_discovery_clusters.json": clusters,
    }
    for name, payload in outputs.items():
        (args.diagnostics_dir / name).write_text(
            json.dumps(payload, indent=2, sort_keys=True)
        )
    comparison = activation_comparison(records)
    (args.results_dir / "bridge_activation_trace_comparison.json").write_text(
        json.dumps(comparison, indent=2, sort_keys=True)
    )
    print(json.dumps({
        "rows": len(records),
        "origins": dict(Counter(
            row["provenance"]["origin"] for row in records
        )),
        "activations": comparison["activated_rows"],
        "dominant_class": leading,
        "selected_k": clusters["selected_k"],
        "hierarchical_k": clusters["hierarchical"]["selected_k"],
    }, indent=2))


if __name__ == "__main__":
    main()
