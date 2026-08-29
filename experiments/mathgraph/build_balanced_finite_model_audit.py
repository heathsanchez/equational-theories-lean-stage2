#!/usr/bin/env python3
"""Build a sealed, balanced audit without executing the Fin-4 constructor."""

import argparse
import hashlib
import importlib.util
import json
import math
import random
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"
EXPECTED_SOLVER_SHA256 = (
    "ddb646624106d143a6b0882b1ec46fa9e047dc40214310010b5dda89f55f2eb7"
)
AUTHORITATIVE_HEAD = "1e2d896f0bedc682cb1bee21717ce2d6ed3f48c8"
SEED_TEXT = AUTHORITATIVE_HEAD + "finite-model-balanced-audit-v1"
SEED_HEX = hashlib.sha256(SEED_TEXT.encode("utf-8")).hexdigest()
CORPORA = (
    Path("/Users/heath/Documents/SAIR/examples/problems/normal.jsonl"),
    Path("/Users/heath/Documents/SAIR/examples/problems/hard1.jsonl"),
    Path("/Users/heath/Documents/SAIR/examples/problems/hard2.jsonl"),
    Path("/Users/heath/Documents/SAIR/examples/problems/hard3.jsonl"),
)
MARATHON = Path(
    "/Users/heath/Documents/SAIR/examples/problems/marathon/normal_100.jsonl"
)


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    return sha256_bytes(path.read_bytes())


def load_solver():
    assert sha256_file(SOLVER) == EXPECTED_SOLVER_SHA256
    spec = importlib.util.spec_from_file_location("sealed_audit_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def normalize_equation(module, text):
    left, right, _ = module.parse_equation(text)
    return module.render_term(left) + " = " + module.render_term(right)


def normalize_pair(module, row):
    source = normalize_equation(module, row["equation1"])
    target = normalize_equation(module, row["equation2"])
    digest = sha256_bytes((source + "\0" + target).encode("utf-8"))
    return source, target, digest


def json_rows(path):
    if path.suffix == ".jsonl":
        return [
            json.loads(line)
            for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
    value = json.loads(path.read_text(encoding="utf-8"))
    return value if isinstance(value, list) else []


def term_depth(term):
    if term[0] == "var":
        return 0
    return 1 + max(term_depth(term[1]), term_depth(term[2]))


def variable_counts(term, counts):
    if term[0] == "var":
        counts[term[1]] += 1
        return
    variable_counts(term[1], counts)
    variable_counts(term[2], counts)


def root_profile(module, compiled, order):
    direct = 0
    nested = 0
    for assignment in module.product(
        range(order), repeat=len(compiled[3])
    ):
        values = []
        for node in compiled[0]:
            if node[0] == "variable":
                values.append((1 << assignment[node[1]], None))
                continue
            left = values[node[1]][0]
            right = values[node[2]][0]
            left_value = module.singleton_value(left)
            right_value = module.singleton_value(right)
            cell = (
                order * left_value + right_value
                if left_value is not None and right_value is not None
                else None
            )
            values.append(((1 << order) - 1, cell))
        for root in compiled[1:3]:
            if values[root][1] is None:
                nested += 1
            else:
                direct += 1
    return direct, nested


def structural_features(module, source_text, target_text):
    source = module.parse_equation(source_text)
    target = module.parse_equation(target_text)
    source_compiled = module.compile_equation(source)
    target_compiled = module.compile_equation(target)
    source_counts = Counter()
    target_counts = Counter()
    variable_counts(source[0], source_counts)
    variable_counts(source[1], source_counts)
    variable_counts(target[0], target_counts)
    variable_counts(target[1], target_counts)
    direct, nested = root_profile(module, source_compiled, 3)
    return {
        "source_variables": len(source[2]),
        "target_variables": len(target[2]),
        "source_nodes": len(source_compiled[0]),
        "target_nodes": len(target_compiled[0]),
        "source_depth": max(term_depth(source[0]), term_depth(source[1])),
        "target_depth": max(term_depth(target[0]), term_depth(target[1])),
        "source_repetition": sorted(source_counts.values(), reverse=True),
        "target_repetition": sorted(target_counts.values(), reverse=True),
        "source_assignments_fin2": 2 ** len(source[2]),
        "source_assignments_fin3": 3 ** len(source[2]),
        "direct_root_constraints": direct,
        "nested_root_constraints": nested,
    }


def fin2_profile(module, source, target):
    source_models = 0
    countermodels = 0
    for encoded in range(2 ** 4):
        table = tuple((encoded >> shift) & 1 for shift in range(4))
        rows = [list(table[:2]), list(table[2:])]
        if module.equation_holds(source, rows) is True:
            source_models += 1
            if module.equation_holds(target, rows) is False:
                countermodels += 1
    return source_models, countermodels


def fin3_complete_profile(module, source, target):
    engine = module.FiniteModelEngine(
        3,
        source,
        target,
        module.time.monotonic() + 4.0,
        0,
        64,
    )
    found = engine.search_complete_enumeration(canonical_only=True)
    assert engine.complete or found is not None
    return {
        "countermodel": found is not None,
        "source_models_before_hit": engine.source_models,
        "complete_tables": engine.complete_tables,
        "complete": engine.complete,
    }


def add_provenance(module, registry, row, origin, usage):
    if not isinstance(row, dict):
        return
    if not isinstance(row.get("equation1"), str) or not isinstance(
        row.get("equation2"), str
    ):
        return
    try:
        source, target, digest = normalize_pair(module, row)
    except Exception:
        return
    entry = registry.setdefault(digest, {
        "normalized_source": source,
        "normalized_target": target,
        "pair_content_hash": digest,
        "origins": [],
        "solver_run": False,
        "fin4_run": False,
        "label_observed": False,
        "used_for_tuning": False,
        "used_only_for_final_evaluation": False,
    })
    if origin not in entry["origins"]:
        entry["origins"].append(origin)
    for key, value in usage.items():
        entry[key] = entry.get(key, False) or bool(value)


def build_provenance(module):
    registry = {}
    sources = []
    sample_files = (
        ROOT / "examples/problems/sample_20.json",
        ROOT / "examples/problems/sample_200.json",
    )
    for path in sample_files:
        rows = json_rows(path)
        sources.append({"path": str(path), "rows": len(rows)})
        for row in rows:
            add_provenance(module, registry, row, str(path), {
                "solver_run": True,
                "fin4_run": path.name == "sample_200.json",
                "label_observed": True,
                "used_for_tuning": path.name == "sample_200.json",
                "used_only_for_final_evaluation": path.name == "sample_20.json",
            })
    for path in sorted((ROOT / "experiments/mathgraph/regressions").glob(
        "*_cases.json"
    )):
        rows = json_rows(path)
        sources.append({"path": str(path), "rows": len(rows)})
        for row in rows:
            add_provenance(module, registry, row, str(path), {
                "solver_run": True,
                "fin4_run": True,
                "label_observed": True,
                "used_for_tuning": True,
            })
    marathon_rows = json_rows(MARATHON)
    sources.append({
        "path": str(MARATHON),
        "rows": len(marathon_rows),
        "treatment": "excluded_uncertain_harness_exposure",
    })
    for row in marathon_rows:
        add_provenance(module, registry, row, str(MARATHON), {
            "solver_run": True,
            "fin4_run": False,
            "label_observed": True,
            "used_for_tuning": False,
        })
    # Historical result JSON is scanned recursively for embedded equations.
    for path in sorted((ROOT / "experiments/mathgraph/results").rglob("*.json")):
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        stack = [value]
        found = 0
        while stack:
            item = stack.pop()
            if isinstance(item, dict):
                if "equation1" in item and "equation2" in item:
                    add_provenance(module, registry, item, str(path), {
                        "solver_run": True,
                        "fin4_run": True,
                        "label_observed": True,
                        "used_for_tuning": True,
                    })
                    found += 1
                stack.extend(item.values())
            elif isinstance(item, list):
                stack.extend(item)
        if found:
            sources.append({"path": str(path), "embedded_pairs": found})
    for entry in registry.values():
        entry["origins"].sort()
    return registry, sources


def repetition_distance(left, right):
    size = max(len(left), len(right))
    return sum(
        abs(
            (left[index] if index < len(left) else 0)
            - (right[index] if index < len(right) else 0)
        )
        for index in range(size)
    )


def match_distance(false_row, true_row):
    left = false_row["features"]
    right = true_row["features"]
    distance = (
        4 * abs(left["source_variables"] - right["source_variables"])
        + 3 * abs(left["target_variables"] - right["target_variables"])
        + 2 * abs(left["source_depth"] - right["source_depth"])
        + 2 * abs(left["target_depth"] - right["target_depth"])
        + abs(left["source_nodes"] - right["source_nodes"]) / 3
        + abs(left["target_nodes"] - right["target_nodes"]) / 3
        + repetition_distance(
            left["source_repetition"], right["source_repetition"]
        )
        + repetition_distance(
            left["target_repetition"], right["target_repetition"]
        )
        + abs(left["fin2_source_models"] - right["fin2_source_models"]) / 4
        + abs(
            left["fin3_source_models"] - right["fin3_source_models"]
        ) / 8
        + 3 * (
            left["fin3_source_phenotype"]
            != right["fin3_source_phenotype"]
        )
    )
    return round(distance, 6)


def structural_bucket(features):
    return (
        min(features["source_variables"], 3),
        min(features["target_variables"], 4),
        min(features["source_depth"], 4),
        int(max(features["source_repetition"], default=1) > 1),
        features["fin3_source_phenotype"],
    )


def round_robin_diverse(rows, limit, seed):
    buckets = {}
    for row in rows:
        buckets.setdefault(structural_bucket(row["features"]), []).append(row)
    for bucket, values in buckets.items():
        values.sort(
            key=lambda row: sha256_bytes(
                (seed + repr(bucket) + row["pair_content_hash"]).encode()
            )
        )
    selected = []
    offset = 0
    ordered_buckets = sorted(buckets)
    while len(selected) < limit and any(
        offset < len(buckets[bucket]) for bucket in ordered_buckets
    ):
        for bucket in ordered_buckets:
            values = buckets[bucket]
            if offset < len(values):
                selected.append(values[offset])
                if len(selected) == limit:
                    break
        offset += 1
    return selected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--target-per-label", type=int, default=40)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    module = load_solver()
    built_at = utc_now()
    registry, provenance_sources = build_provenance(module)
    used_hashes = set(registry)
    candidate_rows = []
    exclusions = Counter()
    corpus_manifest = []
    seen_candidates = set()
    for path in CORPORA:
        rows = json_rows(path)
        corpus_manifest.append({
            "path": str(path),
            "sha256": sha256_file(path),
            "rows": len(rows),
        })
        for row in rows:
            try:
                source_text, target_text, digest = normalize_pair(module, row)
            except Exception:
                exclusions["parse_failure"] += 1
                continue
            if digest in used_hashes:
                exclusions["prior_content_hash"] += 1
                continue
            if digest in seen_candidates:
                exclusions["duplicate_candidate_hash"] += 1
                continue
            seen_candidates.add(digest)
            candidate_rows.append({
                "original_id": row.get("id"),
                "origin": str(path),
                "source": source_text,
                "target": target_text,
                "pair_content_hash": digest,
                "label": bool(row["answer"]),
            })
    # Features and exact Fin-2 phenotype are cheap enough for every candidate.
    for index, row in enumerate(candidate_rows, 1):
        if index % 100 == 0:
            print(f"structural/Fin2 {index}/{len(candidate_rows)}", flush=True)
        features = structural_features(module, row["source"], row["target"])
        source = module.parse_equation(row["source"])
        target = module.parse_equation(row["target"])
        source_models, countermodels = fin2_profile(module, source, target)
        features["fin2_source_models"] = source_models
        features["fin2_countermodels"] = countermodels
        features["fin2_phenotype"] = (
            "countermodel" if countermodels else
            "source_models_target_holds" if source_models else
            "no_source_model"
        )
        row["features"] = features

    # FALSE opportunities are selected without Fin-4: require exhaustive
    # absence of an order-2 and order-3 countermodel.
    false_candidates = [
        row for row in candidate_rows
        if not row["label"] and row["features"]["fin2_countermodels"] == 0
    ]
    false_candidates.sort(
        key=lambda row: sha256_bytes(
            (SEED_HEX + row["pair_content_hash"]).encode()
        )
    )
    opportunities = []
    for index, row in enumerate(false_candidates, 1):
        print(
            f"Fin3 FALSE screen {index}/{len(false_candidates)}", flush=True
        )
        source = module.parse_equation(row["source"])
        target = module.parse_equation(row["target"])
        profile = fin3_complete_profile(module, source, target)
        row["features"]["fin3_countermodel"] = profile["countermodel"]
        row["features"]["fin3_source_models"] = profile[
            "source_models_before_hit"
        ]
        row["features"]["fin3_source_phenotype"] = (
            "countermodel" if profile["countermodel"] else
            "source_models_target_holds"
            if profile["source_models_before_hit"] else
            "no_source_model"
        )
        if not profile["countermodel"]:
            opportunities.append(row)

    selected_false = round_robin_diverse(
        opportunities, min(args.target_per_label, len(opportunities)), SEED_HEX
    )
    if not selected_false:
        raise RuntimeError("no unused FALSE opportunities")

    # Structural nearest-neighbour shortlist, then exact Fin-3 source
    # phenotype before final deterministic matching.
    true_pool = [row for row in candidate_rows if row["label"]]
    shortlist = {}
    for false_row in selected_false:
        provisional = []
        false_features = false_row["features"]
        for true_row in true_pool:
            true_features = true_row["features"]
            distance = (
                4 * abs(
                    false_features["source_variables"]
                    - true_features["source_variables"]
                )
                + 3 * abs(
                    false_features["target_variables"]
                    - true_features["target_variables"]
                )
                + 2 * abs(
                    false_features["source_depth"]
                    - true_features["source_depth"]
                )
                + 2 * abs(
                    false_features["target_depth"]
                    - true_features["target_depth"]
                )
                + abs(
                    false_features["source_nodes"]
                    - true_features["source_nodes"]
                ) / 3
                + abs(
                    false_features["target_nodes"]
                    - true_features["target_nodes"]
                ) / 3
            )
            provisional.append((
                distance,
                sha256_bytes(
                    (
                        SEED_HEX
                        + false_row["pair_content_hash"]
                        + true_row["pair_content_hash"]
                    ).encode()
                ),
                true_row,
            ))
        for _, _, true_row in sorted(provisional)[:8]:
            shortlist[true_row["pair_content_hash"]] = true_row
    for index, row in enumerate(shortlist.values(), 1):
        print(f"Fin3 TRUE match {index}/{len(shortlist)}", flush=True)
        source = module.parse_equation(row["source"])
        target = module.parse_equation(row["target"])
        profile = fin3_complete_profile(module, source, target)
        if profile["countermodel"]:
            # A trusted TRUE label conflicting with an official finite
            # countermodel is excluded rather than silently reclassified.
            exclusions["trusted_label_countermodel_conflict"] += 1
            row["excluded"] = True
            continue
        row["features"]["fin3_countermodel"] = False
        row["features"]["fin3_source_models"] = profile[
            "source_models_before_hit"
        ]
        row["features"]["fin3_source_phenotype"] = (
            "source_models_target_holds"
            if profile["source_models_before_hit"] else
            "no_source_model"
        )

    available_true = [
        row for row in shortlist.values() if not row.get("excluded")
    ]
    used_true = set()
    matches = []
    for false_row in selected_false:
        choices = [
            (
                match_distance(false_row, true_row),
                sha256_bytes(
                    (
                        SEED_HEX
                        + false_row["pair_content_hash"]
                        + true_row["pair_content_hash"]
                    ).encode()
                ),
                true_row,
            )
            for true_row in available_true
            if true_row["pair_content_hash"] not in used_true
        ]
        if not choices:
            break
        distance, _, true_row = min(choices)
        used_true.add(true_row["pair_content_hash"])
        matches.append((false_row, true_row, distance))
    selected_false = [item[0] for item in matches]
    selected_true = [item[1] for item in matches]

    rng = random.Random(int(SEED_HEX, 16))
    audit_rows = []
    labels = {}
    matching = {}
    for false_row, true_row, distance in matches:
        for row in (false_row, true_row):
            opaque = "audit_" + sha256_bytes(
                (
                    SEED_HEX + "opaque-id" + row["pair_content_hash"]
                ).encode()
            )[:20]
            audit_rows.append({
                "id": opaque,
                "eq1_id": 960000 + int(row["pair_content_hash"][:6], 16),
                "eq2_id": 980000 + int(row["pair_content_hash"][6:12], 16),
                "equation1": row["source"],
                "equation2": row["target"],
                "content_sha256": row["pair_content_hash"],
                "stratum": row["features"],
            })
            labels[opaque] = row["label"]
        matching[false_row["pair_content_hash"]] = {
            "true_content_sha256": true_row["pair_content_hash"],
            "distance": distance,
        }
    rng.shuffle(audit_rows)
    inputs_path = args.output_dir / "balanced_audit_inputs.json"
    labels_path = args.output_dir / "balanced_audit_labels.sealed.json"
    provenance_path = args.output_dir / "finite_model_provenance.json"
    manifest_path = args.output_dir / "balanced_audit_manifest.json"
    inputs_payload = {
        "audit_version": "finite-model-balanced-audit-v1",
        "built_at_utc": built_at,
        "seed_sha256": SEED_HEX,
        "rows": audit_rows,
    }
    labels_payload = {
        "audit_version": "finite-model-balanced-audit-v1",
        "sealed_at_utc": utc_now(),
        "integrity_note": (
            "Plaintext experimental seal. The runner has no label input; "
            "this is not cryptographic protection against a malicious operator."
        ),
        "labels": labels,
    }
    provenance_payload = {
        "created_at_utc": utc_now(),
        "normalization": "parse then canonical render; ordered source-target pair",
        "sources_scanned": provenance_sources,
        "previously_used_pair_count": len(registry),
        "entries": sorted(
            registry.values(), key=lambda item: item["pair_content_hash"]
        ),
    }
    inputs_path.write_text(
        json.dumps(inputs_payload, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    labels_path.write_text(
        json.dumps(labels_payload, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    provenance_path.write_text(
        json.dumps(provenance_payload, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    distances = [item[2] for item in matches]
    manifest = {
        "created_at_utc": utc_now(),
        "authoritative_head": AUTHORITATIVE_HEAD,
        "frozen_solver_sha256": EXPECTED_SOLVER_SHA256,
        "seed_derivation": (
            "SHA256(authoritative_head || "
            "'finite-model-balanced-audit-v1')"
        ),
        "seed_sha256": SEED_HEX,
        "audit_type_if_valid": (
            "external-large" if len(matches) >= 40 else
            "external-small" if len(matches) >= 10 else
            "insufficient"
        ),
        "corpora": corpus_manifest,
        "candidate_rows_after_hash_exclusion": len(candidate_rows),
        "false_no_fin2_candidates": len(false_candidates),
        "false_no_order_le_3_opportunities": len(opportunities),
        "selected_false": len(selected_false),
        "selected_true": len(selected_true),
        "exclusions": dict(sorted(exclusions.items())),
        "matching": {
            "method": "deterministic greedy nearest neighbour",
            "mean_distance": (
                round(sum(distances) / len(distances), 6)
                if distances else None
            ),
            "median_distance": (
                sorted(distances)[len(distances) // 2]
                if distances else None
            ),
            "maximum_distance": max(distances) if distances else None,
            "exact_structural_bucket_matches": sum(
                structural_bucket(left["features"])
                == structural_bucket(right["features"])
                for left, right, _ in matches
            ),
            "pairs": matching,
        },
        "inputs_sha256": sha256_file(inputs_path),
        "sealed_labels_sha256": sha256_file(labels_path),
        "provenance_sha256": sha256_file(provenance_path),
        "labels_must_not_be_loaded_before_result_hash": True,
        "fin4_used_during_build": False,
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(json.dumps({
        "audit_type": manifest["audit_type_if_valid"],
        "previously_used_pairs": len(registry),
        "candidates": len(candidate_rows),
        "opportunities": len(opportunities),
        "selected_false": len(selected_false),
        "selected_true": len(selected_true),
        "inputs_sha256": manifest["inputs_sha256"],
        "labels_sha256": manifest["sealed_labels_sha256"],
    }, indent=2))


if __name__ == "__main__":
    main()
