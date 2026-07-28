#!/usr/bin/env python3
"""Build a sealed 100+100 order-5 forward-demodulation transfer audit."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import random
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
CORPUS = Path("/Users/heath/Desktop/LOGOS Papers/Maths Derivations/hard5.jsonl")
HELDOUT = (
    Path("/tmp/mathgraph-transfer-provenance/order5_strict.json"),
    Path("/tmp/mathgraph-transfer-provenance/order5_fresh.json"),
)
SEED = hashlib.sha256(
    (
        "69112a31f1e2500b82362c63da4cd0c9719265de"
        "scheduler-local-demodulation-transfer-v2"
    ).encode()
).hexdigest()


def load_solver():
    spec = importlib.util.spec_from_file_location("transfer_builder_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize(module, text):
    equation = module.parse_equation(text)
    return module.render_term(equation[0]) + " = " + module.render_term(equation[1])


def digest(module, row):
    source = normalize(module, row["equation1"])
    target = normalize(module, row["equation2"])
    return source, target, hashlib.sha256((source + "\0" + target).encode()).hexdigest()


def term_depth(term):
    return 0 if term[0] == "var" else 1 + max(
        term_depth(term[1]), term_depth(term[2])
    )


def repetitions(term, output):
    if term[0] == "var":
        output[term[1]] += 1
    else:
        repetitions(term[1], output)
        repetitions(term[2], output)


def features(module, source_text, target_text):
    source = module.parse_equation(source_text)
    target = module.parse_equation(target_text)
    source_repetitions = Counter()
    target_repetitions = Counter()
    for term in source[:2]:
        repetitions(term, source_repetitions)
    for term in target[:2]:
        repetitions(term, target_repetitions)
    return {
        "source_variables": len(source[2]),
        "target_variables": len(target[2]),
        "source_size": sum(module.term_size(term) for term in source[:2]),
        "target_size": sum(module.term_size(term) for term in target[:2]),
        "source_depth": max(term_depth(term) for term in source[:2]),
        "target_depth": max(term_depth(term) for term in target[:2]),
        "source_repetition": sorted(source_repetitions.values(), reverse=True),
        "target_repetition": sorted(target_repetitions.values(), reverse=True),
    }


def distance(left, right):
    score = 0
    for key, weight in (
        ("source_variables", 5),
        ("target_variables", 4),
        ("source_size", 1),
        ("target_size", 1),
        ("source_depth", 3),
        ("target_depth", 3),
    ):
        score += weight * abs(left[key] - right[key])
    score += abs(
        sum(left["source_repetition"]) - sum(right["source_repetition"])
    )
    score += abs(
        sum(left["target_repetition"]) - sum(right["target_repetition"])
    )
    return score


def previous_hashes(module):
    used = set()
    input_paths = list(
        (ROOT / "experiments/mathgraph/audits").glob("*inputs.json")
    ) + list(
        (ROOT / "experiments/mathgraph/paramodulator_control").glob(
            "**/transfer_audit_inputs.json"
        )
    )
    for path in input_paths:
        try:
            payload = json.loads(path.read_text())
        except (json.JSONDecodeError, OSError):
            continue
        rows = payload.get("rows", payload) if isinstance(payload, dict) else payload
        for row in rows:
            if isinstance(row, dict) and "equation1" in row:
                used.add(digest(module, row)[2])
    for path in HELDOUT:
        payload = json.loads(path.read_text())
        rows = payload.get("problems", payload) if isinstance(payload, dict) else payload
        for row in rows:
            if "equation1" in row:
                used.add(digest(module, row)[2])
    residuals = Path("/tmp/mathgraph-six-residuals.json")
    if residuals.exists():
        payload = json.loads(residuals.read_text())
        rows = payload.get("rows", payload) if isinstance(payload, dict) else payload
        for row in rows:
            used.add(digest(module, row)[2])
    return used


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--per-label", type=int, default=100)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    module = load_solver()
    used = previous_hashes(module)
    candidates = []
    excluded = Counter()
    for line in CORPUS.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        source, target, content_hash = digest(module, row)
        if content_hash in used:
            excluded["prior_content_hash"] += 1
            continue
        candidates.append({
            "source": source,
            "target": target,
            "content_sha256": content_hash,
            "label": bool(row["answer"]),
            "eq1_id": row.get("eq1_id", row.get("equation1_id")),
            "eq2_id": row.get("eq2_id", row.get("equation2_id")),
            "features": features(module, source, target),
        })
    rng = random.Random(SEED)
    true_pool = [row for row in candidates if row["label"]]
    false_pool = [row for row in candidates if not row["label"]]
    true_pool.sort(key=lambda row: row["content_sha256"])
    rng.shuffle(true_pool)
    selected_true = true_pool[:args.per_label]
    available_false = {row["content_sha256"]: row for row in false_pool}
    selected_false = []
    matching_distances = []
    for true_row in selected_true:
        match = min(
            available_false.values(),
            key=lambda row: (
                distance(true_row["features"], row["features"]),
                row["content_sha256"],
            ),
        )
        matching_distances.append(distance(true_row["features"], match["features"]))
        selected_false.append(match)
        del available_false[match["content_sha256"]]
    selected = selected_true + selected_false
    selected.sort(
        key=lambda row: hashlib.sha256(
            (SEED + row["content_sha256"]).encode()
        ).hexdigest()
    )
    input_rows = []
    labels = {}
    for row in selected:
        opaque = "demod_" + hashlib.sha256(
            (SEED + "opaque" + row["content_sha256"]).encode()
        ).hexdigest()[:20]
        input_rows.append({
            "id": opaque,
            "eq1_id": row["eq1_id"],
            "eq2_id": row["eq2_id"],
            "equation1": row["source"],
            "equation2": row["target"],
            "content_sha256": row["content_sha256"],
            "matching_features": row["features"],
        })
        labels[opaque] = row["label"]
    inputs_path = args.output_dir / "transfer_audit_inputs.json"
    labels_path = args.output_dir / "transfer_audit_labels.sealed.json"
    manifest_path = args.output_dir / "transfer_audit_manifest.json"
    inputs_path.write_text(json.dumps({"rows": input_rows}, indent=2) + "\n")
    labels_path.write_text(json.dumps({"labels": labels}, indent=2) + "\n")
    manifest = {
        "schema": "mathgraph.forward-demodulation-transfer-manifest.v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "seed_sha256": SEED,
        "corpus": str(CORPUS),
        "corpus_sha256": sha256(CORPUS),
        "candidate_rows": len(candidates),
        "excluded": dict(excluded),
        "selected_true": len(selected_true),
        "selected_false": len(selected_false),
        "matching": {
            "mean_distance": sum(matching_distances) / len(matching_distances),
            "maximum_distance": max(matching_distances),
        },
        "inputs_sha256": sha256(inputs_path),
        "labels_sha256": sha256(labels_path),
        "labels_not_for_runner": True,
    }
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
