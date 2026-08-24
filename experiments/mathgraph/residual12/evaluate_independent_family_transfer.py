#!/usr/bin/env python3
"""Reveal sealed labels only after the raw transfer result has been hashed."""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


EXPECTED_INPUT_SHA256 = "075f7a3b8d0dd389c2d2a12d444af435eb921f622954185cb3d0f867d7cdb503"
EXPECTED_LABEL_SHA256 = "5c07bcfe3659f7abfa14b2594000bee01cb9618aed5901941b6dd67c771d987a"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valid_hit(attempt):
    return (
        attempt.get("found") is True
        and attempt.get("root_matches") is True
        and attempt.get("replayed") is True
        and attempt.get("certificate_bytes", 100001) <= 100000
        and attempt.get("judge_status") == "accepted"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--raw-hash", type=Path, required=True)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--labels", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if digest(args.inputs) != EXPECTED_INPUT_SHA256:
        raise SystemExit("frozen inputs changed")
    if digest(args.labels) != EXPECTED_LABEL_SHA256:
        raise SystemExit("sealed labels changed")
    raw_sha256 = digest(args.raw)
    recorded = args.raw_hash.read_text(encoding="utf-8").split()[0]
    if raw_sha256 != recorded:
        raise SystemExit("raw result changed after pre-reveal hash")
    raw = json.loads(args.raw.read_text(encoding="utf-8"))
    labels = json.loads(args.labels.read_text(encoding="utf-8"))["labels"]
    if set(labels) != {row["id"] for row in raw["rows"]}:
        raise SystemExit("raw rows and sealed labels differ")
    hits = {"3": [], "5": []}
    invalid_internal_hits = []
    for row in raw["rows"]:
        for budget in ("3", "5"):
            attempt = row["attempts"][budget]
            if attempt.get("found") and not valid_hit(attempt):
                invalid_internal_hits.append({"id": row["id"], "budget": budget})
            if valid_hit(attempt):
                hits[budget].append({
                    "id": row["id"], "label": labels[row["id"]],
                    "source_family": row["source_family"],
                    "source_law_id": row["source_law_id"],
                })
    true_hits = {b: [h for h in hs if h["label"]] for b, hs in hits.items()}
    false_hits = {b: [h for h in hs if not h["label"]] for b, hs in hits.items()}
    ids3 = {h["id"] for h in true_hits["3"]}
    five_only = [h for h in true_hits["5"] if h["id"] not in ids3]
    families = sorted({h["source_family"] for h in true_hits["5"]})
    source_laws = sorted({h["source_law_id"] for h in true_hits["5"]})
    valid_boundary = not invalid_internal_hits and not false_hits["3"] and not false_hits["5"]
    transfer = valid_boundary and bool(true_hits["5"])
    result = {
        "schema": "mathgraph.residual12-independent-family-evaluation.v1",
        "raw_result_sha256_before_label_reveal": raw_sha256,
        "inputs_sha256": EXPECTED_INPUT_SHA256,
        "labels_sha256": EXPECTED_LABEL_SHA256,
        "counts": {
            "labels": dict(Counter(str(v).lower() for v in labels.values())),
            "true_hits_3s": len(true_hits["3"]),
            "true_hits_5s": len(true_hits["5"]),
            "five_second_only_true_hits": len(five_only),
            "false_hits_3s": len(false_hits["3"]),
            "false_hits_5s": len(false_hits["5"]),
            "invalid_internal_hits": len(invalid_internal_hits),
            "true_hit_families_5s": len(families),
            "true_hit_source_laws_5s": len(source_laws),
        },
        "true_hits": true_hits,
        "five_second_only_true_hits": five_only,
        "false_hits": false_hits,
        "invalid_internal_hits": invalid_internal_hits,
        "families_with_true_transfer": families,
        "decision": {
            "valid_boundary": valid_boundary,
            "cross_family_transfer_observed": transfer,
            "budget_margin_observed": valid_boundary and bool(five_only),
            "next_action": (
                "run_full_800_budget_delta" if transfer
                else "map_selection_frontier_without_promotion"
            ) if valid_boundary else "stop_for_soundness_or_verifier_failure",
        },
    }
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(result["counts"], sort_keys=True))
    if not valid_boundary:
        raise SystemExit("frozen soundness/verifier boundary failed")


if __name__ == "__main__":
    main()
