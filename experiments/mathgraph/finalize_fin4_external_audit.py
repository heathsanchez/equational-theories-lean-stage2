#!/usr/bin/env python3
"""Merge post-audit production and metamorphic validation into the summary."""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"
BASELINE = ROOT / "experiments/mathgraph/results/fin3_final/sample_200.json"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def finite_metrics(row):
    records = []
    for event in row.get("log", []):
        if event.get("type") != "solver_stderr":
            continue
        for line in event.get("tail", "").splitlines():
            if not line.startswith("MATHGRAPH_METRICS "):
                continue
            try:
                record = json.loads(line.split(" ", 1)[1])
            except json.JSONDecodeError:
                continue
            if record.get("portfolio", "").startswith("fin4-"):
                records.append(record)
    return records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--production", type=Path, required=True)
    parser.add_argument("--metamorphic", type=Path, required=True)
    parser.add_argument("--implementation-commit", required=True)
    args = parser.parse_args()
    summary = json.loads(args.summary.read_text(encoding="utf-8"))
    production = json.loads(args.production.read_text(encoding="utf-8"))
    baseline = {
        row["id"]: row
        for row in json.loads(BASELINE.read_text(encoding="utf-8"))
    }
    metamorphic = json.loads(args.metamorphic.read_text(encoding="utf-8"))
    true_count = sum(
        row.get("solved") and row.get("verdict") == "true"
        for row in production
    )
    false_count = sum(
        row.get("solved") and row.get("verdict") == "false"
        for row in production
    )
    new_rows = [
        row for row in production
        if row.get("solved") and not baseline[row["id"]].get("solved")
    ]
    rejected = Counter()
    llm_calls = 0
    attempts = []
    for row in production:
        llm_calls += row.get("llm_calls", 0)
        attempts.extend(finite_metrics(row))
        for event in row.get("log", []):
            if event.get("type") != "judge":
                continue
            status = event.get("response", {}).get("status", "unparsed")
            if status != "accepted":
                rejected[status] += 1
    unresolved = [row for row in production if not row.get("solved")]
    metric_fields = (
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
        "symmetry_branch_prunes",
        "source_models",
    )
    totals = {
        field: sum(item.get(field, 0) or 0 for item in attempts)
        for field in metric_fields
    }
    totals["attempts"] = len(attempts)
    totals["hits"] = sum(item.get("found", False) for item in attempts)
    totals["maximum_depth"] = max(
        (item.get("maximum_depth", 0) for item in attempts), default=0
    )
    summary["implementation_commit"] = args.implementation_commit
    summary["final_solver"] = {
        "sha256": sha256(SOLVER),
        "size_bytes": SOLVER.stat().st_size,
        "promoted_portfolio": ["fin4-probe"],
    }
    summary["metamorphic"] = {
        "artifact_sha256": sha256(args.metamorphic),
        "audit_hits": metamorphic["hit_count"],
        "variants_per_hit": metamorphic["variants_per_hit"],
        "constructed_certificates_accepted":
            metamorphic["official_constructed_certificates_accepted"],
        "search_presentations_found":
            metamorphic["search_presentations_found"],
        "search_presentations_attempted":
            metamorphic["search_presentations_attempted"],
        "failures": metamorphic["failures"],
    }
    paired_runtime = round(sum(
        row.get("elapsed_seconds", 0) for row in production
    ), 6)
    summary["production_regression"] = {
        "artifact_sha256": sha256(args.production),
        "accepted_true": true_count,
        "accepted_false": false_count,
        "total": true_count + false_count,
        "unresolved": len(unresolved),
        "new_fin4_false": len(new_rows),
        "new_constructor": "fin4-probe",
        "runtime_seconds": paired_runtime,
        "authoritative_baseline_runtime_seconds": 318.92,
        "runtime_increase_seconds": round(paired_runtime - 318.92, 6),
        "seconds_per_added_acceptance": round(
            (paired_runtime - 318.92) / len(new_rows), 6
        ),
        "paired_clean_disabled_runtime_seconds": 314.4,
        "paired_runtime_increase_seconds": round(
            paired_runtime - 314.4, 6
        ),
        "paired_seconds_per_added_acceptance": round(
            (paired_runtime - 314.4) / len(new_rows), 6
        ),
        "invalid_outcomes": dict(rejected),
        "llm_calls": llm_calls,
        "remaining_known_true": sum(
            row["id"].startswith("true_") for row in unresolved
        ),
        "remaining_known_false": sum(
            row["id"].startswith("false_") for row in unresolved
        ),
        "fin4_metrics": totals,
    }
    checks = summary["preregistered_promotion"]["checks"]
    checks["production_floor_preserved"] = (
        true_count >= 66 and false_count >= 94 and true_count + false_count >= 160
        and not rejected and llm_calls == 0
    )
    summary["preregistered_promotion"]["final_passed"] = all(
        checks.values()
    )
    summary["official_gates"] = {
        "solo": "66/66",
        "marathon": "25/25",
        "finite_model_engine_suite": "pass",
        "fin4_suite": "17 positive certificates accepted",
        "equality_chain_suite": "9/9",
        "source_reentry_suite":
            "8 TRUE, 2 FALSE, 1 expected abstention",
        "contextual_research_suite":
            "12 TRUE, 3 FALSE, 1 expected bounded abstention",
        "sample_20": {
            "accepted_true": 1,
            "accepted_false": 10,
            "unresolved": 9,
            "invalid_outcomes": 0,
        },
    }
    args.summary.write_text(
        json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(json.dumps({
        "score": f"{true_count} TRUE + {false_count} FALSE",
        "new_fin4": len(new_rows),
        "runtime": paired_runtime,
        "final_rule_passed":
            summary["preregistered_promotion"]["final_passed"],
        "solver_sha256": summary["final_solver"]["sha256"],
    }, indent=2))


if __name__ == "__main__":
    main()
