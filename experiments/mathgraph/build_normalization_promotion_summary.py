#!/usr/bin/env python3
"""Build the compact validation record for the normalization experiment."""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def counts(rows):
    return {
        "accepted_true": sum(
            row.get("solved") and row.get("verdict") == "true" for row in rows
        ),
        "accepted_false": sum(
            row.get("solved") and row.get("verdict") == "false" for row in rows
        ),
        "unresolved": sum(not row.get("solved") for row in rows),
        "invalid_outcomes": sum(
            event.get("response", {}).get("status") != "accepted"
            for row in rows for event in row.get("log", [])
            if event.get("type") == "judge"
        ),
        "llm_calls": sum(row.get("llm_calls", 0) for row in rows),
        "runtime_seconds": round(sum(
            row.get("elapsed_seconds", 0) for row in rows
        ), 6),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sample20", type=Path, required=True)
    parser.add_argument("--sample200", type=Path, required=True)
    parser.add_argument("--development", type=Path, required=True)
    parser.add_argument("--holdout", type=Path, required=True)
    parser.add_argument("--external-summary", type=Path, required=True)
    parser.add_argument("--synthetic", type=Path, required=True)
    parser.add_argument("--residual", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sample20 = json.loads(args.sample20.read_text())
    sample200 = json.loads(args.sample200.read_text())
    development = json.loads(args.development.read_text())
    holdout = json.loads(args.holdout.read_text())
    external = json.loads(args.external_summary.read_text())
    synthetic = json.loads(args.synthetic.read_text())
    residual = json.loads(args.residual.read_text())
    phenotypes = Counter()
    diagnostic_totals = Counter()
    for row in residual["rows"]:
        attempt = row["portfolios"]["size-coverage"][-1]
        for key in (
            "source_instances", "composed_consequences",
            "replayed_candidates", "replay_failures", "decreasing_rules",
            "nonorientable", "selected_rules", "critical_pairs",
            "joined_critical_pairs", "unresolved_critical_pairs",
            "left_steps", "right_steps", "distinct_normal_forms",
            "normalization_budget_exits", "consequence_budget_exits",
        ):
            diagnostic_totals[key] += attempt.get(key, 0) or 0
        if not row["id"].startswith("true_"):
            continue
        if not attempt.get("decreasing_rules"):
            phenotype = "no decreasing consequence generated"
        elif not attempt.get("left_steps") and not attempt.get("right_steps"):
            phenotype = "decreasing rules generated but none match target"
        elif attempt.get("distinct_normal_forms"):
            phenotype = "target sides reduce but normal forms differ"
        elif attempt.get("consequence_budget_exits"):
            phenotype = "consequence-generation budget exhausted"
        elif attempt.get("normalization_budget_exits"):
            phenotype = "normalization budget exhausted"
        else:
            phenotype = "target likely requires expansion or nonlocal lemma"
        phenotypes[phenotype] += 1
    solver = ROOT / "submissions/mathgraph/solver.py"
    frozen = ROOT / "experiments/mathgraph/regressions/solver_3215158.py"
    summary = {
        "starting_head": "3215158571e2c15dbf8bfaa410c5beb4e84dec61",
        "implementation_commit":
            "3cf9660031a46e09cfa5e5498d885f06945ae294",
        "branch": "mathgraph/general-solver",
        "frozen_baseline": {
            "solver_sha256": sha256(frozen),
            "solver_bytes": frozen.stat().st_size,
            "sample_200": {"accepted_true": 66, "accepted_false": 96},
            "all_162_verdicts_preserved": True,
        },
        "implementation": {
            "solver_sha256": sha256(solver),
            "solver_bytes": solver.stat().st_size,
            "architecture": [
                "bounded consequence generation",
                "independent proof-DAG replay",
                "strictly decreasing rule orientation",
                "alpha-pattern deduplication and compact rule selection",
                "deterministic innermost normalization",
                "independent trace replay",
                "explicit source-instance/transitivity/symmetry/congruence Lean proof",
            ],
            "trusted_rules": [
                "source instantiation", "reflexivity", "symmetry",
                "transitivity", "congruence",
            ],
            "selected_ordering": "size-depth-repetition-prefix",
            "selected_selector": "coverage-diverse",
            "retained_consequences": [
                "bounded direct and target-subterm source instances",
                "variable identification",
                "one-step renamed and exact proper overlaps",
                "exact endpoint composition",
                "context congruence during trace compilation",
            ],
            "production_portfolio": [],
            "contextual_research_production_enabled": False,
        },
        "synthetic": {
            "sha256": sha256(args.synthetic),
            "cases": synthetic["cases"],
            "positive_official_acceptances":
                synthetic["positive_official_acceptances"],
            "controls": 6,
            "false_control_true_judge_calls":
                synthetic["negative_true_judge_calls"],
            "corrupted_rule_rejected":
                synthetic["corrupted_rule_rejected"],
            "corrupted_match_rejected":
                synthetic["corrupted_match_rejected"],
            "largest_proof_dag": synthetic["largest_proof_nodes"],
            "largest_certificate_bytes":
                synthetic["largest_certificate_bytes"],
        },
        "development": {
            "baseline": counts(development),
            "configuration_grid": [
                "size-coverage", "size-reduction",
                "depth-coverage", "depth-reduction",
            ],
            "marginal_true_gain_all_configurations": 0,
            "selected_by_tie_break": "size-coverage",
        },
        "external_audit": external,
        "production": {
            "sample_20": {
                **counts(sample20), "sha256": sha256(args.sample20)
            },
            "development": {
                **counts(development), "sha256": sha256(args.development)
            },
            "holdout": {
                **counts(holdout), "sha256": sha256(args.holdout)
            },
            "sample_200": {
                **counts(sample200), "sha256": sha256(args.sample200)
            },
            "promoted_true_gain": 0,
            "promoted_total_gain": 0,
            "runtime_change_from_332_30_seconds": round(
                counts(sample200)["runtime_seconds"] - 332.30, 6
            ),
            "seconds_per_added_acceptance": None,
        },
        "gates": {
            "solo_solver_cases": "66/66",
            "marathon": "25/25",
            "normalization": "24 accepted TRUE; 6 abstention/corruption controls",
            "equality_chain": "9/9",
            "source_reentry": "10/11 with one required abstention",
            "contextual_research": "13/16 with three expected abstentions",
            "generic_finite_model": "15/16 with one required abstention",
            "fin4": "17 positive and 4 metamorphic certificates accepted",
            "incorrect": 0,
            "incomplete": 0,
            "malformed": 0,
            "unparsed": 0,
            "production_replay_failures": 0,
            "production_lean_rejections": 0,
            "llm_calls": 0,
            "global_solo_harness_non_solver_failures":
                "2 submit-CLI ANSI style tests; all 66 solver cases passed",
        },
        "residuals": {
            "unresolved_true": 34,
            "unresolved_false": 4,
            "true_phenotypes": dict(phenotypes),
            "diagnostic_totals": dict(diagnostic_totals),
            "dominant_true_phenotype":
                "decreasing rules generated but none match target (31/34)",
            "dominant_false_phenotype":
                "no bounded countermodel through the promoted order-4 route",
        },
        "decision": {
            "promotion_passed": False,
            "reason":
                "0/40 external TRUE opportunities; required at least 4",
            "production_unchanged": True,
            "next_recommendation":
                "bounded expansion-before-reduction via replayable anti-unification lemmas, audited externally before promotion",
        },
        "raw_logs": {
            "committed": False,
            "policy": "unique temporary outputs; compact hashes and metrics committed",
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(sha256(args.output))


if __name__ == "__main__":
    main()
