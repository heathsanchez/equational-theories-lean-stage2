#!/usr/bin/env python3
"""Build a sealed external BridgeIR audit without executing BridgeIR."""

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
HEAD = "f9430e5d6210e1e0fe5b8878a5b3b35b3c86d0ce"
SEED = hashlib.sha256(
    (HEAD + "bridge-ir-external-audit-v1").encode()
).hexdigest()
CORPORA = (
    Path("/Users/heath/Documents/SAIR/examples/problems/normal.jsonl"),
    Path("/Users/heath/Documents/SAIR/examples/problems/hard1.jsonl"),
    Path("/Users/heath/Documents/SAIR/examples/problems/hard2.jsonl"),
    Path("/Users/heath/Documents/SAIR/examples/problems/hard3.jsonl"),
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def load_solver():
    spec = importlib.util.spec_from_file_location("bridge_audit_builder", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rows(path):
    return [
        json.loads(line) for line in path.read_text().splitlines()
        if line.strip()
    ]


def normalize(module, text):
    equation = module.parse_equation(text)
    return (
        module.render_term(equation[0])
        + " = "
        + module.render_term(equation[1])
    )


def pair(module, row):
    source = normalize(module, row["equation1"])
    target = normalize(module, row["equation2"])
    digest = hashlib.sha256((source + "\0" + target).encode()).hexdigest()
    return source, target, digest


def depth(term):
    return 0 if term[0] == "var" else 1 + max(
        depth(term[1]), depth(term[2])
    )


def variable_counts(term, output):
    if term[0] == "var":
        output[term[1]] += 1
    else:
        variable_counts(term[1], output)
        variable_counts(term[2], output)


def fin2(module, source, target):
    source_models = 0
    countermodels = 0
    for encoded in range(16):
        table = tuple((encoded >> shift) & 1 for shift in range(4))
        matrix = [list(table[:2]), list(table[2:])]
        if module.equation_holds(source, matrix):
            source_models += 1
            if not module.equation_holds(target, matrix):
                countermodels += 1
    return source_models, countermodels


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
    source_models, countermodels = fin2(module, source, target)
    target_subterms = set(module.walk_subterms(target[0])) | set(
        module.walk_subterms(target[1])
    )
    direct_instances = 0
    for side in source[:2]:
        for term in target_subterms:
            mapping = {}
            if (
                module.match_term(side, term, mapping)
                and all(variable in mapping for variable in source[2])
            ):
                direct_instances += 1
    return {
        "source_variables": len(source[2]),
        "target_variables": len(target[2]),
        "source_depth": max(depth(source[0]), depth(source[1])),
        "target_depth": max(depth(target[0]), depth(target[1])),
        "source_nodes": len(source_compiled[0]),
        "target_nodes": len(target_compiled[0]),
        "source_repetition": sorted(source_counts.values(), reverse=True),
        "target_repetition": sorted(target_counts.values(), reverse=True),
        "fin2_source_models": source_models,
        "fin2_countermodels": countermodels,
        "direct_source_instances": direct_instances,
        "target_subterms": len(target_subterms),
    }


def normalization_phenotype(module, source_text, target_text):
    source = module.parse_equation(source_text)
    target = module.parse_equation(target_text)
    configuration = dict(module.NORMALIZATION_PORTFOLIO[1])
    started = time.monotonic()
    search = module.EquationalNormalizer(
        source, target, started + configuration["seconds"], configuration
    )
    search.generate_consequences()
    search.orient()
    search.select_rulebook()
    initial_matches = (
        len(search.rewrite_candidates(target[0]))
        + len(search.rewrite_candidates(target[1]))
    )
    return {
        "decreasing_rules": search.decreasing_rules,
        "selected_rules": len(search.selected_rules),
        "initial_normalizer_matches": initial_matches,
        "local_critical_pairs": search.local_critical_pairs,
        "unresolved_critical_pairs": search.unresolved_critical_pairs,
        "normalizer_seconds": round(time.monotonic() - started, 6),
    }


def distance(left, right):
    weights = (
        ("source_variables", 4),
        ("target_variables", 3),
        ("source_depth", 2),
        ("target_depth", 2),
        ("source_nodes", 0.5),
        ("target_nodes", 0.5),
        ("fin2_source_models", 0.25),
        ("direct_source_instances", 1),
        ("target_subterms", 0.25),
        ("decreasing_rules", 0.03),
        ("selected_rules", 0.1),
        ("initial_normalizer_matches", 2),
        ("local_critical_pairs", 0.05),
        ("unresolved_critical_pairs", 0.1),
    )
    value = sum(
        weight * abs(left[key] - right[key]) for key, weight in weights
    )
    value += abs(
        sum(left["source_repetition"]) - sum(right["source_repetition"])
    )
    value += abs(
        sum(left["target_repetition"]) - sum(right["target_repetition"])
    )
    return round(value, 6)


def baseline(problem):
    from pipeline.proxy import load_config, run_solver

    result = run_solver(
        str(ROOT / "submissions/mathgraph"), problem, load_config()
    )
    rejected = [
        event.get("response", {}).get("status", "unparsed")
        for event in result.get("log", [])
        if event.get("type") == "judge"
        and event.get("response", {}).get("status") != "accepted"
    ]
    if rejected or result.get("llm_calls"):
        raise RuntimeError("baseline produced invalid audit outcome")
    return {
        "solved": bool(result.get("solved")),
        "verdict": result.get("verdict"),
        "judge_calls": result.get("judge_calls", 0),
    }


def official_problem(row):
    return {
        "id": "screen_" + row["content_sha256"][:16],
        "eq1_id": row["eq1_id"],
        "eq2_id": row["eq2_id"],
        "equation1": row["source"],
        "equation2": row["target"],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--per-label", type=int, default=40)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    module = load_solver()
    prior_path = (
        ROOT / "experiments/mathgraph/audits/normalization_provenance.json"
    )
    prior = json.loads(prior_path.read_text())
    registry = {
        item["pair_content_hash"]: item for item in prior["entries"]
    }
    additional_sources = []
    for path in (
        ROOT / "experiments/mathgraph/audits/normalization_audit_inputs.json",
        ROOT / "experiments/mathgraph/audits/balanced_audit_inputs.json",
        ROOT / "experiments/mathgraph/regressions/bridge_ir_cases.json",
    ):
        payload = json.loads(path.read_text())
        extra_rows = payload.get("rows", []) if isinstance(payload, dict) else payload
        for row in extra_rows:
            source, target, digest = pair(module, row)
            entry = registry.setdefault(digest, {
                "normalized_source": source,
                "normalized_target": target,
                "pair_content_hash": digest,
                "origins": [],
                "solver_run": True,
                "label_observed": True,
                "used_for_tuning": True,
                "used_only_for_final_evaluation": False,
            })
            entry["origins"] = sorted(set(
                entry.get("origins", []) + [str(path)]
            ))
        additional_sources.append({"path": str(path), "rows": len(extra_rows)})
    used = set(registry)
    candidates = []
    exclusions = Counter()
    seen = set()
    corpora = []
    for path in CORPORA:
        corpus_rows = rows(path)
        corpora.append({
            "path": str(path), "sha256": sha256(path), "rows": len(corpus_rows)
        })
        for row in corpus_rows:
            source, target, digest = pair(module, row)
            if digest in used:
                exclusions["prior_content_hash"] += 1
                continue
            if digest in seen:
                exclusions["duplicate_candidate_hash"] += 1
                continue
            seen.add(digest)
            candidates.append({
                "origin": str(path),
                "source": source,
                "target": target,
                "content_sha256": digest,
                "label": bool(row["answer"]),
                "eq1_id": row["eq1_id"],
                "eq2_id": row["eq2_id"],
            })
    for index, row in enumerate(candidates, 1):
        if index % 200 == 0:
            print(f"structural features {index}/{len(candidates)}", flush=True)
        row["features"] = structural_features(
            module, row["source"], row["target"]
        )
    true_order = sorted(
        (row for row in candidates if row["label"]),
        key=lambda row: hashlib.sha256(
            (SEED + "true" + row["content_sha256"]).encode()
        ).hexdigest(),
    )
    selected_true = []
    for index, row in enumerate(true_order, 1):
        if len(selected_true) >= args.per_label:
            break
        print(
            f"TRUE screen {index}, selected {len(selected_true)}", flush=True
        )
        outcome = baseline(official_problem(row))
        if outcome["solved"]:
            continue
        phenotype = normalization_phenotype(
            module, row["source"], row["target"]
        )
        if (
            phenotype["decreasing_rules"] > 0
            and phenotype["initial_normalizer_matches"] == 0
        ):
            row["features"].update(phenotype)
            row["baseline"] = outcome
            selected_true.append(row)
    if len(selected_true) < 20:
        raise RuntimeError("insufficient unused TRUE opportunities")

    false_order = sorted(
        (
            row for row in candidates
            if not row["label"] and not row["features"]["fin2_countermodels"]
        ),
        key=lambda row: hashlib.sha256(
            (SEED + "false" + row["content_sha256"]).encode()
        ).hexdigest(),
    )
    false_pool = []
    target_pool = max(args.per_label + 20, 60)
    for index, row in enumerate(false_order, 1):
        if len(false_pool) >= target_pool:
            break
        print(
            f"FALSE screen {index}, selected {len(false_pool)}", flush=True
        )
        outcome = baseline(official_problem(row))
        if outcome["solved"]:
            continue
        phenotype = normalization_phenotype(
            module, row["source"], row["target"]
        )
        if (
            phenotype["decreasing_rules"] > 0
            and phenotype["initial_normalizer_matches"] == 0
        ):
            row["features"].update(phenotype)
            row["baseline"] = outcome
            false_pool.append(row)
    matches = []
    used_false = set()
    for true_row in selected_true:
        choices = [
            (
                distance(true_row["features"], false_row["features"]),
                hashlib.sha256((
                    SEED + true_row["content_sha256"]
                    + false_row["content_sha256"]
                ).encode()).hexdigest(),
                false_row,
            )
            for false_row in false_pool
            if false_row["content_sha256"] not in used_false
        ]
        if not choices:
            break
        score, _, false_row = min(choices)
        used_false.add(false_row["content_sha256"])
        matches.append((true_row, false_row, score))
    if len(matches) < 20:
        raise RuntimeError("insufficient matched FALSE controls")

    audit_rows = []
    labels = {}
    match_records = []
    for true_row, false_row, score in matches:
        for row in (true_row, false_row):
            opaque = "bridge_" + hashlib.sha256((
                SEED + "opaque" + row["content_sha256"]
            ).encode()).hexdigest()[:20]
            audit_rows.append({
                "id": opaque,
                "eq1_id": row["eq1_id"],
                "eq2_id": row["eq2_id"],
                "equation1": row["source"],
                "equation2": row["target"],
                "content_sha256": row["content_sha256"],
                "stratum": row["features"],
                "baseline": row["baseline"],
            })
            labels[opaque] = row["label"]
            registry[row["content_sha256"]] = {
                "normalized_source": row["source"],
                "normalized_target": row["target"],
                "pair_content_hash": row["content_sha256"],
                "origins": [row["origin"], "bridge-ir-external-audit-v1"],
                "solver_run": True,
                "label_observed": True,
                "used_for_tuning": False,
                "used_only_for_final_evaluation": True,
            }
        match_records.append({
            "true_content_sha256": true_row["content_sha256"],
            "false_content_sha256": false_row["content_sha256"],
            "distance": score,
        })
    audit_rows.sort(key=lambda row: hashlib.sha256(
        (SEED + row["id"]).encode()
    ).hexdigest())
    inputs = args.output_dir / "bridge_ir_audit_inputs.json"
    labels_path = args.output_dir / "bridge_ir_audit_labels.sealed.json"
    provenance = args.output_dir / "bridge_ir_provenance.json"
    manifest = args.output_dir / "bridge_ir_audit_manifest.json"
    inputs.write_text(json.dumps({
        "audit_version": "bridge-ir-external-audit-v1",
        "seed_sha256": SEED,
        "rows": audit_rows,
    }, indent=2, sort_keys=True))
    labels_path.write_text(json.dumps({
        "audit_version": "bridge-ir-external-audit-v1",
        "sealed_at_utc": now(),
        "integrity_note": (
            "Plaintext process seal; runner receives no label path. "
            "This is not cryptographic protection."
        ),
        "labels": labels,
    }, indent=2, sort_keys=True))
    provenance.write_text(json.dumps({
        "created_at_utc": now(),
        "previous_registry_sha256": sha256(prior_path),
        "additional_sources": additional_sources,
        "entries": sorted(
            registry.values(), key=lambda item: item["pair_content_hash"]
        ),
    }, indent=2, sort_keys=True))
    distances = [item[2] for item in matches]
    manifest.write_text(json.dumps({
        "created_at_utc": now(),
        "authoritative_head": HEAD,
        "implementation_commit":
            "f243df7c118e9cedd606c341c057e4c244cd4f42",
        "seed_sha256": SEED,
        "solver_sha256": sha256(SOLVER),
        "solver_bytes": SOLVER.stat().st_size,
        "corpora": corpora,
        "candidate_rows_after_exclusion": len(candidates),
        "exclusions": dict(exclusions),
        "true_opportunities": len(matches),
        "false_controls": len(matches),
        "opportunity_phenotype":
            "decreasing rules > 0 and zero initial normalizer matches",
        "matching": {
            "method": "deterministic nearest neighbour",
            "mean_distance": round(sum(distances) / len(distances), 6),
            "median_distance": sorted(distances)[len(distances) // 2],
            "maximum_distance": max(distances),
            "pairs": match_records,
        },
        "inputs_sha256": sha256(inputs),
        "labels_sha256": sha256(labels_path),
        "provenance_sha256": sha256(provenance),
        "bridge_ir_used_during_build": False,
    }, indent=2, sort_keys=True))
    print(json.dumps({
        "true_opportunities": len(matches),
        "false_controls": len(matches),
        "inputs_sha256": sha256(inputs),
        "labels_sha256": sha256(labels_path),
    }, indent=2))


if __name__ == "__main__":
    main()
