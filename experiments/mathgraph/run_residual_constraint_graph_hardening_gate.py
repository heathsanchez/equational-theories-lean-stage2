#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
import math
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
OUT = RESULTS / "residual-constraint-graph-hardening-gate.json"
SEED = 20260821
NULL_REPS = 48


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def num(x):
    return float(x) if isinstance(x, (int, float, bool)) else 0.0


def source_total(m):
    return sum(float(v) for v in m.get("source_instances", {}).values() if isinstance(v, (int, float)))


def accepted(row):
    return any(e.get("type") == "judge" and e.get("response", {}).get("status") == "accepted" for e in row.get("log", []))


def first_probe(ms):
    for m in ms:
        if m.get("portfolio") not in (None, "initial-chain", "target-narrowing"):
            return m
    return None


def quantile(values, q):
    s = sorted(values)
    if not s:
        return 0.0
    return s[min(len(s) - 1, max(0, int(round(q * (len(s) - 1)))))]


def bacc(y, pred):
    pos = [i for i, z in enumerate(y) if z]
    neg = [i for i, z in enumerate(y) if not z]
    if not pos or not neg:
        return 0.5
    tpr = sum(bool(pred[i]) for i in pos) / len(pos)
    tnr = sum(not bool(pred[i]) for i in neg) / len(neg)
    return 0.5 * (tpr + tnr)


def confusion(y, pred):
    tp = sum(bool(a) and bool(b) for a, b in zip(y, pred))
    tn = sum((not bool(a)) and (not bool(b)) for a, b in zip(y, pred))
    fp = sum((not bool(a)) and bool(b) for a, b in zip(y, pred))
    fn = sum(bool(a) and (not bool(b)) for a, b in zip(y, pred))
    return {"tp": tp, "tn": tn, "fp": fp, "fn": fn}


def atom_holds(x, atom):
    v = x.get(atom["feature"], 0.0)
    return v >= atom["threshold"] if atom["direction"] == "ge" else v <= atom["threshold"]


def predict(rows, conjunction):
    return [all(atom_holds(r["x"], a) for a in conjunction) for r in rows]


def view_for(feature):
    if feature.startswith("response."):
        if any(s in feature for s in ("nodes", "edges", "term_size", "generations")):
            return "response_structural"
        if any(s in feature for s in ("source_",)):
            return "response_identity"
        return "response_operational"
    if any(s in feature for s in ("nodes", "edges", "term_size", "generations", "saturation")):
        return "static_structural"
    if any(s in feature for s in ("source_", "entropy", "density")):
        return "static_identity"
    return "static_operational"


def build_atoms(train, features):
    out = []
    seen = set()
    for f in features:
        vals = [r["x"].get(f, 0.0) for r in train]
        if len(set(vals)) < 2:
            continue
        for q in (0.2, 0.35, 0.5, 0.65, 0.8):
            t = quantile(vals, q)
            for direction in ("le", "ge"):
                key = (f, direction, t)
                if key in seen:
                    continue
                seen.add(key)
                out.append({"feature": f, "direction": direction, "threshold": t, "view": view_for(f)})
    return out


def score(train, conjunction):
    y = [r["y"] for r in train]
    p = predict(train, conjunction)
    c = confusion(y, p)
    support = c["tp"] + c["fp"]
    positives = c["tp"] + c["fn"]
    precision = c["tp"] / max(1, support)
    recall = c["tp"] / max(1, positives)
    ba = bacc(y, p)
    if support < 3 or c["tp"] < 2:
        return None
    objective = ba + 0.04 * precision + 0.02 * recall - 0.02 * (len(conjunction) - 1)
    return objective, ba, precision, recall, support


def mine(train, features, max_k=3, require_cross_view=False):
    atoms = build_atoms(train, features)
    singleton_rank = []
    for a in atoms:
        s = score(train, (a,))
        if s:
            singleton_rank.append((s[0], a))
    singleton_rank.sort(reverse=True, key=lambda z: z[0])
    base = [a for _, a in singleton_rank[:32]]
    candidates = []
    for k in range(1, max_k + 1):
        for conj in itertools.combinations(base, k):
            if len({a["feature"] for a in conj}) < k:
                continue
            if require_cross_view:
                views = {a["view"] for a in conj}
                has_static = any(v.startswith("static_") for v in views)
                has_response = any(v.startswith("response_") for v in views)
                if k < 2 or not (has_static and has_response):
                    continue
            s = score(train, conj)
            if s:
                candidates.append((s[0], s, conj))
    candidates.sort(reverse=True, key=lambda z: z[0])
    return candidates


def fit(train, test, features, max_k=3, require_cross_view=False):
    candidates = mine(train, features, max_k=max_k, require_cross_view=require_cross_view)
    if not candidates:
        return {"heldout_bacc": 0.5, "train_bacc": 0.5, "k": 0, "atoms": [], "confusion": confusion([r["y"] for r in test], [False] * len(test))}
    _, s, conj = candidates[0]
    p = predict(test, conj)
    return {
        "heldout_bacc": round(bacc([r["y"] for r in test], p), 4),
        "train_bacc": round(s[1], 4),
        "k": len(conj),
        "atoms": list(conj),
        "confusion": confusion([r["y"] for r in test], p),
        "train_precision": round(s[2], 4),
        "train_recall": round(s[3], 4),
        "train_support": s[4],
    }


def median(values):
    s = sorted(values)
    return s[len(s) // 2] if s else 0.0


def build_examples():
    rrt = load(HERE / "run_residual_representation_tournament.py", "rrt_hardening")
    frozen = {r["id"]: r for r in json.loads((RESULTS / "contextual_development_frozen/sample_200_development.json").read_text())}
    developed = {r["id"]: r for r in json.loads((RESULTS / "contextual_development_all/sample_200_development.json").read_text())}
    examples = []
    for rid in sorted(set(frozen) & set(developed)):
        x0, _, dm = rrt.feat(frozen[rid], developed[rid])
        initial = next((m for m in dm if m.get("portfolio") == "initial-chain"), {})
        probe = first_probe(dm)
        x = {k: float(v) for k, v in x0.items() if k.startswith("static.") and k != "static.true_problem" and isinstance(v, (int, float, bool))}
        response = {
            "response.probe_present": float(probe is not None),
            "response.nodes_delta": 0.0,
            "response.edges_delta": 0.0,
            "response.source_total_delta": 0.0,
            "response.generations_delta": 0.0,
            "response.max_term_size_delta": 0.0,
            "response.replay_seconds_delta": 0.0,
            "response.source_family_delta": 0.0,
            "response.exhaustion_changed": 0.0,
            "response.found": 0.0,
        }
        if probe is not None:
            response.update({
                "response.nodes_delta": num(probe.get("equality_nodes")) - num(initial.get("equality_nodes")),
                "response.edges_delta": num(probe.get("graph_edges")) - num(initial.get("graph_edges")),
                "response.source_total_delta": source_total(probe) - source_total(initial),
                "response.generations_delta": num(probe.get("generations")) - num(initial.get("generations")),
                "response.max_term_size_delta": num(probe.get("max_term_size")) - num(initial.get("max_term_size")),
                "response.replay_seconds_delta": num(probe.get("replay_seconds")) - num(initial.get("replay_seconds")),
                "response.source_family_delta": float(len(probe.get("source_instances", {})) - len(initial.get("source_instances", {}))),
                "response.exhaustion_changed": float(probe.get("exhaustion") != initial.get("exhaustion")),
                "response.found": float(bool(probe.get("found"))),
            })
        x.update(response)
        later = [m for m in dm if m is not initial and m is not probe]
        labels = {
            "target_narrowing": int(accepted(developed[rid]) and any(m.get("portfolio") == "target-narrowing" and bool(m.get("found")) for m in dm)),
            "component_bridge": int(any(num(m.get("components_joined")) > 0 for m in later)),
        }
        examples.append({"id": rid, "x": x, "labels": labels})
    return examples


def positive_leave_one_out(rows, features, require_cross_view):
    positives = [r for r in rows if r["y"]]
    negatives = [r for r in rows if not r["y"]]
    records = []
    for j, held in enumerate(positives):
        # Hold out the positive plus a deterministic panel of negatives so both classes are visible.
        panel = [held]
        for n in negatives:
            h = int(hashlib.sha256((held["id"] + "|" + n["id"] + "|ploo").encode()).hexdigest(), 16)
            if h % 7 == 0:
                panel.append(n)
        if len(panel) < 5:
            panel += negatives[: max(0, 5 - len(panel))]
        panel_ids = {r["id"] for r in panel}
        train = [r for r in rows if r["id"] not in panel_ids]
        if sum(r["y"] for r in train) < 2:
            continue
        model = fit(train, panel, features, max_k=3, require_cross_view=require_cross_view)
        preds = predict(panel, model["atoms"]) if model["atoms"] else [False] * len(panel)
        held_pred = preds[0]
        neg_preds = preds[1:]
        records.append({
            "held_positive_id": held["id"],
            "held_positive_recovered": bool(held_pred),
            "negative_specificity": round(sum(not p for p in neg_preds) / max(1, len(neg_preds)), 4),
            "atoms": model["atoms"],
        })
    return {
        "cases": len(records),
        "positive_recall": round(sum(r["held_positive_recovered"] for r in records) / max(1, len(records)), 4),
        "median_negative_specificity": round(median([r["negative_specificity"] for r in records]), 4),
        "records": records,
    }


def search_corrected_null(train, test, features, observed_bacc, require_cross_view, seed):
    rng = random.Random(seed)
    null_scores = []
    labels = [r["y"] for r in train]
    for _ in range(NULL_REPS):
        shuffled = labels[:]
        rng.shuffle(shuffled)
        shtrain = [{"id": r["id"], "x": r["x"], "y": y} for r, y in zip(train, shuffled)]
        null_scores.append(fit(shtrain, test, features, max_k=3, require_cross_view=require_cross_view)["heldout_bacc"])
    p = (1 + sum(v >= observed_bacc for v in null_scores)) / (1 + len(null_scores))
    return {"p_search_corrected": round(p, 4), "null_median_bacc": round(median(null_scores), 4), "null_max_bacc": round(max(null_scores), 4)}


def main():
    examples = build_examples()
    features = sorted(examples[0]["x"])
    feature_views = {f: view_for(f) for f in features}
    ontology_hash = hashlib.sha256(json.dumps(feature_views, sort_keys=True).encode()).hexdigest()
    targets = {}

    for target in ("target_narrowing", "component_bridge"):
        rows = [{"id": e["id"], "x": e["x"], "y": e["labels"][target]} for e in examples]
        positives = sum(r["y"] for r in rows)
        negatives = len(rows) - positives
        split_records = []
        for rep in range(24):
            train, test = [], []
            for r in rows:
                h = int(hashlib.sha256((r["id"] + "|hardening|" + str(rep)).encode()).hexdigest(), 16)
                (test if h % 5 == 0 else train).append(r)
            if sum(r["y"] for r in train) < 3 or sum(not r["y"] for r in train) < 3 or sum(r["y"] for r in test) < 1 or sum(not r["y"] for r in test) < 1:
                continue
            singleton = fit(train, test, features, max_k=1, require_cross_view=False)
            unrestricted = fit(train, test, features, max_k=3, require_cross_view=False)
            cross_view = fit(train, test, features, max_k=3, require_cross_view=True)
            null = search_corrected_null(train, test, features, cross_view["heldout_bacc"], True, SEED + rep * 101 + positives)
            split_records.append({"rep": rep, "train": len(train), "test": len(test), "singleton": singleton, "unrestricted": unrestricted, "cross_view": cross_view, "null": null})

        cv_bacc = [r["cross_view"]["heldout_bacc"] for r in split_records]
        singleton_bacc = [r["singleton"]["heldout_bacc"] for r in split_records]
        unrestricted_bacc = [r["unrestricted"]["heldout_bacc"] for r in split_records]
        pvals = [r["null"]["p_search_corrected"] for r in split_records]
        recurring = {}
        for r in split_records:
            sig = " & ".join(sorted(a["feature"] + ":" + a["direction"] for a in r["cross_view"]["atoms"]))
            recurring[sig] = recurring.get(sig, 0) + 1
        ploo = positive_leave_one_out(rows, features, require_cross_view=True)
        targets[target] = {
            "positives": positives,
            "negatives": negatives,
            "valid_splits": len(split_records),
            "median_cross_view_bacc": round(median(cv_bacc), 4),
            "median_singleton_bacc": round(median(singleton_bacc), 4),
            "median_unrestricted_bacc": round(median(unrestricted_bacc), 4),
            "median_cross_view_gain_vs_singleton": round(median([a - b for a, b in zip(cv_bacc, singleton_bacc)]), 4),
            "median_cross_view_gap_vs_unrestricted": round(median([a - b for a, b in zip(cv_bacc, unrestricted_bacc)]), 4),
            "search_corrected_null_pass_rate_p_le_005": round(sum(p <= 0.05 for p in pvals) / max(1, len(pvals)), 4),
            "median_search_corrected_p": round(median(pvals), 4),
            "positive_leave_one_out": ploo,
            "recurring_cross_view_specs": [{"signature": k, "count": v} for k, v in sorted(recurring.items(), key=lambda kv: (-kv[1], kv[0]))[:10]],
            "operator_family_elimination": {
                "interpretation": "cross-view conjunction is a provisional admissibility specification for this later operator family",
                "heldout_family_recall": ploo["positive_recall"],
                "heldout_wrong_case_elimination": ploo["median_negative_specificity"],
            },
            "splits": split_records,
        }

    # Hardening cannot launder induced correlations into verified law.
    epistemic_policy = {
        "verified_constraint": "direct verifier/intervention result only",
        "contextual_constraint": "empirical invariant scoped to a frozen workload/regime",
        "provisional_specification": "train-derived conjunction surviving heldout controls; never promoted to verified law by prediction alone",
        "promotion_rule": "requires a newly constructed operator satisfying the conjunction, verifier-visible closure, causal ablation, and transfer",
    }

    tn = targets["target_narrowing"]
    cb = targets["component_bridge"]
    per_target = {}
    for name, t in targets.items():
        per_target[name] = {
            "G_valid_splits": t["valid_splits"] >= 12,
            "G_cross_view_bacc": t["median_cross_view_bacc"] >= 0.65,
            "G_beats_singleton": t["median_cross_view_gain_vs_singleton"] >= 0.03,
            "G_search_corrected": t["search_corrected_null_pass_rate_p_le_005"] >= 0.5,
            "G_positive_leave_one_out": t["positive_leave_one_out"]["positive_recall"] >= 0.6,
            "G_wrong_case_elimination": t["positive_leave_one_out"]["median_negative_specificity"] >= 0.7,
        }
        per_target[name]["pass"] = all(per_target[name].values())

    gates = {
        "G1_feature_view_ontology_frozen": True,
        "G2_cross_view_required_not_optional": True,
        "G3_search_process_inside_permutation_null": True,
        "G4_rare_positive_leave_one_out": True,
        "G5_epistemic_status_separated": True,
        "G6_target_narrowing_hardened": per_target["target_narrowing"]["pass"],
        "G7_second_operator_family_hardened": per_target["component_bridge"]["pass"],
        "G8_two_family_specification_synthesis": per_target["target_narrowing"]["pass"] and per_target["component_bridge"]["pass"],
    }

    out = {
        "schema": "mathgraph.residual-constraint-graph-hardening.v1",
        "protocol": {
            "feature_view_ontology_sha256": ontology_hash,
            "feature_views": feature_views,
            "preoutcome_only": True,
            "target_portfolio_identity_excluded": True,
            "later_target_metrics_excluded": True,
            "problem_disjoint_repeated_hash_holdout": True,
            "cross_view_definition": "every credited conjunction must contain >=1 static and >=1 response atom",
            "max_conjunction_size": 3,
            "null_repetitions_per_split": NULL_REPS,
            "null_repeats_full_train_side_search": True,
            "rare_class_control": "leave one positive case out plus deterministic negative panel",
        },
        "epistemic_policy": epistemic_policy,
        "targets": targets,
        "target_gates": per_target,
        "gates": gates,
        "decision": "HARDENED_TWO_FAMILY_SPECIFICATION_PASS" if gates["G8_two_family_specification_synthesis"] else "PARTIAL_OR_FAIL",
        "next_required": "If two-family pass: freeze recurring cross-view specifications and run direct operator construction/admissibility with verified closure, ablation, transfer, and specification-removal controls. If partial/fail: retain only the passing family as provisional and expand relational cross-residual evidence rather than adding scalar features.",
    }
    RESULTS.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
