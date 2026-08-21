#!/usr/bin/env python3
"""Residual-conditioned operator induction v2.

Correction to v1: the residual world must contain the original source law.
V1 built the bounded cut only from derived installed macros; on order5_0014
that produced singleton left/right regions and identically-zero bridge scores.

V2 freezes the trusted source equation plus the same replay-verified G1/G2
operator layer, recomputes the cut, and repeats matched A/B/C/ablation arms.
No external proof trace, answer label, or target-specific operator identity is
used. Derived macros remain replay-verified back to source primitives.
"""
from __future__ import annotations

import importlib.util
import json
import sys
import time
from pathlib import Path

from datasets import load_dataset

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "experiments/mathgraph"
V1 = HERE / "run_residual_conditioned_operator_induction_gate.py"
SOLVER = ROOT / "submissions/mathgraph/solver.py"
SYM = HERE / "run_symbolic_superposition_research.py"
SELF = HERE / "run_verified_self_embedding_gate.py"
OPC = HERE / "run_verified_operator_closure_gate.py"
OUT = HERE / "results/residual-conditioned-operator-induction-gate-v2.json"
RID = "evaluation_order5_0014"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def contact_stats(v1, m, item, left, right):
    """Measure whether an operator can act on either side of the frozen cut."""
    schema = item["schema"]
    lvals = list(left.values())[:260]
    rvals = list(right.values())[:260]
    lc, rc = set(left), set(right)
    applications = 0
    new_states = 0
    exact = False
    best_improvement = 0

    def nearest(t, vals):
        return min((v1.term_distance(t, z) for z in vals), default=10**9)

    for src, opp, ownkeys, oppkeys in ((lvals, rvals, lc, rc), (rvals, lvals, rc, lc)):
        for t in src:
            base = nearest(t, opp)
            for nt in v1.rewrite_once(m, t, schema, max_size=90):
                applications += 1
                k = m.alpha_canonical_term(nt, {})
                if k not in ownkeys:
                    new_states += 1
                if k in oppkeys:
                    exact = True
                best_improvement = max(best_improvement, base - nearest(nt, opp))
    score = (1000000 if exact else 0) + 1000 * max(0, best_improvement) + 10 * new_states + min(applications, 9)
    return {
        "score": score,
        "exact_bridge": exact,
        "applications": applications,
        "new_states": new_states,
        "best_distance_improvement": best_improvement,
    }


def main():
    v1 = load(V1, "residual_induction_v1_helpers")
    m = load(SOLVER, "mg_residual_induction_v2")
    sym = load(SYM, "sym_residual_induction_v2")
    selfmod = load(SELF, "self_residual_induction_v2")
    op = load(OPC, "op_residual_induction_v2")
    op.selfmod = selfmod

    row = next(
        dict(r)
        for r in load_dataset(
            "SAIRfoundation/equational-theories-selected-problems",
            "evaluation_order5",
            split="train",
        )
        if r["id"] == RID
    )
    source = m.parse_equation(row["equation1"])
    target = m.parse_equation(row["equation2"])

    g1 = []
    for p in selfmod.proposals(m, source):
        proof = selfmod.compile_proposal(m, source, target, p)
        if proof:
            schema = p["schema"]
            g1.append(
                {
                    "schema": schema,
                    "proof": proof,
                    "name": "g1",
                    "activation": selfmod.activation(m, schema, target),
                    "meta": p,
                }
            )
    g1.sort(key=lambda x: (-x["activation"], m.term_size(x["schema"][0]) + m.term_size(x["schema"][1])))
    g2 = v1.generation(m, op, source, target, g1, limit=420)
    for x in g2:
        x["name"] = "g2"

    frozen = g1[:32] + g2[:96]

    # Critical v2 correction: source is part of the trusted rewrite world.
    schemas = [source] + [x["schema"] for x in frozen]
    left = v1.bounded_reach(m, target[0], schemas, depth=3, cap=1800, max_size=90)
    right = v1.bounded_reach(m, target[1], schemas, depth=3, cap=1800, max_size=90)
    intersection = set(left).intersection(right)
    cut = {
        "left_states": len(left),
        "right_states": len(right),
        "intersection": len(intersection),
        "depth": 3,
        "cap": 1800,
        "source_law_included": True,
        "derived_frozen_operators": len(frozen),
    }

    arm_a = v1.run_arm(m, sym, source, target, frozen, 20.0, "A_frozen_g1_g2")

    g3b = v1.generation(m, op, source, target, g2[:24], limit=420)
    for x in g3b:
        x["name"] = "g3_unconstrained"
    bins = g1[:24] + g2[:48] + g3b[:64]
    arm_b = v1.run_arm(m, sym, source, target, bins, 20.0, "B_unconstrained_g3")

    scored = []
    for x0 in g2:
        x = dict(x0)
        st = contact_stats(v1, m, x, left, right)
        x.update(st)
        scored.append(x)
    scored.sort(
        key=lambda x: (
            -x["score"],
            -x.get("activation", 0),
            m.term_size(x["schema"][0]) + m.term_size(x["schema"][1]),
        )
    )
    cparents = scored[:24]

    g3c_raw = v1.generation(m, op, source, target, cparents, limit=420)
    g3c = []
    for x0 in g3c_raw:
        x = dict(x0)
        x["name"] = "g3_conditioned"
        x.update(contact_stats(v1, m, x, left, right))
        g3c.append(x)
    g3c.sort(key=lambda x: (-x["score"], -x.get("activation", 0), m.term_size(x["schema"][0]) + m.term_size(x["schema"][1])))

    g4c = []
    if g3c:
        for x0 in v1.generation(m, op, source, target, g3c[:20], limit=420):
            x = dict(x0)
            x["name"] = "g4_conditioned"
            x.update(contact_stats(v1, m, x, left, right))
            g4c.append(x)
        g4c.sort(key=lambda x: (-x["score"], -x.get("activation", 0), m.term_size(x["schema"][0]) + m.term_size(x["schema"][1])))

    c_new = g3c[:44] + g4c[:44]
    cins = g1[:24] + g2[:48] + c_new[:64]
    arm_c = v1.run_arm(m, sym, source, target, cins, 20.0, "C_residual_conditioned_g3_g4_v2")
    ablation = v1.run_arm(m, sym, source, target, g1[:24] + g2[:48], 20.0, "C_ablation_remove_induced") if arm_c["closure"] else None

    def show(xs, n=12):
        return [
            {
                "lhs": m.render_term(x["schema"][0]),
                "rhs": m.render_term(x["schema"][1]),
                "activation": x.get("activation", 0),
                "score": x.get("score"),
                "exact_bridge": x.get("exact_bridge", False),
                "applications": x.get("applications"),
                "new_states": x.get("new_states"),
                "best_distance_improvement": x.get("best_distance_improvement"),
                "name": x.get("name"),
            }
            for x in xs[:n]
        ]

    nonzero_g2 = sum(x.get("score", 0) > 0 for x in scored)
    nonzero_g3 = sum(x.get("score", 0) > 0 for x in g3c)
    nonzero_g4 = sum(x.get("score", 0) > 0 for x in g4c)
    informative_cut = len(left) > 1 and len(right) > 1 and (nonzero_g2 + nonzero_g3 + nonzero_g4) > 0

    if arm_c["closure"] and not arm_a["closure"] and not arm_b["closure"] and ablation and not ablation["closure"]:
        decision = "PASS"
    elif arm_c["closure"]:
        decision = "PARTIAL_CLOSURE"
    elif informative_cut:
        decision = "INFORMATIVE_NO_CLOSURE"
    else:
        decision = "NONINFORMATIVE_NO_CLOSURE"

    out = {
        "schema": "mathgraph.residual-conditioned-operator-induction.v2",
        "id": RID,
        "correction": "source law included in residual reachability world",
        "protocol": {
            "no_external_proof_trace": True,
            "no_answer_label_in_generator": True,
            "no_target_specific_identity": True,
            "all_macros_replay_to_source": True,
            "matched_arm_seconds": 20.0,
        },
        "source": v1.show_eq(m, source),
        "target": v1.show_eq(m, target),
        "cut": cut,
        "counts": {
            "g1": len(g1),
            "g2": len(g2),
            "g3_unconstrained": len(g3b),
            "g3_conditioned": len(g3c),
            "g4_conditioned": len(g4c),
            "g2_nonzero_contact": nonzero_g2,
            "g3_nonzero_contact": nonzero_g3,
            "g4_nonzero_contact": nonzero_g4,
            "g2_exact_bridges": sum(x.get("exact_bridge", False) for x in scored),
            "g3_exact_bridges": sum(x.get("exact_bridge", False) for x in g3c),
            "g4_exact_bridges": sum(x.get("exact_bridge", False) for x in g4c),
        },
        "informative_cut": informative_cut,
        "arms": {"A": arm_a, "B": arm_b, "C": arm_c, "C_ablation": ablation},
        "top_conditioned_g2": show(scored),
        "top_conditioned_g3": show(g3c),
        "top_conditioned_g4": show(g4c),
        "decision": decision,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
