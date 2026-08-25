#!/usr/bin/env python3
from __future__ import annotations

import json
import time
from pathlib import Path

import run_residual3_fairness_proof_sweep as base

OUT = Path(__file__).parent / "results/corridor-aware-continuation.json"
WINDOWS = (0, 1, 2, 4)
RATIO = 7
THRESHOLD = 0.5347
RESIDUAL = base.RESIDUAL_IDS


def ckey(m, c):
    names = {}
    a = (m.alpha_canonical_term(c.lhs, names), m.alpha_canonical_term(c.rhs, names))
    names = {}
    b = (m.alpha_canonical_term(c.rhs, names), m.alpha_canonical_term(c.lhs, names))
    return min(a, b)


def term_size(t):
    if getattr(t, "is_var", False):
        return 1
    if isinstance(t, tuple):
        if t and t[0] in ("var", "v"):
            return 1
        if len(t) >= 3:
            return 1 + term_size(t[1]) + term_size(t[2])
    for left, right in (("left", "right"), ("lhs", "rhs")):
        if hasattr(t, left) and hasattr(t, right):
            return 1 + term_size(getattr(t, left)) + term_size(getattr(t, right))
    if hasattr(t, "args"):
        return 1 + sum(term_size(x) for x in t.args)
    return 1


def clause_size(c):
    return term_size(c.lhs) + term_size(c.rhs)


def corridor_fraction(m, search, active, parent, deadline):
    """Fraction of unique one-step children with reduced size delta in [-6, 0]."""
    rules = [q for c in active if (q := search.orient(c)) is not None]
    pr = search.orient(parent)
    rules2 = rules + ([pr] if pr is not None else [])
    psize = clause_size(parent)
    seen = set()
    moderate = total = 0
    for oi, other in enumerate(active + [parent]):
        for bo, bi, a, b in ((parent, other, 9999, oi), (other, parent, oi, 9999)):
            for oside, outer in enumerate(base.oriented_variants(m, bo)):
                for iside, inner in enumerate(base.oriented_variants(m, bi)):
                    for path in m.nonvariable_positions(
                        outer.lhs,
                        maximum_depth=search.limits["maximum_depth"],
                        include_root=True,
                    ):
                        if time.monotonic() >= deadline or search.expired():
                            return (moderate / total if total else 0.0), total
                        q = search.critical_pair(outer, inner, a * 2 + oside, b * 2 + iside, path)
                        if q is None:
                            continue
                        qr = search.interreduce(q, rules2)
                        k = ckey(m, qr)
                        if k in seen:
                            continue
                        seen.add(k)
                        total += 1
                        d = clause_size(qr) - psize
                        if -6 <= d <= 0:
                            moderate += 1
    return (moderate / total if total else 0.0), total


def one(m, r, window, seconds):
    source = m.parse_equation(r["equation1"])
    target = m.parse_equation(r["equation2"])
    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds": seconds,
        "maximum_term_size": 65,
        "maximum_replay_term_size": 300,
        "maximum_depth": 12,
        "maximum_rules": 1024,
        "maximum_rounds": 96,
        "new_clauses_per_round": 512,
        "maximum_clauses": 16000,
        "normalization_steps": 384,
        "maximum_proof_nodes": 60000,
    })
    started = time.monotonic()
    deadline = started + seconds
    eng = m.TargetGroundedRefutation(source, target, deadline, limits)

    passive = list(eng.search.clauses)
    active = []
    age = {ckey(m, c): i for i, c in enumerate(passive)}
    next_age = len(passive)
    continuation_scores = {}
    remaining = 0
    given = age_picks = target_picks = continuation_picks = 0
    proposals_total = accepted_total = corridor_scored = corridor_pass = 0
    corridor_children = 0
    recipe = None

    while passive and given < 1024 and not eng.search.expired():
        rules = [q for c in active if (q := eng.search.orient(c)) is not None]
        recipe = eng.search.target_proof(rules)
        if recipe is not None:
            break

        cand = [i for i, c in enumerate(passive) if remaining > 0 and ckey(m, c) in continuation_scores]
        use_age = given > 0 and given % (RATIO + 1) == RATIO
        if cand:
            # Prefer corridor occupancy first; target score is only a tie-breaker.
            idx = min(
                cand,
                key=lambda i: (
                    -continuation_scores.get(ckey(m, passive[i]), 0.0),
                    eng.search.target_score(passive[i]),
                    age.get(ckey(m, passive[i]), 10**18),
                ),
            )
            continuation_picks += 1
            remaining -= 1
        elif use_age:
            idx = min(range(len(passive)), key=lambda i: age.get(ckey(m, passive[i]), 10**18))
            age_picks += 1
        else:
            idx = min(
                range(len(passive)),
                key=lambda i: (eng.search.target_score(passive[i]), age.get(ckey(m, passive[i]), 10**18)),
            )
            target_picks += 1

        selected = eng.search.interreduce(passive.pop(idx), rules)
        active.append(selected)
        given += 1
        selected_was_age = use_age and not cand

        rules = [q for c in active if (q := eng.search.orient(c)) is not None]
        recipe = eng.search.target_proof(rules)
        if recipe is not None:
            break

        parent_size = clause_size(selected)
        proposals = []
        raw_gate = {}
        for oi, other in enumerate(active):
            for bo, bi, a, b in ((selected, other, given, oi), (other, selected, oi, given)):
                for oside, outer in enumerate(base.oriented_variants(m, bo)):
                    for iside, inner in enumerate(base.oriented_variants(m, bi)):
                        for path in m.nonvariable_positions(
                            outer.lhs,
                            maximum_depth=eng.search.limits["maximum_depth"],
                            include_root=True,
                        ):
                            if eng.search.expired():
                                break
                            q = eng.search.critical_pair(outer, inner, a * 2 + oside, b * 2 + iside, path)
                            if q is None:
                                continue
                            raw_size = clause_size(q)
                            qr = eng.search.interreduce(q, rules)
                            k = ckey(m, qr)
                            raw_gate[k] = raw_gate.get(k, False) or (raw_size <= parent_size + 1)
                            proposals.append((eng.search.target_score(qr), qr))

        proposals_total += len(proposals)
        proposals.sort(key=lambda x: x[0])
        admitted = []
        for _, q in proposals[: eng.search.limits["new_clauses_per_round"]]:
            if eng.search.add_clause(q):
                passive.append(q)
                k = ckey(m, q)
                age[k] = next_age
                next_age += 1
                accepted_total += 1
                if raw_gate.get(k, False):
                    admitted.append(q)

        if selected_was_age and window > 0 and admitted:
            scored = {}
            # Score only raw-size-admitted descendants and stop scoring if the
            # experiment's own solver deadline is reached.
            for q in admitted:
                if eng.search.expired():
                    break
                frac, nchild = corridor_fraction(m, eng.search, active, q, deadline)
                corridor_scored += 1
                corridor_children += nchild
                if frac > THRESHOLD:
                    scored[ckey(m, q)] = frac
                    corridor_pass += 1
            continuation_scores = scored
            remaining = window

        new_passive = []
        seen = set()
        surviving = {}
        for c in passive:
            if eng.search.expired():
                break
            c = eng.search.interreduce(c, rules)
            k = ckey(m, c)
            if k in seen:
                continue
            seen.add(k)
            new_passive.append(c)
            if k in continuation_scores:
                surviving[k] = continuation_scores[k]
        passive = new_passive
        continuation_scores = surviving

    if recipe is None:
        rules = [q for c in active if (q := eng.search.orient(c)) is not None]
        recipe = eng.search.target_proof(rules)

    found = recipe is not None
    inline_ok = compile_ok = replay_ok = False
    nodes_n = None
    err = None
    if found:
        try:
            rr = eng.inline_recipe(recipe)
            inline_ok = rr is not None
            if rr is not None:
                compiler = m.CompactSuperposition(m, eng.source, eng.target, time.monotonic() + 4.0, eng.search.limits)
                compiled = compiler.compile(rr)
                if compiled is not None:
                    nodes, root = compiled
                    nodes_n = len(nodes)
                    compile_ok = True
                    replay_ok = bool(m.replay_dag(source, nodes, root))
        except Exception as exc:
            err = type(exc).__name__ + ": " + str(exc)

    return {
        "window": window,
        "ratio": RATIO,
        "threshold": THRESHOLD,
        "recipe_found": found,
        "inline_ok": inline_ok,
        "compile_ok": compile_ok,
        "replay_ok": replay_ok,
        "proof_nodes": nodes_n,
        "seconds": round(time.monotonic() - started, 4),
        "error": err,
        "given": given,
        "age_picks": age_picks,
        "target_picks": target_picks,
        "continuation_picks": continuation_picks,
        "proposals": proposals_total,
        "accepted": accepted_total,
        "corridor_scored": corridor_scored,
        "corridor_pass": corridor_pass,
        "corridor_children": corridor_children,
    }


def main():
    td, m = base.load_solver()
    byid = base.rows()
    out = {
        "ratio": RATIO,
        "windows": WINDOWS,
        "threshold": THRESHOLD,
        "policy": "after 7:1 age rescue, among raw_size<=parent+1 descendants prefer moderate_contraction_fraction([-6,0]) > 0.5347",
        "residuals": [],
    }
    try:
        for rid in RESIDUAL:
            rec = {"id": rid, "runs": {}}
            for w in WINDOWS:
                rec["runs"][str(w)] = one(m, byid[rid], w, 28.0)
            out["residuals"].append(rec)
            print("CORRIDOR_CAUSAL_RESIDUAL", json.dumps(rec, sort_keys=True), flush=True)

        summary = {}
        for w in WINDOWS:
            k = str(w)
            summary[k] = {
                "residual_replay": sum(int(x["runs"][k]["replay_ok"]) for x in out["residuals"]),
                "residual_recipe": sum(int(x["runs"][k]["recipe_found"]) for x in out["residuals"]),
                "corridor_picks": sum(x["runs"][k]["continuation_picks"] for x in out["residuals"]),
                "corridor_pass": sum(x["runs"][k]["corridor_pass"] for x in out["residuals"]),
            }
        out["summary"] = summary
        print("CORRIDOR_CAUSAL_SUMMARY", json.dumps(summary, sort_keys=True), flush=True)
    finally:
        td.cleanup()

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
