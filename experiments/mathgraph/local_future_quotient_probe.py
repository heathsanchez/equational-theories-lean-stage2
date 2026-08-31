#!/usr/bin/env python3
"""Measure a bounded behavioural quotient of one fresh Stage-2 residual.

This diagnostic is deliberately non-solving.  It constructs a bounded proof
world from the source equation, represents each replayable consequence by the
set of one-step continuation signatures it admits against a fixed probe basis,
quotients consequences with identical futures, and extracts cover edges under
future-set inclusion.  It then asks whether generic dependency reducers and
shared-anchor fibers split the pre-repair quotient.
"""

import argparse
import importlib.util
import json
import time
from collections import defaultdict


def load_solver(path):
    spec = importlib.util.spec_from_file_location("mgsolver", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", required=True)
    ap.add_argument("--row", required=True)
    ap.add_argument("--seconds", type=float, default=32.0)
    ap.add_argument("--probe-partners", type=int, default=32)
    ap.add_argument("--objects", type=int, default=192)
    args = ap.parse_args()

    m = load_solver(args.solver)
    row = json.load(open(args.row))
    source = m.parse_equation(row["equation1"])
    target = m.parse_equation(row["equation2"])

    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds": args.seconds,
        "maximum_term_size": 65,
        "maximum_replay_term_size": 300,
        "maximum_depth": 12,
        "maximum_rules": 768,
        "maximum_rounds": 128,
        "new_clauses_per_round": 64,
        "maximum_clauses": 12000,
        "normalization_steps": 256,
        "maximum_proof_nodes": 60000,
    })
    engine = m.TargetGroundedRefutation(
        source, target, time.monotonic() + args.seconds, limits
    )
    search = engine.search

    # Build the same small streaming proof world used by the behavioural
    # fallback, but stop before any quotient-dependent repair is made.
    batch_size = 128
    enumerated = 0
    for _ in range(3):
        rules = search.rules()
        snapshot = list(rules)
        proposals = []
        for oi, outer in enumerate(snapshot):
            for ii, inner in enumerate(snapshot):
                for path in m.nonvariable_positions(
                    outer.lhs, maximum_depth=12, include_root=True
                ):
                    if search.expired():
                        break
                    candidate = search.critical_pair(outer, inner, oi, ii, path)
                    if candidate is None:
                        continue
                    candidate = search.interreduce(candidate, rules)
                    proposals.append((search.target_score(candidate), candidate))
                    enumerated += 1
                    if len(proposals) >= batch_size:
                        proposals.sort(key=lambda x: x[0])
                        added = 0
                        for _, proposal in proposals:
                            if search.add_clause(proposal):
                                search.superpositions += 1
                                added += 1
                            if added >= 64:
                                break
                        proposals = []
                        rules = search.rules()
                if search.expired():
                    break
            if search.expired():
                break
        if proposals and not search.expired():
            proposals.sort(key=lambda x: x[0])
            added = 0
            for _, proposal in proposals:
                if search.add_clause(proposal):
                    search.superpositions += 1
                    added += 1
                if added >= 64:
                    break
        if search.expired():
            break

    base_objects = sorted(search.clauses, key=search.target_score)[:args.objects]
    probes = base_objects[:args.probe_partners]

    def informative(recipe):
        names = m.term_variables(recipe.lhs) | m.term_variables(recipe.rhs)
        return recipe.lhs != recipe.rhs and not any(x.startswith("@") for x in names)

    def profile(recipe):
        lv = m.term_variables(recipe.lhs)
        rv = m.term_variables(recipe.rhs)
        for variable_side, other_side in ((recipe.lhs, recipe.rhs), (recipe.rhs, recipe.lhs)):
            if variable_side[0] == "var":
                anchor = variable_side[1]
                ov = m.term_variables(other_side)
                if anchor not in ov:
                    return (0, 0, len(ov))
                return (1, len(ov - {anchor}), len(ov))
        if lv < rv:
            return (2, len(rv - lv), len(rv))
        if rv < lv:
            return (2, len(lv - rv), len(lv))
        return (3, len(lv | rv), len(lv | rv))

    source_recipe = m.Recipe(source[0], source[1], "reflexivity")
    source_profile = profile(source_recipe)
    reducer_candidates = []
    seen = set()
    rules = search.rules()
    for oi, outer in enumerate(rules):
        for ii, inner in enumerate(rules):
            for path in m.nonvariable_positions(outer.lhs, maximum_depth=12, include_root=True):
                if search.expired():
                    break
                c = search.critical_pair(outer, inner, oi, ii, path)
                if c is None:
                    continue
                c = search.interreduce(c, rules)
                if not informative(c) or not profile(c) < source_profile:
                    continue
                key = (search.alpha_signature(c.lhs, c.rhs), c.lhs, c.rhs)
                if key in seen:
                    continue
                seen.add(key)
                nodes, root = search.compile(c)
                if m.replay_dag(source, nodes, root, maximum_term_size=300, maximum_nodes=60000):
                    reducer_candidates.append(c)
            if search.expired():
                break
        if search.expired():
            break
    reducer_candidates.sort(key=lambda q: (profile(q), m.term_size(q.lhs)+m.term_size(q.rhs), q.cost, m.render_term(q.lhs), m.render_term(q.rhs)))
    reducers = []
    if reducer_candidates:
        best = profile(reducer_candidates[0])
        reducers = [q for q in reducer_candidates if profile(q) == best][:8]

    def variable_form(recipe):
        if recipe.lhs[0] == "var":
            return "left", recipe.lhs[1], recipe.rhs
        if recipe.rhs[0] == "var":
            return "right", recipe.rhs[1], recipe.lhs
        return None

    def instantiate(recipe, mapping):
        return m.Recipe(
            m.substitute_partial(recipe.lhs, mapping),
            m.substitute_partial(recipe.rhs, mapping),
            "instantiate", (recipe,), tuple(sorted(mapping.items())),
        )

    def compose(first, second):
        f, s = variable_form(first), variable_form(second)
        if f is None or s is None or f[0] != s[0]:
            return None
        if f[0] == "left":
            rev = m.Recipe(first.rhs, first.lhs, "symmetry", (first,))
            return m.Recipe(rev.lhs, second.rhs, "transitivity", (rev, second))
        rev = m.Recipe(second.rhs, second.lhs, "symmetry", (second,))
        return m.Recipe(first.lhs, rev.rhs, "transitivity", (first, rev))

    fibers = []
    tv = list(target[2])
    if len(tv) >= 3:
        anchor, a, b = tv[:3]
        instances = []
        for r in reducers:
            form = variable_form(r)
            if form is None:
                continue
            _, distinguished, body = form
            params = sorted(m.term_variables(body) - {distinguished})
            if len(params) != 1:
                continue
            param = params[0]
            names = sorted(m.term_variables(r.lhs) | m.term_variables(r.rhs))
            base = {name: ("var", anchor) for name in names}
            base[distinguished] = ("var", anchor)
            ma, mb = dict(base), dict(base)
            ma[param], mb[param] = ("var", a), ("var", b)
            ia, ib = instantiate(r, ma), instantiate(r, mb)
            instances.append((ia, ib))
            f = compose(ia, ib)
            if f is not None and informative(f):
                nodes, root = search.compile(f)
                if m.replay_dag(source, nodes, root, maximum_term_size=300, maximum_nodes=60000):
                    fibers.append(f)
        for i in range(len(instances)):
            for j in range(i+1, len(instances)):
                ia, ib = instances[i]
                ja, jb = instances[j]
                for left, right in ((ia, ja), (ib, jb), (ia, jb), (ib, ja)):
                    f = compose(left, right)
                    if f is None or not informative(f):
                        continue
                    nodes, root = search.compile(f)
                    if m.replay_dag(source, nodes, root, maximum_term_size=300, maximum_nodes=60000):
                        fibers.append(f)

    def alpha(recipe):
        return str(search.alpha_signature(recipe.lhs, recipe.rhs))

    def orient(recipe, reverse):
        return recipe if not reverse else m.Recipe(recipe.rhs, recipe.lhs, "symmetry", (recipe,))

    def future_signature(rule):
        out = set()
        calls = 0
        for pi, partner in enumerate(probes):
            for first, second in ((rule, partner), (partner, rule)):
                for fr in (False, True):
                    aa = orient(first, fr)
                    for sr in (False, True):
                        bb = orient(second, sr)
                        for path in m.nonvariable_positions(aa.lhs, maximum_depth=6, include_root=True):
                            child = search.critical_pair(aa, bb, 0, pi, path)
                            if child is None:
                                continue
                            calls += 1
                            out.add(alpha(child))
        return frozenset(out), calls

    labelled = [("base", q) for q in base_objects]
    labelled += [("reducer", q) for q in reducers]
    labelled += [("fiber", q) for q in fibers]
    signatures = []
    total_calls = 0
    for kind, q in labelled:
        sig, calls = future_signature(q)
        total_calls += calls
        signatures.append((kind, q, sig))

    # Quotient by exact bounded future equality.
    class_of = {}
    classes = []
    sig_to_class = {}
    for idx, (kind, q, sig) in enumerate(signatures):
        cid = sig_to_class.get(sig)
        if cid is None:
            cid = len(classes)
            sig_to_class[sig] = cid
            classes.append({"signature": sig, "members": []})
        class_of[idx] = cid
        classes[cid]["members"].append(idx)

    base_class_ids = {class_of[i] for i, x in enumerate(signatures) if x[0] == "base"}
    reducer_class_ids = {class_of[i] for i, x in enumerate(signatures) if x[0] == "reducer"}
    fiber_class_ids = {class_of[i] for i, x in enumerate(signatures) if x[0] == "fiber"}
    new_reducer_classes = sorted(reducer_class_ids - base_class_ids)
    new_fiber_classes = sorted(fiber_class_ids - base_class_ids)

    # Local dominance: A dominates B iff Future(B) subset Future(A).
    dominance = set()
    for i, ci in enumerate(classes):
        for j, cj in enumerate(classes):
            if i != j and cj["signature"] < ci["signature"]:
                dominance.add((i, j))
    covers = []
    for i, j in sorted(dominance):
        if not any((i, k) in dominance and (k, j) in dominance for k in range(len(classes)) if k not in (i, j)):
            covers.append((i, j))

    def snap(kind, q, sig, cid):
        return {
            "kind": kind,
            "class": cid,
            "future_size": len(sig),
            "profile": list(profile(q)),
            "lhs": m.render_term(q.lhs),
            "rhs": m.render_term(q.rhs),
            "term_size": m.term_size(q.lhs) + m.term_size(q.rhs),
        }

    special = []
    for i, (kind, q, sig) in enumerate(signatures):
        if kind != "base":
            special.append(snap(kind, q, sig, class_of[i]))

    report = {
        "id": row["id"],
        "source_profile": list(source_profile),
        "world_clauses": len(search.clauses),
        "world_enumerated": enumerated,
        "objects": len(base_objects),
        "probe_partners": len(probes),
        "future_calls": total_calls,
        "base_classes": len(base_class_ids),
        "all_classes": len(classes),
        "reducers": len(reducers),
        "fibers": len(fibers),
        "new_reducer_classes": new_reducer_classes,
        "new_fiber_classes": new_fiber_classes,
        "reducers_split_quotient": bool(new_reducer_classes),
        "fibers_split_quotient": bool(new_fiber_classes),
        "dominance_edges": len(dominance),
        "cover_edges": len(covers),
        "special": special,
        "covers_touching_new": [
            [a, b] for a, b in covers
            if a in set(new_reducer_classes + new_fiber_classes)
            or b in set(new_reducer_classes + new_fiber_classes)
        ][:64],
    }
    print("LOCAL_FUTURE_QUOTIENT " + json.dumps(report, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
