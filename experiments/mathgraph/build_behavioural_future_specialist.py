#!/usr/bin/env python3
"""Build the Stage 2 solver with the verified behavioural-future fallback.

The generated fallback is deliberately problem-blind.  It receives only the
parsed source/target equations and the ordinary solver budget.  It does not
contain evaluation IDs, proof IDs, named bridge equations, public recipes, or
benchmark labels.

The mechanism is the frozen one that was first isolated on normal_0040 and
then transferred unchanged to fresh rows: two independently scheduled bounded
proof worlds are crossed, candidate equations are retained only when they add
a previously unseen one-step future behaviour, a low-novelty bridge tail is
recursively promoted, and final recognition is performed only after recipe
inlining.  Every emitted proof is independently replayed before the official
judge is called.
"""

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASE = ROOT / "submissions/mathgraph/solver.py"
MARKER = "# MATHGRAPH_BEHAVIOURAL_FUTURE_V1"
INSERT_BEFORE = "\ndef run_solo():\n"
CALL_BEFORE = "    # Unresolved: EOF is intentional. Never guess and never ask an LLM.\n"

FALLBACK = r'''

# MATHGRAPH_BEHAVIOURAL_FUTURE_V1
# Generic residual-driven representation repair.  This is intentionally a
# late fallback: all previously promoted deterministic routes run first.
def run_behavioural_future_fallback(source, target, timeout):
    frontier_seconds = min(12.0, max(0.5, timeout / 40.0))
    given_seconds = min(5.0, max(0.5, timeout / 80.0))
    frontier_rounds = 3
    given_steps = 16
    candidate_budget = 512
    behavioural_keep = 512
    probe_partners = 64
    closure_rounds = 2
    closure_new_per_round = 128
    tail_novelty_max = 80

    base = dict(COMPACT_SUPERPOSITION_PROBE)
    base.update({
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

    def setup(seconds):
        limits = dict(base)
        limits["seconds"] = seconds
        engine = TargetGroundedRefutation(
            source, target, time.monotonic() + seconds, limits
        )
        search = engine.search
        original_critical_pair = search.critical_pair

        # Target grounding introduces reverse constants.  Before worlds are
        # crossed, rematerialize them back into ordinary terms so the
        # cross-world equation remains a theorem of the original source.
        def expand_term(term):
            if term[0] == "var" and term[1] in engine.reverse_constants:
                return expand_term(engine.reverse_constants[term[1]])
            if term[0] == "op":
                return ("op", expand_term(term[1]), expand_term(term[2]))
            return term

        def expand_recipe(recipe, cache=None):
            cache = {} if cache is None else cache
            key = id(recipe)
            if key in cache:
                return cache[key]
            parents = tuple(expand_recipe(p, cache) for p in recipe.parents)
            data = recipe.data
            if recipe.kind == "source":
                substitution, reverse = data
                data = (
                    tuple((k, expand_term(v)) for k, v in substitution),
                    reverse,
                )
            elif recipe.kind == "instantiate":
                data = tuple((k, expand_term(v)) for k, v in data)
            elif recipe.kind == "congruence":
                data = (data[0], expand_term(data[1]))
            expanded = Recipe(
                expand_term(recipe.lhs), expand_term(recipe.rhs),
                recipe.kind, parents, data,
            )
            cache[key] = expanded
            return expanded

        def safe_critical_pair(outer, inner, outer_index, inner_index, path):
            return original_critical_pair(
                expand_recipe(outer), expand_recipe(inner),
                outer_index, inner_index, path,
            )

        search.critical_pair = safe_critical_pair
        return engine, search, original_critical_pair, expand_recipe

    def orient(recipe, reverse):
        if not reverse:
            return recipe
        return Recipe(recipe.rhs, recipe.lhs, "symmetry", (recipe,))

    def exact_target(engine, recipe):
        inlined = engine.inline_recipe(recipe)
        endpoints = (inlined.lhs, inlined.rhs)
        return endpoints == target[:2] or endpoints == (target[1], target[0])

    def finish(engine, search, recipe):
        if recipe is None:
            return False
        inlined = engine.inline_recipe(recipe)
        if (inlined.lhs, inlined.rhs) == (target[1], target[0]):
            inlined = Recipe(
                inlined.rhs, inlined.lhs, "symmetry", (inlined,)
            )
        if (inlined.lhs, inlined.rhs) != target[:2]:
            return False
        nodes, root = search.compile(inlined)
        if not replay_dag(
            source, nodes, root,
            maximum_term_size=300, maximum_nodes=60000,
        ):
            return False
        code, proof_nodes = make_dag_certificate(target, nodes, root)
        if "_mg_elide_have_types" in globals():
            old_lines = code.splitlines()
            new_lines = _mg_elide_have_types(code).splitlines()
            code = "\n".join(
                old if ":=" in old and old.rstrip().endswith(":= rfl") else new
                for old, new in zip(old_lines, new_lines)
            ) + "\n"
        code_bytes = len(code.encode("utf-8"))
        print(
            "MATHGRAPH_METRICS " + json.dumps({
                "portfolio": "behavioural-future-v1",
                "found": True,
                "proof_nodes": proof_nodes,
                "certificate_bytes": code_bytes,
            }, separators=(",", ":")),
            file=sys.stderr, flush=True,
        )
        if code_bytes > 100000:
            return False
        return judge("true", code).get("status") == "accepted"

    try:
        # World A: streaming frontier.
        frontier_engine, frontier, frontier_pair, expand_frontier = setup(
            frontier_seconds
        )
        frontier_enumerated = 0
        batch_size = 128
        for _ in range(frontier_rounds):
            rules = frontier.rules()
            snapshot = list(rules)
            proposals = []
            for outer_index, outer in enumerate(snapshot):
                for inner_index, inner in enumerate(snapshot):
                    for path in nonvariable_positions(
                        outer.lhs, maximum_depth=12, include_root=True
                    ):
                        if frontier.expired():
                            break
                        candidate = frontier.critical_pair(
                            outer, inner, outer_index, inner_index, path
                        )
                        if candidate is None:
                            continue
                        candidate = frontier.interreduce(candidate, rules)
                        proposals.append((frontier.target_score(candidate), candidate))
                        frontier_enumerated += 1
                        if len(proposals) >= batch_size:
                            proposals.sort(key=lambda item: item[0])
                            added = 0
                            for _, proposal in proposals:
                                if frontier.add_clause(proposal):
                                    frontier.superpositions += 1
                                    added += 1
                                if added >= 64:
                                    break
                            proposals = []
                            rules = frontier.rules()
                    if frontier.expired():
                        break
                if frontier.expired():
                    break
            if proposals and not frontier.expired():
                proposals.sort(key=lambda item: item[0])
                added = 0
                for _, proposal in proposals:
                    if frontier.add_clause(proposal):
                        frontier.superpositions += 1
                        added += 1
                    if added >= 64:
                        break
            if frontier.expired():
                break

        # World B: age/focus given-clause activation.
        given_engine, given, given_pair, expand_given = setup(given_seconds)

        def variants(search, clause):
            oriented = search.orient(clause)
            if oriented is not None:
                return [oriented]
            out = []
            if clause.lhs[0] != "var":
                out.append(clause)
            if clause.rhs[0] != "var":
                out.append(Recipe(
                    clause.rhs, clause.lhs, "symmetry", (clause,)
                ))
            return out

        def rule_key(search, recipe):
            return (
                search.alpha_signature(recipe.lhs, recipe.rhs),
                recipe.lhs, recipe.rhs,
            )

        pending = []
        queued = set()
        processed = set()
        active = []

        def enqueue(recipe):
            key = rule_key(given, recipe)
            if key in queued or key in processed:
                return
            queued.add(key)
            pending.append(recipe)

        for recipe in given.rules():
            enqueue(recipe)
        givens = 0
        given_enumerated = 0
        while pending and not given.expired() and givens < given_steps:
            pending.sort(key=given.target_score)
            selected = pending.pop(0)
            key = rule_key(given, selected)
            queued.discard(key)
            if key in processed:
                continue
            processed.add(key)
            givens += 1
            rules = given.rules()
            proposals = []
            pairings = []
            for previous in active:
                pairings.extend(((selected, previous), (previous, selected)))
            pairings.append((selected, selected))
            for pair_index, (outer, inner) in enumerate(pairings):
                for path in nonvariable_positions(
                    outer.lhs, maximum_depth=12, include_root=True
                ):
                    if given.expired():
                        break
                    candidate = given.critical_pair(
                        outer, inner, pair_index, pair_index + 1, path
                    )
                    if candidate is None:
                        continue
                    candidate = given.interreduce(candidate, rules)
                    proposals.append((given.target_score(candidate), candidate))
                    given_enumerated += 1
                if given.expired():
                    break
            proposals.sort(key=lambda item: item[0])
            added = 0
            for _, candidate in proposals:
                before = len(given.clauses)
                if given.add_clause(candidate):
                    given.superpositions += 1
                    added += 1
                    for clause in given.clauses[before:]:
                        for recipe in variants(given, clause):
                            enqueue(recipe)
                    if added >= 64:
                        break
            active.append(selected)

        # Build a small protected future basis from both worlds.
        pool = [expand_frontier(c) for c in frontier.clauses]
        pool.extend(expand_frontier(expand_given(c)) for c in given.clauses)
        probes = sorted(pool, key=frontier.target_score)[:probe_partners]

        def signature(candidate):
            return str(frontier.alpha_signature(candidate.lhs, candidate.rhs))

        def future_signature(rule):
            outcomes = set()
            target_child = None
            calls = 0
            for partner_index, partner in enumerate(probes):
                for first, second in ((rule, partner), (partner, rule)):
                    for first_reverse in (False, True):
                        a = orient(first, first_reverse)
                        for second_reverse in (False, True):
                            b = orient(second, second_reverse)
                            for path in nonvariable_positions(
                                a.lhs, maximum_depth=6, include_root=True
                            ):
                                child = frontier_pair(
                                    a, b, 0, partner_index, path
                                )
                                if child is None:
                                    continue
                                calls += 1
                                outcomes.add(signature(child))
                                if exact_target(frontier_engine, child):
                                    target_child = child
            return outcomes, target_child, calls

        baseline = set()
        baseline_calls = 0
        for recipe in probes:
            outcomes, _, calls = future_signature(recipe)
            baseline.update(outcomes)
            baseline_calls += calls

        # Cross the two schedules in both parent directions.  The candidates
        # are still ordinary source consequences; schedule identity is not
        # preserved in the emitted certificate.
        raw = []
        cross_enumerated = 0
        for left_index, left0 in enumerate(frontier.clauses):
            left = expand_frontier(left0)
            for right_index, right0 in enumerate(given.clauses):
                right = expand_frontier(expand_given(right0))
                for first, second, oi, ii in (
                    (left, right, left_index, right_index),
                    (right, left, right_index, left_index),
                ):
                    for first_reverse in (False, True):
                        a = orient(first, first_reverse)
                        for second_reverse in (False, True):
                            b = orient(second, second_reverse)
                            for path in nonvariable_positions(
                                a.lhs, maximum_depth=12, include_root=True
                            ):
                                candidate = frontier_pair(a, b, oi, ii, path)
                                if candidate is None:
                                    continue
                                cross_enumerated += 1
                                raw.append((frontier.target_score(candidate), candidate))
        raw.sort(key=lambda item: item[0])
        candidates = []
        seen = set()
        for score, candidate in raw:
            key = (
                frontier.alpha_signature(candidate.lhs, candidate.rhs),
                candidate.lhs, candidate.rhs,
            )
            if key in seen:
                continue
            seen.add(key)
            candidates.append((score, candidate))
            if len(candidates) >= candidate_budget:
                break

        retained = []
        novelty_sizes = []
        target_recipe = None
        target_origin = None
        current = set(baseline)
        behavioural_tests = 0
        future_calls = 0
        for _, candidate in candidates:
            outcomes, child, calls = future_signature(candidate)
            behavioural_tests += 1
            future_calls += calls
            novelty = outcomes - current
            if not novelty:
                continue
            retained.append(candidate)
            novelty_sizes.append(len(novelty))
            current.update(outcomes)
            if child is not None:
                target_recipe = child
                target_origin = "behavioural-future"
                break
            if len(retained) >= behavioural_keep:
                break

        # Promote only the low-novelty bridge tail into two bounded recursive
        # closure rounds.  This is a measured representation repair, not wider
        # saturation of the original search.
        closure_enumerated = 0
        closure_generated = []
        tail = [
            recipe for recipe, novelty in zip(retained, novelty_sizes)
            if novelty <= tail_novelty_max
        ]
        if target_recipe is None:
            partners = list(pool)
            closure_frontier = list(tail)
            closure_seen = set(
                (frontier.alpha_signature(q.lhs, q.rhs), q.lhs, q.rhs)
                for q in partners + closure_frontier
            )
            for closure_round in range(closure_rounds):
                proposals = []
                for new_index, new in enumerate(closure_frontier):
                    for partner_index, partner in enumerate(partners):
                        for first, second, label in (
                            (new, partner, "tail-frontier-partner"),
                            (partner, new, "tail-partner-frontier"),
                        ):
                            for first_reverse in (False, True):
                                a = orient(first, first_reverse)
                                for second_reverse in (False, True):
                                    b = orient(second, second_reverse)
                                    for path in nonvariable_positions(
                                        a.lhs, maximum_depth=12,
                                        include_root=True,
                                    ):
                                        child = frontier_pair(
                                            a, b, new_index,
                                            partner_index, path,
                                        )
                                        if child is None:
                                            continue
                                        closure_enumerated += 1
                                        if exact_target(frontier_engine, child):
                                            target_recipe = child
                                            target_origin = (
                                                label + "-round-" +
                                                str(closure_round + 1)
                                            )
                                            break
                                        key = (
                                            frontier.alpha_signature(
                                                child.lhs, child.rhs
                                            ), child.lhs, child.rhs,
                                        )
                                        if key not in closure_seen:
                                            closure_seen.add(key)
                                            proposals.append((
                                                frontier.target_score(child),
                                                child,
                                            ))
                                    if target_recipe is not None:
                                        break
                                if target_recipe is not None:
                                    break
                            if target_recipe is not None:
                                break
                        if target_recipe is not None:
                            break
                    if target_recipe is not None:
                        break
                if target_recipe is not None:
                    break
                proposals.sort(key=lambda item: item[0])
                closure_frontier = [
                    q for _, q in proposals[:closure_new_per_round]
                ]
                closure_generated.append(len(closure_frontier))
                if not closure_frontier:
                    break
                partners.extend(closure_frontier)

        print(
            "MATHGRAPH_METRICS " + json.dumps({
                "portfolio": "behavioural-future-v1",
                "found": target_recipe is not None,
                "frontier_clauses": len(frontier.clauses),
                "frontier_enumerated": frontier_enumerated,
                "given_clauses": len(given.clauses),
                "given_steps": givens,
                "given_enumerated": given_enumerated,
                "cross_enumerated": cross_enumerated,
                "candidate_budget": len(candidates),
                "probe_partners": len(probes),
                "baseline_future_signatures": len(baseline),
                "baseline_future_calls": baseline_calls,
                "behavioural_tests": behavioural_tests,
                "future_calls": future_calls,
                "behavioural_retained": len(retained),
                "closure_enumerated": closure_enumerated,
                "closure_generated": closure_generated,
                "target_origin": target_origin,
            }, separators=(",", ":")),
            file=sys.stderr, flush=True,
        )
        return finish(frontier_engine, frontier, target_recipe)
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError,
        ValueError,
    ):
        return False
'''

CALL = '''    # Verified developmental fallback: preserve only distinctions that
    # change reachable future proof behaviour, then replay before judging.
    if run_behavioural_future_fallback(source, target, timeout):
        return

'''


def build(base: Path, output: Path) -> None:
    text = base.read_text()
    if MARKER in text:
        raise SystemExit("behavioural-future fallback is already integrated")
    if INSERT_BEFORE not in text:
        raise SystemExit("run_solo insertion marker not found")
    if CALL_BEFORE not in text:
        raise SystemExit("unresolved insertion marker not found")
    text = text.replace(INSERT_BEFORE, FALLBACK + INSERT_BEFORE, 1)
    text = text.replace(CALL_BEFORE, CALL + CALL_BEFORE, 1)
    if len(text.encode("utf-8")) > 500_000:
        raise SystemExit("generated solver exceeds 500 KB submission cap")
    compile(text, str(output), "exec")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f"built {output} ({len(text.encode('utf-8'))} bytes)")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default=str(DEFAULT_BASE))
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    build(Path(args.base), Path(args.output))


if __name__ == "__main__":
    main()
