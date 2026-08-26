#!/usr/bin/env python3
"""Test generic target-subterm materialization plus rigid-preserving parent views."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'experiments/mathgraph/run_796_0040_materialize_overlap_continue.py'
source = BASE.read_text()

marker = 'def main():\n'
helper = r'''
def expand_rigid_recipe_for_overlap(recipe, engine, m, cache=None):
    cache = {} if cache is None else cache
    if id(recipe) in cache:
        return cache[id(recipe)]
    def expand(term):
        if term[0] == "var":
            name = term[1]
            if name in engine.reverse_constants:
                return expand(engine.reverse_constants[name])
            return term
        return ("op", expand(term[1]), expand(term[2]))
    parents = tuple(expand_rigid_recipe_for_overlap(p, engine, m, cache) for p in recipe.parents)
    data = recipe.data
    if recipe.kind == "source":
        substitution, reverse = data
        data = (tuple((v, expand(x)) for v, x in substitution), reverse)
    elif recipe.kind == "instantiate":
        data = tuple((v, expand(x)) for v, x in data)
    elif recipe.kind == "congruence":
        data = (data[0], expand(data[1]))
    result = m.Recipe(expand(recipe.lhs), expand(recipe.rhs), recipe.kind, parents, data)
    cache[id(recipe)] = result
    return result

def install_target_materialized_parent_views(engine, m):
    original_rules = engine.search.rules
    rigid = engine.search.m
    target_terms = []
    seen_terms = set()
    for term in engine.reverse_constants.values():
        expanded = expand_rigid_recipe_for_overlap(m.Recipe(term, term, "reflexivity"), engine, m).lhs
        key = m.render_term(expanded)
        if key not in seen_terms:
            seen_terms.add(key)
            target_terms.append(expanded)
    target_terms.sort(key=lambda t: (m.term_size(t), m.render_term(t)))

    stats = {"calls": 0, "raw_materializations": 0, "retained_views": 0}
    def rules_with_materialized_views():
        stats["calls"] += 1
        base = original_rules()
        candidates = []
        seen = set()

        def offer(candidate):
            if max(rigid.term_size(candidate.lhs), rigid.term_size(candidate.rhs)) > engine.search.limits["maximum_term_size"]:
                return
            sig = engine.search.alpha_signature(candidate.lhs, candidate.rhs)
            rev = engine.search.alpha_signature(candidate.rhs, candidate.lhs)
            key = min((sig, rev))
            if key in seen:
                return
            seen.add(key)
            candidates.append(candidate)

        for rule in base:
            expanded = expand_rigid_recipe_for_overlap(rule, engine, m)
            offer(rule)
            offer(expanded)
            # Strategically instantiate a schematic parent only where one of
            # its structural subterms matches an actual rigid target subterm.
            # This is bounded by target structure, not arbitrary substitutions.
            for side in (expanded.lhs, expanded.rhs):
                for path in rigid.nonvariable_positions(
                    side,
                    maximum_depth=engine.search.limits["maximum_depth"],
                    include_root=True,
                ):
                    pattern = rigid.get_subterm(side, path)
                    if not rigid.term_variables(pattern):
                        continue
                    for concrete in target_terms:
                        mapping = {}
                        if not rigid.match_term(pattern, concrete, mapping) or not mapping:
                            continue
                        instantiated = engine.search.instantiate(expanded, mapping)
                        stats["raw_materializations"] += 1
                        offer(instantiated)

        candidates.sort(key=engine.search.target_score)
        result = candidates[:engine.search.limits["maximum_rules"]]
        stats["retained_views"] += len(result)
        return result

    engine.search.rules = rules_with_materialized_views
    engine.materialized_parent_stats = stats

'''
if marker not in source:
    raise SystemExit('main marker missing')
source = source.replace(marker, helper + marker, 1)

baseline_needle = '        baseline = engine.solve()\n'
if source.count(baseline_needle) != 1:
    raise SystemExit('baseline solve marker missing')
source = source.replace(
    baseline_needle,
    '        install_target_materialized_parent_views(engine, m)\n        baseline = engine.solve()\n',
    1,
)

out_needle = "out={'id':RID,'baseline_found':bool(baseline)"
if source.count(out_needle) != 1:
    raise SystemExit('output marker missing')
source = source.replace(
    out_needle,
    "out={'id':RID,'baseline_found':bool(baseline),'generic_materialization_stats':dict(engine.materialized_parent_stats)",
    1,
)

# Keep the known corridor diagnostics as a control.
needle = "q,details=derive_pair(mats.get('f19'),f196mat,'f217',('f19-f196-remat','f196-remat-f19'))"
replacement = "f19e=expand_rigid_recipe_for_overlap(mats.get('f19'),engine,m); f196e=expand_rigid_recipe_for_overlap(f196mat,engine,m); q,details=derive_pair(f19e,f196e,'f217',('f19-rigid-expand-f196-rigid-expand','f196-rigid-expand-f19-rigid-expand'))"
if source.count(needle) != 1:
    raise SystemExit('expected one f217 rematerialized derive site')
source = source.replace(needle, replacement, 1)

code = compile(source, str(BASE) + ':generic-target-materialized-parent-views', 'exec')
exec(code, {'__name__': '__main__', '__file__': str(BASE)})
