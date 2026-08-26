#!/usr/bin/env python3
"""Test generic rigid-preserving expanded parent views in target-grounded search."""
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

def install_expanded_parent_views(engine, m):
    original_rules = engine.search.rules
    def rules_with_expanded_views():
        base = original_rules()
        candidates = []
        seen = set()
        for rule in base:
            for candidate in (rule, expand_rigid_recipe_for_overlap(rule, engine, m)):
                if max(engine.search.m.term_size(candidate.lhs), engine.search.m.term_size(candidate.rhs)) > engine.search.limits["maximum_term_size"]:
                    continue
                sig = engine.search.alpha_signature(candidate.lhs, candidate.rhs)
                rev = engine.search.alpha_signature(candidate.rhs, candidate.lhs)
                key = min((sig, rev))
                if key in seen:
                    continue
                seen.add(key)
                candidates.append(candidate)
        candidates.sort(key=engine.search.target_score)
        return candidates[:engine.search.limits["maximum_rules"]]
    engine.search.rules = rules_with_expanded_views

'''
if marker not in source:
    raise SystemExit('main marker missing')
source = source.replace(marker, helper + marker, 1)

baseline_needle = '        baseline = engine.solve()\n'
if source.count(baseline_needle) != 1:
    raise SystemExit('baseline solve marker missing')
source = source.replace(baseline_needle, '        install_expanded_parent_views(engine, m)\n        baseline = engine.solve()\n', 1)

# Keep the known corridor diagnostics as a control; if generic search succeeds,
# baseline_found becomes true before any Vampire-guided materialization executes.
needle = "q,details=derive_pair(mats.get('f19'),f196mat,'f217',('f19-f196-remat','f196-remat-f19'))"
replacement = "f19e=expand_rigid_recipe_for_overlap(mats.get('f19'),engine,m); f196e=expand_rigid_recipe_for_overlap(f196mat,engine,m); q,details=derive_pair(f19e,f196e,'f217',('f19-rigid-expand-f196-rigid-expand','f196-rigid-expand-f19-rigid-expand'))"
if source.count(needle) != 1:
    raise SystemExit('expected one f217 rematerialized derive site')
source = source.replace(needle, replacement, 1)

code = compile(source, str(BASE) + ':generic-expanded-parent-views', 'exec')
exec(code, {'__name__': '__main__', '__file__': str(BASE)})
