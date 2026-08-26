#!/usr/bin/env python3
"""Test rigid-preserving expansion and whether replayed f278 is the 0040 goal."""
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

    parents = tuple(
        expand_rigid_recipe_for_overlap(parent, engine, m, cache)
        for parent in recipe.parents
    )
    data = recipe.data
    if recipe.kind == "source":
        substitution, reverse = data
        data = (tuple((variable, expand(value)) for variable, value in substitution), reverse)
    elif recipe.kind == "instantiate":
        data = tuple((variable, expand(value)) for variable, value in data)
    elif recipe.kind == "congruence":
        data = (data[0], expand(data[1]))
    result = m.Recipe(expand(recipe.lhs), expand(recipe.rhs), recipe.kind, parents, data)
    cache[id(recipe)] = result
    return result

'''
if marker not in source:
    raise SystemExit('main marker missing')
source = source.replace(marker, helper + marker, 1)

needle = "q,details=derive_pair(mats.get('f19'),f196mat,'f217',('f19-f196-remat','f196-remat-f19'))"
replacement = "f19e=expand_rigid_recipe_for_overlap(mats.get('f19'),engine,m); f196e=expand_rigid_recipe_for_overlap(f196mat,engine,m); out['rigid_expand_trace']={'f19':[m.render_term(f19e.lhs),m.render_term(f19e.rhs)],'f196':[m.render_term(f196e.lhs),m.render_term(f196e.rhs)]}; forced=engine.search.critical_pair(orient(f19e,True),orient(f196e,True),0,1,('L',)); out['rigid_expand_trace']['forced_none']=forced is None; out['rigid_expand_trace']['forced_clause']=None if forced is None else [m.render_term(engine.inline_recipe(forced).lhs),m.render_term(engine.inline_recipe(forced).rhs)]; out['rigid_expand_trace']['forced_replay']=False if forced is None else replay_recipe(forced)[0]; q,details=derive_pair(f19e,f196e,'f217',('f19-rigid-expand-f196-rigid-expand','f196-rigid-expand-f19-rigid-expand'))"
if source.count(needle) != 1:
    raise SystemExit('expected one f217 rematerialized derive site')
source = source.replace(needle, replacement, 1)

needle278 = "derive_and_add(mats.get('f15'),derived.get('f259'),'f278',('f15-f259','f259-f15'))"
replacement278 = "f278=derive_and_add(mats.get('f15'),derived.get('f259'),'f278',('f15-f259','f259-f15')); out['f278_goal']={'present':f278 is not None};\n            if f278 is not None:\n                f278i=engine.inline_recipe(f278); out['f278_goal'].update({'clause':[m.render_term(f278i.lhs),m.render_term(f278i.rhs)],'target':[m.render_term(target[0]),m.render_term(target[1])],'exact':(f278i.lhs,f278i.rhs)==target[:2] or (f278i.rhs,f278i.lhs)==target[:2]}); nodes278,root278=engine.search.compile(f278i); out['f278_goal'].update({'nodes':len(nodes278),'replay':bool(m.replay_dag(source,nodes278,root278,maximum_term_size=260,maximum_nodes=50000)),'compiled':[m.render_term(nodes278[root278].lhs),m.render_term(nodes278[root278].rhs)]})"
if source.count(needle278) != 1:
    raise SystemExit('expected one f278 derive site')
source = source.replace(needle278, replacement278, 1)

code = compile(source, str(BASE) + ':rigid-expand-f278-goal', 'exec')
exec(code, {'__name__': '__main__', '__file__': str(BASE)})
