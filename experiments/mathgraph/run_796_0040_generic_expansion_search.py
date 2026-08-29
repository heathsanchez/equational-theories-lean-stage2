#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from judge.verify import _resolve_config, verify_answer

SOLVER = ROOT / 'submissions/mathgraph/solver.py'
RID = 'evaluation_normal_0040'


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load_row(path):
    with open(path) as f:
        for line in f:
            row = json.loads(line)
            if row.get('id') == RID:
                return row
    raise RuntimeError('0040 not found')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', required=True)
    ap.add_argument('--output', required=True)
    ap.add_argument('--seconds', type=float, default=120.0)
    a = ap.parse_args()

    m = load(SOLVER, 'mg_generic_expansion_search')
    row = load_row(a.input)
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])
    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        'seconds': a.seconds,
        'maximum_term_size': 65,
        'maximum_replay_term_size': 300,
        'maximum_depth': 12,
        'maximum_rules': 768,
        'maximum_rounds': 64,
        'new_clauses_per_round': 512,
        'maximum_clauses': 12000,
        'normalization_steps': 256,
        'maximum_proof_nodes': 60000,
    })
    engine = m.TargetGroundedRefutation(source, target, time.monotonic() + a.seconds, limits)
    original_cp = engine.search.critical_pair
    expansion_calls = 0
    expansion_changed = 0

    def expand_term(term):
        if term[0] == 'var' and term[1] in engine.reverse_constants:
            return expand_term(engine.reverse_constants[term[1]])
        if term[0] == 'op':
            return ('op', expand_term(term[1]), expand_term(term[2]))
        return term

    def expand_recipe(recipe, cache=None):
        cache = {} if cache is None else cache
        if id(recipe) in cache:
            return cache[id(recipe)]
        parents = tuple(expand_recipe(p, cache) for p in recipe.parents)
        data = recipe.data
        if recipe.kind == 'source':
            sub, rev = data
            data = (tuple((k, expand_term(v)) for k, v in sub), rev)
        elif recipe.kind == 'instantiate':
            data = tuple((k, expand_term(v)) for k, v in data)
        elif recipe.kind == 'congruence':
            data = (data[0], expand_term(data[1]))
        out = m.Recipe(expand_term(recipe.lhs), expand_term(recipe.rhs), recipe.kind, parents, data)
        cache[id(recipe)] = out
        return out

    def expanded_cp(outer, inner, outer_index, inner_index, path):
        nonlocal expansion_calls, expansion_changed
        expansion_calls += 1
        eo = expand_recipe(outer)
        ei = expand_recipe(inner)
        if (eo.lhs, eo.rhs, ei.lhs, ei.rhs) != (outer.lhs, outer.rhs, inner.lhs, inner.rhs):
            expansion_changed += 1
        return original_cp(eo, ei, outer_index, inner_index, path)

    engine.search.critical_pair = expanded_cp
    start = time.monotonic()
    recipe = engine.search.solve()
    elapsed = time.monotonic() - start
    out = {
        'id': RID,
        'found_recipe': bool(recipe),
        'seconds': elapsed,
        'rounds': engine.search.rounds,
        'clauses': len(engine.search.clauses),
        'generated': engine.search.generated,
        'superpositions': engine.search.superpositions,
        'reductions': engine.search.reductions,
        'expansion_calls': expansion_calls,
        'expansion_changed': expansion_changed,
        'target_hit': False,
        'replay': False,
        'proof_nodes': None,
        'certificate_bytes': None,
        'judge_status': None,
        'judge_error_code': None,
    }
    if recipe is not None:
        rr = engine.inline_recipe(recipe)
        compiler = m.CompactSuperposition(m, source, target, time.monotonic() + 3.0, limits)
        nodes, root = compiler.compile(rr)
        out['target_hit'] = (nodes[root].lhs, nodes[root].rhs) == target[:2]
        out['replay'] = bool(m.replay_dag(source, nodes, root, maximum_term_size=limits['maximum_replay_term_size'], maximum_nodes=limits['maximum_proof_nodes']))
        if out['target_hit'] and out['replay']:
            code, proof_nodes = m.make_dag_certificate(target, nodes, root)
            if hasattr(m, '_mg_elide_have_types'):
                code = m._mg_elide_have_types(code)
            out['proof_nodes'] = proof_nodes
            out['certificate_bytes'] = len(code.encode('utf-8'))
            if out['certificate_bytes'] <= 100000:
                cfg = replace(_resolve_config(None), max_code_length=100000)
                result = verify_answer(row, json.dumps({'verdict': 'true', 'code': code}), config=cfg)
                out['judge_status'] = result.get('status')
                out['judge_error_code'] = result.get('error_code')
                out['judge_message'] = result.get('message')
    Path(a.output).parent.mkdir(parents=True, exist_ok=True)
    Path(a.output).write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('GENERIC_EXPANSION_SEARCH', json.dumps(out, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
