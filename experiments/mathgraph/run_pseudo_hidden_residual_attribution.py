import importlib.util
import json
import sys
import time
from pathlib import Path

SOLVER = Path('submissions/mathgraph/solver.py')
SPEC = importlib.util.spec_from_file_location('mg_residual', SOLVER)
m = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = m
SPEC.loader.exec_module(m)

WANTED = {
    'hard1_0067': True, 'hard1_0005': False, 'hard1_0017': False,
    'hard2_0107': True, 'hard2_0098': True, 'hard2_0021': True,
    'hard2_0199': True, 'hard2_0165': False,
    'hard3_0197': True, 'hard3_0199': True, 'hard3_0208': True,
}


def load_rows():
    rows = {}
    for path in Path('examples/problems').glob('*.jsonl'):
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            if row.get('id') in WANTED:
                rows[row['id']] = row
    missing = sorted(set(WANTED) - set(rows))
    if missing:
        raise SystemExit(f'missing residual rows: {missing}')
    return rows


def replay(source, target, result, maximum_term_size=256, maximum_nodes=50000):
    if not (isinstance(result, tuple) and len(result) == 2):
        return False
    nodes, root = result
    try:
        return bool(
            (nodes[root].lhs, nodes[root].rhs) == target[:2]
            and m.replay_dag(
                source, nodes, root,
                maximum_term_size=maximum_term_size,
                maximum_nodes=maximum_nodes,
            )
        )
    except Exception:
        return False


def probe_true(source, target):
    attempts = []

    for seconds in (2.0, 5.0):
        started = time.monotonic()
        try:
            search = m.EqualitySearch(source, target, time.monotonic() + seconds)
            result = search.solve()
            ok = replay(source, target, result,
                        maximum_term_size=getattr(search, 'max_term_size', 256),
                        maximum_nodes=getattr(search, 'max_derivation_nodes', 50000))
            attempts.append({
                'route': f'equality-search-{seconds:g}s', 'closed': ok,
                'seconds': time.monotonic() - started,
                'nodes': len(getattr(search, 'nodes', ())),
                'edges': getattr(search, 'graph_edges', None),
                'exhaustion': getattr(search, 'exhaustion', None),
            })
            if ok:
                return attempts
        except Exception as exc:
            attempts.append({'route': f'equality-search-{seconds:g}s', 'closed': False,
                             'error': type(exc).__name__})

    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        'seconds': 5.0,
        'maximum_term_size': 80,
        'maximum_replay_term_size': 256,
        'maximum_depth': 14,
        'maximum_rules': 384,
        'maximum_rounds': 64,
        'new_clauses_per_round': 256,
        'maximum_clauses': 12000,
        'normalization_steps': 192,
        'maximum_proof_nodes': 50000,
    })
    started = time.monotonic()
    try:
        search = m.CompactSuperposition(
            m, source, target, time.monotonic() + 5.0, limits
        )
        recipe = search.solve()
        result = search.compile(recipe) if recipe is not None else None
        ok = replay(source, target, result, 256, 50000)
        attempts.append({
            'route': 'compact-superposition-expanded', 'closed': ok,
            'seconds': time.monotonic() - started,
            'clauses': len(getattr(search, 'clauses', ())),
            'rounds': getattr(search, 'rounds', None),
            'superpositions': getattr(search, 'superpositions', None),
            'reductions': getattr(search, 'reductions', None),
        })
    except Exception as exc:
        attempts.append({'route': 'compact-superposition-expanded', 'closed': False,
                         'error': type(exc).__name__})
    return attempts


def probe_false(source, target):
    attempts = []
    configs = [
        (3, 5.0, 250000, 50000),
        (4, 7.0, 500000, 100000),
    ]
    for domain, seconds, states, models in configs:
        started = time.monotonic()
        try:
            search = m.FiniteModelEngine(
                domain, source, target, time.monotonic() + seconds,
                states, models,
            )
            found = search.search_target_guided()
            closed = found is not None
            attempts.append({
                'route': f'fin{domain}-target-guided-expanded',
                'closed': closed,
                'seconds': time.monotonic() - started,
                'states': getattr(search, 'states', None),
                'models': getattr(search, 'models', None),
                'exhaustion': getattr(search, 'exhaustion', None),
            })
            if closed:
                return attempts
        except Exception as exc:
            attempts.append({'route': f'fin{domain}-target-guided-expanded',
                             'closed': False, 'error': type(exc).__name__})
    return attempts


def main():
    rows = load_rows()
    output = []
    for rid in sorted(WANTED):
        row = rows[rid]
        source = m.parse_equation(row['equation1'])
        target = m.parse_equation(row['equation2'])
        expected = WANTED[rid]
        attempts = probe_true(source, target) if expected else probe_false(source, target)
        closed = any(a.get('closed') for a in attempts)
        item = {'id': rid, 'expected': expected, 'closed': closed, 'attempts': attempts}
        output.append(item)
        print('RESIDUAL_CASE', json.dumps(item, sort_keys=True), flush=True)

    closed = [x['id'] for x in output if x['closed']]
    open_ = [x['id'] for x in output if not x['closed']]
    summary = {
        'schema': 'mathgraph.pseudo-hidden-residual-attribution.v1',
        'n': len(output),
        'closed_count': len(closed),
        'open_count': len(open_),
        'closed': closed,
        'still_open': open_,
        'rows': output,
    }
    out = Path('experiments/mathgraph/results/pseudo-hidden-residual-attribution.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('RESIDUAL_SUMMARY', json.dumps({k: summary[k] for k in ('n','closed_count','open_count','closed','still_open')}, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
