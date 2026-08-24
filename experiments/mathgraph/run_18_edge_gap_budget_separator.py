import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

GAPS = [
    (2666, 2860),
    (2860, 2062),
    (3366, 41),
    (1367, 678),
    (2920, 1151),
    (1151, 689),
]

STRONG_LIMITS = {
    'maximum_term_size': 65,
    'maximum_replay_term_size': 260,
    'maximum_depth': 12,
    'maximum_rules': 768,
    'maximum_rounds': 64,
    'new_clauses_per_round': 512,
    'maximum_clauses': 12000,
    'normalization_steps': 256,
    'maximum_proof_nodes': 50000,
}

WIDE_EQUALITY_LIMITS = {
    'max_term_size': 21,
    'max_pool_terms': 80,
    'max_core_terms': 12,
    'max_source_edges': 6000,
    'max_graph_edges': 16000,
    'max_derivation_nodes': 17000,
    'max_congruence_rounds': 5,
}


def replay_recipe(m, source, recipe, max_term=260, max_nodes=50000):
    if not (isinstance(recipe, tuple) and len(recipe) == 2):
        return False, None
    nodes, root = recipe
    try:
        ok = m.replay_dag(source, nodes, root)
    except TypeError:
        ok = m.replay_dag(
            source, nodes, root,
            maximum_term_size=max_term,
            maximum_nodes=max_nodes,
        )
    return bool(ok), h.proof_summary(nodes, root)


def run_strong(m, source, target):
    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update(STRONG_LIMITS)
    start = time.monotonic()
    engine = m.TargetGroundedRefutation(source, target, time.monotonic() + 30.0, limits)
    recipe = engine.solve()
    seconds = time.monotonic() - start
    replayed, proof = replay_recipe(m, source, recipe)
    return {
        'found': bool(recipe),
        'replayed': replayed,
        'proof': proof,
        'seconds': seconds,
        'clauses': len(getattr(engine.search, 'clauses', ())),
        'rounds': getattr(engine.search, 'rounds', None),
        'superpositions': getattr(engine.search, 'superpositions', None),
        'reductions': getattr(engine.search, 'reductions', None),
    }


def run_wide_equality(m, source, target):
    start = time.monotonic()
    search = m.EqualitySearch(
        source, target, time.monotonic() + 12.0, limits=dict(WIDE_EQUALITY_LIMITS)
    )
    found = search.solve()
    result = {
        'found': bool(found),
        'seconds': time.monotonic() - start,
        'exhaustion': getattr(search, 'exhaustion', None),
        'graph_edges': getattr(search, 'graph_edges', None),
        'nodes': len(getattr(search, 'nodes', ())),
        'generations': getattr(search, 'generations_completed', None),
    }
    if isinstance(found, tuple) and len(found) == 2:
        nodes, root = found
        result['proof'] = h.proof_summary(nodes, root)
        try:
            result['replayed'] = bool(m.replay_dag(source, nodes, root))
        except TypeError:
            result['replayed'] = bool(m.replay_dag(
                source, nodes, root,
                maximum_term_size=WIDE_EQUALITY_LIMITS['max_term_size'],
                maximum_nodes=WIDE_EQUALITY_LIMITS['max_derivation_nodes'],
            ))
    else:
        result['replayed'] = False
    return result


def main():
    equations = h.load_equations()
    m = h.load_solver()
    out = {
        'schema': 'mathgraph.18-edge-gap-budget-separator.v1',
        'gaps': GAPS,
        'strong_limits': STRONG_LIMITS,
        'wide_equality_limits': WIDE_EQUALITY_LIMITS,
        'rows': [],
    }
    for source_id, target_id in GAPS:
        source = m.parse_equation(equations[source_id])
        target = m.parse_equation(equations[target_id])
        row = {
            'source_id': source_id,
            'target_id': target_id,
            'source_equation': equations[source_id],
            'target_equation': equations[target_id],
        }
        try:
            row['strong_target_grounded'] = run_strong(m, source, target)
        except Exception as error:
            row['strong_target_grounded'] = {
                'found': False,
                'replayed': False,
                'error': type(error).__name__ + ': ' + str(error),
            }
        try:
            row['wide_equality'] = run_wide_equality(m, source, target)
        except Exception as error:
            row['wide_equality'] = {
                'found': False,
                'replayed': False,
                'error': type(error).__name__ + ': ' + str(error),
            }
        out['rows'].append(row)
        print(json.dumps({
            'edge': f'{source_id}->{target_id}',
            'strong_found': row['strong_target_grounded'].get('found'),
            'strong_replayed': row['strong_target_grounded'].get('replayed'),
            'strong_seconds': row['strong_target_grounded'].get('seconds'),
            'wide_found': row['wide_equality'].get('found'),
            'wide_replayed': row['wide_equality'].get('replayed'),
            'wide_exhaustion': row['wide_equality'].get('exhaustion'),
        }, sort_keys=True), flush=True)

    out['strong_replayed_count'] = sum(
        bool(r['strong_target_grounded'].get('replayed')) for r in out['rows']
    )
    out['strong_gaps'] = [
        [r['source_id'], r['target_id']]
        for r in out['rows'] if not r['strong_target_grounded'].get('replayed')
    ]
    out['wide_equality_replayed_count'] = sum(
        bool(r['wide_equality'].get('replayed')) for r in out['rows']
    )
    out['wide_equality_gaps'] = [
        [r['source_id'], r['target_id']]
        for r in out['rows'] if not r['wide_equality'].get('replayed')
    ]

    path = Path('experiments/mathgraph/results/18-edge-gap-budget-separator.json')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('SUMMARY', json.dumps({
        'strong_replayed': out['strong_replayed_count'],
        'strong_gaps': out['strong_gaps'],
        'wide_replayed': out['wide_equality_replayed_count'],
        'wide_gaps': out['wide_equality_gaps'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
