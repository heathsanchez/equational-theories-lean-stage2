import json
import re
from pathlib import Path

BASE_TEMPLATE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')
SRC_TEMPLATE = Path('experiments/mathgraph/run_3366_iterated_contextual_contraction.py')
OUT = Path('experiments/mathgraph/results/18-edge-contextual-contraction-transfer.json')

# Frozen residual edges from the 18-edge separator. Five already replay under
# the baseline EqualitySearch and are excluded from this specialist transfer.
EDGES = [
    (2666, 2860), (2860, 2062),
    (3366, 41), (41, 3390),
    (1367, 678), (678, 1696), (1696, 979), (979, 2945),
    (2938, 2922), (2920, 1151), (1151, 689), (688, 2), (41, 3602),
]
# Skip edges known replayed in the frozen 18-edge gate if present above.
KNOWN_REPLAYED = {(2945,2938),(2922,2920),(689,688),(2,41),(3602,3599)}
EDGES = [e for e in EDGES if e not in KNOWN_REPLAYED]


def patch_base(source_id, target_id, base_result):
    s = BASE_TEMPLATE.read_text()
    s = s.replace('eqs[3366]', f'eqs[{source_id}]', 1)
    s = s.replace('eqs[41]', f'eqs[{target_id}]', 1)
    s = s.replace("'edge':'3366->41'", f"'edge':'{source_id}->{target_id}'", 1)
    s = s.replace(
        "Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')",
        f"Path({str(base_result)!r})",
        1,
    )
    return s


def patch_src(base_file, base_result, out_file):
    s = SRC_TEMPLATE.read_text()
    s = s.replace(
        "BASE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')",
        f"BASE = Path({str(base_file)!r})",
        1,
    )
    s = s.replace(
        "BASE_RESULT = Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')",
        f"BASE_RESULT = Path({str(base_result)!r})",
        1,
    )
    s = s.replace(
        "OUT = Path('experiments/mathgraph/results/3366-iterated-contextual-contraction.json')",
        f"OUT = Path({str(out_file)!r})",
        1,
    )
    # Frozen promoted policy: only the two strict contextual generations that
    # succeeded on 3366; no bridge slack and no edge-specific tuning.
    s = s.replace('CONTEXT_GENERATIONS = 3', 'CONTEXT_GENERATIONS = 2', 1)
    return s


def run_edge(source_id, target_id):
    tmp = Path('experiments/mathgraph/.transfer_tmp')
    tmp.mkdir(parents=True, exist_ok=True)
    tag = f'{source_id}_{target_id}'
    base_file = tmp / f'base_{tag}.py'
    base_result = tmp / f'base_{tag}.json'
    out_file = tmp / f'out_{tag}.json'
    base_file.write_text(patch_base(source_id, target_id, base_result))
    src = patch_src(base_file, base_result, out_file)
    ns = {'__name__': f'transfer_{tag}'}
    exec(compile(src, f'<transfer-{tag}>', 'exec'), ns, ns)
    ns['main']()
    result = json.loads(out_file.read_text())
    c = result['attribution']['iterated_contextual_contraction']
    rows = c.get('rows', [])
    distances = [r.get('best_distance') for r in rows]
    replay_failures = sum(r.get('replay_failures', 0) for r in rows)
    direct = c.get('direct_target')
    solved = bool(direct and direct.get('replayed'))
    improved = bool(rows and any(r.get('improved') for r in rows))
    return {
        'edge': f'{source_id}->{target_id}',
        'source_id': source_id,
        'target_id': target_id,
        'round8_target_found': bool(result.get('target_found')),
        'baseline_distance': c.get('baseline_distance'),
        'distances': distances,
        'improved': improved,
        'direct_target_replayed': solved,
        'replay_failures': replay_failures,
        'active_round8': result.get('active_round8'),
        'nodes': result.get('nodes'),
    }


def main():
    rows = []
    for source_id, target_id in EDGES:
        try:
            row = run_edge(source_id, target_id)
        except Exception as exc:
            row = {
                'edge': f'{source_id}->{target_id}',
                'source_id': source_id,
                'target_id': target_id,
                'error': type(exc).__name__ + ': ' + str(exc),
                'improved': False,
                'direct_target_replayed': False,
                'replay_failures': None,
            }
        rows.append(row)
        print('TRANSFER_EDGE', json.dumps(row, sort_keys=True), flush=True)

    out = {
        'schema': 'mathgraph.18-edge-contextual-contraction-transfer.v1',
        'teacher_information_used': False,
        'policy': {
            'frontier_cap': 16,
            'basis_cap': 6,
            'rounds': 8,
            'context_generations': 2,
            'context_keep': 8,
        },
        'rows': rows,
        'tested': len(rows),
        'improved_edges': [r['edge'] for r in rows if r.get('improved')],
        'solved_edges': [r['edge'] for r in rows if r.get('direct_target_replayed')],
        'errors': [r['edge'] for r in rows if r.get('error')],
        'replay_failures_total': sum(
            r.get('replay_failures') or 0 for r in rows
        ),
    }
    out['promotion_gate'] = bool(out['improved_edges']) and not out['errors'] and out['replay_failures_total'] == 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('TRANSFER_SUMMARY', json.dumps({
        'tested': out['tested'],
        'improved_edges': out['improved_edges'],
        'solved_edges': out['solved_edges'],
        'errors': out['errors'],
        'replay_failures_total': out['replay_failures_total'],
        'promotion_gate': out['promotion_gate'],
    }, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
