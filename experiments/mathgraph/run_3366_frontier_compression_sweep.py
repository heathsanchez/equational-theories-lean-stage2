import importlib.util
import json
import sys
from pathlib import Path

SOURCE = Path('experiments/mathgraph/run_3366_dynamic_compatibility_basis.py')
RESULT = Path('experiments/mathgraph/results/3366-dynamic-compatibility-basis.json')
OUT = Path('experiments/mathgraph/results/3366-frontier-compression-sweep.json')


def load_module(tag):
    spec = importlib.util.spec_from_file_location('mg_frontier_' + tag, SOURCE)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main():
    rows = []
    # Hold the compatibility selector, term ceiling, node ceiling, basis width,
    # and continuation operators fixed. Change only how many verified frontier
    # states survive to drive the next round.
    for cap in (16, 32, 64):
        module = load_module(str(cap))
        module.FRONTIER_CAP = cap
        module.main()
        result = json.loads(RESULT.read_text())
        transfer = result['transfer']
        snapshots = transfer.get('snapshots', [])
        row = {
            'frontier_cap': cap,
            'found': bool(transfer.get('found')),
            'replayed': bool(transfer.get('replayed')),
            'nodes': transfer.get('nodes'),
            'rounds_completed': len(snapshots),
            'last_round': snapshots[-1]['round'] if snapshots else None,
            'last_frontier': snapshots[-1]['frontier'] if snapshots else None,
            'snapshots': snapshots,
        }
        rows.append(row)
        print(json.dumps(row, sort_keys=True), flush=True)

    ranked = sorted(rows, key=lambda r: (
        0 if r['replayed'] else 1,
        -r['rounds_completed'],
        r['nodes'],
        r['frontier_cap'],
    ))
    output = {
        'schema': 'mathgraph.3366-frontier-compression-sweep.v1',
        'edge': '3366->41',
        'teacher_information_used': False,
        'frozen_mechanism': 'dynamic compatibility basis + role-aware continuation',
        'changed_variable': 'frontier retention cap only',
        'caps': [16, 32, 64],
        'rows': rows,
        'best': ranked[0],
        'promotion_gate': {
            'passed': any(r['replayed'] for r in rows),
            'depth_improved': any(r['rounds_completed'] >= 7 and r['nodes'] < 50000 for r in rows),
        },
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
    print('SUMMARY', json.dumps(output['promotion_gate'], sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
