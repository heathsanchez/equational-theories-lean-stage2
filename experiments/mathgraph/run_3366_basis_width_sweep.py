import importlib.util
import json
import sys
from pathlib import Path

SCRIPT = Path('experiments/mathgraph/run_3366_role_aware_transfer.py')
spec = importlib.util.spec_from_file_location('transfer3366_width_sweep', SCRIPT)
t = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = t
spec.loader.exec_module(t)

OUT = Path('experiments/mathgraph/results/3366-role-aware-transfer.json')
SWEEP = Path('experiments/mathgraph/results/3366-basis-width-sweep.json')
CAPS = (6, 12, 24)


def main():
    arms = []
    for cap in CAPS:
        t.BASIS_CAP = cap
        print(f'=== BASIS_CAP={cap} ===', flush=True)
        t.main()
        row = json.loads(OUT.read_text())
        arms.append({
            'basis_cap': cap,
            'candidate_source_instances': row['basis']['candidate_source_instances'],
            'selected': row['basis']['selected'],
            'oriented': row['basis']['oriented'],
            'baseline_replayed': row['baseline']['replayed'],
            'transfer_found': row['transfer']['found'],
            'transfer_replayed': row['transfer']['replayed'],
            'nodes': row['transfer']['nodes'],
            'rounds': row['transfer']['rounds'],
            'promotion_gate': row['promotion_gate']['passed'],
        })

    # Discriminator: a smaller basis is useful only if it either solves/replays,
    # or survives strictly deeper than the 24-atom arm before the 50k cap.
    def reached_round(a):
        rs = a.get('rounds') or []
        return max((r['round'] for r in rs), default=1)

    wide = next(a for a in arms if a['basis_cap'] == 24)
    best = max(arms, key=lambda a: (a['transfer_replayed'], reached_round(a), -a['nodes'], -a['basis_cap']))
    out = {
        'schema': 'mathgraph.3366-basis-width-sweep.v1',
        'edge': '3366->41',
        'teacher_information_used': False,
        'mechanism_fixed': 'persistent-oriented-basis + role-aware continuation',
        'selector_fixed': 'target-distance + term-size rank',
        'basis_caps': list(CAPS),
        'arms': arms,
        'discriminator': {
            'wide_round': reached_round(wide),
            'best_basis_cap': best['basis_cap'],
            'best_round': reached_round(best),
            'any_replayed': any(a['transfer_replayed'] for a in arms),
            'basis_width_is_bottleneck': bool(best['transfer_replayed'] or reached_round(best) > reached_round(wide)),
        },
    }
    SWEEP.parent.mkdir(parents=True, exist_ok=True)
    SWEEP.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('SWEEP_SUMMARY', json.dumps(out['discriminator'], sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
