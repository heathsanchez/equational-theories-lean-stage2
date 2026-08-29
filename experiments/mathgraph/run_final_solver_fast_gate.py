import importlib.util
import json
import sys
import time
import urllib.request
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('fast_gate_helper', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

BASELINE_REF = 'mathgraph/superposition-selector-tournament-20260820'
PER_EDGE_SECONDS = 1.25


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def run_one(m, source, target):
    started = time.monotonic()
    search = m.EqualitySearch(source, target, time.monotonic() + PER_EDGE_SECONDS)
    result = search.solve()
    found = isinstance(result, tuple) and len(result) == 2
    replayed = False
    proof_nodes = None
    if found:
        nodes, root = result
        proof_nodes = len(h.proof_ids(nodes, root))
        try:
            replayed = bool(m.replay_dag(source, nodes, root))
        except TypeError:
            replayed = bool(m.replay_dag(source, nodes, root,
                maximum_term_size=getattr(search, 'max_term_size', 256),
                maximum_nodes=getattr(search, 'max_derivation_nodes', 50000)))
    return {
        'found': found,
        'replayed': replayed,
        'proof_nodes': proof_nodes,
        'seconds': time.monotonic() - started,
        'nodes': len(getattr(search, 'nodes', ())),
        'edges': getattr(search, 'graph_edges', None),
        'exhaustion': getattr(search, 'exhaustion', None),
    }


def main():
    # Gate 1: import/compile the actual candidate solver.
    candidate_path = Path('submissions/mathgraph/solver.py')
    candidate = load_module(candidate_path, 'mg_fast_candidate')

    # Frozen baseline from the strongest pre-separator branch.
    url = ('https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/'
           + BASELINE_REF + '/submissions/mathgraph/solver.py')
    baseline_path = Path('/tmp/mathgraph_baseline_solver.py')
    baseline_path.write_bytes(urllib.request.urlopen(url, timeout=30).read())
    baseline = load_module(baseline_path, 'mg_fast_baseline')

    equations = h.load_equations()
    rows = []
    for route_name, route_index, sid, tid in h.EDGES:
        source_text, target_text = equations[sid], equations[tid]
        cs, ct = candidate.parse_equation(source_text), candidate.parse_equation(target_text)
        bs, bt = baseline.parse_equation(source_text), baseline.parse_equation(target_text)
        c = run_one(candidate, cs, ct)
        b = run_one(baseline, bs, bt)
        row = {'edge': f'{sid}->{tid}', 'route': route_name, 'candidate': c, 'baseline': b}
        rows.append(row)
        print(json.dumps(row, sort_keys=True), flush=True)

    c_replayed = sum(r['candidate']['replayed'] for r in rows)
    b_replayed = sum(r['baseline']['replayed'] for r in rows)
    gains = [r['edge'] for r in rows if r['candidate']['replayed'] and not r['baseline']['replayed']]
    losses = [r['edge'] for r in rows if r['baseline']['replayed'] and not r['candidate']['replayed']]
    bad_replays = [r['edge'] for r in rows if r['candidate']['found'] and not r['candidate']['replayed']]
    c_times = sorted(r['candidate']['seconds'] for r in rows)
    p95 = c_times[max(0, int(0.95 * len(c_times)) - 1)]
    summary = {
        'schema': 'mathgraph.final-fast-gate.v1',
        'baseline_ref': BASELINE_REF,
        'per_edge_seconds': PER_EDGE_SECONDS,
        'candidate_replayed': c_replayed,
        'baseline_replayed': b_replayed,
        'gains': gains,
        'losses': losses,
        'bad_replays': bad_replays,
        'candidate_p95_seconds': p95,
        'zero_replay_regressions': not losses,
        'replay_integrity': not bad_replays,
        'promotion_gate': (not losses and not bad_replays and c_replayed >= b_replayed),
        'rows': rows,
    }
    out = Path('experiments/mathgraph/results/final-solver-fast-gate.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('SUMMARY', json.dumps({k: summary[k] for k in (
        'candidate_replayed','baseline_replayed','gains','losses','bad_replays',
        'candidate_p95_seconds','promotion_gate')}, sort_keys=True), flush=True)
    if not summary['replay_integrity']:
        raise SystemExit('FAIL: candidate emitted a non-replayable proof')


if __name__ == '__main__':
    main()
