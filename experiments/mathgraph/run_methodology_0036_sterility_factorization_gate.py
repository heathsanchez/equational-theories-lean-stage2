#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import combinations
from pathlib import Path
from datasets import load_dataset

ROOT = Path(__file__).resolve().parents[2]
PROTO = ROOT / 'experiments/mathgraph/protocols/methodology-0036-sterility-factorization-v1.json'
OUT = ROOT / 'experiments/mathgraph/results/methodology-0036-sterility-factorization-gate.json'
RID = 'evaluation_normal_0036'
HIST = 'origin/mathgraph/superposition-selector-tournament-20260820'


def load_historical():
    text = subprocess.check_output(['git', 'show', f'{HIST}:submissions/mathgraph/solver.py'], text=True)
    p = Path(tempfile.gettempdir()) / 'mathgraph_methodology_0036_hist.py'
    p.write_text(text)
    spec = importlib.util.spec_from_file_location('mg_methodology_0036_hist', p)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


def alpha_term(t, env=None):
    env = {} if env is None else env
    if t[0] == 'var':
        if t[1] not in env:
            env[t[1]] = f'v{len(env)}'
        return ('var', env[t[1]])
    return ('op', alpha_term(t[1], env), alpha_term(t[2], env))


def alpha_key(t):
    return repr(alpha_term(t, {}))


def nonvar_subterm_keys(m, sides):
    out = set()
    for side in sides:
        for s in m.walk_subterms(side):
            if s[0] == 'op':
                out.add(alpha_key(s))
    return out


def coverage(m, terms, basis):
    seen = set()
    for term in terms:
        for s in m.walk_subterms(term):
            k = alpha_key(s)
            if k in basis:
                seen.add(k)
    return seen


def eq_distance(m, lhs, rhs, target):
    tl, tr = target[:2]
    direct = m.structural_distance(lhs, tl) + m.structural_distance(rhs, tr)
    swapped = m.structural_distance(lhs, tr) + m.structural_distance(rhs, tl)
    return min(direct, swapped)


def subst_map(node):
    try:
        return {str(v): alpha_key(t) for v, t in node.substitution}
    except Exception:
        return {}


def compatible(a, b):
    sa, sb = a['subst'], b['subst']
    common = set(sa) & set(sb)
    return all(sa[k] == sb[k] for k in common)


def main():
    protocol = json.loads(PROTO.read_text())
    assert protocol['frozen_before_execution'] is True
    assert protocol['id'] == RID
    assert RID not in protocol['sealed_transfer_ids']
    m = load_historical()
    row = next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems', 'evaluation_normal', split='train') if r['id'] == RID)
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])
    target_basis = nonvar_subterm_keys(m, target[:2])
    source_basis = nonvar_subterm_keys(m, source[:2])
    baseline_target_cov = coverage(m, source[:2], target_basis)
    baseline_source_cov = coverage(m, source[:2], source_basis)
    baseline_distance = eq_distance(m, source[0], source[1], target)

    captured = []
    Base = m.ContextualSearch
    class Instrumented(Base):
        def add_node(self, node, graph_edge=True):
            nid = super().add_node(node, graph_edge=graph_edge)
            if nid is not None and getattr(node, 'constructor', None) == 'target-narrowing':
                captured.append(node)
            return nid

    cfg = m.CONTEXTUAL_PORTFOLIO[0]
    limits = dict(cfg['limits'])
    search = Instrumented(source, target, time.monotonic() + 8.0, limits)
    found = search.solve_target_narrowing(cfg['maximum_depth'], cfg['branching'], cfg['maximum_terms'], cfg['maximum_context_depth'])

    rows = []
    dedup = {}
    for node in captured:
        terms = (node.lhs, node.rhs)
        key = (repr(node.lhs), repr(node.rhs))
        cov = coverage(m, terms, target_basis)
        sham = coverage(m, terms, source_basis)
        rec = {
            'lhs': m.render_term(node.lhs),
            'rhs': m.render_term(node.rhs),
            'distance': eq_distance(m, node.lhs, node.rhs, target),
            'target_coverage': sorted(cov),
            'target_coverage_count': len(cov),
            'target_gain_count': len(cov - baseline_target_cov),
            'source_sham_coverage_count': len(sham),
            'source_sham_gain_count': len(sham - baseline_source_cov),
            'subst': subst_map(node),
            'generation': getattr(node, 'generation', None),
        }
        old = dedup.get(key)
        if old is None or rec['distance'] < old['distance']:
            dedup[key] = rec
    rows = list(dedup.values())

    improving_distance = [r for r in rows if r['distance'] < baseline_distance]
    direct_gains = [r for r in rows if r['target_gain_count'] > 0]
    pair_union_gains = []
    complementary_incompatible = []
    for a, b in combinations(rows, 2):
        ua = set(a['target_coverage']); ub = set(b['target_coverage'])
        union = ua | ub
        gain = union - baseline_target_cov
        if gain:
            rec = {
                'union_gain_count': len(gain),
                'compatible': compatible(a, b),
                'a_distance': a['distance'],
                'b_distance': b['distance'],
                'gain': sorted(gain),
            }
            pair_union_gains.append(rec)
            if not rec['compatible']:
                complementary_incompatible.append(rec)

    max_target_gain = max((r['target_gain_count'] for r in rows), default=0)
    max_pair_gain = max((r['union_gain_count'] for r in pair_union_gains), default=0)
    max_sham_gain = max((r['source_sham_gain_count'] for r in rows), default=0)
    if max_target_gain > 0 or any(r['compatible'] for r in pair_union_gains):
        decision = 'CURRENT_FRAME_ADEQUATE'
    elif pair_union_gains and complementary_incompatible:
        decision = 'COMPOSITION_INTERFACE'
    elif improving_distance:
        decision = 'DISTANCE_SURROGATE'
    else:
        decision = 'OPERATOR_COVERAGE_INVARIANT'

    out = {
        'schema': 'mathgraph.methodology-0036-sterility-factorization.v1',
        'id': RID,
        'protocol_commit_boundary': 'protocol existed before executable commit',
        'equations': {'source': row['equation1'], 'target': row['equation2']},
        'parent_reproduction': {
            'closure': bool(found is not None),
            'narrowing_successors_counter': search.narrowing_successors,
            'graph_edges': search.graph_edges,
            'missing_target_introduced': search.missing_target_introduced,
            'components_joined': search.components_joined,
            'captured_target_narrowing_nodes': len(captured),
            'unique_captured_equalities': len(rows),
        },
        'baseline': {
            'structural_distance': baseline_distance,
            'target_basis_size': len(target_basis),
            'target_coverage_count': len(baseline_target_cov),
            'source_sham_basis_size': len(source_basis),
            'source_sham_coverage_count': len(baseline_source_cov),
        },
        'diagnostic': {
            'distance_improving_successors': len(improving_distance),
            'best_successor_distance': min((r['distance'] for r in rows), default=None),
            'successors_with_direct_target_gain': len(direct_gains),
            'maximum_direct_target_gain': max_target_gain,
            'pairs_with_union_target_gain': len(pair_union_gains),
            'maximum_pair_target_gain': max_pair_gain,
            'complementary_but_incompatible_pairs': len(complementary_incompatible),
            'maximum_source_sham_gain': max_sham_gain,
        },
        'decision': decision,
        'rows': sorted(rows, key=lambda r: (r['distance'], -r['target_gain_count'], r['lhs'], r['rhs']))[:80],
        'top_pair_union_gains': sorted(pair_union_gains, key=lambda r: (-r['union_gain_count'], not r['compatible']))[:40],
        'sealed_transfer_ids_loaded': [],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
