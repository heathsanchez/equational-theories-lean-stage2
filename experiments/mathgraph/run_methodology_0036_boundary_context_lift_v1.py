#!/usr/bin/env python3
# Implementation-only CI retrigger after tuple-API repair; frozen protocol unchanged.
import copy, json, sys
from itertools import product
from pathlib import Path
from datasets import load_dataset

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour
import run_methodology_0036_goal_cut_descaffold_v1 as desc
import run_methodology_0036_postcontractor_factorization_v1 as post

ROOT = Path(__file__).resolve().parents[2]
PROTO = ROOT / 'experiments/mathgraph/protocols/methodology-0036-boundary-context-lift-v1.json'
OUT = ROOT / 'experiments/mathgraph/results/methodology-0036-boundary-context-lift-v1.json'
RID = 'evaluation_normal_0036'


def proper_positions(term):
    out = []
    def rec(t, path):
        if path:
            out.append((path, t))
        if t[0] == 'op':
            rec(t[1], path + ('L',))
            rec(t[2], path + ('R',))
    rec(term, ())
    return out


def replace_at(term, path, replacement):
    if not path:
        return replacement
    if term[0] != 'op':
        raise ValueError('path enters variable')
    if path[0] == 'L':
        return ('op', replace_at(term[1], path[1:], replacement), term[2])
    return ('op', term[1], replace_at(term[2], path[1:], replacement))


def context_chain(term, path):
    cur = term
    chain = []
    for direction in path:
        if cur[0] != 'op':
            raise ValueError('invalid context path')
        sibling = cur[2] if direction == 'L' else cur[1]
        chain.append((direction, sibling))
        cur = cur[1] if direction == 'L' else cur[2]
    return chain


def boundary_terms(m, st):
    rendered = {}
    for t in st['lhs_members'] + st['rhs_members']:
        rendered[m.render_term(t)] = t
    out = []
    for rec in st.get('boundary_pairs', []):
        for key in ('lhs_component_term', 'rhs_component_term'):
            t = rendered.get(rec[key])
            if t is not None and t not in out:
                out.append(t)
    return sorted(out, key=lambda t: (m.term_size(t), m.render_term(t)))


def enumerate_lifts(m, s, source, target, st, fills, cap, limit):
    source_vars = source[2]
    candidates = []
    seen = set()
    attempted = 0
    rejected_cap = 0
    matched_positions = 0
    for endpoint in boundary_terms(m, st):
        for path, subterm in proper_positions(endpoint):
            for orientation, pattern in enumerate(source[:2]):
                partial = {}
                if not m.match_term(pattern, subterm, partial):
                    continue
                matched_positions += 1
                missing = [v for v in source_vars if v not in partial]
                for values in product(fills, repeat=len(missing)):
                    mapping = dict(partial)
                    mapping.update(zip(missing, values))
                    inst_l = m.substitute(source[0], mapping)
                    inst_r = m.substitute(source[1], mapping)
                    matched = inst_l if orientation == 0 else inst_r
                    other = inst_r if orientation == 0 else inst_l
                    if matched != subterm or other == subterm:
                        continue
                    attempted += 1
                    rewritten = replace_at(endpoint, path, other)
                    if max(m.term_size(inst_l), m.term_size(inst_r), m.term_size(rewritten)) > cap:
                        rejected_cap += 1
                        continue
                    edge_key = frozenset((endpoint, rewritten))
                    if endpoint == rewritten or edge_key in seen or post.edge_exists(s, endpoint, rewritten):
                        continue
                    seen.add(edge_key)
                    c = {
                        'endpoint': endpoint,
                        'rewritten': rewritten,
                        'path': path,
                        'mapping': mapping,
                        'orientation': orientation,
                        'inst_l': inst_l,
                        'inst_r': inst_r,
                        'max_term_size': max(m.term_size(inst_l), m.term_size(inst_r), m.term_size(rewritten)),
                    }
                    c['post_separation'] = desc.simulate_goal_separation(
                        m, s, target, {'lhs': endpoint, 'rhs': rewritten}
                    )
                    candidates.append(c)
                    if len(candidates) >= limit:
                        return candidates, attempted, rejected_cap, matched_positions, True
    return candidates, attempted, rejected_cap, matched_positions, False


def apply_lift(m, s, source, c):
    source_vars = source[2]
    substitution = tuple((v, c['mapping'][v]) for v in source_vars)
    sid = s.add_node(m.EqualityNode(
        c['inst_l'], c['inst_r'], 'source instance', substitution=substitution,
        orientation=False, constructor='boundary-context-lift',
    ), graph_edge=False)
    if sid is None:
        return None
    current = sid
    if c['orientation'] == 1:
        current = s.add_node(m.EqualityNode(
            c['inst_r'], c['inst_l'], 'symmetry', parents=(current,),
            constructor='boundary-context-lift',
        ), graph_edge=False)
        if current is None:
            return None
    chain = context_chain(c['endpoint'], c['path'])
    for index, (direction, sibling) in enumerate(reversed(chain)):
        parent = s.nodes[current]
        final = index == len(chain) - 1
        if direction == 'L':
            lhs = ('op', parent.lhs, sibling)
            rhs = ('op', parent.rhs, sibling)
            kind = 'congruence on left child'
            context = ('left', sibling)
        else:
            lhs = ('op', sibling, parent.lhs)
            rhs = ('op', sibling, parent.rhs)
            kind = 'congruence on right child'
            context = ('right', sibling)
        current = s.add_node(m.EqualityNode(
            lhs, rhs, kind, parents=(current,), context=context,
            constructor='boundary-context-lift',
        ), graph_edge=final)
        if current is None:
            return None
    return current


def public(m, c):
    return {
        'endpoint': m.render_term(c['endpoint']),
        'rewritten': m.render_term(c['rewritten']),
        'path': list(c['path']),
        'source_instance_lhs': m.render_term(c['inst_l']),
        'source_instance_rhs': m.render_term(c['inst_r']),
        'matched_source_side': 'lhs' if c['orientation'] == 0 else 'rhs',
        'post_separation': c['post_separation'],
        'max_term_size': c['max_term_size'],
        'mapping': {k: m.render_term(v) for k, v in sorted(c['mapping'].items())},
    }


def main():
    p = json.loads(PROTO.read_text())
    assert p['frozen_before_execution'] is True
    assert p['id'] == RID
    assert RID not in p['sealed_transfer_ids']
    m = tour.cut.load_hist()
    row = next(dict(r) for r in load_dataset(
        'SAIRfoundation/equational-theories-selected-problems', 'evaluation_normal', split='train'
    ) if r['id'] == RID)
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])
    cfg = m.CONTEXTUAL_PORTFOLIO[0]
    base, old, new, admitted, edges, first, nid, st = post.reconstruct_post_step(m, source, target, cfg)
    parent_ok = (
        base.max_term_size == 19 and len(old) == 45 and admitted == 9 and edges == 9
        and nid is not None and st is not None and not st.get('connected')
        and st.get('cross_distance') == 8
    )
    if not parent_ok:
        out = {
            'schema': p['schema'], 'id': RID, 'decision': 'MEASUREMENT_FAILURE',
            'measurement_ok': False, 'sealed_transfer_ids_loaded': []
        }
    else:
        _, fills = post.l1_terms(m, base, target, st)
        candidates, attempted, rejected_cap, matched_positions, truncated = enumerate_lifts(
            m, base, source, target, st, fills,
            p['constraints']['operative_term_cap'], p['constraints']['maximum_candidates']
        )
        scored = [c for c in candidates if c['post_separation'] is not None]
        strict = sorted(
            [c for c in scored if c['post_separation'] < 8],
            key=lambda c: (c['post_separation'], c['max_term_size'], len(c['path']),
                           m.render_term(c['endpoint']), m.render_term(c['rewritten']))
        )
        best = strict[0] if strict else None
        proof_replay = None
        post_sep = None
        connected = False
        target_replay = None
        final_node = None
        if best is not None:
            trial = copy.deepcopy(base)
            final_node = apply_lift(m, trial, source, best)
            if final_node is not None:
                proof_replay = bool(m.replay_dag(
                    source, trial.nodes, final_node,
                    maximum_term_size=p['constraints']['operative_term_cap']
                ))
                pst = tour.cut.component_state(m, trial, target, 1000000)
                if pst is not None:
                    connected = bool(pst.get('connected'))
                    post_sep = 0 if connected else pst.get('cross_distance')
                root = trial.shortest_path()
                target_replay = bool(root is not None and m.replay_dag(
                    source, trial.nodes, root,
                    maximum_term_size=p['constraints']['operative_term_cap']
                ))
            if final_node is None or not proof_replay or post_sep != best['post_separation'] or (connected and not target_replay):
                decision = 'MEASUREMENT_FAILURE'
            else:
                decision = 'BOUNDARY_CONTEXT_LIFT_CONTRACTS'
        else:
            decision = 'BOUNDARY_CONTEXT_LIFT_EXHAUSTED'
        examples = [public(m, c) for c in strict[:p['constraints']['report_examples']]]
        out = {
            'schema': p['schema'], 'id': RID, 'decision': decision,
            'measurement_ok': decision != 'MEASUREMENT_FAILURE',
            'parent': {
                'cross_distance': 8,
                'boundary_endpoint_count': len(boundary_terms(m, st)),
                'fill_count': len(fills),
                'observed_invariant': p['observed_parent_invariant'],
            },
            'search': {
                'matched_position_orientations': matched_positions,
                'instantiations_attempted': attempted,
                'cap_rejections': rejected_cap,
                'unique_context_lifts': len(candidates),
                'scored_context_lifts': len(scored),
                'strict_contractors': len(strict),
                'truncated_at_candidate_limit': truncated,
                'best_post_separation': None if best is None else best['post_separation'],
                'examples': examples,
            },
            'best_application': None if best is None else {
                'candidate': public(m, best),
                'proof_replay': proof_replay,
                'final_node': final_node,
                'post_separation_recomputed': post_sep,
                'connected': connected,
                'target_replayable_closure': target_replay,
            },
            'sealed_transfer_ids_loaded': [],
        }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
