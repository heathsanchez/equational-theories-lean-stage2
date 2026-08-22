#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT = Path(__file__).resolve().parents[2]
PROTO = ROOT / 'experiments/mathgraph/protocols/methodology-0036-local-overlap-bridge-v1.json'
PARENT = ROOT / 'experiments/mathgraph/results/methodology-0036-size-compression-matched-v2.json'
OUT = ROOT / 'experiments/mathgraph/results/methodology-0036-local-overlap-bridge-v1.json'
RID = 'evaluation_normal_0036'
HIST = 'origin/mathgraph/superposition-selector-tournament-20260820'


def load_historical():
    text = subprocess.check_output(['git', 'show', f'{HIST}:submissions/mathgraph/solver.py'], text=True)
    p = Path(tempfile.gettempdir()) / 'mathgraph_methodology_0036_overlap_hist.py'
    p.write_text(text)
    spec = importlib.util.spec_from_file_location('mg_methodology_0036_overlap_hist', p)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


def connected(search, target):
    comps = search.components()
    a, b = target[:2]
    return a in comps and b in comps and comps[a] == comps[b]


def main():
    protocol = json.loads(PROTO.read_text())
    assert protocol['frozen_before_execution'] is True
    parent = json.loads(PARENT.read_text()) if PARENT.exists() else {'decision':'MISSING'}
    activation = parent.get('decision') == 'SIZE_GATE_CAUSAL_BUT_NOT_SUFFICIENT'
    if not activation:
        out = {
            'schema': protocol['schema'], 'id': RID,
            'decision': 'SKIPPED_PARENT_DECISION',
            'parent_decision': parent.get('decision'),
            'sealed_transfer_ids_loaded': []
        }
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
        print(json.dumps(out, indent=2, sort_keys=True), flush=True)
        return

    m = load_historical()
    row = next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems', 'evaluation_normal', split='train') if r['id'] == RID)
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])
    tr = target[1]
    captured = []
    Base = m.ContextualSearch
    class Instrumented(Base):
        def add_node(self, node, graph_edge=True):
            nid = super().add_node(node, graph_edge=graph_edge)
            if nid is not None and getattr(node, 'constructor', None) == 'target-narrowing':
                captured.append(nid)
            return nid

    cfg = m.CONTEXTUAL_PORTFOLIO[0]
    search = Instrumented(source, target, time.monotonic() + 8.0, dict(cfg['limits']))
    search.solve_target_narrowing(cfg['maximum_depth'], cfg['branching'], cfg['maximum_terms'], cfg['maximum_context_depth'])
    old_nodes = sorted(set(captured))
    rhs_parent_ids = sorted({nid for nid in old_nodes if search.nodes[nid].lhs == tr or search.nodes[nid].rhs == tr})

    raw_term_size = m.term_size
    def compressed_size(term):
        if term == tr:
            return 1
        if term[0] == 'var':
            return 1
        return 1 + compressed_size(term[1]) + compressed_size(term[2])
    m.term_size = compressed_size
    search.max_term_size = 13
    search.deadline = time.monotonic() + 8.0

    source_vars = list(source[2])
    target_vars = [('var', v) for v in target[2]]
    before_new = len(search.nodes)
    before_edges = search.graph_edges
    admitted = 0
    for xv, yv in product(target_vars, repeat=2):
        values = [None] * len(source_vars)
        values[source_vars.index('x')] = xv
        values[source_vars.index('y')] = yv
        values[source_vars.index('z')] = tr
        origins = tuple((var, val, tuple(rhs_parent_ids) if val == tr else ()) for var,val in zip(source_vars,values))
        if search.add_source_substitution(values, generation=1, origins=origins) is not None:
            admitted += 1
    reentry_edges = search.graph_edges - before_edges
    before_cong = search.graph_edges
    search.add_congruence_round([tr], before_new, edge_limit=search.max_graph_edges)
    congruence_edges = search.graph_edges - before_cong

    new_nodes = [
        nid for nid in range(before_new, len(search.nodes))
        if search.nodes[nid].kind in ('source reentry','congruence on left child','congruence on right child')
    ]
    pre_overlap_connected = connected(search, target)
    pre_root = search.shortest_path()
    pre_replay = bool(pre_root is not None and m.replay_dag(source, search.nodes, pre_root))

    maxc = protocol['constraints']['maximum_candidates_per_direction']
    maxd = protocol['constraints']['maximum_context_depth']
    forward = search.collect_overlap_candidates(new_nodes, old_nodes, maxd, maxc) if new_nodes and old_nodes else []
    reverse = search.collect_overlap_candidates(old_nodes, new_nodes, maxd, maxc) if new_nodes and old_nodes else []
    ordered = [('NEW_TO_OLD', c) for c in forward] + [('OLD_TO_NEW', c) for c in reverse]

    applied = 0
    first_join = None
    first_replay = None
    for direction, candidate in ordered:
        before_join_count = search.components_joined
        nid = search.apply_overlap(candidate, 1)
        if nid is None:
            continue
        applied += 1
        joined_now = search.components_joined > before_join_count or connected(search, target)
        root = search.shortest_path()
        replay = bool(root is not None and m.replay_dag(source, search.nodes, root))
        if joined_now and first_join is None:
            first_join = {'direction': direction, 'applied_index': applied, 'node_id': nid}
        if replay:
            first_replay = {'direction': direction, 'applied_index': applied, 'node_id': nid, 'root': root}
            break

    final_connected = connected(search, target)
    final_root = search.shortest_path()
    final_replay = bool(final_root is not None and m.replay_dag(source, search.nodes, final_root))
    if final_replay or final_connected or first_join is not None:
        decision = 'R1_CONTEXTUAL_OVERLAP_BRIDGE'
    elif ordered:
        decision = 'R2_LOCAL_OVERLAP_EXISTS_BUT_INSUFFICIENT'
    else:
        decision = 'R3_NO_LOCAL_OVERLAP'

    m.term_size = raw_term_size
    out = {
        'schema': protocol['schema'], 'id': RID,
        'parent_decision': parent.get('decision'),
        'admitted_reentry_instances': admitted,
        'reentry_edges_added': reentry_edges,
        'congruence_edges_added': congruence_edges,
        'old_target_narrowing_nodes': len(old_nodes),
        'new_reentry_congruence_nodes': len(new_nodes),
        'pre_overlap_connected': pre_overlap_connected,
        'pre_overlap_replay': pre_replay,
        'forward_candidates': len(forward),
        'reverse_candidates': len(reverse),
        'overlaps_applied': applied,
        'first_component_join': first_join,
        'first_replayable_closure': first_replay,
        'final_connected': final_connected,
        'final_replay': final_replay,
        'decision': decision,
        'sealed_transfer_ids_loaded': []
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
