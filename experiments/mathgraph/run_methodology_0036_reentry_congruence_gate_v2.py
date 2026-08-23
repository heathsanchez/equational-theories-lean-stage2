#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from pathlib import Path
from datasets import load_dataset

ROOT = Path(__file__).resolve().parents[2]
PROTO = ROOT / 'experiments/mathgraph/protocols/methodology-0036-reentry-congruence-gate-v2.json'
OUT = ROOT / 'experiments/mathgraph/results/methodology-0036-reentry-congruence-gate-v2.json'
RID = 'evaluation_normal_0036'
HIST = 'origin/mathgraph/superposition-selector-tournament-20260820'


def load_historical():
    text = subprocess.check_output(['git', 'show', f'{HIST}:submissions/mathgraph/solver.py'], text=True)
    p = Path(tempfile.gettempdir()) / 'mathgraph_methodology_0036_reentry_v2_hist.py'
    p.write_text(text)
    spec = importlib.util.spec_from_file_location('mg_methodology_0036_reentry_v2_hist', p)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


def connected(search, target):
    comps = search.components()
    a, b = target[:2]
    return a in comps and b in comps and comps[a] == comps[b]


def replay_root(m, source, search):
    root = search.shortest_path()
    return root, bool(root is not None and m.replay_dag(source, search.nodes, root))


def main():
    protocol = json.loads(PROTO.read_text())
    assert protocol['frozen_before_execution'] is True
    assert protocol['id'] == RID
    assert RID not in protocol['constraints']['sealed_transfer_ids']
    m = load_historical()
    row = next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems', 'evaluation_normal', split='train') if r['id'] == RID)
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])

    captured = []
    Base = m.ContextualSearch
    class Instrumented(Base):
        def add_node(self, node, graph_edge=True):
            nid = super().add_node(node, graph_edge=graph_edge)
            if nid is not None and getattr(node, 'constructor', None) == 'target-narrowing':
                captured.append((nid, node))
            return nid

    cfg = m.CONTEXTUAL_PORTFOLIO[0]
    search = Instrumented(source, target, time.monotonic() + 8.0, dict(cfg['limits']))
    parent_found = search.solve_target_narrowing(cfg['maximum_depth'], cfg['branching'], cfg['maximum_terms'], cfg['maximum_context_depth'])
    parent_edges = search.graph_edges
    parent_nodes = len(search.nodes)
    parent_connected = connected(search, target)
    parent_root, parent_replay = replay_root(m, source, search)

    tl, tr = target[:2]
    by_term = {}
    endpoint_records = []
    for nid, node in captured:
        for side_name, term in (('lhs', node.lhs), ('rhs', node.rhs)):
            if term == tl or term == tr:
                which = 'target_lhs' if term == tl else 'target_rhs'
                endpoint_records.append({'node_id': nid, 'side': side_name, 'which': which, 'rendered': m.render_term(term)})
                by_term.setdefault(term, set()).add(nid)

    if tr not in by_term:
        decision = 'R5_MEASUREMENT_ARTIFACT'
        reentry_added = congruence_added = 0
        after_reentry_connected = after_congruence_connected = parent_connected
        reentry_replay = congruence_replay = parent_replay
        reentry_root = congruence_root = parent_root
    else:
        selected = [(term, tuple(sorted(ids))) for term, ids in sorted(by_term.items(), key=lambda kv: search.term_key(kv[0]))]
        before_reentry_edges = search.graph_edges
        before_reentry_nodes = len(search.nodes)
        reentry_added_instances = search.instantiate_reentry(
            selected,
            generation=1,
            maximum_instances=protocol['constraints']['maximum_reentry_instances'],
            targeted=False,
        )
        reentry_added = search.graph_edges - before_reentry_edges
        after_reentry_connected = connected(search, target)
        reentry_root, reentry_replay = replay_root(m, source, search)

        before_congruence_edges = search.graph_edges
        search.add_congruence_round(
            [term for term, _ in selected],
            before_reentry_nodes,
            edge_limit=search.max_graph_edges,
        )
        congruence_added = search.graph_edges - before_congruence_edges
        after_congruence_connected = connected(search, target)
        congruence_root, congruence_replay = replay_root(m, source, search)

        if congruence_replay or after_congruence_connected:
            decision = 'R1_REENTRY_CONGRUENCE_CLOSES'
        elif reentry_added == 0:
            decision = 'R2_REENTRY_DOES_NOT_ADD'
        elif congruence_added == 0:
            decision = 'R3_CONGRUENCE_DOES_NOT_ADD'
        else:
            decision = 'R4_CONTEXTUAL_SUPERPOSITION_NEEDED'

    out = {
        'schema': 'mathgraph.methodology-0036-reentry-congruence-gate.v2',
        'id': RID,
        'protocol_precommitted': True,
        'supersedes_v1_before_observing_v1_outcome': True,
        'equations': {'source': row['equation1'], 'target': row['equation2']},
        'parent': {
            'closure': bool(parent_found is not None),
            'graph_edges': parent_edges,
            'nodes': parent_nodes,
            'connected': parent_connected,
            'replayable': parent_replay,
            'captured_target_narrowing_nodes': len(captured)
        },
        'literal_endpoint_audit': {
            'records': endpoint_records,
            'unique_literal_target_terms': len(by_term),
            'has_literal_target_rhs': tr in by_term
        },
        'reentry_stage': {
            'new_graph_edges': reentry_added,
            'post_connected': after_reentry_connected,
            'replayable_closure': reentry_replay,
            'root': reentry_root
        },
        'congruence_stage': {
            'new_graph_edges': congruence_added,
            'post_connected': after_congruence_connected,
            'replayable_closure': congruence_replay,
            'root': congruence_root
        },
        'decision': decision,
        'sealed_transfer_ids_loaded': []
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
