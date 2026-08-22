#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT = Path(__file__).resolve().parents[2]
PROTO = ROOT / 'experiments/mathgraph/protocols/methodology-0036-size-compression-threshold-v1.json'
OUT = ROOT / 'experiments/mathgraph/results/methodology-0036-size-compression-threshold-v1.json'
RID = 'evaluation_normal_0036'
HIST = 'origin/mathgraph/superposition-selector-tournament-20260820'


def load_historical(tag):
    text = subprocess.check_output(['git', 'show', f'{HIST}:submissions/mathgraph/solver.py'], text=True)
    p = Path(tempfile.gettempdir()) / f'mathgraph_methodology_0036_size_{tag}.py'
    p.write_text(text)
    spec = importlib.util.spec_from_file_location(f'mg_methodology_0036_size_{tag}', p)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


def connected(search, target):
    comps = search.components()
    a, b = target[:2]
    return a in comps and b in comps and comps[a] == comps[b]


def raw_sizes(m, source, target):
    tr = target[1]
    target_vars = [('var', v) for v in target[2]]
    source_vars = list(source[2])
    rows = []
    for pos, source_var in enumerate(source_vars):
        other = [i for i in range(len(source_vars)) if i != pos]
        for fillers in product(target_vars, repeat=len(other)):
            values = [None] * len(source_vars)
            values[pos] = tr
            for i, filler in zip(other, fillers):
                values[i] = filler
            mapping = dict(zip(source_vars, values))
            lhs = m.substitute(source[0], mapping)
            rhs = m.substitute(source[1], mapping)
            rows.append({
                'target_rhs_slot': source_var,
                'fillers': [m.render_term(v) for v in values],
                'lhs_size': m.term_size(lhs),
                'rhs_size': m.term_size(rhs),
                'max_size': max(m.term_size(lhs), m.term_size(rhs))
            })
    return sorted(rows, key=lambda r: (r['max_size'], r['target_rhs_slot'], r['fillers']))


def run_arm(tag, row, mode, protocol):
    m = load_historical(tag)
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])
    tr = target[1]
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
    search.solve_target_narrowing(cfg['maximum_depth'], cfg['branching'], cfg['maximum_terms'], cfg['maximum_context_depth'])
    frozen_cap = search.max_term_size
    parent_edges = search.graph_edges
    parent_nodes = len(search.nodes)
    parent_connected = connected(search, target)

    rhs_parent_ids = []
    for nid, node in captured:
        if node.lhs == tr or node.rhs == tr:
            rhs_parent_ids.append(nid)
    selected = [(tr, tuple(sorted(set(rhs_parent_ids))))] if rhs_parent_ids else []

    original_term_size = m.term_size
    nominal_cap = frozen_cap
    if mode == 'B_MINIMUM_RAW_CAP':
        search.max_term_size = 17
    elif mode == 'C_MACRO_COMPRESSED':
        def weighted_term_size(term):
            if term == tr:
                return 1
            if term[0] == 'var':
                return 1
            return 1 + weighted_term_size(term[1]) + weighted_term_size(term[2])
        m.term_size = weighted_term_size
        search.max_term_size = nominal_cap

    before_reentry = search.graph_edges
    before_nodes = len(search.nodes)
    added_instances = 0
    if selected:
        added_instances = search.instantiate_reentry(
            selected,
            generation=1,
            maximum_instances=protocol['constraints']['maximum_reentry_instances'],
            targeted=False,
        )
    reentry_edges = search.graph_edges - before_reentry
    after_reentry_connected = connected(search, target)
    root_reentry = search.shortest_path()
    replay_reentry = bool(root_reentry is not None and m.replay_dag(source, search.nodes, root_reentry))

    before_congruence = search.graph_edges
    if selected:
        search.add_congruence_round([tr], before_nodes, edge_limit=search.max_graph_edges)
    congruence_edges = search.graph_edges - before_congruence
    after_congruence_connected = connected(search, target)
    root_final = search.shortest_path()
    replay_final = bool(root_final is not None and m.replay_dag(source, search.nodes, root_final))

    m.term_size = original_term_size
    return {
        'arm': mode,
        'frozen_cap': frozen_cap,
        'nominal_cap': nominal_cap if mode == 'C_MACRO_COMPRESSED' else search.max_term_size,
        'literal_target_rhs_parent_nodes': len(set(rhs_parent_ids)),
        'parent_graph_edges': parent_edges,
        'parent_nodes': parent_nodes,
        'parent_connected': parent_connected,
        'reentry_instances_added': added_instances,
        'reentry_graph_edges_added': reentry_edges,
        'congruence_graph_edges_added': congruence_edges,
        'after_reentry_connected': after_reentry_connected,
        'after_congruence_connected': after_congruence_connected,
        'replay_after_reentry': replay_reentry,
        'replay_final': replay_final,
        'raw_final_graph_edges': search.graph_edges,
    }


def main():
    protocol = json.loads(PROTO.read_text())
    assert protocol['frozen_before_execution'] is True
    assert protocol['id'] == RID
    m0 = load_historical('measure')
    row = next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems', 'evaluation_normal', split='train') if r['id'] == RID)
    source = m0.parse_equation(row['equation1'])
    target = m0.parse_equation(row['equation2'])
    size_rows = raw_sizes(m0, source, target)
    target_rhs_size = m0.term_size(target[1])

    # Independently reconstruct A first to obtain the actual frozen cap.
    A = run_arm('arm_a', row, 'A_FROZEN', protocol)
    actual_cap = A['frozen_cap']
    predicted_min = size_rows[0]['max_size'] if size_rows else None
    if actual_cap != 13 or target_rhs_size != 9 or predicted_min != 17:
        out = {
            'schema': protocol['schema'], 'id': RID,
            'decision': 'MEASUREMENT_MISMATCH',
            'actual_frozen_cap': actual_cap,
            'target_rhs_raw_size': target_rhs_size,
            'predicted_minimum_reentry_size': predicted_min,
            'size_rows': size_rows,
            'A_FROZEN': A,
            'sealed_transfer_ids_loaded': []
        }
    else:
        B = run_arm('arm_b', row, 'B_MINIMUM_RAW_CAP', protocol)
        C = run_arm('arm_c', row, 'C_MACRO_COMPRESSED', protocol)
        a_effect = A['after_congruence_connected'] or A['replay_final']
        b_effect = B['after_congruence_connected'] or B['replay_final']
        c_effect = C['after_congruence_connected'] or C['replay_final']
        if b_effect and c_effect and not a_effect:
            decision = 'COMPRESSED_REPRESENTATION_SUFFICIENT'
        elif b_effect and not c_effect:
            decision = 'RAW_BUDGET_ONLY'
        elif (B['reentry_graph_edges_added'] > 0 and C['reentry_graph_edges_added'] > 0 and A['reentry_graph_edges_added'] == 0 and not b_effect and not c_effect):
            decision = 'SIZE_GATE_REAL_BUT_INSUFFICIENT'
        else:
            decision = 'SIZE_NOT_CAUSAL'
        out = {
            'schema': protocol['schema'], 'id': RID,
            'decision': decision,
            'actual_frozen_cap': actual_cap,
            'target_rhs_raw_size': target_rhs_size,
            'predicted_minimum_reentry_size': predicted_min,
            'size_rows': size_rows,
            'arms': {'A_FROZEN': A, 'B_MINIMUM_RAW_CAP': B, 'C_MACRO_COMPRESSED': C},
            'sealed_transfer_ids_loaded': []
        }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
