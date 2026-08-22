#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT = Path(__file__).resolve().parents[2]
PROTO = ROOT / 'experiments/mathgraph/protocols/methodology-0036-size-compression-matched-v2.json'
OUT = ROOT / 'experiments/mathgraph/results/methodology-0036-size-compression-matched-v2.json'
RID = 'evaluation_normal_0036'
HIST = 'origin/mathgraph/superposition-selector-tournament-20260820'


def load_historical(tag):
    text = subprocess.check_output(['git', 'show', f'{HIST}:submissions/mathgraph/solver.py'], text=True)
    p = Path(tempfile.gettempdir()) / f'mathgraph_methodology_0036_matched_{tag}.py'
    p.write_text(text)
    spec = importlib.util.spec_from_file_location(f'mg_methodology_0036_matched_{tag}', p)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


def connected(search, target):
    comps = search.components()
    a, b = target[:2]
    return a in comps and b in comps and comps[a] == comps[b]


def build_parent(m, row):
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
    search.solve_target_narrowing(cfg['maximum_depth'], cfg['branching'], cfg['maximum_terms'], cfg['maximum_context_depth'])
    return source, target, search, captured


def run_arm(tag, row, arm):
    m = load_historical(tag)
    source, target, search, captured = build_parent(m, row)
    tr = target[1]
    parent_ids = sorted({nid for nid,node in captured if node.lhs == tr or node.rhs == tr})
    frozen_cap = search.max_term_size
    raw_term_size = m.term_size

    if arm == 'B_CAP17_RAW':
        search.max_term_size = 17
    elif arm == 'C_CAP13_MACRO':
        def compressed_size(term):
            if term == tr:
                return 1
            if term[0] == 'var':
                return 1
            return 1 + compressed_size(term[1]) + compressed_size(term[2])
        m.term_size = compressed_size
        search.max_term_size = 13

    source_vars = list(source[2])
    target_vars = [('var', v) for v in target[2]]
    z_index = source_vars.index('z')
    signatures = []
    admitted = []
    before_nodes = len(search.nodes)
    before_edges = search.graph_edges
    for xv, yv in product(target_vars, repeat=2):
        values = [None] * len(source_vars)
        values[source_vars.index('x')] = xv
        values[source_vars.index('y')] = yv
        values[z_index] = tr
        origins = []
        for variable, value in zip(source_vars, values):
            origins.append((variable, value, tuple(parent_ids) if value == tr else ()))
        mapping = dict(zip(source_vars, values))
        lhs = m.substitute(source[0], mapping)
        rhs = m.substitute(source[1], mapping)
        raw_max = max(raw_term_size(lhs), raw_term_size(rhs))
        signature = tuple(m.render_term(v) for v in values)
        signatures.append({'values': signature, 'raw_max_size': raw_max})
        nid = search.add_source_substitution(values, generation=1, origins=tuple(origins))
        if nid is not None:
            admitted.append(signature)

    reentry_edges = search.graph_edges - before_edges
    after_reentry_connected = connected(search, target)
    root_reentry = search.shortest_path()
    replay_reentry = bool(root_reentry is not None and m.replay_dag(source, search.nodes, root_reentry))

    before_cong = search.graph_edges
    search.add_congruence_round([tr], before_nodes, edge_limit=search.max_graph_edges)
    congruence_edges = search.graph_edges - before_cong
    after_cong_connected = connected(search, target)
    root_final = search.shortest_path()
    replay_final = bool(root_final is not None and m.replay_dag(source, search.nodes, root_final))

    m.term_size = raw_term_size
    return {
        'arm': arm,
        'frozen_cap': frozen_cap,
        'effective_cap': search.max_term_size,
        'literal_target_rhs_parent_nodes': len(parent_ids),
        'candidate_signatures': signatures,
        'admitted_signatures': admitted,
        'admitted_count': len(admitted),
        'reentry_graph_edges_added': reentry_edges,
        'congruence_graph_edges_added': congruence_edges,
        'after_reentry_connected': after_reentry_connected,
        'after_congruence_connected': after_cong_connected,
        'replay_after_reentry': replay_reentry,
        'replay_final': replay_final,
    }


def main():
    protocol = json.loads(PROTO.read_text())
    assert protocol['frozen_before_execution'] is True
    assert protocol['id'] == RID
    row = next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems', 'evaluation_normal', split='train') if r['id'] == RID)

    A = run_arm('a', row, 'A_CAP13_RAW')
    raw_sizes = sorted({rec['raw_max_size'] for rec in A['candidate_signatures']})
    if A['frozen_cap'] != 13 or raw_sizes != [17]:
        out = {
            'schema': protocol['schema'], 'id': RID,
            'decision': 'MEASUREMENT_MISMATCH',
            'A_CAP13_RAW': A,
            'raw_candidate_sizes': raw_sizes,
            'sealed_transfer_ids_loaded': []
        }
    else:
        B = run_arm('b', row, 'B_CAP17_RAW')
        C = run_arm('c', row, 'C_CAP13_MACRO')
        a_set = set(map(tuple, A['admitted_signatures']))
        b_set = set(map(tuple, B['admitted_signatures']))
        c_set = set(map(tuple, C['admitted_signatures']))
        b_effect = B['after_congruence_connected'] or B['replay_final']
        c_effect = C['after_congruence_connected'] or C['replay_final']
        if not a_set and b_set == c_set and b_set:
            if b_effect == c_effect and b_effect:
                decision = 'MACRO_EQUIVALENT_TO_MIN_CAP'
            elif not b_effect and not c_effect:
                decision = 'SIZE_GATE_CAUSAL_BUT_NOT_SUFFICIENT'
            else:
                decision = 'ADMISSION_MATCH_OUTCOME_DIVERGENCE'
        elif b_effect and not c_effect:
            decision = 'RAW_SIZE_SEMANTICS_MATTER'
        else:
            decision = 'SIZE_NOT_CAUSAL_OR_CONTROL_FAILED'
        out = {
            'schema': protocol['schema'], 'id': RID,
            'decision': decision,
            'raw_candidate_sizes': raw_sizes,
            'arms': {'A_CAP13_RAW': A, 'B_CAP17_RAW': B, 'C_CAP13_MACRO': C},
            'admission_sets_equal_B_C': b_set == c_set,
            'sealed_transfer_ids_loaded': []
        }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
