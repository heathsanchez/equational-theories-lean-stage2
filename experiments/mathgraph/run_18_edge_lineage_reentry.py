import importlib.util
import itertools
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_lineage', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

GAPS = [(2666,2860),(2860,2062),(3366,41),(1367,678),(2920,1151)]

INITIAL_LIMITS = {
    'max_term_size': 15,
    'max_pool_terms': 56,
    'max_core_terms': 10,
    'max_source_edges': 3000,
    'max_graph_edges': 7000,
    'max_derivation_nodes': 9000,
    'max_congruence_rounds': 3,
}
LINEAGE = {
    'generations': 4,
    'lineages_per_generation': 96,
    'terms_per_lineage': 14,
    'instances_per_generation': 6000,
    'max_term_size': 31,
    'max_nodes': 50000,
    'max_edges': 45000,
    'seconds': 35.0,
}


class LineageSearch:
    def __init__(self, m, source, target, deadline):
        self.m = m
        self.search = m.EqualitySearch(source, target, deadline, limits=dict(INITIAL_LIMITS))
        self.source = source
        self.target = target
        self.deadline = deadline
        self.lineage_instances = {}
        self.lineage_candidates = {}
        self.lineage_composites = {}

    def expired(self):
        return time.monotonic() >= self.deadline

    def term_key(self, term):
        return self.m.term_size(term), self.m.render_term(term)

    def proof(self):
        root = self.search.shortest_path()
        return (self.search.nodes, root) if root is not None else None

    def local_terms(self, node_id):
        m = self.m
        nodes = self.search.nodes
        ids = {node_id}
        frontier = [node_id]
        # Preserve a shallow causal neighborhood, rather than flattening all proof state.
        for _ in range(2):
            nxt = []
            for current in frontier:
                for parent in getattr(nodes[current], 'parents', ()):
                    if parent not in ids:
                        ids.add(parent); nxt.append(parent)
            frontier = nxt
        terms = set()
        for current in ids:
            node = nodes[current]
            for side in (node.lhs, node.rhs):
                terms.update(m.walk_subterms(side))
        # Keep target anchors visible to every lineage, but do not mix unrelated derived terms.
        target_terms = set(m.walk_subterms(self.target[0])) | set(m.walk_subterms(self.target[1]))
        terms.update(target_terms)
        base = sorted(terms, key=self.term_key)

        # One constructive step: terms born from this lineage may themselves become arguments.
        composites = set()
        small = base[:12]
        for left in small:
            for right in small:
                term = ('op', left, right)
                if m.term_size(term) <= self.search.max_term_size:
                    composites.add(term)
        self.lineage_composites[node_id] = len(composites)
        terms.update(composites)

        tl, tr = self.target[:2]
        def score(term):
            return (
                min(m.structural_distance(term, tl), m.structural_distance(term, tr)),
                0 if term in target_terms else 1,
                m.term_size(term),
                m.render_term(term),
            )
        return sorted(terms, key=score)[:LINEAGE['terms_per_lineage']]

    def lineage_rank(self, node_id):
        m = self.m
        node = self.search.nodes[node_id]
        tl, tr = self.target[:2]
        return (
            min(
                m.structural_distance(node.lhs, tl), m.structural_distance(node.lhs, tr),
                m.structural_distance(node.rhs, tl), m.structural_distance(node.rhs, tr),
            ),
            m.term_size(node.lhs) + m.term_size(node.rhs),
            node_id,
        )

    def add_generation(self, generation):
        m = self.m
        source_vars = self.source[2]
        # Only expand lineages created in the immediately preceding generation.
        previous = [
            i for i, node in enumerate(self.search.nodes)
            if getattr(node, 'generation', 0) == generation - 1
            and node.kind not in ('symmetry','transitivity','reflexivity')
        ]
        previous = sorted(previous, key=self.lineage_rank)[:LINEAGE['lineages_per_generation']]
        self.lineage_candidates[generation] = len(previous)
        added = 0
        new_node_start = len(self.search.nodes)
        sibling_terms = []

        for node_id in previous:
            if self.expired() or added >= LINEAGE['instances_per_generation']:
                break
            pool = self.local_terms(node_id)
            sibling_terms.extend(pool[:4])
            # Fair layer enumeration within one causal cohort. Require at least one
            # non-target-derived composite/local term by provenance through node_id.
            for values in itertools.product(pool, repeat=len(source_vars)):
                if self.expired() or added >= LINEAGE['instances_per_generation']:
                    break
                origins = tuple((var, value, (node_id,)) for var, value in zip(source_vars, values))
                before = len(self.search.nodes)
                made = self.search.add_source_substitution(
                    values, generation=generation, origins=origins
                )
                if made is not None and len(self.search.nodes) > before:
                    added += 1
                    if added % 64 == 0 and self.search.shortest_path() is not None:
                        self.lineage_instances[generation] = added
                        return True
        self.lineage_instances[generation] = added

        # Existing logical constructor: congruence, now fed only causally adjacent terms.
        unique_siblings = []
        for term in sibling_terms:
            if term not in unique_siblings:
                unique_siblings.append(term)
        self.search.add_congruence_round(unique_siblings[:16], new_node_start)
        return self.search.shortest_path() is not None

    def solve(self):
        initial = self.search.solve()
        if initial is not None:
            return initial, 'initial'
        self.search.max_term_size = LINEAGE['max_term_size']
        self.search.max_derivation_nodes = LINEAGE['max_nodes']
        self.search.max_graph_edges = LINEAGE['max_edges']
        self.search.exhaustion = None
        for generation in range(1, LINEAGE['generations'] + 1):
            if self.add_generation(generation):
                return self.proof(), f'lineage-{generation}'
            if self.expired():
                self.search.exhaustion = 'timeout'
                break
        return self.proof(), 'lineage-exhausted'


def run_edge(m, source, target):
    engine = LineageSearch(m, source, target, time.monotonic() + LINEAGE['seconds'])
    started = time.monotonic()
    found, stage = engine.solve()
    result = {
        'stage': stage,
        'found': bool(found),
        'seconds': time.monotonic() - started,
        'graph_edges': engine.search.graph_edges,
        'nodes': len(engine.search.nodes),
        'exhaustion': engine.search.exhaustion,
        'lineage_candidates': engine.lineage_candidates,
        'lineage_instances': engine.lineage_instances,
        'lineage_composites_total': sum(engine.lineage_composites.values()),
    }
    if found:
        nodes, root = found
        try:
            replayed = m.replay_dag(source, nodes, root)
        except TypeError:
            replayed = m.replay_dag(
                source, nodes, root,
                maximum_term_size=LINEAGE['max_term_size'],
                maximum_nodes=LINEAGE['max_nodes'],
            )
        result['replayed'] = bool(replayed)
        result['proof'] = h.proof_summary(nodes, root)
    else:
        result['replayed'] = False
    return result


def main():
    equations = h.load_equations(); m = h.load_solver()
    out = {
        'schema': 'mathgraph.18-edge-lineage-reentry.v1',
        'hypothesis': 'preserve local derivation lineage when constructing and reusing new source arguments',
        'gaps': GAPS,
        'initial_limits': INITIAL_LIMITS,
        'lineage': LINEAGE,
        'rows': [],
    }
    for s, t in GAPS:
        source = m.parse_equation(equations[s]); target = m.parse_equation(equations[t])
        try:
            result = run_edge(m, source, target)
        except Exception as error:
            result = {'found': False, 'replayed': False, 'error': type(error).__name__ + ': ' + str(error)}
        out['rows'].append({'source_id': s, 'target_id': t, 'result': result})
        print(json.dumps({'edge': f'{s}->{t}', **result}, sort_keys=True, default=str), flush=True)
    out['replayed_count'] = sum(bool(row['result'].get('replayed')) for row in out['rows'])
    out['gaps_after_lineage'] = [[row['source_id'],row['target_id']] for row in out['rows'] if not row['result'].get('replayed')]
    path = Path('experiments/mathgraph/results/18-edge-lineage-reentry.json')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('SUMMARY', json.dumps({'replayed': out['replayed_count'], 'gaps': out['gaps_after_lineage']}, sort_keys=True))

if __name__ == '__main__':
    main()
