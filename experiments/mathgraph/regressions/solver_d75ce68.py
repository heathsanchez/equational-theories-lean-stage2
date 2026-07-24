"""Deterministic MathGraph Stage 2 solver.

The submission is deliberately fail-closed: it asks the official judge only
about certificates reconstructed from the incoming equation strings, and
exits without a verdict when no replayable certificate is available.
"""

import json
import sys
import time
import heapq
from itertools import product


class ParseError(ValueError):
    pass


class Parser:
    """Full-consumption parser for the official single-operation equation DSL."""

    def __init__(self, text):
        self.tokens = self._tokenize(text)
        self.pos = 0

    @staticmethod
    def _tokenize(text):
        if not isinstance(text, str):
            raise ParseError("equation is not text")
        out = []
        i = 0
        while i < len(text):
            c = text[i]
            if c.isspace():
                i += 1
            elif c in "()=◇*":
                out.append("◇" if c == "*" else c)
                i += 1
            elif "a" <= c <= "z":
                # The official judge binds single lowercase variable names.
                if i + 1 < len(text) and text[i + 1].isalnum():
                    raise ParseError("variables must be single lowercase letters")
                out.append(c)
                i += 1
            else:
                raise ParseError("unexpected character")
        return out

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise ParseError("unexpected token")
        self.pos += 1
        return token

    def atom(self):
        token = self.peek()
        if token == "(":
            self.take("(")
            term = self.term()
            self.take(")")
            return term
        if token is not None and len(token) == 1 and "a" <= token <= "z":
            self.take()
            return ("var", token)
        raise ParseError("expected a variable or parenthesized term")

    def term(self):
        # Lean parses this operator left-associatively when parentheses are
        # omitted. Official data parenthesizes every nontrivial ambiguity.
        node = self.atom()
        while self.peek() == "◇":
            self.take("◇")
            node = ("op", node, self.atom())
        return node

    def equation(self):
        lhs = self.term()
        self.take("=")
        rhs = self.term()
        if self.peek() is not None:
            raise ParseError("trailing input")
        variables = []
        seen = set()
        for token in self.tokens:
            if len(token) == 1 and "a" <= token <= "z" and token not in seen:
                seen.add(token)
                variables.append(token)
        if not variables:
            raise ParseError("equation has no variables")
        return lhs, rhs, tuple(variables)


def parse_equation(text):
    return Parser(text).equation()


def render_term(term):
    if term[0] == "var":
        return term[1]
    return "(" + render_term(term[1]) + " ◇ " + render_term(term[2]) + ")"


def match_term(pattern, concrete, substitution):
    """Match a source term against a target term, extending substitution."""
    if pattern[0] == "var":
        name = pattern[1]
        previous = substitution.get(name)
        if previous is None:
            substitution[name] = concrete
            return True
        return previous == concrete
    return (
        concrete[0] == "op"
        and match_term(pattern[1], concrete[1], substitution)
        and match_term(pattern[2], concrete[2], substitution)
    )


def source_instance(source, target):
    """Return (arguments, symmetric) if target is one source instance."""
    sl, sr, source_vars = source
    tl, tr, _ = target
    for left, right, symmetric in ((tl, tr, False), (tr, tl, True)):
        substitution = {}
        if match_term(sl, left, substitution) and match_term(sr, right, substitution):
            if all(v in substitution for v in source_vars):
                return [substitution[v] for v in source_vars], symmetric
    return None


def term_size(term):
    if term[0] == "var":
        return 1
    return 1 + term_size(term[1]) + term_size(term[2])


def term_variables(term):
    if term[0] == "var":
        return {term[1]}
    return term_variables(term[1]) | term_variables(term[2])


def walk_subterms(term):
    yield term
    if term[0] == "op":
        yield from walk_subterms(term[1])
        yield from walk_subterms(term[2])


def substitute(term, mapping):
    if term[0] == "var":
        return mapping[term[1]]
    return ("op", substitute(term[1], mapping), substitute(term[2], mapping))


def structural_distance(left, right):
    """Small deterministic tree distance used only for target-guided ranking."""
    if left == right:
        return 0
    if left[0] != right[0]:
        return term_size(left) + term_size(right)
    if left[0] == "var":
        return 1
    return (
        structural_distance(left[1], right[1])
        + structural_distance(left[2], right[2])
    )


def is_subterm(needle, term):
    return needle == term or (
        term[0] == "op"
        and (is_subterm(needle, term[1]) or is_subterm(needle, term[2]))
    )


class EqualityNode:
    """A single immutable-by-convention equality derivation."""

    __slots__ = (
        "lhs", "rhs", "kind", "parents", "substitution", "context",
        "orientation", "generation", "term_origins",
    )

    def __init__(
        self, lhs, rhs, kind, parents=(), substitution=(), context=None,
        orientation=False, generation=0, term_origins=(),
    ):
        self.lhs = lhs
        self.rhs = rhs
        self.kind = kind
        self.parents = tuple(parents)
        self.substitution = tuple(substitution)
        self.context = context
        self.orientation = orientation
        self.generation = generation
        self.term_origins = tuple(term_origins)


class EqualitySearch:
    MAX_TERM_SIZE = 13
    MAX_POOL_TERMS = 40
    MAX_CORE_TERMS = 9
    MAX_SOURCE_ATTEMPTS = 1000000
    MAX_SOURCE_EDGES = 1600
    # Graph saturation stops at 4,000 edges; reserve 500 additional nodes for
    # the final explicit symmetry/transitivity proof chain.
    MAX_DERIVATION_NODES = 4500
    MAX_GRAPH_EDGES = 4000
    MAX_CONGRUENCE_ROUNDS = 3
    MAX_CERTIFICATE_BYTES = 50000

    def __init__(self, source, target, deadline, limits=None):
        self.source = source
        self.target = target
        self.deadline = deadline
        limits = limits or {}
        self.max_term_size = limits.get("max_term_size", self.MAX_TERM_SIZE)
        self.max_pool_terms = limits.get("max_pool_terms", self.MAX_POOL_TERMS)
        self.max_core_terms = limits.get("max_core_terms", self.MAX_CORE_TERMS)
        self.max_source_attempts = limits.get(
            "max_source_attempts", self.MAX_SOURCE_ATTEMPTS
        )
        self.max_source_edges = limits.get(
            "max_source_edges", self.MAX_SOURCE_EDGES
        )
        self.max_derivation_nodes = limits.get(
            "max_derivation_nodes", self.MAX_DERIVATION_NODES
        )
        self.max_graph_edges = limits.get(
            "max_graph_edges", self.MAX_GRAPH_EDGES
        )
        self.max_congruence_rounds = limits.get(
            "max_congruence_rounds", self.MAX_CONGRUENCE_ROUNDS
        )
        self.nodes = []
        self.adjacency = {}
        self.edge_keys = set()
        self.graph_edges = 0
        self.initial_pool = ()
        self.generations_completed = 0
        self.source_instances_by_generation = {}
        self.exhaustion = None
        self.reentry_terms_used = set()

    def expired(self):
        return time.monotonic() >= self.deadline

    @staticmethod
    def term_key(term):
        return term_size(term), render_term(term)

    def add_node(self, node, graph_edge=True):
        if len(self.nodes) >= self.max_derivation_nodes:
            self.exhaustion = self.exhaustion or "term budget exhausted"
            return None
        if graph_edge:
            key = (node.lhs, node.rhs)
            reverse = (node.rhs, node.lhs)
            if key in self.edge_keys or reverse in self.edge_keys:
                return None
            if self.graph_edges >= self.max_graph_edges:
                self.exhaustion = self.exhaustion or "term budget exhausted"
                return None
            self.edge_keys.add(key)
            self.graph_edges += 1
        node_id = len(self.nodes)
        self.nodes.append(node)
        if graph_edge:
            self.adjacency.setdefault(node.lhs, []).append((node.rhs, node_id, False))
            self.adjacency.setdefault(node.rhs, []).append((node.lhs, node_id, True))
        return node_id

    def make_pool(self):
        _, _, target_vars = self.target
        allowed = set(target_vars)
        terms = {("var", v) for v in target_vars}
        for side in self.target[:2]:
            terms.update(walk_subterms(side))
        for side in self.source[:2]:
            for term in walk_subterms(side):
                if term_variables(term) <= allowed:
                    terms.add(term)
        seeds = sorted(terms, key=self.term_key)
        for left in seeds:
            for right in seeds:
                composed = ("op", left, right)
                if term_size(composed) <= 9:
                    terms.add(composed)
                if len(terms) >= self.max_pool_terms * 2:
                    break
            if len(terms) >= self.max_pool_terms * 2:
                break
        return sorted(terms, key=self.term_key)[:self.max_pool_terms]

    def add_source_substitution(
        self, values, generation=0, origins=(), orientation=False
    ):
        sl, sr, source_vars = self.source
        mapping = dict(zip(source_vars, values))
        lhs = substitute(sl, mapping)
        rhs = substitute(sr, mapping)
        if (
            term_size(lhs) > self.max_term_size
            or term_size(rhs) > self.max_term_size
        ):
            return None
        substitution = tuple((v, mapping[v]) for v in source_vars)
        node_id = self.add_node(EqualityNode(
            lhs, rhs, "source instance" if generation == 0 else "source reentry",
            substitution=substitution, orientation=orientation,
            generation=generation, term_origins=origins,
        ))
        if node_id is not None:
            self.source_instances_by_generation[generation] = (
                self.source_instances_by_generation.get(generation, 0) + 1
            )
        return node_id

    def instantiate_sources(self, pool):
        source_vars = self.source[2]
        core = pool[:self.max_core_terms]
        attempts = 0

        # Target-guided instances first: match either source side against each
        # useful term and fill only the still-unbound variables.
        for pattern in self.source[:2]:
            for concrete in pool:
                partial = {}
                if not match_term(pattern, concrete, partial):
                    continue
                missing = [v for v in source_vars if v not in partial]
                fill_pool = core[:6]
                for fill in product(fill_pool, repeat=len(missing)):
                    mapping = dict(partial)
                    mapping.update(zip(missing, fill))
                    self.add_source_substitution([mapping[v] for v in source_vars])
                    attempts += 1
                    if (
                        attempts >= self.max_source_attempts
                        or self.graph_edges >= self.max_source_edges
                        or self.expired()
                    ):
                        if attempts >= self.max_source_attempts:
                            self.exhaustion = "instance budget exhausted"
                        elif self.expired():
                            self.exhaustion = "timeout"
                        return

        # Fair bounded enumeration: layer k includes every substitution whose
        # largest pool index is k, avoiding lexicographic starvation.
        for layer in range(len(core)):
            for indexes in product(range(layer + 1), repeat=len(source_vars)):
                if layer and max(indexes) != layer:
                    continue
                self.add_source_substitution([core[i] for i in indexes])
                attempts += 1
                if (
                    attempts >= self.max_source_attempts
                    or self.graph_edges >= self.max_source_edges
                    or self.expired()
                ):
                    if attempts >= self.max_source_attempts:
                        self.exhaustion = "instance budget exhausted"
                    elif self.expired():
                        self.exhaustion = "timeout"
                    return

    def node_cost(self, node_id):
        node = self.nodes[node_id]
        if node.kind == "source instance":
            return 1, 0, term_size(node.lhs) + term_size(node.rhs)
        if node.kind in ("congruence on left child", "congruence on right child"):
            parent = self.node_cost(node.parents[0])
            return parent[0], parent[1] + 1, parent[2] + term_size(node.lhs) + term_size(node.rhs)
        return 0, 0, term_size(node.lhs) + term_size(node.rhs)

    def shortest_path(self):
        start, goal = self.target[:2]
        if start == goal:
            node_id = self.add_node(
                EqualityNode(start, goal, "reflexivity"), graph_edge=False
            )
            return node_id
        queue = [((0, 0, 0, 0), 0, start)]
        best = {start: (0, 0, 0, 0)}
        previous = {}
        serial = 1
        while queue:
            cost, _, term = heapq.heappop(queue)
            if best.get(term) != cost:
                continue
            if term == goal:
                break
            for neighbor, node_id, reverse in self.adjacency.get(term, ()):
                edge_cost = self.node_cost(node_id)
                candidate = (
                    cost[0] + edge_cost[0],
                    cost[1] + edge_cost[1],
                    cost[2] + edge_cost[2],
                    cost[3] + 1,
                )
                if candidate < best.get(neighbor, (10**9,) * 4):
                    best[neighbor] = candidate
                    previous[neighbor] = (term, node_id, reverse)
                    heapq.heappush(queue, (candidate, serial, neighbor))
                    serial += 1
        if goal not in previous:
            return None

        path = []
        cursor = goal
        while cursor != start:
            parent_term, node_id, reverse = previous[cursor]
            path.append((node_id, reverse))
            cursor = parent_term
        path.reverse()

        oriented = []
        for node_id, reverse in path:
            if reverse:
                parent = self.nodes[node_id]
                node_id = self.add_node(EqualityNode(
                    parent.rhs, parent.lhs, "symmetry", parents=(node_id,)
                ), graph_edge=False)
                if node_id is None:
                    return None
            oriented.append(node_id)
        root = oriented[0]
        for next_id in oriented[1:]:
            left = self.nodes[root]
            right = self.nodes[next_id]
            if left.rhs != right.lhs:
                return None
            root = self.add_node(EqualityNode(
                left.lhs, right.rhs, "transitivity", parents=(root, next_id)
            ), graph_edge=False)
            if root is None:
                return None
        return root

    def add_congruence_round(self, siblings, first_node, edge_limit=None):
        edge_limit = (
            self.max_graph_edges if edge_limit is None else edge_limit
        )
        snapshot_end = len(self.nodes)
        for parent_id in range(first_node, snapshot_end):
            if self.expired() or self.graph_edges >= edge_limit:
                if self.expired():
                    self.exhaustion = "timeout"
                return
            parent = self.nodes[parent_id]
            if parent.kind in ("symmetry", "transitivity", "reflexivity"):
                continue
            for sibling in siblings:
                left_lhs = ("op", parent.lhs, sibling)
                left_rhs = ("op", parent.rhs, sibling)
                if (
                    term_size(left_lhs) <= self.max_term_size
                    and term_size(left_rhs) <= self.max_term_size
                ):
                    self.add_node(EqualityNode(
                        left_lhs, left_rhs, "congruence on left child",
                        parents=(parent_id,), context=("left", sibling),
                        generation=parent.generation,
                    ))
                right_lhs = ("op", sibling, parent.lhs)
                right_rhs = ("op", sibling, parent.rhs)
                if (
                    term_size(right_lhs) <= self.max_term_size
                    and term_size(right_rhs) <= self.max_term_size
                ):
                    self.add_node(EqualityNode(
                        right_lhs, right_rhs, "congruence on right child",
                        parents=(parent_id,), context=("right", sibling),
                        generation=parent.generation,
                    ))

    def solve(self):
        pool = self.make_pool()
        self.initial_pool = tuple(pool)
        self.instantiate_sources(pool)
        root = self.shortest_path()
        if root is not None:
            return self.nodes, root
        siblings = pool[:10]
        first = 0
        for _ in range(self.max_congruence_rounds):
            before = len(self.nodes)
            self.add_congruence_round(siblings, first)
            root = self.shortest_path()
            if root is not None:
                return self.nodes, root
            first = before
            if self.expired() or len(self.nodes) == before:
                break
        return None

    def components(self):
        """Return graph component IDs without mutating the search state."""
        component = {}
        for start in sorted(self.adjacency, key=self.term_key):
            if start in component:
                continue
            component_id = len(component)
            stack = [start]
            component[start] = component_id
            while stack:
                term = stack.pop()
                for neighbor, _, _ in self.adjacency.get(term, ()):
                    if neighbor not in component:
                        component[neighbor] = component_id
                        stack.append(neighbor)
        return component

    def collect_reentry_terms(self, generation, maximum, targeted=False):
        """Select bounded derived arguments and retain their provenance."""
        target_left, target_right = self.target[:2]
        target_subterms = set(walk_subterms(target_left)) | set(
            walk_subterms(target_right)
        )
        components = self.components()
        target_components = {
            components[t]
            for t in (target_left, target_right)
            if t in components
        }
        initial = set(self.initial_pool)
        origins = {}

        def record(term, node_id):
            if term_size(term) <= self.max_term_size:
                origins.setdefault(term, set()).add(node_id)

        for node_id, node in enumerate(self.nodes):
            if node.kind in ("symmetry", "transitivity", "reflexivity"):
                continue
            record(node.lhs, node_id)
            record(node.rhs, node_id)
            for term in walk_subterms(node.lhs):
                record(term, node_id)
            for term in walk_subterms(node.rhs):
                record(term, node_id)

        # Deterministic representatives of every merged equality class.
        by_component = {}
        for term, component_id in components.items():
            by_component.setdefault(component_id, []).append(term)
        representatives = {
            min(terms, key=self.term_key) for terms in by_component.values()
        }

        source_sides = self.source[:2]

        def unifies_source_side(term):
            for pattern in source_sides:
                substitution = {}
                if match_term(pattern, term, substitution):
                    return True
            return False

        def connected_target(term):
            return components.get(term) in target_components

        candidates = []
        for term, parent_ids in origins.items():
            if term in initial or term in self.reentry_terms_used:
                continue
            target_related = (
                term in target_subterms
                or connected_target(term)
                or any(is_subterm(term, context) for context in target_subterms)
                or any(is_subterm(context, term) for context in target_subterms)
            )
            if targeted and not target_related:
                continue
            score = (
                0 if any(
                    self.nodes[parent_id].generation == generation - 1
                    for parent_id in parent_ids
                ) else 1,
                0 if connected_target(term) else 1,
                0 if term in target_subterms else 1,
                min(
                    structural_distance(term, target_left),
                    structural_distance(term, target_right),
                ),
                0 if term in representatives else 1,
                0 if unifies_source_side(term) else 1,
                term_size(term),
                render_term(term),
            )
            candidates.append((score, term, tuple(sorted(parent_ids))))
        candidates.sort()
        selected = [
            (term, parent_ids)
            for _, term, parent_ids in candidates[:maximum]
        ]
        self.reentry_terms_used.update(term for term, _ in selected)
        return selected

    def reentry_instance_rank(self, values, components, target_subterms):
        sl, sr, source_vars = self.source
        mapping = dict(zip(source_vars, values))
        lhs, rhs = substitute(sl, mapping), substitute(sr, mapping)
        target_left, target_right = self.target[:2]
        left_component = components.get(lhs)
        right_component = components.get(rhs)
        target_components = {
            components[t]
            for t in (target_left, target_right)
            if t in components
        }
        connects_regions = (
            left_component is not None
            and right_component is not None
            and left_component != right_component
        )
        connected_to_target = (
            left_component in target_components
            or right_component in target_components
        )
        involves_target_subterm = lhs in target_subterms or rhs in target_subterms
        distance = min(
            structural_distance(lhs, target_left),
            structural_distance(lhs, target_right),
            structural_distance(rhs, target_left),
            structural_distance(rhs, target_right),
        )
        unifies = False
        for side in (lhs, rhs):
            for pattern in self.source[:2]:
                substitution = {}
                if match_term(pattern, side, substitution):
                    unifies = True
                    break
            if unifies:
                break
        return (
            0 if connects_regions else 1,
            0 if connected_to_target else 1,
            0 if involves_target_subterm else 1,
            distance,
            0 if unifies else 1,
            term_size(lhs) + term_size(rhs),
            tuple(render_term(value) for value in values),
        )

    def instantiate_reentry(
        self, selected, generation, maximum_instances, targeted=False
    ):
        """Rank and add a bounded second-generation source portfolio."""
        source_vars = self.source[2]
        origin_by_term = {term: ids for term, ids in selected}
        new_terms = [term for term, _ in selected]
        base = list(self.initial_pool[:6])
        pool = []
        for term in new_terms + base:
            if term not in pool:
                pool.append(term)
        components = self.components()
        target_subterms = set(walk_subterms(self.target[0])) | set(
            walk_subterms(self.target[1])
        )
        connected_components = {
            components[target]
            for target in self.target[:2]
            if target in components
        }
        ranked = {}
        attempt_cap = max(maximum_instances * 20, 1000)
        attempts = 0

        def consider(mapping):
            nonlocal attempts
            if attempts >= attempt_cap:
                return
            attempts += 1
            values = tuple(mapping[v] for v in source_vars)
            if not any(value in origin_by_term for value in values):
                return
            lhs = substitute(self.source[0], mapping)
            rhs = substitute(self.source[1], mapping)
            if (
                term_size(lhs) > self.max_term_size
                or term_size(rhs) > self.max_term_size
            ):
                return
            if targeted and not (
                lhs in target_subterms
                or rhs in target_subterms
                or components.get(lhs) in connected_components
                or components.get(rhs) in connected_components
            ):
                return
            ranked[values] = self.reentry_instance_rank(
                values, components, target_subterms
            )

        # First bind a source side to every selected/target term and fill the
        # remaining variables from a small fair pool.
        useful = new_terms + sorted(target_subterms, key=self.term_key)
        for pattern in self.source[:2]:
            for concrete in useful:
                partial = {}
                if not match_term(pattern, concrete, partial):
                    continue
                missing = [v for v in source_vars if v not in partial]
                for fill in product(pool[:10], repeat=len(missing)):
                    mapping = dict(partial)
                    mapping.update(zip(missing, fill))
                    consider(mapping)
                    if attempts >= attempt_cap or self.expired():
                        break
                if attempts >= attempt_cap or self.expired():
                    break
            if attempts >= attempt_cap or self.expired():
                break

        # Ensure substitutions using several derived arguments are considered.
        if not self.expired():
            for values in product(pool[:12], repeat=len(source_vars)):
                consider(dict(zip(source_vars, values)))
                if attempts >= attempt_cap or self.expired():
                    break

        added = 0
        for values, _ in sorted(ranked.items(), key=lambda item: item[1]):
            origin_records = tuple(
                (
                    variable,
                    value,
                    origin_by_term.get(value, ()),
                )
                for variable, value in zip(source_vars, values)
            )
            if self.add_source_substitution(
                values, generation=generation, origins=origin_records
            ) is not None:
                added += 1
            if added >= maximum_instances or self.expired():
                break
        if added >= maximum_instances:
            self.exhaustion = "instance budget exhausted"
        elif self.expired():
            self.exhaustion = "timeout"
        return added

    def solve_reentry(self, generations, new_terms, instances, targeted=False):
        """Continue a completed initial closure under bounded source re-entry."""
        for generation in range(1, generations + 1):
            remaining_generations = generations - generation + 1
            edge_limit = self.graph_edges + max(
                1,
                (self.max_graph_edges - self.graph_edges)
                // remaining_generations,
            )
            selected = self.collect_reentry_terms(
                generation, new_terms, targeted=targeted
            )
            if not selected:
                break
            before = len(self.nodes)
            self.instantiate_reentry(
                selected,
                generation,
                min(
                    instances,
                    max(1, (edge_limit - self.graph_edges) // 2),
                ),
                targeted=targeted,
            )
            # A re-entered law can become useful only after a congruence wrap.
            self.add_congruence_round(
                [term for term, _ in selected[:10]], before, edge_limit=edge_limit
            )
            self.generations_completed = generation
            # Partial-state validation is deliberate: check the graph even if
            # a wall-time or instance limit fired during this generation.
            root = self.shortest_path()
            if root is not None:
                return self.nodes, root
            if self.expired():
                self.exhaustion = "timeout"
                break
        # One final prefix check prevents a just-completed proof from being
        # discarded when the deadline fired at the end of the last loop.
        root = self.shortest_path()
        if root is not None:
            return self.nodes, root
        return None


def replay_dag(source, nodes, root):
    if root is None or root >= len(nodes):
        return False
    sl, sr, source_vars = source
    for node_id, node in enumerate(nodes):
        if node.kind in ("source instance", "source reentry"):
            mapping = dict(node.substitution)
            if tuple(mapping) != source_vars:
                return False
            lhs, rhs = substitute(sl, mapping), substitute(sr, mapping)
            if node.orientation:
                lhs, rhs = rhs, lhs
            if (node.lhs, node.rhs) != (lhs, rhs):
                return False
            if node.kind == "source instance":
                if node.generation != 0 or node.term_origins:
                    return False
            else:
                if node.generation <= 0:
                    return False
                origin_variables = tuple(record[0] for record in node.term_origins)
                if origin_variables != source_vars:
                    return False
                for variable, term, parent_ids in node.term_origins:
                    if mapping.get(variable) != term:
                        return False
                    for parent_id in parent_ids:
                        if parent_id >= node_id:
                            return False
                        parent = nodes[parent_id]
                        if not (
                            is_subterm(term, parent.lhs)
                            or is_subterm(term, parent.rhs)
                        ):
                            return False
        elif node.kind == "symmetry":
            if len(node.parents) != 1 or node.parents[0] >= node_id:
                return False
            parent = nodes[node.parents[0]]
            if (node.lhs, node.rhs) != (parent.rhs, parent.lhs):
                return False
        elif node.kind == "transitivity":
            if len(node.parents) != 2 or max(node.parents) >= node_id:
                return False
            left, right = (nodes[p] for p in node.parents)
            if left.rhs != right.lhs:
                return False
            if (node.lhs, node.rhs) != (left.lhs, right.rhs):
                return False
        elif node.kind in ("congruence on left child", "congruence on right child"):
            if len(node.parents) != 1 or node.parents[0] >= node_id:
                return False
            parent = nodes[node.parents[0]]
            side, sibling = node.context
            if side == "left":
                expected = (
                    ("op", parent.lhs, sibling), ("op", parent.rhs, sibling)
                )
            else:
                expected = (
                    ("op", sibling, parent.lhs), ("op", sibling, parent.rhs)
                )
            if (node.lhs, node.rhs) != expected:
                return False
        elif node.kind == "reflexivity":
            if node.lhs != node.rhs:
                return False
        else:
            return False
    return True


def make_dag_certificate(target, nodes, root):
    needed = set()

    def visit(node_id):
        if node_id in needed:
            return
        for parent in nodes[node_id].parents:
            visit(parent)
        needed.add(node_id)

    visit(root)
    ordered = sorted(needed)
    names = {node_id: "p" + str(i) for i, node_id in enumerate(ordered)}
    maximum_generation = max((nodes[node_id].generation for node_id in ordered), default=0)
    constructor = (
        "source-reentry generation " + str(maximum_generation)
        if maximum_generation
        else "equality-chain"
    )
    lines = [
        "import JudgeProblem",
        "-- mathgraph constructor: " + constructor,
        "",
        "def submission : Goal := by",
        "  intro G _ h",
    ]
    target_vars = target[2]
    if target_vars:
        lines.append("  intro " + " ".join(target_vars))
    for node_id in ordered:
        node = nodes[node_id]
        if node.kind in ("source instance", "source reentry"):
            mapping = dict(node.substitution)
            expression = "h" + "".join(
                " (" + render_term(mapping[v]) + ")" for v in mapping
            )
            if node.orientation:
                expression = "Eq.symm (" + expression + ")"
        elif node.kind == "symmetry":
            expression = "Eq.symm " + names[node.parents[0]]
        elif node.kind == "transitivity":
            expression = (
                "Eq.trans " + names[node.parents[0]] + " " + names[node.parents[1]]
            )
        elif node.kind == "congruence on left child":
            sibling = render_term(node.context[1])
            expression = (
                "congrArg (fun t => t ◇ " + sibling + ") "
                + names[node.parents[0]]
            )
        elif node.kind == "congruence on right child":
            sibling = render_term(node.context[1])
            expression = (
                "congrArg (fun t => " + sibling + " ◇ t) "
                + names[node.parents[0]]
            )
        else:
            expression = "rfl"
        lines.append(
            "  have " + names[node_id] + " : " + render_term(node.lhs)
            + " = " + render_term(node.rhs) + " := " + expression
        )
    lines.append("  exact " + names[root])
    return "\n".join(lines) + "\n", len(ordered)


def eval_term(term, assignment, table):
    if term[0] == "var":
        return assignment[term[1]]
    return table[eval_term(term[1], assignment, table)][
        eval_term(term[2], assignment, table)
    ]


def equation_holds(equation, table, deadline=None):
    lhs, rhs, variables = equation
    n = len(table)
    for values in product(range(n), repeat=len(variables)):
        if deadline is not None and time.monotonic() >= deadline:
            return None
        assignment = dict(zip(variables, values))
        if eval_term(lhs, assignment, table) != eval_term(rhs, assignment, table):
            return False
    return True


def find_fin2_countermodel(source, target, deadline):
    """Exhaust all 16 binary operations on Fin 2 and revalidate the winner."""
    for encoded in range(16):
        if time.monotonic() >= deadline:
            return None
        table = [
            [(encoded >> (2 * row + col)) & 1 for col in range(2)]
            for row in range(2)
        ]
        source_holds = equation_holds(source, table, deadline)
        if source_holds is None:
            return None
        target_holds = (
            equation_holds(target, table, deadline) if source_holds else True
        )
        if target_holds is None:
            return None
        if source_holds and not target_holds:
            # Deliberate second replay before certificate generation.
            source_replay = equation_holds(source, table, deadline)
            target_replay = equation_holds(target, table, deadline)
            if source_replay is True and target_replay is False:
                return table
    return None


def make_true_certificate(target, instance):
    _, _, target_vars = target
    arguments, symmetric = instance
    binders = " ".join(target_vars)
    applied = "h" + "".join(" (" + render_term(arg) + ")" for arg in arguments)
    if symmetric:
        applied = "(" + applied + ").symm"
    intro = "  intro " + binders + "\n" if binders else ""
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        + intro
        + "  exact "
        + applied
        + "\n"
    )


def make_false_certificate(table):
    compact = json.dumps(table, separators=(",", ":"))
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
        "  let candidateMagma : Magma (Fin 2) := {\n"
        '    op := finOpTable "'
        + compact
        + '"\n'
        "  }\n"
        "  refine ⟨Fin 2, candidateMagma, ?_⟩\n"
        "  decideFin!\n"
    )


def read_message():
    line = sys.stdin.readline()
    if not line:
        return None
    try:
        value = json.loads(line)
    except (json.JSONDecodeError, ValueError):
        return None
    return value if isinstance(value, dict) else None


def judge(verdict, code):
    print(json.dumps({"call": "judge", "verdict": verdict, "code": code}), flush=True)
    response = read_message()
    return response if response is not None else {}


REENTRY_PORTFOLIO = (
    {
        "name": "light",
        "seconds": 1.0,
        "generations": 1,
        "new_terms": 24,
        "instances": 400,
        "targeted": False,
        "reentry_term_size": 15,
        "reentry_nodes": 1500,
        "reentry_edges": 1400,
        "limits": {
            "max_term_size": 13,
            "max_pool_terms": 36,
            "max_core_terms": 8,
            "max_source_attempts": 8000,
            "max_source_edges": 600,
            "max_derivation_nodes": 900,
            "max_graph_edges": 800,
            "max_congruence_rounds": 2,
        },
    },
    {
        "name": "medium",
        "seconds": 3.0,
        "generations": 2,
        "new_terms": 32,
        "instances": 1000,
        "targeted": False,
        "reentry_term_size": 15,
        "reentry_nodes": 4000,
        "reentry_edges": 3600,
        "limits": {
            "max_term_size": 13,
            "max_pool_terms": 40,
            "max_core_terms": 9,
            "max_source_attempts": 18000,
            "max_source_edges": 1200,
            "max_derivation_nodes": 2200,
            "max_graph_edges": 1800,
            "max_congruence_rounds": 3,
        },
    },
    {
        "name": "targeted",
        "seconds": 5.0,
        "generations": 2,
        "new_terms": 32,
        "instances": 2000,
        "targeted": True,
        "reentry_term_size": 15,
        "reentry_nodes": 6000,
        "reentry_edges": 5600,
        "limits": {
            "max_term_size": 13,
            "max_pool_terms": 40,
            "max_core_terms": 9,
            "max_source_attempts": 24000,
            "max_source_edges": 1600,
            "max_derivation_nodes": 3000,
            "max_graph_edges": 2400,
            "max_congruence_rounds": 3,
        },
    },
)

# The content-hash development half promoted only medium. Light added no
# accepted development case, and targeted added no win after medium; retaining
# either in production would add runtime without improving the selection score.
PROMOTED_REENTRY_PORTFOLIO = (REENTRY_PORTFOLIO[1],)


def report_search(search, portfolio, found, replay_seconds=0.0, code_bytes=0):
    maximum_term = 0
    for node in search.nodes:
        maximum_term = max(
            maximum_term, term_size(node.lhs), term_size(node.rhs)
        )
    payload = {
        "portfolio": portfolio,
        "found": bool(found),
        "generations": search.generations_completed,
        "source_instances": search.source_instances_by_generation,
        "equality_nodes": len(search.nodes),
        "graph_edges": search.graph_edges,
        "max_term_size": maximum_term,
        "certificate_bytes": code_bytes,
        "replay_seconds": round(replay_seconds, 6),
        "exhaustion": search.exhaustion,
    }
    print(
        "MATHGRAPH_METRICS " + json.dumps(payload, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )


def finish_dag_candidate(source, target, search, found, portfolio):
    if found is None:
        report_search(search, portfolio, False)
        return False
    nodes, root = found
    replay_start = time.monotonic()
    replayed = replay_dag(source, nodes, root)
    replay_seconds = time.monotonic() - replay_start
    if not replayed or (nodes[root].lhs, nodes[root].rhs) != target[:2]:
        report_search(search, portfolio, False, replay_seconds)
        return False
    code, _ = make_dag_certificate(target, nodes, root)
    code_bytes = len(code.encode("utf-8"))
    report_search(search, portfolio, True, replay_seconds, code_bytes)
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("true", code).get("status") == "accepted"


def run_solo():
    startup = read_message()
    if startup is None:
        return
    problem = startup.get("problem")
    budget = startup.get("budget")
    if not isinstance(problem, dict) or not isinstance(budget, dict):
        return
    try:
        source = parse_equation(problem.get("equation1"))
        target = parse_equation(problem.get("equation2"))
    except (ParseError, TypeError, RecursionError):
        return

    instance = source_instance(source, target)
    if instance is not None:
        code = make_true_certificate(target, instance)
        if judge("true", code).get("status") == "accepted":
            return

    timeout = budget.get("timeout_seconds", 0)
    if not isinstance(timeout, (int, float)) or timeout <= 0:
        return

    # Preserve the validated generation-zero constructor as an independent
    # gate before any source re-entry experiment.
    chain_deadline = time.monotonic() + min(2.0, max(0.1, timeout / 20.0))
    try:
        chain_search = EqualitySearch(source, target, chain_deadline)
        found = chain_search.solve()
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError
    ):
        return
    if found is not None:
        if finish_dag_candidate(
            source, target, chain_search, found, "initial-chain"
        ):
            return
    else:
        report_search(chain_search, "initial-chain", False)

    # Fin 2 is tiny, but retain an explicit hard local deadline so malformed
    # or unexpectedly large incoming terms cannot turn this stage unbounded.
    deadline = time.monotonic() + min(1.0, max(0.05, timeout / 20.0))
    try:
        table = find_fin2_countermodel(source, target, deadline)
    except (KeyError, IndexError, RecursionError, TypeError):
        return
    if table is not None:
        code = make_false_certificate(table)
        if judge("false", code).get("status") == "accepted":
            return

    for configuration in PROMOTED_REENTRY_PORTFOLIO:
        seconds = min(
            configuration["seconds"], max(0.1, timeout / 20.0)
        )
        reentry_deadline = time.monotonic() + seconds
        try:
            search = EqualitySearch(
                source, target, reentry_deadline, configuration["limits"]
            )
            initial = search.solve()
            if initial is not None:
                # The pass tests re-entry in isolation. A generation-zero hit
                # under a different budget is not promoted as a re-entry win.
                report_search(search, configuration["name"], False)
                continue
            search.max_term_size = configuration["reentry_term_size"]
            search.max_derivation_nodes = configuration["reentry_nodes"]
            search.max_graph_edges = configuration["reentry_edges"]
            search.exhaustion = None
            found = search.solve_reentry(
                configuration["generations"],
                configuration["new_terms"],
                configuration["instances"],
                targeted=configuration["targeted"],
            )
        except (
            KeyError, IndexError, MemoryError, RecursionError, TypeError,
            ValueError,
        ):
            continue
        if found is not None and finish_dag_candidate(
            source, target, search, found, configuration["name"]
        ):
            return
        if found is None:
            report_search(search, configuration["name"], False)
    # Unresolved: EOF is intentional. Never guess and never ask an LLM.


def main():
    run_solo()


if __name__ == "__main__":
    main()
