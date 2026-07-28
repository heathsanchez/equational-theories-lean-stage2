"""Deterministic MathGraph Stage 2 solver.

The submission is deliberately fail-closed: it asks the official judge only
about certificates reconstructed from the incoming equation strings, and
exits without a verdict when no replayable certificate is available.
"""

import json
import sys
import time
import heapq
from collections import defaultdict, deque
from itertools import permutations, product


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


def get_subterm(term, path):
    cursor = term
    for direction in path:
        if cursor[0] != "op":
            raise ValueError("context path enters a variable")
        if direction == "L":
            cursor = cursor[1]
        elif direction == "R":
            cursor = cursor[2]
        else:
            raise ValueError("invalid context direction")
    return cursor


def replace_subterm(term, path, replacement):
    if not path:
        return replacement
    if term[0] != "op":
        raise ValueError("context path enters a variable")
    direction = path[0]
    if direction == "L":
        return ("op", replace_subterm(term[1], path[1:], replacement), term[2])
    if direction == "R":
        return ("op", term[1], replace_subterm(term[2], path[1:], replacement))
    raise ValueError("invalid context direction")


def nonvariable_positions(term, maximum_depth, include_root=True):
    """Yield deterministic paths whose selected subterm is an operation."""
    if term[0] != "op":
        return
    if include_root:
        yield ()
    if maximum_depth <= 0:
        return
    for direction, child in (("L", term[1]), ("R", term[2])):
        if child[0] != "op":
            continue
        path = (direction,)
        yield path
        if maximum_depth > 1:
            for suffix in nonvariable_positions(
                child, maximum_depth - 1, include_root=False
            ):
                if suffix:
                    yield path + suffix


class EqualityNode:
    """A single immutable-by-convention equality derivation."""

    __slots__ = (
        "lhs", "rhs", "kind", "parents", "substitution", "context",
        "orientation", "generation", "term_origins", "constructor",
        "derivation_depth", "context_record", "overlap_record",
    )

    def __init__(
        self, lhs, rhs, kind, parents=(), substitution=(), context=None,
        orientation=False, generation=0, term_origins=(), constructor=None,
        derivation_depth=0, context_record=None, overlap_record=None,
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
        self.constructor = constructor
        self.derivation_depth = derivation_depth
        self.context_record = context_record
        self.overlap_record = overlap_record


def variable_omission_collapse(source, target):
    """Build a two-instance proof when the source collapses every element."""
    left, right, variables = source
    if left[0] == "var" and left[1] not in term_variables(right):
        collapsed_variable, body, reverse = left[1], right, False
    elif right[0] == "var" and right[1] not in term_variables(left):
        collapsed_variable, body, reverse = right[1], left, True
    else:
        return None
    target_left, target_right, target_variables = target
    if not target_variables:
        return None
    anchor = ("var", target_variables[0])

    def make_mapping(collapsed_term):
        return {
            variable: (
                collapsed_term if variable == collapsed_variable else anchor
            )
            for variable in variables
        }

    left_mapping = make_mapping(target_left)
    right_mapping = make_mapping(target_right)
    common = substitute(body, left_mapping)
    if common != substitute(body, right_mapping):
        return None
    nodes = [
        EqualityNode(
            target_left, common, "source instance",
            substitution=tuple(
                (variable, left_mapping[variable]) for variable in variables
            ),
            orientation=reverse, constructor="variable-omission-collapse",
        ),
        EqualityNode(
            target_right, common, "source instance",
            substitution=tuple(
                (variable, right_mapping[variable]) for variable in variables
            ),
            orientation=reverse, constructor="variable-omission-collapse",
        ),
        EqualityNode(
            common, target_right, "symmetry", parents=(1,),
            constructor="variable-omission-collapse",
        ),
        EqualityNode(
            target_left, target_right, "transitivity", parents=(0, 2),
            constructor="variable-omission-collapse",
        ),
    ]
    return (nodes, 3) if replay_dag(source, nodes, 3) else None


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
        if node.kind in ("source instance", "source reentry"):
            return 1, 0, term_size(node.lhs) + term_size(node.rhs)
        if node.kind in ("congruence on left child", "congruence on right child"):
            parent = self.node_cost(node.parents[0])
            return parent[0], parent[1] + 1, parent[2] + term_size(node.lhs) + term_size(node.rhs)
        if node.kind == "symmetry":
            return self.node_cost(node.parents[0])
        if node.kind == "transitivity":
            left = self.node_cost(node.parents[0])
            right = self.node_cost(node.parents[1])
            return (
                left[0] + right[0],
                left[1] + right[1],
                left[2] + right[2] + term_size(node.lhs) + term_size(node.rhs),
            )
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


class ContextualSearch(EqualitySearch):
    """Bounded target narrowing and concrete contextual-overlap search."""

    def __init__(self, source, target, deadline, limits=None):
        super().__init__(source, target, deadline, limits)
        self.narrowing_successors = 0
        self.overlap_candidates = 0
        self.overlaps_added = 0
        self.missing_target_introduced = 0
        self.components_joined = 0
        self.overlap_depth_counts = {}
        self.term_size_rejections = 0
        self.variable_overlap_suppressed = 0

    def oriented_edge_node(self, lhs, rhs):
        for neighbor, node_id, reverse in self.adjacency.get(lhs, ()):
            if neighbor != rhs:
                continue
            if not reverse:
                return node_id
            parent = self.nodes[node_id]
            return self.add_node(
                EqualityNode(
                    parent.rhs, parent.lhs, "symmetry", parents=(node_id,)
                ),
                graph_edge=False,
            )
        return None

    def ensure_source_mapping(
        self, mapping, orientation, constructor, derivation_depth
    ):
        sl, sr, source_vars = self.source
        if any(variable not in mapping for variable in source_vars):
            return None
        lhs, rhs = substitute(sl, mapping), substitute(sr, mapping)
        if orientation:
            lhs, rhs = rhs, lhs
        if (
            term_size(lhs) > self.max_term_size
            or term_size(rhs) > self.max_term_size
        ):
            self.term_size_rejections += 1
            return None
        existing = self.oriented_edge_node(lhs, rhs)
        if existing is not None:
            return existing
        substitution = tuple((v, mapping[v]) for v in source_vars)
        return self.add_node(EqualityNode(
            lhs,
            rhs,
            "source instance",
            substitution=substitution,
            orientation=orientation,
            constructor=constructor,
            derivation_depth=derivation_depth,
        ))

    def wrap_context(
        self, parent_id, root, path, constructor, derivation_depth
    ):
        """Lift one equality through a structural one-hole context."""
        parent = self.nodes[parent_id]
        original = get_subterm(root, path)
        if original != parent.lhs:
            return None
        replacement = replace_subterm(root, path, parent.rhs)
        current_id = parent_id
        for index in range(len(path) - 1, -1, -1):
            current = self.nodes[current_id]
            context_term = get_subterm(root, path[:index])
            direction = path[index]
            if context_term[0] != "op":
                return None
            if direction == "L":
                sibling = context_term[2]
                lhs = ("op", current.lhs, sibling)
                rhs = ("op", current.rhs, sibling)
                kind = "congruence on left child"
                context = ("left", sibling)
            else:
                sibling = context_term[1]
                lhs = ("op", sibling, current.lhs)
                rhs = ("op", sibling, current.rhs)
                kind = "congruence on right child"
                context = ("right", sibling)
            context_record = None
            if index == 0:
                context_record = (
                    root, tuple(path), original, parent.rhs, replacement
                )
            node_id = self.add_node(EqualityNode(
                lhs,
                rhs,
                kind,
                parents=(current_id,),
                context=context,
                constructor=constructor,
                derivation_depth=derivation_depth,
                context_record=context_record,
            ))
            if node_id is None:
                node_id = self.oriented_edge_node(lhs, rhs)
            if node_id is None:
                return None
            current_id = node_id
        final = self.nodes[current_id]
        if (final.lhs, final.rhs) != (root, replacement):
            return None
        return current_id

    def target_score(self, before, after, components):
        target_left, target_right = self.target[:2]
        target_subterms = set(walk_subterms(target_left)) | set(
            walk_subterms(target_right)
        )
        absent = {
            target
            for target in (target_left, target_right)
            if target not in self.adjacency
        }
        joins = (
            before in components
            and after in components
            and components[before] != components[after]
        )
        return (
            0 if after in absent else 1,
            0 if after in target_subterms else 1,
            0 if joins else 1,
            min(
                structural_distance(after, target_left),
                structural_distance(after, target_right),
            ),
            0 if term_size(after) < term_size(before) else 1,
            len(term_variables(after)),
            term_size(after),
            render_term(after),
        )

    def narrowing_candidates(self, term, maximum_context_depth, branching):
        source_vars = self.source[2]
        pool = list(self.initial_pool or self.make_pool())[:5]
        components = self.components()
        ranked = {}
        for path in nonvariable_positions(
            term, maximum_context_depth, include_root=True
        ):
            subterm = get_subterm(term, path)
            for source_side, pattern in enumerate(self.source[:2]):
                partial = {}
                if not match_term(pattern, subterm, partial):
                    continue
                missing = [v for v in source_vars if v not in partial]
                fills = product(pool, repeat=len(missing))
                for fill_index, fill in enumerate(fills):
                    if fill_index >= branching:
                        break
                    mapping = dict(partial)
                    mapping.update(zip(missing, fill))
                    opposite = substitute(
                        self.source[1 - source_side], mapping
                    )
                    result = replace_subterm(term, path, opposite)
                    if term_size(result) > self.max_term_size:
                        self.term_size_rejections += 1
                        continue
                    key = (
                        term, result, tuple(path),
                        tuple((v, mapping[v]) for v in source_vars),
                    )
                    ranked[key] = (
                        self.target_score(term, result, components),
                        mapping,
                        source_side,
                        tuple(path),
                        result,
                    )
        return sorted(ranked.values(), key=lambda item: item[0])[:branching]

    def solve_target_narrowing(
        self, maximum_depth, branching, maximum_terms, maximum_context_depth
    ):
        self.initial_pool = tuple(self.make_pool())
        frontier = list(self.target[:2])
        seen = set(frontier)
        for depth in range(1, maximum_depth + 1):
            next_frontier = []
            for term in sorted(frontier, key=self.term_key):
                if self.expired() or len(seen) >= maximum_terms:
                    break
                candidates = self.narrowing_candidates(
                    term, maximum_context_depth, branching
                )
                for _, mapping, source_side, path, result in candidates:
                    if self.expired() or len(seen) >= maximum_terms:
                        break
                    introduced_missing = (
                        result in self.target[:2]
                        and result not in self.adjacency
                    )
                    parent_id = self.ensure_source_mapping(
                        mapping,
                        source_side == 1,
                        "target-narrowing",
                        depth,
                    )
                    if parent_id is None:
                        continue
                    wrapped_id = self.wrap_context(
                        parent_id,
                        term,
                        path,
                        "target-narrowing",
                        depth,
                    )
                    if wrapped_id is None:
                        continue
                    self.narrowing_successors += 1
                    if introduced_missing:
                        self.missing_target_introduced += 1
                    if result not in seen:
                        seen.add(result)
                        next_frontier.append(result)
                root = self.shortest_path()
                if root is not None:
                    return self.nodes, root
            components = self.components()
            target_components = {
                components[target]
                for target in self.target[:2]
                if target in components
            }
            connected = [
                term
                for term, component in components.items()
                if component in target_components and term not in seen
            ]
            for term in sorted(connected, key=self.term_key)[:maximum_terms]:
                seen.add(term)
                next_frontier.append(term)
            frontier = next_frontier[:maximum_terms]
            if not frontier:
                break
        if self.expired():
            self.exhaustion = "timeout"
        elif len(seen) >= maximum_terms:
            self.exhaustion = "term budget exhausted"
        root = self.shortest_path()
        return (self.nodes, root) if root is not None else None

    def overlap_score(self, outer_term, changed, consequence, components):
        target_left, target_right = self.target[:2]
        target_subterms = set(walk_subterms(target_left)) | set(
            walk_subterms(target_right)
        )
        absent = {
            target
            for target in (target_left, target_right)
            if target not in self.adjacency
        }
        joins = (
            consequence[0] in components
            and consequence[1] in components
            and components[consequence[0]] != components[consequence[1]]
        )
        exposes_match = False
        for side in self.source[:2]:
            substitution = {}
            if match_term(side, changed, substitution):
                exposes_match = True
                break
        return (
            0 if changed in absent or consequence[1] in absent else 1,
            0 if changed in target_subterms else 1,
            0 if joins else 1,
            min(
                structural_distance(changed, target_left),
                structural_distance(changed, target_right),
                structural_distance(consequence[1], target_left),
                structural_distance(consequence[1], target_right),
            ),
            0 if exposes_match else 1,
            0 if term_size(changed) < term_size(outer_term) else 1,
            len(term_variables(changed)),
            max(term_size(changed), term_size(consequence[1])),
            render_term(changed),
        )

    def collect_overlap_candidates(
        self, outer_nodes, inner_nodes, maximum_context_depth, maximum_candidates
    ):
        inner_index = {}
        for node_id in inner_nodes:
            node = self.nodes[node_id]
            inner_index.setdefault(node.lhs, []).append((node_id, 0))
            inner_index.setdefault(node.rhs, []).append((node_id, 1))
        components = self.components()
        candidates = {}
        for outer_id in outer_nodes:
            if self.expired() or len(candidates) >= maximum_candidates:
                break
            outer = self.nodes[outer_id]
            for outer_side, outer_term in enumerate((outer.lhs, outer.rhs)):
                # Bare variable positions are never yielded.
                self.variable_overlap_suppressed += len(
                    term_variables(outer_term)
                )
                for path in nonvariable_positions(
                    outer_term, maximum_context_depth, include_root=False
                ):
                    before = get_subterm(outer_term, path)
                    for inner_id, inner_side in inner_index.get(before, ()):
                        if outer_id == inner_id and outer_side == inner_side:
                            continue
                        inner = self.nodes[inner_id]
                        after = inner.rhs if inner_side == 0 else inner.lhs
                        changed = replace_subterm(outer_term, path, after)
                        if (
                            changed == outer_term
                            or term_size(changed) > self.max_term_size
                        ):
                            if term_size(changed) > self.max_term_size:
                                self.term_size_rejections += 1
                            continue
                        other = outer.rhs if outer_side == 0 else outer.lhs
                        consequence = (other, changed)
                        key = (
                            outer_id, inner_id, outer_side, inner_side,
                            tuple(path), changed,
                        )
                        score = self.overlap_score(
                            outer_term, changed, consequence, components
                        )
                        candidates[key] = (
                            score, outer_id, inner_id, outer_side, inner_side,
                            tuple(path), before, after, changed,
                        )
                        if len(candidates) >= maximum_candidates:
                            break
                    if len(candidates) >= maximum_candidates:
                        break
                if len(candidates) >= maximum_candidates:
                    break
        ordered = sorted(candidates.values(), key=lambda item: item[0])
        self.overlap_candidates += len(ordered)
        return ordered

    def apply_overlap(self, candidate, depth):
        (
            score, outer_id, inner_id, outer_side, inner_side, path,
            before, after, changed,
        ) = candidate
        outer = self.nodes[outer_id]
        introduced_missing = (
            changed in self.target[:2] and changed not in self.adjacency
        )
        components_before = self.components()
        outer_term = outer.lhs if outer_side == 0 else outer.rhs
        other = outer.rhs if outer_side == 0 else outer.lhs
        if inner_side == 0:
            inner_oriented = inner_id
        else:
            inner = self.nodes[inner_id]
            inner_oriented = self.add_node(
                EqualityNode(
                    inner.rhs, inner.lhs, "symmetry", parents=(inner_id,)
                ),
                graph_edge=False,
            )
        if inner_oriented is None:
            return None
        wrapped_id = self.wrap_context(
            inner_oriented,
            outer_term,
            path,
            "contextual-overlap",
            depth,
        )
        if wrapped_id is None:
            return None
        if outer_side == 0:
            outer_oriented = self.add_node(
                EqualityNode(
                    outer.rhs, outer.lhs, "symmetry", parents=(outer_id,)
                ),
                graph_edge=False,
            )
        else:
            outer_oriented = outer_id
        if outer_oriented is None:
            return None
        left = self.nodes[outer_oriented]
        right = self.nodes[wrapped_id]
        if left.rhs != right.lhs:
            return None
        record = (
            outer_id, inner_id, outer_side, inner_side, tuple(path),
            outer_term, before, after, changed, other, score,
        )
        consequence_id = self.add_node(EqualityNode(
            left.lhs,
            right.rhs,
            "transitivity",
            parents=(outer_oriented, wrapped_id),
            constructor="contextual-overlap",
            derivation_depth=depth,
            overlap_record=record,
        ))
        if consequence_id is None:
            consequence_id = self.oriented_edge_node(left.lhs, right.rhs)
        if consequence_id is None:
            return None
        self.overlaps_added += 1
        self.overlap_depth_counts[depth] = (
            self.overlap_depth_counts.get(depth, 0) + 1
        )
        if introduced_missing:
            self.missing_target_introduced += 1
        if (
            left.lhs in components_before
            and right.rhs in components_before
            and components_before[left.lhs] != components_before[right.rhs]
        ):
            self.components_joined += 1
        return consequence_id

    def solve_contextual_overlap(
        self,
        maximum_overlap_depth,
        maximum_context_depth,
        maximum_source_instances,
        maximum_candidates,
        maximum_new_nodes,
    ):
        self.initial_pool = tuple(self.make_pool())
        previous_source_edges = self.max_source_edges
        self.max_source_edges = min(
            self.max_source_edges, maximum_source_instances
        )
        self.instantiate_sources(self.initial_pool)
        self.max_source_edges = previous_source_edges
        source_nodes = [
            node_id
            for node_id, node in enumerate(self.nodes)
            if node.kind in ("source instance", "source reentry")
        ][:maximum_source_instances]
        if not source_nodes:
            return None
        start_nodes = len(self.nodes)
        outer_nodes = list(source_nodes)
        for depth in range(1, maximum_overlap_depth + 1):
            candidates = self.collect_overlap_candidates(
                outer_nodes,
                source_nodes,
                maximum_context_depth,
                maximum_candidates - self.overlap_candidates,
            )
            added_this_depth = []
            for index, candidate in enumerate(candidates):
                if (
                    self.expired()
                    or len(self.nodes) - start_nodes >= maximum_new_nodes
                    or self.overlap_candidates > maximum_candidates
                ):
                    break
                node_id = self.apply_overlap(candidate, depth)
                if node_id is not None:
                    added_this_depth.append(node_id)
                if index % 32 == 31:
                    root = self.shortest_path()
                    if root is not None:
                        return self.nodes, root
            root = self.shortest_path()
            if root is not None:
                return self.nodes, root
            outer_nodes = added_this_depth
            if not outer_nodes:
                break
        if self.expired():
            self.exhaustion = "timeout"
        elif self.overlap_candidates >= maximum_candidates:
            self.exhaustion = "overlap budget exhausted"
        elif len(self.nodes) - start_nodes >= maximum_new_nodes:
            self.exhaustion = "node budget exhausted"
        root = self.shortest_path()
        return (self.nodes, root) if root is not None else None


def replay_dag(
    source, nodes, root, maximum_term_size=None, maximum_nodes=None
):
    if root is None or root >= len(nodes):
        return False
    if maximum_nodes is not None and len(nodes) > maximum_nodes:
        return False
    sl, sr, source_vars = source
    for node_id, node in enumerate(nodes):
        if (
            maximum_term_size is not None
            and max(term_size(node.lhs), term_size(node.rhs))
            > maximum_term_size
        ):
            return False
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
            if node.overlap_record is not None:
                (
                    outer_id, inner_id, outer_side, inner_side, path,
                    outer_term, before, after, changed, other, _,
                ) = node.overlap_record
                if outer_id >= node_id or inner_id >= node_id:
                    return False
                outer = nodes[outer_id]
                inner = nodes[inner_id]
                expected_outer = (
                    outer.lhs if outer_side == 0 else outer.rhs
                )
                expected_before = (
                    inner.lhs if inner_side == 0 else inner.rhs
                )
                expected_after = (
                    inner.rhs if inner_side == 0 else inner.lhs
                )
                expected_other = (
                    outer.rhs if outer_side == 0 else outer.lhs
                )
                try:
                    selected = get_subterm(outer_term, path)
                    replaced = replace_subterm(outer_term, path, after)
                except (IndexError, TypeError, ValueError):
                    return False
                if (
                    outer_term != expected_outer
                    or before != expected_before
                    or after != expected_after
                    or other != expected_other
                    or selected != before
                    or replaced != changed
                    or (node.lhs, node.rhs) != (other, changed)
                ):
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
            if node.context_record is not None:
                root_term, path, original, replacement, result = (
                    node.context_record
                )
                try:
                    selected = get_subterm(root_term, path)
                    replaced = replace_subterm(
                        root_term, path, replacement
                    )
                except (IndexError, TypeError, ValueError):
                    return False
                if (
                    selected != original
                    or replaced != result
                    or (node.lhs, node.rhs) != (root_term, result)
                ):
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
    maximum_generation = max(
        (nodes[node_id].generation for node_id in ordered), default=0
    )
    constructors = {
        nodes[node_id].constructor
        for node_id in ordered
        if nodes[node_id].constructor
    }
    contextual_depth = max(
        (
            nodes[node_id].derivation_depth
            for node_id in ordered
            if nodes[node_id].constructor == "contextual-overlap"
        ),
        default=0,
    )
    narrowing_depth = max(
        (
            nodes[node_id].derivation_depth
            for node_id in ordered
            if nodes[node_id].constructor == "target-narrowing"
        ),
        default=0,
    )
    if "contextual-overlap" in constructors:
        constructor = "contextual-overlap depth " + str(contextual_depth)
    elif "target-narrowing" in constructors:
        constructor = "target-narrowing depth " + str(narrowing_depth)
    elif maximum_generation:
        constructor = "source-reentry generation " + str(maximum_generation)
    else:
        constructor = "equality-chain"
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
                "congrArg (fun _mg_t => _mg_t ◇ " + sibling + ") "
                + names[node.parents[0]]
            )
        elif node.kind == "congruence on right child":
            sibling = render_term(node.context[1])
            expression = (
                "congrArg (fun _mg_t => " + sibling + " ◇ _mg_t) "
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


def compile_equation(equation):
    """Compile both sides to one shared subterm DAG for cached evaluation."""
    lhs, rhs, variables = equation
    variable_index = {variable: index for index, variable in enumerate(variables)}
    nodes = []
    node_ids = {}

    def visit(term):
        previous = node_ids.get(term)
        if previous is not None:
            return previous
        if term[0] == "var":
            node = ("variable", variable_index[term[1]])
        else:
            node = ("operation", visit(term[1]), visit(term[2]))
        node_id = len(nodes)
        nodes.append(node)
        node_ids[term] = node_id
        return node_id

    left_id = visit(lhs)
    right_id = visit(rhs)
    return tuple(nodes), left_id, right_id, tuple(variables)


def evaluate_compiled(compiled, assignment, flat_table, domain_size=3):
    """Evaluate a compiled equation; repeated subterms are evaluated once."""
    nodes, left_id, right_id, _ = compiled
    values = []
    for node in nodes:
        if node[0] == "variable":
            values.append(assignment[node[1]])
        else:
            values.append(
                flat_table[
                    domain_size * values[node[1]] + values[node[2]]
                ]
            )
    return values[left_id], values[right_id]


def singleton_value(domain):
    if domain <= 0 or domain & (domain - 1):
        return None
    return domain.bit_length() - 1


def evaluate_compiled_domains(
    compiled, assignment, domains, domain_size
):
    """Evaluate to possible-value domains and an optional root table cell."""
    nodes, left_id, right_id, _ = compiled
    values = []
    for node in nodes:
        if node[0] == "variable":
            values.append((1 << assignment[node[1]], None))
            continue
        left_domain = values[node[1]][0]
        right_domain = values[node[2]][0]
        output_domain = 0
        left_singleton = singleton_value(left_domain)
        right_singleton = singleton_value(right_domain)
        root_cell = None
        for left in range(domain_size):
            if not (left_domain & (1 << left)):
                continue
            for right in range(domain_size):
                if right_domain & (1 << right):
                    output_domain |= domains[domain_size * left + right]
        if left_singleton is not None and right_singleton is not None:
            root_cell = domain_size * left_singleton + right_singleton
        values.append((output_domain, root_cell))
    return values[left_id], values[right_id]


def ordered_assignments(compiled, domain_size):
    """Order assignments by cheap direct dependencies and repeated values."""
    nodes, _, _, variables = compiled
    assignments = list(product(range(domain_size), repeat=len(variables)))

    def key(assignment):
        dependencies = set()
        for node in nodes:
            if node[0] != "operation":
                continue
            left, right = nodes[node[1]], nodes[node[2]]
            if left[0] == "variable" and right[0] == "variable":
                dependencies.add(
                    domain_size * assignment[left[1]] + assignment[right[1]]
                )
        return len(dependencies), len(set(assignment)), assignment

    assignments.sort(key=key)
    return tuple(assignments)


def relabel_table(flat_table, domain_size, permutation):
    relabelled = [0] * (domain_size * domain_size)
    for left in range(domain_size):
        for right in range(domain_size):
            relabelled[
                domain_size * permutation[left] + permutation[right]
            ] = (
                permutation[flat_table[domain_size * left + right]]
            )
    return tuple(relabelled)


def canonical_table(flat_table, domain_size):
    table = tuple(flat_table)
    return min(
        relabel_table(table, domain_size, permutation)
        for permutation in permutations(range(domain_size))
    )


def serialize_flat_table(flat_table, order):
    rows = [
        list(flat_table[row * order:(row + 1) * order])
        for row in range(order)
    ]
    return json.dumps(rows, separators=(",", ":"))


def replay_countermodel(source, target, flat_table, order, witness, serialized):
    """Independent total semantic replay, including witness and serialization."""
    if (
        not isinstance(flat_table, (tuple, list))
        or len(flat_table) != order * order
        or any(
            not isinstance(value, int) or value < 0 or value >= order
            for value in flat_table
        )
    ):
        return False
    if serialized != serialize_flat_table(flat_table, order):
        return False
    table = [
        list(flat_table[row * order:(row + 1) * order])
        for row in range(order)
    ]
    if equation_holds(source, table) is not True:
        return False
    if (
        not isinstance(witness, (tuple, list))
        or len(witness) != len(target[2])
        or any(
            not isinstance(value, int) or value < 0 or value >= order
            for value in witness
        )
    ):
        return False
    assignment = dict(zip(target[2], witness))
    if eval_term(target[0], assignment, table) == eval_term(
        target[1], assignment, table
    ):
        return False
    return equation_holds(target, table) is False




# External Stair-climber specialist, reproducibly generated by
# experiments/mathgraph/build_stair_climber_specialist.py.
EXTERNAL_STAIR_MODEL_BANK = (('stair-bank-0', 2, (0, 0, 0, 0)), ('stair-bank-1', 2, (1, 1, 0, 0)), ('stair-bank-2', 2, (1, 0, 1, 0)), ('stair-bank-3', 2, (0, 1, 1, 0)), ('stair-bank-4', 3, (1, 2, 0, 1, 2, 0, 1, 2, 0)), ('stair-bank-5', 2, (0, 1, 0, 1)), ('stair-bank-6', 2, (0, 0, 1, 1)), ('stair-bank-7', 3, (1, 1, 1, 2, 2, 2, 0, 0, 0)), ('stair-bank-8', 2, (0, 1, 0, 0)), ('stair-bank-9', 3, (0, 0, 0, 2, 0, 0, 0, 0, 0)), ('stair-bank-10', 2, (0, 0, 1, 0)), ('stair-bank-11', 3, (0, 2, 0, 0, 0, 0, 0, 0, 0)), ('stair-bank-12', 2, (1, 0, 0, 0)), ('stair-bank-13', 3, (0, 0, 0, 1, 1, 0, 2, 0, 2)), ('stair-bank-14', 4, (0, 0, 1, 1, 2, 2, 3, 3, 0, 0, 1, 1, 2, 2, 3, 3)), ('stair-bank-15', 5, (0, 2, 4, 1, 3, 4, 1, 3, 0, 2, 3, 0, 2, 4, 1, 2, 4, 1, 3, 0, 1, 3, 0, 2, 4)), ('stair-bank-16', 5, (0, 4, 3, 2, 1, 2, 1, 0, 4, 3, 4, 3, 2, 1, 0, 1, 0, 4, 3, 2, 3, 2, 1, 0, 4)), ('stair-bank-17', 4, (1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0)), ('stair-bank-18', 3, (1, 0, 2, 0, 2, 1, 2, 1, 0)), ('stair-bank-19', 5, (0, 3, 1, 4, 2, 3, 1, 4, 2, 0, 1, 4, 2, 0, 3, 4, 2, 0, 3, 1, 2, 0, 3, 1, 4)), ('stair-bank-20', 3, (0, 1, 2, 0, 1, 0, 0, 0, 2)), ('stair-bank-21', 3, (2, 0, 2, 1, 1, 1, 0, 2, 0)), ('stair-bank-22', 3, (2, 1, 0, 0, 1, 2, 2, 1, 0)), ('stair-bank-23', 3, (1, 1, 0, 1, 1, 0, 0, 0, 0)), ('stair-bank-24', 2, (0, 0, 0, 1)), ('stair-bank-25', 3, (0, 0, 0, 0, 2, 0, 0, 0, 0)), ('stair-bank-26', 4, (1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 0, 0, 0, 0)), ('stair-bank-27', 3, (0, 0, 0, 1, 1, 0, 2, 0, 0)), ('stair-bank-28', 3, (0, 1, 2, 0, 1, 2, 1, 0, 2)), ('stair-bank-29', 3, (0, 1, 2, 2, 0, 1, 1, 2, 0)), ('stair-bank-30', 4, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0)), ('stair-bank-31', 4, (0, 0, 1, 1, 2, 0, 3, 3, 0, 0, 1, 1, 2, 0, 3, 3)), ('stair-bank-32', 4, (0, 1, 2, 3, 0, 2, 3, 1, 0, 2, 3, 1, 0, 2, 3, 1)), ('stair-bank-33', 5, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0)), ('stair-bank-34', 6, (1, 2, 0, 0, 0, 0, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3, 0, 3, 3, 2, 3, 4, 2, 4, 4, 2, 0, 5, 0, 5, 5)), ('stair-bank-35', 7, (0, 6, 5, 4, 3, 2, 1, 2, 1, 0, 6, 5, 4, 3, 4, 3, 2, 1, 0, 6, 5, 6, 5, 4, 3, 2, 1, 0, 1, 0, 6, 5, 4, 3, 2, 3, 2, 1, 0, 6, 5, 4, 5, 4, 3, 2, 1, 0, 6)), ('stair-bank-36', 3, (0, 0, 0, 0, 0, 2, 0, 0, 0)), ('stair-bank-37', 3, (0, 0, 0, 1, 1, 0, 1, 2, 0)), ('stair-bank-38', 3, (0, 0, 0, 1, 1, 1, 0, 1, 0)), ('stair-bank-39', 3, (0, 0, 0, 2, 2, 0, 0, 0, 0)), ('stair-bank-40', 3, (0, 0, 2, 1, 1, 1, 0, 0, 2)), ('stair-bank-41', 3, (0, 2, 0, 1, 1, 0, 2, 0, 2)), ('stair-bank-42', 3, (0, 2, 1, 1, 0, 2, 2, 1, 0)), ('stair-bank-43', 3, (0, 2, 1, 2, 1, 0, 1, 0, 2)), ('stair-bank-44', 3, (0, 2, 2, 1, 1, 0, 2, 1, 0)), ('stair-bank-45', 3, (1, 2, 0, 1, 1, 0, 1, 1, 0)), ('stair-bank-46', 3, (2, 0, 1, 0, 1, 2, 1, 2, 0)), ('stair-bank-47', 4, (0, 0, 0, 0, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3)), ('stair-bank-48', 4, (0, 0, 1, 1, 2, 2, 3, 3, 0, 0, 0, 0, 2, 2, 3, 3)), ('stair-bank-49', 4, (0, 1, 2, 3, 1, 2, 3, 0, 2, 3, 0, 1, 3, 0, 1, 2)), ('stair-bank-50', 4, (0, 2, 0, 2, 0, 2, 0, 2, 1, 3, 1, 3, 1, 3, 1, 3)), ('stair-bank-51', 4, (0, 2, 3, 1, 3, 1, 0, 2, 1, 3, 2, 0, 2, 0, 1, 3)), ('stair-bank-52', 4, (1, 2, 3, 0, 3, 0, 1, 2, 1, 2, 3, 0, 3, 0, 1, 2)), ('stair-bank-53', 5, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0)), ('stair-bank-54', 5, (0, 2, 4, 1, 3, 2, 4, 1, 3, 0, 4, 1, 3, 0, 2, 1, 3, 0, 2, 4, 3, 0, 2, 4, 1)), ('stair-bank-55', 7, (0, 5, 3, 1, 6, 4, 2, 3, 1, 6, 4, 2, 0, 5, 6, 4, 2, 0, 5, 3, 1, 2, 0, 5, 3, 1, 6, 4, 5, 3, 1, 6, 4, 2, 0, 1, 6, 4, 2, 0, 5, 3, 4, 2, 0, 5, 3, 1, 6)), ('stair-bank-56', 3, (0, 0, 0, 0, 0, 1, 0, 0, 0)), ('stair-bank-57', 3, (0, 0, 0, 1, 1, 0, 0, 0, 0)), ('stair-bank-58', 3, (0, 0, 0, 1, 1, 0, 1, 0, 0)), ('stair-bank-59', 3, (0, 0, 0, 1, 2, 0, 0, 0, 0)), ('stair-bank-60', 3, (0, 0, 0, 1, 2, 0, 2, 0, 0)), ('stair-bank-61', 3, (0, 0, 0, 2, 0, 1, 1, 2, 0)), ('stair-bank-62', 3, (0, 0, 0, 2, 0, 2, 1, 1, 0)), ('stair-bank-63', 3, (0, 0, 1, 0, 0, 1, 1, 0, 0)), ('stair-bank-64', 3, (0, 1, 0, 2, 1, 2, 0, 1, 0)), ('stair-bank-65', 3, (0, 1, 1, 0, 1, 2, 0, 1, 0)), ('stair-bank-66', 3, (0, 1, 1, 2, 0, 2, 0, 0, 0)), ('stair-bank-67', 3, (0, 1, 2, 0, 0, 1, 0, 0, 0)), ('stair-bank-68', 3, (0, 1, 2, 0, 1, 0, 0, 0, 0)), ('stair-bank-69', 3, (0, 1, 2, 2, 1, 0, 0, 0, 2)), ('stair-bank-70', 3, (0, 1, 2, 2, 1, 0, 2, 1, 0)), ('stair-bank-71', 3, (0, 2, 0, 0, 0, 1, 0, 0, 0)), ('stair-bank-72', 3, (0, 2, 0, 1, 0, 1, 0, 0, 0)), ('stair-bank-73', 3, (0, 2, 0, 1, 1, 1, 0, 2, 0)), ('stair-bank-74', 3, (0, 2, 0, 2, 1, 1, 0, 1, 0)), ('stair-bank-75', 3, (0, 2, 1, 0, 0, 1, 0, 2, 0)), ('stair-bank-76', 3, (0, 2, 2, 1, 1, 1, 2, 0, 0)), ('stair-bank-77', 3, (1, 0, 0, 1, 0, 0, 0, 0, 0)), ('stair-bank-78', 3, (1, 0, 1, 0, 1, 0, 1, 0, 0)), ('stair-bank-79', 3, (1, 0, 1, 1, 0, 0, 1, 0, 0)), ('stair-bank-80', 3, (1, 0, 1, 2, 2, 1, 2, 0, 0)), ('stair-bank-81', 3, (1, 2, 1, 2, 2, 0, 1, 0, 0)), ('stair-bank-82', 3, (2, 0, 0, 1, 0, 0, 1, 0, 0)), ('stair-bank-83', 3, (2, 0, 1, 1, 1, 1, 1, 2, 0)), ('stair-bank-84', 3, (2, 1, 2, 0, 1, 0, 0, 0, 0)), ('stair-bank-85', 3, (2, 2, 1, 0, 1, 2, 1, 0, 0)), ('stair-bank-86', 4, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0)), ('stair-bank-87', 4, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 2)), ('stair-bank-88', 4, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 3)), ('stair-bank-89', 4, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0)), ('stair-bank-90', 4, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0)), ('stair-bank-91', 4, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0)), ('stair-bank-92', 4, (0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 1, 0)), ('stair-bank-93', 4, (0, 0, 0, 0, 1, 2, 2, 2, 2, 3, 3, 3, 3, 1, 1, 1)), ('stair-bank-94', 4, (0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0)), ('stair-bank-95', 4, (0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3)), ('stair-bank-96', 4, (0, 1, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 1, 2, 1)), ('stair-bank-97', 4, (0, 1, 2, 3, 0, 1, 2, 3, 2, 2, 0, 0, 2, 2, 0, 1)), ('stair-bank-98', 4, (0, 1, 3, 2, 1, 0, 2, 3, 0, 1, 3, 2, 1, 0, 2, 3)), ('stair-bank-99', 4, (0, 2, 0, 2, 3, 1, 3, 1, 3, 1, 3, 1, 0, 2, 0, 2)), ('stair-bank-100', 4, (0, 3, 1, 2, 2, 1, 3, 0, 3, 0, 2, 1, 1, 2, 0, 3)), ('stair-bank-101', 4, (1, 0, 0, 1, 0, 0, 0, 0, 3, 3, 3, 3, 2, 2, 2, 2)), ('stair-bank-102', 4, (1, 1, 1, 3, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 0)), ('stair-bank-103', 4, (1, 2, 1, 2, 1, 0, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2)), ('stair-bank-104', 4, (1, 2, 3, 0, 1, 2, 3, 0, 3, 0, 1, 2, 3, 0, 1, 2)), ('stair-bank-105', 4, (1, 3, 1, 3, 2, 0, 2, 0, 3, 1, 3, 1, 0, 2, 0, 2)), ('stair-bank-106', 5, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0)), ('stair-bank-107', 5, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0)), ('stair-bank-108', 5, (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0)), ('stair-bank-109', 5, (0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 3, 2, 3, 3, 2, 3, 3, 4, 4, 4)), ('stair-bank-110', 5, (0, 1, 2, 3, 4, 1, 0, 4, 2, 3, 2, 3, 0, 4, 1, 3, 4, 1, 0, 2, 4, 2, 3, 1, 0)), ('stair-bank-111', 5, (0, 1, 2, 4, 3, 0, 1, 2, 4, 3, 0, 1, 2, 4, 3, 2, 0, 1, 4, 3, 1, 2, 0, 4, 3)), ('stair-bank-112', 5, (0, 2, 4, 1, 3, 1, 3, 0, 2, 4, 2, 4, 1, 3, 0, 3, 0, 2, 4, 1, 4, 1, 3, 0, 2)), ('stair-bank-113', 5, (0, 3, 1, 4, 2, 1, 4, 2, 0, 3, 2, 0, 3, 1, 4, 3, 1, 4, 2, 0, 4, 2, 0, 3, 1)), ('stair-bank-114', 6, (2, 0, 1, 0, 0, 0, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 5, 3, 3, 0, 3, 3, 1, 4, 3, 1, 4, 4, 1, 5, 0, 0, 5, 5)), ('stair-bank-115', 6, (2, 2, 2, 5, 1, 1, 0, 1, 2, 3, 4, 5, 1, 1, 3, 3, 3, 0, 0, 1, 4, 0, 1, 0, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5)), ('stair-bank-116', 6, (2, 2, 3, 3, 2, 3, 3, 3, 5, 5, 3, 5, 4, 4, 0, 0, 4, 0, 0, 0, 1, 1, 0, 1, 5, 5, 2, 2, 5, 2, 1, 1, 4, 4, 1, 4)), ('stair-bank-117', 7, (0, 0, 0, 0, 4, 0, 0, 1, 1, 2, 1, 1, 5, 6, 1, 1, 2, 2, 4, 5, 6, 3, 3, 3, 3, 6, 3, 6, 0, 0, 2, 0, 4, 0, 0, 5, 1, 2, 1, 3, 5, 6, 6, 1, 2, 3, 6, 5, 6)), ('stair-bank-118', 7, (0, 1, 2, 3, 4, 5, 6, 4, 5, 6, 0, 1, 2, 3, 1, 2, 3, 4, 5, 6, 0, 5, 6, 0, 1, 2, 3, 4, 2, 3, 4, 5, 6, 0, 1, 6, 0, 1, 2, 3, 4, 5, 3, 4, 5, 6, 0, 1, 2)), ('stair-bank-119', 7, (0, 2, 4, 6, 1, 3, 5, 6, 1, 3, 5, 0, 2, 4, 5, 0, 2, 4, 6, 1, 3, 4, 6, 1, 3, 5, 0, 2, 3, 5, 0, 2, 4, 6, 1, 2, 4, 6, 1, 3, 5, 0, 1, 3, 5, 0, 2, 4, 6)), ('stair-bank-120', 7, (0, 3, 6, 2, 5, 1, 4, 5, 1, 4, 0, 3, 6, 2, 3, 6, 2, 5, 1, 4, 0, 1, 4, 0, 3, 6, 2, 5, 6, 2, 5, 1, 4, 0, 3, 4, 0, 3, 6, 2, 5, 1, 2, 5, 1, 4, 0, 3, 6)), ('stair-bank-121', 7, (0, 4, 6, 4, 5, 0, 0, 1, 2, 0, 0, 0, 1, 1, 2, 2, 4, 4, 0, 2, 0, 3, 5, 0, 2, 0, 3, 2, 4, 5, 4, 6, 6, 4, 5, 5, 5, 5, 1, 1, 5, 1, 6, 5, 5, 5, 6, 6, 3)), ('stair-bank-122', 7, (0, 6, 4, 1, 5, 2, 3, 4, 6, 0, 1, 5, 2, 3, 0, 6, 4, 3, 5, 2, 1, 5, 6, 4, 1, 0, 2, 3, 0, 3, 4, 1, 5, 2, 6, 0, 1, 4, 6, 5, 2, 3, 2, 6, 4, 1, 5, 0, 3)), ('stair-bank-123', 7, (2, 2, 5, 2, 2, 5, 5, 5, 5, 2, 5, 5, 2, 2, 4, 4, 4, 3, 3, 4, 3, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 4, 6, 6, 6, 6, 6, 6, 6)), ('stair-bank-124', 7, (3, 0, 3, 1, 5, 1, 0, 5, 1, 5, 5, 5, 6, 1, 4, 2, 3, 1, 0, 1, 2, 3, 3, 3, 4, 6, 3, 3, 0, 4, 5, 4, 5, 1, 4, 3, 5, 6, 6, 5, 3, 5, 4, 6, 6, 4, 1, 2, 6)), ('stair-bank-125', 7, (5, 5, 3, 5, 5, 5, 5, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 3, 6, 5, 3, 0, 3, 3, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6, 6, 6, 6, 6, 0, 0, 0, 0, 3, 0, 0)), ('stair-bank-126', 8, (0, 2, 5, 7, 6, 4, 3, 1, 4, 1, 3, 6, 7, 0, 5, 2, 6, 5, 2, 4, 0, 7, 1, 3, 2, 0, 6, 3, 5, 1, 7, 4, 7, 3, 1, 0, 4, 6, 2, 5, 3, 7, 4, 2, 1, 5, 0, 6, 1, 4, 7, 5, 3, 2, 6, 0, 5, 6, 0, 1, 2, 3, 4, 7)), ('stair-bank-127', 8, (0, 4, 6, 5, 7, 2, 1, 3, 3, 5, 2, 4, 1, 6, 7, 0, 4, 0, 7, 3, 6, 1, 2, 5, 6, 7, 0, 1, 4, 3, 5, 2, 5, 3, 1, 0, 2, 7, 6, 4, 1, 2, 5, 6, 3, 4, 0, 7, 7, 6, 4, 2, 0, 5, 3, 1, 2, 1, 3, 7, 5, 0, 4, 6)), ('stair-bank-128', 8, (0, 5, 1, 4, 2, 7, 3, 6, 6, 3, 7, 2, 4, 1, 5, 0, 7, 2, 6, 3, 5, 0, 4, 1, 1, 4, 0, 5, 3, 6, 2, 7, 5, 0, 4, 1, 7, 2, 6, 3, 3, 6, 2, 7, 1, 4, 0, 5, 2, 7, 3, 6, 0, 5, 1, 4, 4, 1, 5, 0, 6, 3, 7, 2)), ('stair-bank-129', 8, (0, 6, 5, 4, 7, 3, 2, 1, 4, 7, 2, 0, 6, 1, 5, 3, 1, 5, 6, 3, 2, 4, 7, 0, 2, 3, 4, 5, 1, 6, 0, 7, 5, 1, 0, 2, 3, 7, 4, 6, 6, 0, 1, 7, 4, 2, 3, 5, 7, 4, 3, 6, 0, 5, 1, 2, 3, 2, 7, 1, 5, 0, 6, 4)), ('stair-bank-130', 8, (1, 3, 7, 5, 4, 2, 0, 6, 4, 6, 0, 2, 1, 5, 7, 3, 6, 4, 2, 0, 3, 7, 5, 1, 3, 1, 5, 7, 6, 0, 2, 4, 2, 0, 6, 4, 5, 1, 3, 7, 0, 2, 4, 6, 7, 3, 1, 5, 7, 5, 1, 3, 0, 6, 4, 2, 5, 7, 3, 1, 2, 4, 6, 0)), ('stair-bank-131', 8, (1, 5, 0, 2, 3, 7, 6, 4, 6, 2, 3, 5, 0, 4, 1, 7, 3, 7, 6, 4, 1, 5, 0, 2, 7, 3, 2, 0, 5, 1, 4, 6, 2, 6, 7, 1, 4, 0, 5, 3, 5, 1, 4, 6, 7, 3, 2, 0, 4, 0, 5, 3, 2, 6, 7, 1, 0, 4, 1, 7, 6, 2, 3, 5)), ('stair-bank-132', 8, (2, 3, 7, 0, 6, 5, 1, 4, 6, 0, 5, 3, 2, 7, 4, 1, 5, 1, 6, 4, 7, 2, 3, 0, 4, 7, 3, 5, 1, 0, 6, 2, 1, 5, 0, 7, 4, 3, 2, 6, 3, 2, 4, 6, 0, 1, 5, 7, 0, 6, 1, 2, 3, 4, 7, 5, 7, 4, 2, 1, 5, 6, 0, 3)), ('stair-bank-133', 8, (2, 3, 7, 6, 4, 0, 5, 1, 6, 1, 0, 2, 5, 7, 4, 3, 4, 7, 3, 5, 2, 1, 6, 0, 0, 5, 6, 7, 1, 2, 3, 4, 5, 0, 1, 4, 6, 3, 2, 7, 1, 6, 5, 3, 0, 4, 7, 2, 3, 2, 4, 1, 7, 5, 0, 6, 7, 4, 2, 0, 3, 6, 1, 5)), ('stair-bank-134', 8, (4, 5, 2, 6, 3, 0, 7, 1, 7, 0, 3, 1, 2, 5, 4, 6, 5, 4, 1, 3, 6, 7, 0, 2, 3, 6, 7, 5, 4, 1, 2, 0, 2, 1, 4, 0, 7, 6, 3, 5, 6, 3, 0, 4, 5, 2, 1, 7, 1, 2, 5, 7, 0, 3, 6, 4, 0, 7, 6, 2, 1, 4, 5, 3)), ('stair-bank-135', 8, (5, 4, 6, 1, 2, 3, 0, 7, 0, 3, 1, 6, 7, 4, 5, 2, 1, 7, 0, 5, 3, 2, 6, 4, 3, 0, 7, 2, 1, 5, 4, 6, 6, 2, 5, 0, 4, 7, 1, 3, 7, 1, 3, 4, 0, 6, 2, 5, 2, 6, 4, 3, 5, 1, 7, 0, 4, 5, 2, 7, 6, 0, 3, 1)), ('stair-bank-136', 8, (6, 4, 3, 2, 1, 7, 0, 5, 4, 6, 5, 3, 0, 2, 1, 7, 2, 7, 1, 4, 5, 0, 3, 6, 7, 5, 4, 0, 3, 6, 2, 1, 1, 0, 7, 5, 4, 3, 6, 2, 5, 3, 0, 6, 2, 1, 7, 4, 0, 1, 2, 7, 6, 5, 4, 3, 3, 2, 6, 1, 7, 4, 5, 0)), ('stair-bank-137', 8, (7, 3, 1, 0, 4, 6, 2, 5, 2, 0, 6, 3, 5, 1, 7, 4, 0, 2, 5, 7, 6, 4, 3, 1, 6, 5, 2, 4, 0, 7, 1, 3, 3, 7, 4, 2, 1, 5, 0, 6, 5, 6, 0, 1, 2, 3, 4, 7, 1, 4, 7, 5, 3, 2, 6, 0, 4, 1, 3, 6, 7, 0, 5, 2)), ('stair-bank-138', 9, (3, 8, 4, 6, 1, 0, 2, 5, 7, 4, 0, 7, 1, 5, 2, 8, 6, 3, 3, 8, 4, 6, 1, 0, 2, 5, 7, 7, 2, 3, 5, 6, 8, 0, 1, 4, 7, 2, 3, 5, 6, 8, 0, 1, 4, 4, 0, 7, 1, 5, 2, 8, 6, 3, 4, 0, 7, 1, 5, 2, 8, 6, 3, 7, 2, 3, 5, 6, 8, 0, 1, 4, 3, 8, 4, 6, 1, 0, 2, 5, 7)), ('affine-right-offset-5', 5, (1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0)))
_STAIR_ENGINE_PAYLOAD = 'c-rl~?RMKnwjlbSPl3R_mVg+dEhgznGfnqV61h8P96KXB{c&X;8YDpx5lPShD2q`v>-?K}fLUvvWY+vYkJ3+a_eXuBKvIs=H$8W}x+4&%+O=y})vo<jyB>V>Xj7Gs#`)?|wz>}1+j?HCKIwGAFnpP>E*IJHEMH{7tMl*Ajwi)(y~ygkSOry`US`2%w#v%1&ZfbvESAA+kzQ8we0_ZVsZn-R&$HuoSzKpj7oc`J`Ep&9bx?2DS=H%0@FM^vC&lWr99`vg@b`cJAHigv=BogJ<g+|0gNFfsPRq++k}f9LLNN=lS-`gpqD8vOf|Fpq*en6|W!&v_Ud^*0U)9+q;9Qi)R05#XWjd*YXk4V_G+0)bLGN+zw~zl*@6+SQpMUndPd_>S{G=E6gOrIt?R2UvEhlrRU1kBinQkUo1tq@v)9E+Q3EebU<W(I2O4VjuXXP>|vv*})L$P|ELhs9TRn3ZWiNCYXWsxq9s^Hn5ULuACz6->=b9hG(S5tVMSHTjRgCVIm<*EvRI#eMIe%MSev*R*Lr`yi6EL{bJX%ZAAH2p(1si|<aU5<-I4kTM_185&cF3W&60sLbUS9P`y2ElE(PV0Ht55i~X-ENo!;Z?qx;_unJX&C$zgk^S(uVDl#e4PRbgTMdJ{}xQ*04m%ONaNp68f3SdzzYQs#-OSR<bod)w=R}0%KUO98)J-C**o*i9d_g602|>tlJx0xT4ojWe?^4->ihHav*)h@`WA&D^cF}}C&9Bv=kPq4=L;ymiU}I@Hn5>BH!!f-+fBLvfUpo&bxvzwehkC+1rU3^NGI@nyoFaVdIScDCBQ86vIM$E^es4k!u7Z@>OPgCml5_kHXG#E(C-*Va#h2`<)QpSO)rOZ)QW&ZZJo>d*Ex*XJfKfqm=?<}%}IQR-wB_ELTC!D_qjUs`Z_Ih=y#$gwTZ9nQzYP+|EyN61_=jh6^B$}uPF?yghp@<Yl7Mz!y+ikX;ywgOGUk`f?@>}aT;EyFr+a0RsLf}Y@*oUf`S1BCUgc&U>mFpSV~o&DiWjFj%Z0l+1rx@2B4Sl5{U!sVpLou!7R(B<8*QbuO0;J4RQlwU`g;_|Kor0SO}KX1_~h2LLH5Z>6TG_AlV%7)x4}~7~C|k#LzC&t84^QahX>Yki-jcwplC!;sKLlngx;IxDNweFYa_+W{cS|@;|7SP5ZF$r;B_{!~=-SaW<V2je+KAP!$Vg;OlKL-oWw*qE!)$MzalYp=>mgJRSMeGN1CE0iY+aFjgt=80jpFyTLhd-;6K-WMJm>VF;?a8YyNEO#nOk4)=>yx|%?N?1nhB++|=s<mK^XkpqS$%!MUj&%{OSqG!*(6^sl&lriGe!Bsz*XOk<~8RqF?CO9I1d~)*H<6xXl162?Bcpdzhl?8KD=mw4eK@giuhd=-)F4imH;DE!3h%%~ymyX7>YQ&onFd~>=Fc)~AT)@nmc01-C_(N5!I-Re-IsNv<^RI#Rgup-HYiF`Zfn9xt=$s+9i2j@|HW@v}JU;=-sp#h{1*E2mvx~_yA+mn~<SL^qMr?V{I;K5K&RgD*I}d`t|Bru%|1nF%ZdBsUKg<813y5~m9{@)$*04J)vKca{{BmB$u(w1Z@CSIkN|zZ-{%JM~aPVkUM#Va+VVVirmKpA?0lw)9ZXSgnLtQaYP@U=nOR2IEk}Rr3)d~i&>H^L4b;PXi-5l4#B3nV3;K?B9(MDcfJRSxE81N_*zmHG&MI81O=bC2gdY-_NuVL~|0rcY}cvWsPRRA~e99BNA(QLI@k~F4}k^gd#i$r7n#?DG@1P=$niS;R4s9JGrtz)+q)Zs5s?=f{O4}LE@e;k}N0qMRyO&3+x_&x@K=Bi`B7Zq$sMD~l5J`m9&KKG=`?9v*hATX@98s-2K_?Wx2pR}!H^^kN2IX$G*r6p@XQfkWD05tY_N8lx2J+TUlc`eq5IeRbqqQ)?GK1fIpVep1=+_B*Bic<4kt_!R>LcSvx6kt@#36FIeDAgAyLlg8YjBYg)_!!>>w}KY%WPIwur#Q40BuYxi`^+W1m{-6H<~UE9tG-*U7kM3p1L(|&)kT980KujWK$9I-l84!3m1V&Ci%pGlGpi%0eKAy13zP?#SZy3gPOo`4uhPYOo<=cE0eZ10-eskF0WeSnpyr%K0dKk>`bLwvErkJ2-E_UqR{E3ZFMJVQT4d>L1pTTGAH-W6s5=v!0R+boxUl&KhE6nwk~MCfX&u!G$?u{~q|_99hwm)X5Go%5DlnJrZi}{`7c0$8a10OyVo=nBXCX0$0MW3RzCcOveFLS0q*O%<B)g53fB>aBJCRf^iBbqf682fxwp>kwpeKwIu)HDTl>|)CW<@S-Rqr*b8zWIskC!k(P;EYN>_zeJWhT+9eYgnlR6w?%-}a2R3L#vYq~s~yi$4;{x+j|w#`XegKDO5vt%-jGvsPt;a3`C_a+|Wb17dgNaty=n51@oZP%w@gC1qcCY;90PE$z7DYj$^YVz{u7DHfW>7ZxmoNXeTtwYKpuD=_kG7#Rw8G+!jayoCP~LrDl}+!Yd12gS>G^Q_E_iG$2oPbrK4%KB(A3By>C55*V!7UNRJAKak9s!2UF#r0WuOAX)kVRdEGD!4W3-7z9KOGA&LLyC5=1s(-QJV3H$jD4#a8liL-#zHHkWrKE`>%O^5r7<;h4dlTU@gwZhCcR?j*QfxAU8=iT;okXiWbOb2gSHvD(63P;sbJ4XxehBTnk%{i(8EYX<k-OHRk1pDRQcNq^rUPW0WcukZhFb8RX@<A(|CcLU`=vnJ2;D6R)n)kzk`L%pon1R{?KM0P%7Fvl>*WW)0$y?6E?T=jO}>ZUMRH8DH-ClIVa*hXigIscG9D-UOa#K>ZjtT)e-)Brhg`&?2XWvlCUH;&S3O1@gtqVA0`7D2Fb2q3`_7X2j+!lrD8?Ozf=^1C|^w$n<?2ZGtqstVopG-m))hmJiTB#X{iY4!%eEea6b3=Gp}g)<_L1SJ`}k0761t5&YV}wDL`{0(kDdT82gN$>D`XW843#m8s5ek3=YoBY`Lzt+N_JC6N*-WfueN@5W8HMMxUwX*F-A(IST=?vhEvVtf&sFdDszp$&A$cXjxtE;xlNiei($WSE2aB6P1TW;D$^0Dq*v(rOODyoY*p_Lp`hpn{7U+9i@`c!@dC6+bd*rP%#A&a*URhQ14!3jvY|@Bp$F4I6)Sx%Ah6KDnq8>gl)~Si5{{V5)cL337?&Z`!GZ9Mp)e9e?Kbkf(VUVXzq;-=&<$?2Q7<=VG$Ckg#{GNE0Qtyv~9OrZeXbwvl*=+vbA_P8gNF>%n+j~5Fmo(C|4nc5;n#=bXeqQ{s5ko!t8~f?c6*y>B*oTC+(cp{b%g9y62%SzEtG|W>JMJBx1Z`)eV%L$frO8d4wo0^4OJ~kmRuc0-&Y{<xo9{ZV~Vu8uBFR<G!-r!@#xdBPQjcG;BEIO>G<b+iM<?&HKpg))92;h`V(}rt_n_Lt8H=&^nn@1rN%nFb{C+a41U*9X%LYz_;ctk=?E$nUfR)#nwXeB++BS{v8F3caGSWlJz_ko*U)EaVKK|gAV_n6o=15?eRHyI(p|~U;wg_g6^Vyc5;v9p?pq16DJMF9?sQdUX&xClz3Xvl7ZigmAzzy*Gw!LB=5=wwJfeP1Vn!cj40I(MzmuuU6^@jnuf_8w$=<`a)<7cm3_f=D|>VB;*G_Q!agymzU3_p*Ti8fa(;Y^xZkl?YM>XF#0yr~G@s2f5J$+fupbht%1uD4*kyN`U-2OPqgmFjo*bRKT#6_x`4sXnCfSIUp2OPael`fPpF8pFv}@HVYBC{-v^(Y;%e>(sybV!JFYkW3ofP<=)g5puGC1#KaMixueY3h+74KGzAB`Z4n?V9C7ZPx7k3s=WqBskgN*e5r{h!r&0t&P1(opOLa-dtVe#olG9Sf>LU{7dvpztxvSD-AlOfIhklF)jTfe93rpi5nrYUqV_B?m&9NO$>DmA(`eS0Jtx#X@^l(JxuX-QcNIL;&5Rqk#N}lSx(qS7k%qoXvfPE`tVD;uoN`<d-Yp6?K7I>5P;s5T-BZu(cvg3ZO7zI=WJssmrZt>)N67xfU_>)1Z(`@3WgpwysUw(kjRrRx~jq*=1+iU(DbZHoyFO9dT@^VSnzsGF?X~PRrGvuh1u}#``buJ$OSe-vm)A`l*9vj<dJO5#M0tH!%tt1oyPO3>N8fJWVUsJ)eKs=UALK^7|W}uHQn%MLs^N#24ggZ-R7@1O0Jk;B+Q8?-6U-|BBDwl?CXfOHh@r^Rieiaj}uYFi%<g#kd_2&9u)NOnuvD>8<8zNxGtTYyi!aJ=b!KC;~+P@xM)<2*bFGVJC5k@0g2u4A5(`qwN#hmTa~wn=)GekN@p$x7X6Hm?OxU*i|mLG+TDH^#WjM12h>fNp-H!ND=Y&@RKQMj*<Wb7!-B5FuQer0$$(Kl$?*Un>Fr9voHeHthjTdUv5{DHYDOU+I{xn8n)UbG-Si(*5g#fCS++OjGz~@LD=F&iO?Lsw)M!MrBQ2lsES&(f0ofHY$Z8<!m%bCjTBHEOO&tbvIrgm=YzM8FhWn5iOw4)r<~Pc1~x6=Bd#W9wrY(T29^D6c#oNBrxl528zGPM<|nT;G3=NIVu@dji`(#Xw@&ON7)jws)&<tkT<^Dp!rki?Q8KtaY}H8Y7WpbeDqIj0l!I_6%#C|NRwu*b9qmAwMI^_JBzvwq{lkVd{liezLJ@q;YLgRPmZYoXNK>20$H9r%_LVHI4V$XtTEc=QineiX;tr!kZV^dGX3-WjsxFtszK|=mFrH%El@W(&#9$$DIf68pWM$2M6fI}aq8aR2fMRZ<A%GTwMi=^r7Qh9~M(K_hQgTRbW2_>zBAFA^b=~<QD9PLdU$3B?B^-vrO(=*F^n*X5I0zISZyROhQu-s1f9`&zxy_xqLu@)7ki-TY7u<cBWBl;*beUCajK86pV!s)PzlkI84fG>_GTl1^^9O&{Zjyn1<WF*14djDaLo$qk{gaC*elt){{6YCs2I`4FXp7@OKPDX|agy3J(2uHCMHMRfLb<gD`Y~w)GY-rjNi#xmVEsybF^2=^chZS>#c_Yd0D}tS_7-SWUKBM*WUt<3=t!94>n!-!moJ`kATuu+y+kSzxGf4!H_J81Z@j!j@M5J0dMZRnQhK^U@CpN_s|l=!S_V~C9l#702J1yuJal@A(9q~mEm4muG0wWoF7pb*L!&qIHyBS|K^xh1UTmtxwnKsKQyARkGQ|LqY?;>;cjC=Fz0TeQ<3%yKVt3yZFwmtFau<vE*|cNy8J$lYCO!c;V<a7}1_~+0tr8%ng3;LVgfQeZC$0EGvTaOL*q$+}5ZV$S)hjNsW>Hyw{SJNt|LgpVDi%SpAG6f}HJez3D4qj_nEhc~9qDQ^-liYa8$g=pvHcU~{)i%X#mfuw+IG9$p^AMxr{Qi1eq1Bc%$s4DMu<6v-jquLFToL-<u`;6GD<0{ZS!m~6(3b#1Jsj3xfQ3ug^4zHD=beF5OljdGZg;zIz6k-dFTluM17UjU6iS)Cssh><f`kGw!;(QyNpnbn_)bfJOsYVY9#xx@1sLYd=K}%EyRbvI#E8{b%_pzGxN~%cgZ_-x6!|5AZ7$^sqPyB8$ZM<;7WS2J0i}B{cp;rcAZzS_qn97-8ef*VHP+Uw#Qys@mG>EjS@y6mbVPkxT9m|CH7WH<26xQzr&a{<7X*<Hln>SR2yCb1GSgYRhF&$YN~+v2$NbHWt>@h$Q)vWlO`Y#58DvtXAw{+Tk%B@IhfK?L<mN$W}#lQkerb+=p$cUl7GL?6Og(!<b_g~)+$ut05Bi5^jThVkOZDb$~k~Wt#AtOPwQeC;f69&oRZ~Xt3@Rovl+}r07{R@rZs4w&7{IMNNu@Q4c(D8NY(B_D>l{$wZwX@8YO<z)5KIFHMd2}2lt4Sd_6rB?jO!ZVv_w(Gl}Mmwx#5~3?&T&4ziV)D6qNYe%2BxmXX-P;;@J#;6V^?;G>vO=(8URF%o72yv8@Y)#A1-zBx;rH9>QkCnAhJE5)qs=!Jiwr|yNA3kU_n|7be*o#+T-VG{C<W$6i?(7Guo3pc(%2I{pP$Z$x|!C}z^9CKlcBPw!9SnLTeUzmZ>7RTV&6fong0nkOrg+h$M_K`(~RWYcK29mD(@a=f~Hr@_QGmyP-j*BL4&6&>cyfIj_P+4s#I$sUA1wgwpEC9yZl{`xf+(n3Q!lBuDT}EuZJhk6*#H9O%<a~o?hBi`YbHZjWR0+dQld>BZ=c<2facgJ{sJT~gU&$9dv^t9>4+&odA0iH2B|yg?Z1Bx3!-!dQn!6Jw9N#2Rk%<cD)}bb~6-b60DZ-dUyO~6h)o{lxSP0ZKhRMa@dQ_PNMf$yC`INh1l!w5uLRo}#N@gk^M~Yk;HiBBPpc2O<_c1Go`MfKj=ROm=+N{?UIVpUT)YcI`9}R8R#9>cNh{GbEd|^00W9CUGx5X{kmu+~%58*rJ9IlE@IdOOxMb)&;No9?_>K+(NBl)Fa$ZcotRAwJ<XFxz-8}tVwHSVk%oD|%UMI1Ju9z<ugQCI+MoOckKrBt6-tQUULTu!tiI<1a=YBe!sRA=n4sW@(T&ilOADm*|)VQAhNp$R>*gf9?Ars`SNH3fS|I%2zLA1z*vm`rhyc$DB{QRomSgXt`o-U&y6;Z;DTJ+%D+qAYs@tTlrDvV8(9cS!=%xb61=C~Lk6Ji}<Q8AIG*)ZcB(C&WDleM0Ooi#{3P03*O1y}Oa2lEK1Fmr{mitydef62p?!&~HRdE%RYF$p@uWMpU+_*d5x<V>Zpx3qIt806fY}5TGeBxMj}P5B~n&|2?=B;O`Q9{BV=GL(-TpOL|E*`mnPT^gUtOx(VB8qc!^uM)_3Gl;5)gVv{X<dorR;6d&5mJY4-EgfijK@bFPZdfH#JXVnzG!G<}?Q(p3EjO~_HQ9p$N*Pz(bawD8>BrGD?)JTSy^#YZyC`2v9?X^&sq8<2P&tnmC$ObqZw~;U|+lms+ZW4|~b+$K$Lp?Wzm`xupLi}aO**p*NGpvC~l;M}5p=*=jW*~GZd*<@`GDyb-1l<ID_E(ECj+kd2yyW)bz1eu#QmnL#X+F*YPXnJGZ8UAibPAXp>OZu<(IDHeXk%{zP;^LK_m^HMcVYz^sZXrFqW^wkOBgh7SeCGxu_OxaHb@i_$ot3=O+5Pou*DhZ74Qabt-&>@`F62@rZUcCA9I#`IZ+1T*iw~T-m3tbE@0`6)b4ySZ!JyTtfjYmgYb)1!Y7K#i81p&HDnHB(W*muYKx-xv8{Vn7o=|jU5I@!EhG&j-w@r9hfze!BjitF;?r~c>{sm6*n60D(3i#na3;Tf{wpy;65WaKOeU-(ro1{fX5jnLK(TlC5KQZo^|a7FS*e+p87o^hXRM&`8iRpws`^~!WMxWr`pNOL<r){vm*94@n;PeZF;x_86p>9!7uGRm`L2+axYMYjr+9NuP29QEi(8~C0vU@#NGfasJ~$2*V%Q}cu<5ybT3&8&nSV!LK#5>)ExMUUqiHc2jbfuF`cqIppelOc!{cL~u$93;0f%(6s0U$+j#ZF}t4E|9Y_b*Tb{y?F!l=Q~_2WnNyG+V2)#$U{$q2pGBk8T~q9fIssQb_<HuVQUWu)kj-eE%QFjNqO)na>`Pk|!3`EX~AMGkWTPmFKZ*&s*7NmhIun+Iq`b>4jG9BnL>C!!w|K_t72BAr$dI+Dpp(G{QLE_(0DB@x9jY}sPucntu?6t4u#Uj?#|76LD%XQhjMgXOIv?UIlKg^Wr=JnKgSjBM5lB&5C?PCsfD{(I3kz6+U({fM`B9T{f5DOtX|QzDmUIfx^`F%%&)gjj&P(B+4gpr~dLZhxDKv!n48@MJ{`$xt^E;$2_T--Lc)ml=A1FehXl-vYxd;sb#pPGP@Y4@i7qodYyFVVsDTKBGU#J26=LX3~ts$8m5-Nm}O3L`}#FrY~i)Q)KMp0N~L=0RUde$GeW<JJ9nM%E#(UmlKI~msiugjQB@2;ArpcCP(@GN`y$LDiq_v6P^|Z2C<-UkH|@5zyM>tRu!hxN~=kp4=5O1vQz=AgjE^MR9^;UZbkI&R3G@A`~@H2^MH(KlKtm1Rk&|u5;Dgt<Iv0%FCkgJiz^IIeP8rX9uMsSk;s|bFX)p5h>kC`M+p59^JC?cKqUb?#z@;^p0hfqBjQLAbRxYLaA%AT`ewC;1zJt!*)r{SI=GlZsR5qg3c8`Rgcx7f#k_&$_a1*YzNp1?LA{eplXav%eebEID77Le9sU(}^}p%mK^hBGi2h2=|1H+FO8)XU{YI|73q{gf_I~sO(il}TMmG_ov4&(OMgx^V`jjX^BIQhEJEZt6*W6I)m4v=2^(jJVe12jY_>rPhgB=H<n*(tfcJ4Zzvve|NyQRu52=aq66Bi;}SXl4yT{j5cAa-x?a7YGI2PO-i2f<TJB>By^>w<FsRRIQZQ7ono;?nj^8hnI?y&-6CfXHuf=5@#u^o&zB;^7wz-g*Nt=xZQyIl_0SE@heuWS}h{Am?M_CB}KFNnX`k42vT#zMWxCgpsAqU{Wnn9uWB@o~!Nd5HBmw%7`*MMD$-@Kn{fmsN>;OOdPIn*dys<dnJq!Xw*SJgwD^wSajN)A2dlwD3PaRC7GG1B3lN^GXhk1M0V!U=uQP->9|k?N7j17QiTsP{NwE==LmpXbv~VDIIkia7D~Y(QdX!6>{~{_I;n^#y-TeT{lko}0<?lS!!R>Ub0NM+)-EI!Er^OWtNq~gB0;8NY`=0L``qP5DY3*&!@TiTEOvJynchvyeg#C396@?PH8oI1QvPt|50)=feP$pn)rH4J)fT_~5m58(6fN1mn(zwU#{0!ki2fJ}C=63RI#~`1qY$}(oh2fx$G_Te3+0MZaTgjjF^Me1-10elyPEkO_QY{GaCSKR4h!Zu&_wr31a<uEzz)abZ!KWQEhHgy{<&j8e#tnHf3_HqpBex0D~<hVi}L8VB|DLpT03io*R|aWL&lEmIGFx_BSU`Wks(HU9g;%)yAPLc-F)aX9@ym6)q6J~cBAjzgB-9QiFk-#ZYOFBK2bQ_V?&YwExu5e{riy?5u4Su&qjz+(qe9lKE4zWLb{X{8;S;6E}{zhYA71UK^Q~q%if+)#=>mEvq#%CD3_V};Y3WT>}}6mrPr*|(-t8lDK;h&q`|jcs!51Fkm^VkD6AeCjR}jDvWuEH<x>|KU68+o93F)22(S7<p#pZMIVwKd86lt#1@DRrP^In{4e()u0kCg61fZk*%atwTEAPK1uCQrgg4EbH`H>>Yaff8!N|Z?}VFOme)~ZCBsG6z88H5nQsHH<V$1D_hwrRJ)E&Z`~r2m5=6ZrVyz^8crI^q$yu_K%oM?-&L0?#YS7cFQWmxi#QS}`XcUxG5J3XgxY1RGXO>U#>6W}&jBkTh|!>f7Rua2@hi2b5>t?$#a`y|%AfY|${gCdO+ziEAXJ#kHo3-h)pY%~A?-0&AHIMiyo*bF&#OplkiYF#?90(dMbR|MiiDCg!^yz3Un89FG~QD)Q{EE@XVBgSz^QWf=Dm%_wTS)vzI5%rb<@T=NZYSxfo>M{rQFbWH%3=|%}1zBEnkF1y%H;M6X<aM~tqD7O5bzCIk3GO67O=*gKxem{|(H=T~Kkw~3QbIiHos2QnW$IXL^%7GnKTTK5lmH8Lk@4~@N>X7Bw{)a_DgvZDE3UAyoJ^jbKUHufEaByk5ItR*gUf=<+O$=42VYtG>0t0X)D07P(74oYx*0x`snlcQz#vMzT%*C06hGanA$FR7f1B}I$*u&-ZOb(BHxrJr8JiE#3=&@P;M1@dM&cpUuE72u`yEB6r6$C+X;VSCFR@-g&vgsn0HQ_IaMT2lt&yGJ2-L7iSbZ2t4*qt}SW&#8I=Yc66j64zq#CXR14-bsX0LS8zsL>kqsf^~#XQT0EHC<%g_4bQkTCk2W&1<?OEnQ8aJ}Z9}JAsd{^7_$ruQ}l4cJq!4il3K@VhsGC%_%m|()C;Uqg1c!e3>1PB>`|882^Ix??wb2GyZ4j!=G%e0y`Yuw9Lr|iPs|jE{L9;etjMz37~s2i3Oka6}S5V3Ya1N>(f7WJDsoi2c{w0EYjc-M2lrwiU|GS4b|q<QVj8pOi}aueEKB#y{Px38w3}>$22%9tN)W>H|$^xOBJMx)n*w)<Q>Q-AaGxSPV-qv_X#dCyx1z69#@+gCNvNqPf<<y?bl)4?MT#e_T3gUMj*nh8rLTQ{pq38J&1mfLh=)s!2A%$Q119R00nJTbDF6LsJ~efH+)0^dj!j=*PeeBfNfT}xIr(kw?VWns=UsxGYim1dm%|c`AUOYWtS;}N;v5Q%z`aL{ms)u^CtsXk>77oRM=g_f<kFK9cy%4YHG45p^~{5P7hc%5e|1Ok{_(hpOa!OeqJQAMZS*GSVbVF^dU-<-%s<)ysn<aiTgtCgmft!6;INH|6D`}F9t=2Zx#a<u>Re8^x`|?cC!c2<)8P@xTj3E@an~XK6^eoKcj7?E5w?p3@=WP|DW{u$I(zcJU;&2X!!9@7g0R?33DbvVc2X_lzk+sYVQ_r>f$O}k-x1qO$FckWo6^g;Ot}+w0+=JQ_Px!fw&*bxGfAX%`y^7Ovtx(kq;Yp12K<xb@JwIUYIB+Ul|vN(E%)*a9y&fMVOx}b`!!ceI{L<mIbu=%}N;%L9amT9+_r=C*M}K4sRsASavVVVzZ7O8>W6F&9aMMTXIzhv`0e9!1H4?K!mu?L_x2BW{pc<R<yn5ngAm+sfvVz7hV|_VAv6Gqp*O+n5rUF-Hyp7opYbLq+x-Smjj8$ABq8T0n>d?z;p4oC<8X=Oagje!iK_jia(h>Lw$~ALq59My%lt8BaK63XQtxx<&V5OTU1i3pl=#T_BUeFf5q~c$N|D=y4g$w@^){{W0-v-;sn~MGzNNs$DKo_2p}jUVtM>jhC2L6Lx;By;@&Q(L837lxo9=;AOeZ{&KP3D4)4)-sk!IP?ti6P1E#oHO%0NMZoOj7_$)7n@n#dc=T%`%xFVO3=Y!5CBtHHM?++80{gT&+xlEXXE{rQCfMVLdf7m5s9<1Nvt}!1J|CM7uUlIUWfJNiV$W$hBhzUGcS{4+a>KtVl#v<fY{n8S+^y_u8NI^r}s*GYFLWXoz?-4v51<`=K7Dpfs!jF%{FBa(F#c!U*PFgg8p=Ma=eX9jv&IM#$ky)(m8ge)vuns=8`;lNSDq)hgK4<~$**DM6Jkry@MXz5zj9*s|qwdFlh+lVKS0BH=fam!2@OAeO@as3ByB0D0ezZu(uskA@yf*)O0PSGvcT9zzFOV}HJqV~)1X@9S1Um^V4ZihRE@jdv2tiozfZPLUpQ^l$F8(bZe*8KXXKzGVJ1Y;rQz?)<+k`06#M(2FG&(!_9XkVQ4WUT+DT=B~vnWNUk!_e%Ce!WmfPx#>m}Cv@0|8}xzYap(PFc}D3?frj^1avSUFu$T4HyjfhBUD){rATJ<DjEx8+;sWWBAXH_@A3t%P^FZ2+AOi_GPOIbCBBv-f<`rkm7qw?u7AUQ4^<E^oKq+{`%cRm}K$880Xe+LYe-^y7<**(-u{&OK}b2N&&OC^Ey~AYh|Gl!@!+Gp81=nO{Qs0izuHCa3v-tUm1wMiM<}VV9WI(lGO}CW*<Nd-PeJBRIEMxXb{Tmu6@&6HDVXUs1jo)Ps@B{Ty$!-h<ptgm@ftO4rn`oA(QMFuCs<rMquNP;Wld&DUBk(6xkKY<pcR|2GWN!Ac?hQ5I(>rW@9Ni@^`1_rwxwGbO`?q_4L<K1j{CdKNq0ag18^Op2AQ3Yrlpy249jt#Q60!EU!*18~N(RcYpJ-eKZhA_%YN^Sglt;U&rwuko8M2&rZL8`OQ;5C}E9I;EZ}-pFQ{1L34$#{Q23-7tj8D)=Cy(k`PrBfo$}eut%JewhuO0{`%LwL`iOL3~HFPK$1Rv_RV+uK~Up15YM(`&5q~?Q;qonkJ?#T{eU0*KnzP8hkVkW@ilQOlE2MUh5c~ix=FoMjiDE8{RbW7?g1mG18@z=oloKhR539Qf{2r4H#8c~gJ9j<?1p3x?qS`90k=T%4elDSxf@!u19!oD!{$R{F4lV4?7}&pj(}t0MMwA-=O+Gzw`1{kEZ&aw&RRur6ECp}!^8oJQf$O<V;8XgHf~Z~u)<x)qxF@%mh=D{lXyb-2^rDpD?QLxdJ=K#p3dNx5!*XO`uymIqjhiSgr}_SoIt%9Hpzj!I!rW%bWBd-78}SJZ92-82u|i1;b9TlUl8d>+v~}pW!By)j~1~0)Nd`OkGfJck`r!}gZ7cH43`Cyg!1i}rb#L|pg$JJG8AF_)<4*ADO46QE3oc9yJZ8~gl3E>Ecj=`#1%~(Rlz9PrBF8jY`n6q_ycOl_*|@A@D9u0n6af|xGpAq;B}%6t2j97_UC+R`}w(6!lit^tj!9z@_YEQo?@KZG0zM#%OfD!S2BS`N7re2lwfEKT6ChLVtte>5}2E0!S8lD&$4tzIcX}KN^kJk-t<iXnhTa7pCX+D<!j$6^tvG2aj{v!_|e%fngkt6eYM!eUyw#q&_Te3hK&GC>{Nz+ahA@s8*E13BSH3OAQz?IrHd=H@o)%v->{KdrZBdUiqywcwr^RP=+y-lXg4cuM#W^ZDJzi;#A&palgY*DaJwOXMc56g+ijW5Jq#TU9{w^tRmScFO}MB&figW&0xt%Iq1QKRoKY?eab6%o28Dx$kdL3>WQ+0YE}ppn2;tzZ#@d3XFY-EZ$#P=RrS7@kd)D`BtY4orhw{Y815U_uaRgWQn#FtG;xH=c6@>y&QG*=}xI$x)2r*sLvTWLeK!6Mi$NP<)*5M3;1nS!b0Uc5gcVpJug;|d=JNclP^(1B|?U+3P&ViOvBtNo;>x|;zfDNPly;AGs#5a7q)(+#xRgK|eJBaFu0{xMgA`LjrqK(T5Bq^M=BnDfrOSz()lNyMo@BU&R)oli#TIz92J#R}U9Ba|T_O#fJ_}tA0W?Y>Xd$!Z4!LwQlXoeL_1L<Zon!s+uhdJ<`CaY63ka*{#GDE(EXp6h!g<*nkeHerzmC%)LhNqKjxQ}hsK7>r6=F12Pq=;u(Y>$EJZ#Nk+<*ta=p(a>p3yQ^b#7q&dm1V}una3Y-HX+<WCuLFLneun@0-9ohfSuO`UNpn|tlAO-%-)D+(qEo_dnVAK=8aqL1QN}uBtIy@5s7tKM0MPB!n9wqV6aNr-G=eT865=J@O~Q@@y^OQ@_AhDZkr&SlOv9U)dCf_cv7&l=)n?Cy`h~siD;of*|RCHcq(CTf8HJSwD}6d<9MqhX$A!8%>*FQ^)>2>=wP$vS@h*M|9bY-t8e~%rp8qu!Qg|47-5Ao5vI#JL*J?~8wnnnSka~%)b9#$VXn+eifNx#Sy{#1;G8<f_an;T2T0I^`1lDu^f*g$k!XIXCe!R42y)|hbhsWfT3WLPRY!Z`qz%qI-Z_<0A#g!6p2G>kLGW&Rk@D;q0JxK3<E*X#GTs41oA;Gss=+p)0;r3z_?WsMji}g0-#;2qkG;&>#=)dko39gTOl)yXPFJKSz3R~`&;1IziJaH9IZbVvHn)SO>LIfV-&gf`QBLz!idQoM;Nxjta<E~#h*6h@wY*}zfEcBGgO_;D7THaXt3lt<B@@;HFEezG*#;MuIA@my5t;+=l(4N-bc%KQ7GswUy(I3kN}(3^lDioRJY<6j<%tChE7~r!XIQ>&a#!_5u~&BRB3S=25GSc+nG-9Lh(6-H7GS+oL}Q~dlc@;@l6JP7W1_0E7;?!@3v{*9Qz^gO+mTSlQfhGM%aRbop{XsJP}0P>Nmv)QDfzhIdm20~lh`xXBjA{1<(XnNKIO$n;K|s-r@i>Jq2lo0(pnJ3)s1B0@c!xZuVqDjSsABgUS{PbZY9<PiAXn2FG0<w8<Y786E*1#wvE*>bXV3a*cE0mX&<TWPTk(!hrHvS51=LrpM;FY_SQM>`B(^ryDsqVwEMFW8HEe-z=mDUA|Uhli5-os^G<a;otHq<ug_k7^T+2Xq_E|JHoszuc><=zgp<%<!XiLW+-JJp29Ky%l~L?+hY;rr>d>5qpXi!6VL!oSM-+{FS(LB`FT26Z4F>ye`<>2lz;VQMB{5z->52RmIQv71gGk0O$6bK-6mt=*wxU21AhV-vr*y-CxQY&VEZSjE?7*p%QxNkSvvX-X5Db@LW;q_G7?D6HppZ7)Go}Y&Kq^Iyaj@6vBA*iPt&0v_e^^3|NhSlOkC^*XZrG{v!BY+e=>Bg%`LrhuU2-%&KlxoJQ1@q->rI6{eI;)(=SydE7F+P7z?cJU6&MxOOQ(0p+`u=D%OG6}?)XBH6)+5+9b;re6+Q~j#ZwT~#fJ7FGk6#|13;ofw;&v$JO{&6rbJn2Wkm*2Sgc4sF?bk6hSIy7mZAqR4u}(ULbi@nd6$;c;33Ai0`U-t!UtyN<O(Tq8id%zP|k`Cw}r9kFkXCun{Fb+)%@aB5V2@!h?7#7jH&tbCI^DS%*hrr3M0pJ0UI>^K0EvN+tV)sxr6eMKnXl5Pz$1xB>E2TsV9MRE&+*qw?mvsEbrkk5wU`CnNN}P1@mLX7NA5xB$zXEF<X$2ek9T;Y*rMjUR&c2<xsT6bLz}GaDT$V0R|}ygO+Kq9=(#>hRuWOkW!0vupTuI^Qtt)eRX$TB4UK;0=vX_Z{7Q9Py6nt+j}|Pfj86nuBChLJLv@F%t*tZ7hPDlMHkk)q6=%v!CF*Vgi5xsbfA`Pnl3~UQeUq7Ew&C_i8$6Z$PYL;3am`7sI!X7BC4h=V$FkVIm{9Z*XhA;FRn@cau5IEC%eCSRlrQmVHvRdVU3w^Q<PZX?^sJJ_WQoERd94ZhNo3p!Z^akee~!EoqR`+EWskxvAqlwhF3kxIW=|)jdh{1DwKP*Xi^~kc{OAvV?<6!IU~fd(b&n*Xm?*@1Y%E%SS0iq%fu+4&-2^ScQ0N%lgHh|^;=*fo9lP!cml(9InRH%S}a#Z=*(BPLycDXBwK9hFbN7&*F`=ZM6n(|`p_2{^Jd103KA2Mp{Cjtu#yML)OhlF9&T$o60JzZALcZfqGH%j@VD+vLQ|fcMTNKzl&1i28rX1vZzn-@l`|OS5hCo>bZJ<Z)*K#rvF0?U<c@4m5l2g|6oM!74c|zU-Y;sXat%<3^93{xkcW-J{Jv?)`cRfAZ3W^Canxg$KS^-H(X{+eqO57L@@|NQ2=7EPjz;+^uScT@w{T8xfnq3KX)d0Glx1d|gR)(f5<~ss=rH;@k{LWA2{CqS_pI8zw%R>^?Gu>>q;2nR$I*kyVX!<HJFuicI#BV>_UCjmrz7!qdbT`}LR~&ZRYvn?wrYqljj0XDNGW0f;!ChIl_QljGtdqUWs8%8*}y34l7pIq6(v>ES3|3+d`5r7EI?Ftsxl^Iz5qm~AeoN0x`czuXf;w@d&~>qUr>+8C(8^p!Kt3MYKGA4uwo$PRm3{Xp%MRR2PxXIj&b4-a1;yjX9f}mNN8ySAU>AWO#G=>f|Gn|^R)@*E7vo~Yx~ikDd@n8iZJJ<{gt8`Fu1{Nuvk;36*mM;M4iE3BRq@)yBcmmk<mMvaN4&?*IFx-UyWNqeoY}#PM&J2wl;WzK_{r$6m?~bYf>Swek}UZ6TZDj18qfx!hmd4Mu`)*<U}i}_#=ae;u@2J83sN1yCR_2o#E&xtVvJ)ngS=gW@FP;AQ_(i?sJOic11Y{Ew=g`0HbV$q3o*S+{u!&azz3^YJ$d1QJQX169XtPpu#p>E-A(W<pihEIbAT%*I?kWAbCVcKn~ACeGEweIq5rdY_cf@Mrv%yS7IY62iv|)0E1kt%4K`yg;QBw($+jkB~fxS{aF@TzY|%XPV%eEv+#C8$>FW^t=^MMJKfz4OFFua$O%0l9lC+^4#)SwICHQGCdALC4w9&*UDGu?9tF^tm6l)ItPC{QV__Vh@_^IBqg>hYa2evzgw4TFUexpy@?xeLpujQF0AtTgi`3Ud_A1_+yK*npb=pchn(nq(TRAK3y@~>C5q)=m7H>buzANp9YU34FypjB%w_g!KTV>f)T=1ZY0qV_P(!~`PJHit@ldP)CEkQ?<8}0;X|FY5{$nEkGB_8PN1iDh|j<5>f=x~i0>0?ecEq<|u4pl(X%bvbC|I6w5*9u59nU}??SQMA&RgMFZoD~!|PO@(g<gK~`pn8|C!#hrGkaDsCJk-Uh24bK+9g||O+<aRh@Wr-sK&k`;j8S!yIoW7A^&;%pkK`k4$a!@Lq>v`<Nyr9Xvazp$gM%u(YU$LRv?;2m?mkG^dWu;K<s*H++lvBGMwwWX;0@M$6MX;t^y`29{^hH)uTi&NP-=-ox&!m$-5i$9HQ#&?<V(=ja(J=W9<R%6l1-&xxaXg;Vx#4Bl~QN{MzB=U9E4Nm`1l}DMTrjCV4O`zBuCc*nO4Z2JSW?tp?&Q5M-C9a1fk4k3qBJMvOZnnz<r~saR@A$`0O13uw-zi+Y9v4Ib|#<OpWXyr%zv<okL?V1DqwX*v1@wil*_&JY8L8Q0kqI=%k(&Yw5SZIY%-8b}7eblQsI4r|4J?@KPfIq@vL@ZjD1)Rl@lYoS(h?{@JSl*<?v>ld2$;IlvX2CNx~+!PWuoVxjRG63ZWVft(Hg(p|u|ndzqFl#J-4!Ke_8%s9Q0?uZO;>fr8C*U%f362n4J$0<+{9W;o^UtgR9<I-y@OG{|E!~{Q;>FA=&OY?LZh)`Z8;dleABFE6E%gY7!%g8dfS|O%1WV1zjDS~b>f(+kFWXNg2&JE}{T}=?2zEWUb{pl=t_06|uF!+CZ@m=tj)0e@^v$N-kU^duiGDI<%2`8jApt!MkmoqzpXQw!Ipgen{a0a2GR;*@uiME$_Q2bK5a*gpWrzfMwk3apbRA)a=BqRO&RPj;rk*o@WDpCj6v9gjmw+0vi>53*QkY5KYW3-8LUDdjw<}uV^*Hue)=y&_{I>w8(sz4>fZ<YWiaOH2aMcdP5dc(e#KS*jwXNS9uH9aGms-!M9zq`i_8i;yy!JnfK%G2ySRh18@uIwh8xl#5NUi!Kq5>yXh)oN?)YpNJ~Y+sXT=NJj<9X3k)gi(e{0;x*QLPFV2p;XaIIAV>HC4vzTR2l2?Rw*mmQ$^LeaOdhUcqqO$B5Z6i@WTkcl;YDeH{lzvv57)n*(?oP_z2NX0uEF)d`$^P85Aql*!hvva((%L#oinXmbNywo3V5m+gfE9_gr(x#59F4vf7~QI?J?UHwktbimiZb2GC~cqAbxIO3Ve59ai$hwqiS4w1)ys4XLRmnHi&XdTDJfb~cRrkVvG>#g2?>N}MZRl>DNp#QTWl5R71iiIZwrQf~+A*@umOp=M<0;f;sWxt-RkI|PjLDN^J1d_1fvkJ8IoQc=8f)l^~?9M*+TG^v<t*vE6kvVJv3$vk-R{47uc9|`1WNyzIBCvWB8^EV9V4eGFgi0v`tl5InCMzLp^-=KKNERN(j+F}BL1Or+b!mE80&QynimE%3>um18Pc=_t|%V!|%{ptMd^y`<w(dkjZ7b#VkVoP?OqhOD|R3CLNuv*b2W=Sx+Mn8%fKLU~;%EBZ(l1>H)v$VbC$R?>CWXmpw;BePiHK7|0P@kZXArc#FA~D6lEMbf=x(B##uE&>D2bN7)VC5PZF9f5Iz1<*S7Sv%sCSm=U^^oY~QO|T<%rJWhi1s3eMr$lmxnP~Np>Tfn{rUOX^H&|O9_i?hQmSq@4PfAn8ah-9;D6I>k&h|EDD)NSLsV-s0;~eEo*6<`DhPo4ewmMXUP4<1hCA|^i~NQHuZVPIb_p{I_BXUi8bWeLcC=JT_M~=boeg`%cTE?Ynr@|B6g5v02CL_KHYt`oj&$0Tbd{}aoZN&o11a2Y!WnY-<M9(}p<~&nUp)WnEJ*pl1|FD;aQf9nE%m)MrL~}l1ROTXpjwf})p6DJcNlmEtGLcFy%0@Y*0M2Ssmj)a9ru}=IP3MPymtJ{gzOubUK-XUUM)>0T4WpzLRn`9J7eRNcum)+2Fom^V+BN*FJ-JAn|xt7ncQeFk1&s{R^p)`Em2%4-K^WB2Iz<|w$o|XLJ`D{vfLUPX2?y4!Bw^mB48JffGfnL69?O@R&G?BLx9F3XtYHKyA4mnzQJC@FXd0DqfJIQXGS2iiY`OF6A<t)xoWSEb#zISn6_g^cE-~1aQn`#>C!i1!;L_O?Ap4Oh`5p`Zp??D{gOhWdyTg;Dr>J8E)*HWhh%-P(*?hhN@0IhXgQ4|prOZgqRInl$+IDT50K_UDLQoz1W5@NpIC~;Cn=ucGYdJH@GIei5*eVa*M6BniO|?Lss0Q<q$5tD_Wpi2)hRy+?Oh90FFb?zz$l4J)!0~YeLp>a@vYuOUi{^`wTXP;fRbD?W19%Ym}-f$0h}}oGKL|s9azzv?rB{q6BS8a6!|NU#9`)hJlpaJ^f|gkt83r8f%j^Oo565KMYhM05=upSzVKQ@8C7J=qU*rk&$r1<%eMEqHVwC<+&g*p58GXgvY@$mhQA7@;tp?OGp(h>B))S!jkp)w)7{u~G-@F4)tQ#duT0;gI?yy|^i6z-?*yjJ68yf=cV|Cw;$Q8pTX*rjouE4)yq_mj1N>m_&=wq><$@P&FxK8u)>;u|>7B!R=o$qXe<v@xetLfP@=wI5j!|3|L6MQ<(Itk5rzOTi=|j5Cgj`*ZptuN5z9Ko`DhaNQctsU^%#0biJ;haFfEI6E_Dytv=m<55<|c%fN~!v4<Kvt;ghn%l*@b!`Dh)}Q=TJut({)ahprfsjLR#yKecUlSs!NP%``&GY4COYDR!p_yhjPmoZ>gIH0OCuF)b<;ST~xd)=hY!VwAG<+ixm4ROVUC;`DhqTg}mLAnNIis-f1I`wVc`T2_!xB>r4E#Th=$N4<tC#jW~Q;2-_dHzFpn5B(A2Ugc*W6y3BF;M3`8^Bu#6$BlNM@T+XedKLF+FH_uO>iN-A>h9%X@yIyVSnwAvfbKwk_dsdegk1VQ&XGk|bT{kuqEdHL`A_Z9D61=^>Bc+9or?Rq$9#9~mvklPIB4R=Ln0Wfm8JtG+BSQEvCT2D;sySoY!48ONG=oTOy2-nR-BPwySlI-LY2Vb*f^DFV{gW=~m3Bs%JSX-?ZcE!FvqzTulKqCq&MtGMWsK}N?zDt;c+uBJXo@!|#fD+o0zC$D(U8$JEB~pq0*v=D1qswONOl_TLB}qMU2BQ?;-*<Xrbk9TQYZ-|W9ex@JcPvTpl{rGH<H_mp*Tjs_Y&li9#EvW!*_!?4}vOPQ7&n=UFf)MG}_QXPH{L=XSNF3{1N<4I!x&K0568*g(F2IzbItT&|2_qfXdx~%633`>+z$giEQF&H{Q7gMt(ZQaZ4JULt@g@aZw(|WnS@6U02+KIp&LzScDfPagb7P6vREs3n{n||5!8>tMYyTv}R^ZJ3RGDrzPq9=!$Mz3T0EmR7=iG3Xcd;;|)vo*#P7g1U`)h*>v$P-BxOy9zT)mR0?CksVHM5vvy7IoM}ng`wVkCE=;u03Oi?AtWDGG1J|7aO2BwiD_TBMD;5peWHF!S)dbHK15C6#8lcF2`bI3}Hvp+Bh{+2Og8_O5$do|GZ)F^a?u`LUq0jwNV?e7L)KpbK5DZAr?bz0=5mEbK3nDi#;#2uTPB#EuG^dxS!PhW1E0k>&_WJr7s3eWH;zNP~<T^gorE25%a~3(2xfMGc%TLh9Wl^r@`2<(U++5~#xuc+;BN~bY%LlO|<_C@rBxFjl6S~52*~U7phP5Juav!P*TIV6Vl3*6j1@^-5gpYeiLn>6IG`}W7zaX_$Xc&fe@jxHZMl}0@!E!VgAyw1&A)#$?Zi^(YiOrdg(xB$Er%`>G3}#@t(g~6VZ_&n_YBnrnJ0_s=KtN_N{#dLK|L*BoME<ETRu|5<Ls9Fl6^KqR(~``@Bw?a(Pc%6aiHW@?TQl0+Z#i1iNytZyfPBJ5YH6}%p<QWR%?g&Vvf`wxZInt(ImHAe$&p~=4}*QaLi5@JlM5l#Fz)PM(i{sSSGAgF+SC#5Uc~llRXs8d0*YY~pZdqLDaD-<53AYBoP3<fU`2Q;TIW9#VF{6NB9f*je0Xv2kdlf}Zwa2({TB;vfyA+cq*DycvVA@moVSGReR|ta^Q^isdoncBN?RwcM|$tI&wVQ--Mi08#S{uAtCwVmFrd=Gdi%|Zi9pq?(d!$FhfY*KHZOcrH%dF3qTPE(Lzg$>*_4PKXJ1Bw5h8`Bsr%UY!(inkZ^M_Ml{YR-AEEUWxbvJg5on2K<4`So*5R7>hCAgiw5gD{)VbvKb_q5R*ga6xQA@&em$_IY0%N@{Dq{;4tEW<{r{i54P~^gMx0pWrjTCh%n@h;_VzwqXX_;uPM{=!$?!q*Kcc?9I?Se*PMroF@$t5qDZ(3#bz49$aQ*o`lOB<svj-V>8nD<vGeHG+o;A+gB@521kw^piCq_m2Zz9OcT*wfiN-+^yA``FppeiT~<n5p#8hZ?s$)4`1E{4mx+ozus$7}C}2^g);nF$SHCV=|A^s90m>i2`pwuM4UG*je{3O*1Z>QSDX_bM{teMW$wGPoO8iX-42;$Sx=CvX`AOK*Kjv2k6!en7w<!EL&h&K4g^XPW)L;q+5Zkiq^eX>S#1zbWl|*0p|VA57JQsd4_@l>*!Vhk{F?16beHp+04N-6}o(8P7oQse{<u6#i%lLdcmyW91kG#>xeFPGVgj*H1RYhZ_{WT9lzIo9R}czbM?_Ebq{zT<Y8A{hSVrO_LLvDlt;TBHz6*UA}ff1BCd#PdNd4rCcNztVY$cHnoZP&Xl2}NC4H|}#!OwOmFk|p7ddqOU{Y)rQ#KxOPTeiBsz>CTVJbR47<-}!<lg%ft$BP_C9W&h!L2bZ?!tTf4lDv{AA)+aIfXdg^U**u-@|**X~sejt5+si$4n#IkSqUIG-!2E@OsK-Sc$Z2P5y7Ne`&*f^raZZdW#H<ZIXXFJ3kAeQw)%t0Gk2kg6S#PsA|B#P~i=qbokONTVh!>Sc<cf@6b+=O<j|w0f_>gBEhsrczlc#>y+YG9B@9|#g^8BW~kyMWycdeRT0&UAYm2yD{_reB<rliG~mI@LZ;I*Ej`*l7epM)$;X+6R;4Lt?wE7)(C!1%EK6ou%<2M4vPep$P|4WL&PU%c{2MPOotxMw11^Pq9*eL~A*~Q{7+PEcD%o|qLeFS%b(Ljn^Q<hA2S~BWh>Ys6=UAjl1niAN$zqBC)Mw}hIPc!yBR0B^OU&H3#T+pAZ1Ku+l9{u9ud~d>dbb};`nrCFZVzOnhQ(+btTG-vv<w+Z@72l9s?I_Ae|mm)W<bg*@L{yTNb^yNhgW7bUvWdH$c>o6P+V3s*@nlIS$%4N;pIVRZ{_{0cspkxQjgMS897f%i^wZ|S(t8xHC|Xb1*ry|F<V*>ivnXBNxY%BXV#7}aVxK*Ob08EO$H!SbbkN*o2TD=b^7X?7tif=Ca8zo5C=Xx`L+#MGU0YNI0Xh=;Sq*a_D<XWXa$WkoiY*6=b5;eF=$_&J$(Uum9eIy*w6n)V`xNsOconD04_*xfO>XJlZVrnu4-}Igwy3>Mr7;S1$;?S_Y`YpoIjuuAFbPLvwK~nG*|Z3-{Bb*#Fr*-OJ<bc3|of(yAytF70PFpw9zV){{y0)H5&g^G0*KWqoQFohpZemepc)aA@z^QzP3x*cFAq)vL6-)XNr=u;{e(DAk^<ewtJ#|@X);v`Q8H;myC@t@ODz}RYepF=M8{2LZuN?kAHz+;QK_Lc6_8T15E`t>F<pR_5M3NFx8Jq(_Ae1p=I%vtkDm{;fL1m9m?GUBmX%XA7nCaOx**rFUBcuS2d_+`Q%t-7oXr&F@5utpg48`+jd2#ywu@6b<P6QU{m625(WMiM9>1rI6}n9+@lg|1KlD12x*72+>n@q*)4jb$0xu2+yVE9K7BHJ{K@B!>G-#h!a!Oug&h>!6O|uC=JR%7DYJ<ZUM8p_ip!Qsd%|qnh%;po$KicMNIHP{9ON^S{?An!nn?k#Q9&y3D+N+g#(T`cq0*|v-2-<CgU=c4=KXex4|do<+fw_%vq$GZdp4eBSuGO-Ew=q2Y^m-&aY3Do?@%}LelPj^2jWBrhh;4O&+>8}D$q&qxbIMf!+$TXhr4>*h=KNUyy1aVvi;lUu6VGE+e@Pa-6w*L8-V32lZ4HPo$~(&5j#KEW$W{ydU%oENvjKEM23f$Ticzs_jAHJnhl;O$ee^ovd6W@AMZ;)!7!}Ad4s*NCrw)xE4tsXVQ-B0d51rgGq}Y!EW2^ni0N0T=o1`Pci69{Z$CUZgStPdIfd%*)lHPXye+-ChptpfV&N~*GfKod>He#;^KbF^hrC;w?`OxICI|Jj4FB!*%ZIP4hp&J0^mX@j_3`VAsQYpJdic8g2l(|HHxa+OlZfx<j(i!=^|jgN-H?2k9;BvqHsKo{Z$lL9(AshmChEBd&+Na22l8>Ui&@^*&HH{8*gL*D$YNg#?OsCdy;MAwqfZ8P)0AMi63o}Qg2a&wYNc<bkM?Gc#zP!k?Es^6VfK{K&6|16sGjsfaY8WM0H<xvIy*x(Cc+Y6W%x%?T7{bzTJ6-hl+R~|N&?*>6hBhl7v=R~;u+x-I+uR5D`&p+nCE;eHYR%{pC&m5n6c<9v->#P**#7P=_C8LCJO52!%}q-OisGp$yE>uX8_9F00>hC;1xHhI;B%OS}SsAvOipau@ZmKHF;H5bFRaR^JNi&bf0}Nc|Cn7&#`tptq$|LY;~7&d1yvuif>%$qWspr`(A8Ex!}hVR7D=M=z<c=1S?93=Cnt8ptyn__ycz6Hy8jB?_{}G*><o<m*Xic@jenK;w)?GUJ(j>GLVVUrG+nn6!KPq_^^p+?`NT!8JiVwl}0<{JCpOoEM+z<1$4nsk+%x4;%??2^R-zau?QPmwAOstYb9tjp|y0i4H+xo9v62w+fJjQ-M4C3ZSwUR_A7nQh9HD=(NIb{qon#8o2AR0rS+Wwn(6a8X@t8R8tB5{Xu~mss*G)?udncEe(urdp8HvBPJK*OCqlCpIw6;i$y!{<XMD|(Snv)XS{9OszJfyKoNLMGDtN_@!#jOi4@kqf7~squvu{w6OIR03Azd2R4qoQK6OV<D*}2{>TV0|@<-i*VUoJ7!biFCF<L~J0PS~&;*G0Wub6E1(f9VCU&c8onQKIU0Ix=HY8eIPt4Src#Vz#BS&S&YQW(N*19@JJ!Jh5__VIrGu5PVYy*^>Od(%^JV{$0LH5by9)asVEPfvR~4IOfZ7RszRg|1PN2-bMBs+BV7>-9VG9s%D!-hq2`RvG(PP3(WI_W|n6eR?SM0P%*3YEo>~R{rU9Vz8UFe`(yK7B)Tq%WU_ymrgcj9)#zJmz9Q0!8^xx5yh&NyCB*WBezTwhOzMV`(*9{Be$<tw*}9$+Yv=n$lw2q-7vWVySBy}l7|%Zt)C>A=!aszf;a)u=G9pCb$LMkW`~UoJVeGk%WY<+BUA&xf9mQ=|lBn+*byj8aA35$r(17sHWj;O;!L;*swi6S#li*<!G~LbSdv9IMh5^o~?^Gr_^0sxNDP=kp`@uHP7E|%jhpKhQEEgu}rqK{z1V(TG$MBh9tJ+zuXH`2lbp_laf!Q<dUE1OVzktpR^+kbw6shQ)ye+UJbj7|d&bq97gP;l7mSy+ea)n$2kj*QxKZ-l_=uq3Q^sYgqW&7=dlI&_R>V=*dtNa6ug0duFDjH0V?A-n+zssALeRCpi4hWV$jOu<Li9vN;z(*-P=2%Yit8q~*`erQ@6bV%D1eP{V4g96jGl%*WNW0y<qVS@~SPF)$Lz0QTw&mq&BxE9e(cW7QHSau}3wf;#a(PQ8WKl$32iSt7V{~XO=2{*^$Hn0dmj!&7KIhIT%Kmu;V*KdFzwW!>j*ooc=zIO+>Yh3VHDoPK?&5fEV~8ywl;0B+<EzMtH4CqA;rm^<XCPG@Eo0}>xjAf&5-lT^F4psO1e#n6-$-mx!W}S#!WoY7R>>$;wZ<mjF)A2@bSHxy7m=n+U$Y~rCvsstZk8K+%E_D_c(LVJ>?joagVqz>1I5!ic1jte2s!nYrh~8G`x2EDg6HIel;Vq^B45Ahh$9?MIDy5rgLyaE6iQNbBd`X?qW0)rmS4`%|3T8B78GqcM@v>(Lg6ai1s@&rePXRmHYkGdk?O(%qVVVRT<Rxz56m%V(U4GbUj{!J`#P?Bab3N^7nljVySXfAu?0>QGhhseM;gVf;9e@|HTg@o9T^6Eju3oxq2bakwL}1K5^pTs@x9b&3?u+%9m*7Glj9><3VyWTQST>VzZC;@u($;W!-?6P0KEAyQut_4tNr#W7h^p)Jq`4913le<GbfcmbeXL%y1-Zl32DNp@3?D2FEWaXbbBa3@tu7V2LHOfGt6EyD^7;P_`QHi3lMV_sJ;8rU3HYC#8rMElBJ2H%%n~A-v?7>lUUtC)szI@0lUlSXin8+L>P2Urdmt^IOdCQIcbm9Aae}I>vp?C#Rhbp#{PMd1R?`8TBwj;F<rczO=`fq%Bej7;jvv$Loip70%jE|J%w;;h;ov7iF(cc^b$3lN~g}Et<H(AqloZC^>b(WQkP$}mX|o$G&hU_^?byk_7M&{*$p^_p_U!sue@Ep<l7&}t%x}+hx$Dp(m;VeJR$Gsgy{H8dW(B}xyOW*43&XX-bkH@Ye5K*fgV)BtnMwFqQZ;ZDd9&0ZkPwt^2X4?97bed-F)qf7SVI=j;_-P+KS+Gy9+h8z`XE;O^(@q@>LdPZ;6J$9x$`Ghn|LUrD>qa-iq7DF}pk6<QoQpOtTP;cDL7ep^kfKQ7c(65|E1NmX5bJI>enFG<zz#Xrxg9RLoskLKL5XSols<sWvmTIw0l`m<SO{WK6y|1Ysr8Ur<qrX$0vvjT_y~Dh4i$?SYH9rTCUxF$aR9?I^{2n}w!Ty%A!Ja3p$^9T~3M*bW<^!vEiDMjq7%N1jM<cWY`)KU=kN=xrFP91X`U*z*)LmOpGA%X9&JZ3J^GzsBq}?Xq^O33IRNqU9D-A+h4N8~T|Yl5JQKW?4BBR&#cMQ3~efX38@JZwPAnrcyUEPuAs~cZyf@PYMFU#du?sp<q63HcC1~G1Z_Yy6+{|OlNH~#?$B~OB%CqcB_%O3myG#rc<`HKq(J^@*%I@?Kp|4jlt=P6g`Um?)A1B<xV4SwNu~_I5I)cJri2*NM!BG>hG0j`fyd?y)LBvB`%_UzYA!Mjk)dWS>F)0-al(^^j@}RSTO7xy#_`akQw<Zqg!*C<kPz-O>T`V$&%2haBI#hQPvUsR9D1Yx{G6m;5u`dTSQ@)ShH2zNn}3~yAQZ%Z>+UVPAVG;y+Q-ViNQ}N>55}Xed>tA)f{EeBMN>bM8U?q)j0x8&y@<2Hn^I}oAl~%^eHV~qc0O<n8vWhGe=D*<dFg&N#N@~$H;^=p8S$l6-G~`nv<Emd_tlCePKAu#U`ziDhRLrVby!GI{Bn2U}xYJEnV<dWQ9I>F$*WRIgY6iRdW$sk*zjMx=|-m4T;kaL{R%sG@g*4glttLBO630lDSE#i7~Xp2u{MjId@O!3f-a#lLmz`Hr2d3^0ARcCG6Q?dL|f~6p4^q9RQ!$06y7?hrF~hI*DC4pIUJ21T3FA5xF$m?N>hcfa-xJczjr`a%U|Hpo@C3gTiC|Gd3e0&}n3ion`Bm0ee8Xp}7{t8>Sl))Ih=y;L`?xPZa<pn2i+d3Svq~u}aT5dLoTk`Q1p+zU90R#37jDz~h}8l_(~`r{;~Mjpi=QKt;vMhFw@6z+}?Rg7!wA4VkOJws<j&rMFGx;(fcxHkoi28m60^uSY0{hX1h2-f|>?bRJ|Ys*S+3Qftctpyu(BV5sce%+(fqxi0g974{&aJm5gL(KzQE*SnSa$HMOIqXK?1cNl%uZI-UzcJaUKO*N0GOGyw(G%$MiEhqUllM=n<j8V*D1sz}*WBbLY;swlt98(RD(FCWdkm5l}$W{}~7$LvVJQxa*<)-Ek)6bX{lQpj<m&Riu<EJJ6uJdKq#s3H&Fo&Hw@v*?=F$N}^wm6R0<z|KX)Y46j7YJ`vJK_V+NzuNJeXG=m7W<6ei}{W{F)+faZ_RSD@HfPXTO$^HkuP&0uzH8ta%b}=Or=7H22|7j8z5kQ3Cx~wGyTKviZYfmG~~Vgw`tin=f31Xam%qv$8_8fSkze5<#vSL_EtNYrQul%RLr(SPqReNqNFi55_eLVW(hr0pA0ycKgfL}xmWuP8}4!N)<yh8!{aZ9g7dq{3~;Id23@yVmAw@XK%pARLx6*J9wrR<uB_X*;)f_)gN{~4;!u$qmJy8#a1mjUN07eua9fh?Ic`k9l<Q2*2CK00=e3am@2?y9HshvD?I3M+9>I7cPFhCaA(ptRb7U|dn_!$`S&djqenpqb`3a&}<U#aM(J{~?Bi#bay@0S-llqg~5-jLSr*jS?m>fn;JAHGXTB8;)YfoxO3oZJTKf#sS^t@o&1e|+`HZ4Mpxd*$r>w)bzPDslg)1;!jZYCG^#_%Qe1e<1trsMA$td2v|^wu04t1Vj;#`hSnrJ5UQxnm>+55UL}Qi?UpD6!|t5xv8AcJ5lL9L+w9L=^VhDx0NwIT~-KY>c8F7_T};(!m+#m8Y1CDiYTSRz_5sx>DYJ=@AyJEy`@Faj>2Vpqlb+!uQygTI~W>+(5A@C#D=bb8l{u#xg2s+aLT1;aX)3+0R_a8IpQl2=CX|z5Uge$WcRt&wX9jSr61bi>s!CnW@9}kgjqQ$L&ZG9hBKEm)^|&&J%`|kC4J22X-fR*>vrKX5Mw*KZ>>0hjy$8T-7|VEaU9Wx{o=WR?!-*mhtW+64-6JVNkeEtNz}c6BG`jm+bFBaPJ><)xq9*VE0=$aqRAU-Wd*jF`wdbu|bQoWZyqAXAUZB4dP){)Py~(xHg;~RGiGy2bDB7X^YAamAHP`XrlbMzi52Oe9~jrdc68xOsz3mQiYN29EO$Jz4zw0IYhhiYgm%C;tsh__`&@B$j^$!l+Kq|oTJ*GxrkJ1y<aN938Wh`-OxE&^;xKlmZTORaB|(#k{6WSS_7Gmm-Nl%#$}dX?MNw;&vv!a2Cw5AaIX*Q*3EpK)*H0Ng_{+b<K3(Up;~Ns6iX?=4iu2sDfKmGan4q*om0tGqKx|O7R(mu8u6zC?-()|dBwye_@vo{t$Cpp*wxLwHKb~yE66uyVs33c8m%@<pB};|urRQNY*vPg>4f4&+~^nSTR2j#i6fYDN7}-E6yJ66HUjlx*foY`7WNJU+as`Okrn{)(E;@dfwH5Cs*9sfj)q*tFt<B3KlRuARMr$0ZdFSkxj-^v8jo~!nMI!^l5@x2W9Vf6B9d>G_H{xNKfm>f_HuZnUWB)Qpv%wh0^<!|EEnA!^q?`$CLlRA?t<SuC6b}L{#Gr=yEwVIiPG2sLkISNQNCWu2rms?om#Q|HG07|mTRb*6G>FqNYy!XDIc^>-*1iHZ++fpZHAhXR80ObofLA{QF$K>hXS9gZAlE_^B+=bh=yCxN*JNjwOl2^EX$^tBo<n^&PrHCBRo(UVZ*VR*X1I__oLzpv!p=Hj&sDTxazwZNJJIc0#%ehc5E?J6WgZ>bb_|=c~VU2%FJMyUS&x3WnNWiptbQ<<>f^XREPEfC`Zdy<-tIkgtw+~+P7KT_}B)4Z!XXPE)W8}WDsU;K6p%-&vHIJ+(dHNY@#k|3r8R34+EH*Q4^!~<6E#sSA4}!)aLb0f{#DmtWn^r$PUmf!DGt~V4P!^Jb~^(>Jkr%jn7?%6iI+4Voku&#~*VwBjA8DDPf|Bks-o?K8I5-lAO(O=XYc_CU56>HxSiFhA6KN=!#e@?e{OUYO|1`IcEF-YsxzOm&(ZrKs+;Mp_JJsigS(y)DcRR_0yE05GWpFN7e~k4Cews%$I4oZG;JOX}gaiF;#Q$lfY?yfTFkRj+aP!BR0WzZF7{briGK2mKMYY7VTth;^b1xrLw1jB<Qeljm%ZH?aNVs=VneQVFdSF4J5Gj+`gl?MbAePZ9VVxUg`O$_egI|XDe(kqc%XhNJH5Wy*4JCeV>es3KkUZ95|Qld90WK9p(Y-_Ast#mQGQU=?Ak#k=DY;*22Zy<59A5s~$r)S@Z8@ny=W0q-q^ET))H;WJ$F6bbFs2a#p9YOoeTFfXCxZV|Ak8$9|59gNk|W@V<vxvB-;7hN-T8Yv-DN>I%R1L5!8m_Go`IO`ziQXOH2ZQN#n`w{{6>vKQzKf|JMHCilh&O3-F(70HRxsnL@$5-yHrc#bh3icA=iX}S9Ny6hzIIJLx0+BRGtsTyH8t+=)=<%6+BR{xJe*6Zi{&}h@%^<l84*>%WlXqrY8=8aFrlpnZjpjq0$c;GIFW@*VF%w^#z<(;rT=Z1eyI6K0=5VAJH-gh?qa}${+>_IecmfTBXVcVelPVMv(bYdrw%ug&P`Ae+}A+h1D)q+dv{mHD#@|wK~Tae|}U>Qm*2wt0sZJ9LX>;t5J!_Gniq@9h`L~k!s7_?BvAoy;9d=}mk#qavJh8A!n%N!-akq~o^%)>ngC=Cr$EswS@=_unRN0RZP!ai%dBe-!vX<o7_G%umtDH87$i-l+`sF$>TZxNmMiqE@5=)Gd}UQzl`aryv}+VALT6|HUY+BDVi*j*f-42Ax!rwKbxZ+$lRyN))@@K=(?)pzr=C9X?Ra+KZ7fw9(B*|yo|vqjJvcVqD#A=4W!hgs4vRoU^U-TxG%({x>DWnVV&1Fqa-PR-8Q!wNh{0W%T-sC=h_t$Az^9p7g1xe`6)7Y=_JeDYiSwTeX>d}35EdCey#B)O^dy5>u16Lj_j<&t;zV;Pt`Fo3way;Eh6FtA4mkogI>{e9fKsexF=6FuMqdk@KOCfT|U&gc)OQ`?o6VXx%{!+*>|((W1e{T381MHWfRWJQhszf7TtZ~'
_STAIR_REPLAY_PAYLOAD = 'c-oa%&2rl|5Wedv5cEPivJ$(eYNF2ckVB@PbSCxmP+6maNytJ?0W1L8aq6D?2z|dkNp}Gd1Zc^!b+AQn|M%M;=({)XI-}oR3;B-AJJLSbt&-nQD5ald&07wCq$QfS4SOJ4-n3jBvQe7YEhqe|<yx|a{A!udr&S|%*IbiI?OG*~k9D=Mv&rOgD-7AGx@$P8c_V;|S>8O5T5&_9vP1xjwz<?+E44WV&C-b!4cD{DCrhd=uWk(y*0^(4S;GJ9SR?EML25(ph20WH3~w1KBJj_EVNBNG%Dom=$eRhMZ1@h$WL79SBjgg4tIbAK0+e5HQ2R$$-*8~rF#%H1xQ#%|?zk2kf#yJ<CX-39UUT?<`OD8AKa&MK%!1X0rdQ^qSpIbSJ3IZhUWG63Pk&giP9Cp{$E))3zkmOEygDgq2@-0)@fNQk5WB)cK+5@qzz4sAX#6)bR*SYM{kgj3VBmr*SMIr0Mxax0^4=ZXZ^4e?_ycLUOa<d-$85C)4(GtkJvowT<SQes*aULO>u1RIAO$~~3B$>6tm*hit(7jQkav)unxI2;5aaEhu@-?=PzVBzqGvZ+b!~B0lEs416H0gkLi1OHq{L%Sf&%^Ps?!Dli=lAO7+z-8u1I{BN;ay3%zEO~&%plU!pF>6TpsgxCyW7%IXz>4F@a9X(u-cD+5!c5T+m!eu;cB5oaM^7=^Bp;085#@J7hk=0?uq8Z$M=^Qu(}ZRilh6EhwQaH^R{Jg$CPB%V2lvJ5<c3YZ{L{P50LeoqEg5`D>IF^p5GsIyny1khlmKAKc@BiP`W7i|4)ogOwk$TwqrkB?I%1#qdf56jZg~q<@|U6B2K;!23plZKlq_Gl1sJ0n9%Qn}wqWL4k6JkZorJ8iG=<C~I!mv$15;KGg6H7#{kz(%_4@*~XR!r`A<@K^HU{i{m45AhO{lnBZCGFUWOo$R3M*2S%&PX?o&h_q`gRCD?Vt&05H{(lytqORBRFjiEQ=@a#F9nSgpBYt}S~dBFJ!ahkVgF(~oVQU<X(K>S(XPJ52bD^C&(H{G>?fOeJ_=+$&Mz-B-11B~yM?>#E9jOJrRrEE(_eYRSqT8qfx5E`FG1_0a0hQp-i`$_wpR7zH$Tzu<YyXCx{k`09UnpL;2aLyw-5T30t_9)AbqrR_1xi9g0WSjGPWZq%o^FzetkW?gGGaEc_ncW6|p{}u8hkB22tcB*4o1Q{C^7&{0A`=D)hXlAnGM)fPdhvz6bPWKf+$w{*lBqG6*Xuk(0|r%?q>Hc#oM#9N3?T+?U#)l^gK2+^JKq2RG(Yz__Q^;+21|&;bIql95jrDmiw4$Q7HfFuU8uN6-^Ekx#fF}_;{fA0&*rP#t0@T}*{k8pK@CytSk?JKRRQWpa~!i5cUym(SR2b*Qy2?P9ZDG=Kmptk%z<J}&@t3RU>`9=WTRLFrxTwzj~9`J*EYN1w!ru93&k@C2nAeb>#k#Y;kMh!TdD4)<4NG{hnpK6(_v@?J0ca+HysApt@HW(AKXqx(H$x-_lKbW_?ZKAeJqv~)EGLfp4k$LLqD2P_G>`2xIA9wmC~4XA2r~!4@n%-whd0!qO!#|xXVNZ(;*0H5+o#BS^*cjdX2FJ-ef9-)gc`T`&s*yBH;}=Il#OLA-jb!O?@S8?(0#ryXFvN4wi2qD<J)ewbMOTL<w*w-lIkHyVqz5UOds9XfZFquIXC5&B9vfs>j)rT(qDWVDMtWxE>A#L-U9YQz+DJ7(|FB@5M1o{7sz`qdHx|%}*G2GuS&XlD3tp3y~_1jEaXf{%%m1mRAAXUTH{Nc<6yMT3?ZCN&Ck$8hS4@CWudv5FTD6;k=jN+7nR!HS7^vI#1S$v7!53cu-_-_Ux-qeHd80F@L8{rOoT8wDVC!`WA&-$VeOxDjc(8EpFh`uQc}chVORFH8W7<ap;Z=AaS`$8dT^L*)k7wOWJHrZ<mX8mYI}L=Y)9A*l~+LgF#yq#`bjXMMj!9I&cLS6EV)YQEc*SaWXEmM0#um{q8+o#TjZKD1(-A7!5;Wu@;k|(s#i_j7R&v&kEc<S|y+?_f)L2Z5b?<pn|SecyY}}W1@WWYz)#88>Wi`-;H9;x(`XNJ|P89$5=~%Kgvm1voUCCIX|}qq7?_@5!%tE?s(`$9A`9(w=pj7gjRCrx|v1mro<K4D{e1|jJ-EACw5pfG7H>7c-RPX;=e@Zw<GrRXW1uy?f4&epy(t'
_stair_namespaces = None


def _load_stair_specialist():
    global _stair_namespaces
    if _stair_namespaces is None:
        import base64
        import zlib
        engine = {"__name__": "mathgraph_external_stair_engine"}
        replay = {"__name__": "mathgraph_external_stair_replay"}
        exec(zlib.decompress(base64.b85decode(
            _STAIR_ENGINE_PAYLOAD
        )).decode(), engine)
        exec(zlib.decompress(base64.b85decode(
            _STAIR_REPLAY_PAYLOAD
        )).decode(), replay)
        _stair_namespaces = engine, replay
    return _stair_namespaces


def external_paramodulation_candidate(problem, seconds):
    try:
        engine, replay = _load_stair_specialist()
        arguments = engine["argparse"].Namespace(
            max_clauses=8000,
            max_weight=36,
            max_term_size=30,
            pair_budget=300,
            timeout=min(2.0, seconds),
            translate=True,
            unordered=False,
            neg_bias=0,
            old_rules_first=False,
            tautology_prune=False,
            forward_subsumption=False,
        )
        result = engine["pm_solve_with_pruning_portfolio"](
            problem, arguments, deadline=time.time() + seconds
        )
        if (
            result.get("status") != "proved"
            or not result.get("plan_ok")
            or not replay["replay_plan"](result["spec"])
        ):
            return None
        return result["code"], result
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError,
        ValueError,
    ):
        return None


def finish_external_paramodulation_candidate(found):
    if found is None:
        return False
    code, result = found
    code_bytes = len(code.encode("utf-8"))
    print(
        "MATHGRAPH_METRICS " + json.dumps({
            "portfolio": "external-paramodulation",
            "strategy": result.get("strategy"),
            "lemmas": result.get("n_lemmas"),
            "steps": result.get("total_steps"),
            "certificate_bytes": code_bytes,
            "independent_replay": True,
        }, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("true", code).get("status") == "accepted"


STRUCTURED_MODEL_TEMPLATES = (
    (
        "crossed-square-2",
        4,
        tuple(
            2 * (left % 2) + right // 2
            for left in range(4)
            for right in range(4)
        ),
    ),
    (
        "crossed-square-3-perturbed",
        9,
        (
            0, 0, 0, 1, 1, 1, 2, 2, 2,
            3, 3, 3, 4, 4, 4, 5, 5, 5,
            6, 6, 7, 7, 7, 6, 8, 8, 8,
            0, 0, 0, 1, 1, 1, 2, 2, 2,
            3, 3, 3, 4, 4, 4, 5, 5, 5,
            6, 6, 7, 7, 7, 6, 8, 8, 8,
            0, 0, 0, 1, 1, 1, 5, 5, 5,
            3, 3, 3, 4, 4, 4, 2, 2, 2,
            6, 6, 7, 7, 7, 6, 8, 8, 8,
        ),
    ),
)


def large_structured_model_route(source):
    """Structural signature for the balanced three-variable residual family."""
    left, right, variables = source
    if len(variables) != 3:
        return False
    if left[0] == "var" and right[0] == "op":
        bare, compound = left, right
    elif right[0] == "var" and left[0] == "op":
        bare, compound = right, left
    else:
        return False
    counts = {variable: 0 for variable in variables}
    for subterm in walk_subterms(compound):
        if subterm[0] == "var" and subterm[1] in counts:
            counts[subterm[1]] += 1
    return (
        term_size(compound) == 7
        and term_depth(compound) == 2
        and sorted(counts.values()) == [1, 1, 2]
        and counts.get(bare[1]) == 2
    )


def structured_model_candidate(source, target):
    """Try a tiny equation-blind bank of reusable finite geometries."""
    for name, order, flat_table in STRUCTURED_MODEL_TEMPLATES + EXTERNAL_STAIR_MODEL_BANK:
        if order >= 7 and not large_structured_model_route(source):
            continue
        source_assignment_cap = 1000 if order >= 7 else 10000
        if order ** len(source[2]) > source_assignment_cap:
            continue
        serialized = serialize_flat_table(flat_table, order)
        table = [
            list(flat_table[row * order:(row + 1) * order])
            for row in range(order)
        ]
        if equation_holds(source, table) is not True:
            continue
        for witness in product(range(order), repeat=len(target[2])):
            assignment = dict(zip(target[2], witness))
            if eval_term(target[0], assignment, table) == eval_term(
                target[1], assignment, table
            ):
                continue
            if replay_countermodel(
                source,
                target,
                flat_table,
                order,
                witness,
                serialized,
            ):
                return name, order, flat_table, witness
            return None
    return None


def finish_structured_model_candidate(source, target, found):
    if found is None:
        return False
    name, order, table, witness = found
    code = emit_fin_certificate(table, order)
    code_bytes = len(code.encode("utf-8"))
    print(
        "MATHGRAPH_METRICS " + json.dumps({
            "portfolio": "structured-model-template",
            "template": name,
            "order": order,
            "certificate_bytes": code_bytes,
            "witness_cardinality": len(set(witness)),
        }, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("false", code).get("status") == "accepted"


class FiniteModelEngine:
    """Domain-parameterized finite magma CSP with independent replay."""

    UNASSIGNED = None

    def __init__(
        self,
        domain_size,
        source,
        target,
        deadline,
        maximum_states,
        maximum_models,
        maximum_nogoods=4096,
        options=None,
    ):
        if (
            not isinstance(domain_size, int)
            or domain_size < 1
            or domain_size > 6
        ):
            raise ValueError("unsupported finite domain")
        if (
            domain_size ** len(source[2]) > 4096
            or domain_size ** len(target[2]) > 4096
            or max(
                term_size(source[0]),
                term_size(source[1]),
                term_size(target[0]),
                term_size(target[1]),
            ) > 63
        ):
            raise ValueError("finite-model compilation limit exceeded")
        self.domain_size = domain_size
        self.source = source
        self.target = target
        self.deadline = deadline
        self.maximum_states = maximum_states
        self.maximum_models = maximum_models
        self.maximum_nogoods = maximum_nogoods
        self.options = dict(options or {})
        self.support_propagation = bool(
            self.options.get("support_propagation", False)
        )
        self.incremental_propagation = bool(
            self.options.get("incremental_propagation", False)
        )
        self.reversible_trail = bool(
            self.options.get("reversible_trail", False)
        )
        self.symmetry_enabled = self.options.get("symmetry_enabled", True)
        self.diverse_witnesses = bool(
            self.options.get("diverse_witnesses", False)
        )
        self.support_branching = bool(
            self.options.get("support_branching", False)
        )
        self.target_witness_limit = self.options.get(
            "target_witness_limit"
        )
        self.full_domain = (1 << domain_size) - 1
        self.source_compiled = compile_equation(source)
        self.target_compiled = compile_equation(target)
        self.source_assignments = ordered_assignments(
            self.source_compiled, domain_size
        )
        self.target_assignments = self.rank_target_assignments()
        if self.target_witness_limit is not None:
            self.target_assignments = self.target_assignments[
                : max(0, int(self.target_witness_limit))
            ]
        self.partial_states = 0
        self.complete_tables = 0
        self.source_assignments_evaluated = 0
        self.early_source_prunes = 0
        self.target_witnesses_tested = 0
        self.symmetry_duplicates = 0
        self.source_models = 0
        self.target_falsifying_models = 0
        self.exhaustion = None
        self.complete = False
        self.model_bank = []
        self.model_keys = set()
        self.propagation_rounds = 0
        self.domain_reductions = 0
        self.mrv_reductions = 0
        self.nogoods_learned = 0
        self.nogoods_reused = 0
        self.symmetry_branch_prunes = 0
        self.branch_choices = 0
        self.branch_values = 0
        self.maximum_depth = 0
        self.nogoods = []
        self.nogood_records = set()
        self.nogood_index = {}
        self.empty_nogoods = []
        self.literal_frequency = {}
        self.nogood_conflict_activity = [
            0 for _ in range(domain_size * domain_size)
        ]
        self.contradiction_activity = [
            0 for _ in range(domain_size * domain_size)
        ]
        self.trail = []
        self.changed_cells = set()
        self.constraint_evaluations = 0
        self.term_support_evaluations = 0
        self.support_cache_hits = 0
        self.forced_assignments = 0
        self.support_disjoint_contradictions = 0
        self.source_contradictions = 0
        self.target_contradictions = 0
        self.target_support_disjoint_guaranteed = 0
        self.nogoods_minimized = 0
        self.symmetry_permutations_tested = 0
        self.symmetry_seconds = 0.0
        self.propagation_seconds = 0.0
        self.activity_seconds = 0.0
        self.nogood_seconds = 0.0
        self.canonicalization_seconds = 0.0
        self.search_started = time.monotonic()
        self.first_source_model_seconds = None
        self.target_witnesses_fully_searched = 0
        self.nogood_causes = {
            "source": 0,
            "target": 0,
            "domain": 0,
            "support": 0,
            "symmetry": 0,
        }
        self.nogood_minimization_remaining = int(
            self.options.get("nogood_minimization_budget", 0)
        )
        self.static_cell_frequency = self.cell_frequency(
            self.source_compiled, self.source_assignments
        )
        self.target_cell_frequency = self.cell_frequency(
            self.target_compiled, self.target_assignments
        )
        self.constraint_graph = self.build_constraints()
        (
            self.source_constraint_cells,
            self.cell_source_constraints,
        ) = self.build_support_dependencies(
            self.source_compiled, self.source_assignments
        )

    def expired(self):
        return time.monotonic() >= self.deadline

    def cell_frequency(self, compiled, assignments):
        nodes = compiled[0]
        frequency = [0] * (self.domain_size * self.domain_size)
        for assignment in assignments:
            for node in nodes:
                if node[0] != "operation":
                    continue
                left, right = nodes[node[1]], nodes[node[2]]
                if left[0] == "variable" and right[0] == "variable":
                    frequency[
                        self.domain_size * assignment[left[1]]
                        + assignment[right[1]]
                    ] += 1
        return frequency

    def build_constraints(self):
        """Build the static cell-to-source/target assignment graph once."""
        graph = [
            {"source": set(), "target": set()}
            for _ in range(self.domain_size * self.domain_size)
        ]
        for label, compiled, assignments in (
            ("source", self.source_compiled, self.source_assignments),
            ("target", self.target_compiled, self.target_assignments),
        ):
            nodes = compiled[0]
            for assignment_id, assignment in enumerate(assignments):
                for node in nodes:
                    if node[0] != "operation":
                        continue
                    left, right = nodes[node[1]], nodes[node[2]]
                    if left[0] == "variable" and right[0] == "variable":
                        cell = (
                            self.domain_size * assignment[left[1]]
                            + assignment[right[1]]
                        )
                        graph[cell][label].add(assignment_id)
        return tuple(
            (
                tuple(sorted(item["source"])),
                tuple(sorted(item["target"])),
            )
            for item in graph
        )

    def build_support_dependencies(self, compiled, assignments):
        """Conservative assignment dependencies for incremental rescanning."""
        by_assignment = []
        by_cell = [
            set() for _ in range(self.domain_size * self.domain_size)
        ]
        for assignment_id, assignment in enumerate(assignments):
            supports = []
            dependencies = []
            for node in compiled[0]:
                if node[0] == "variable":
                    supports.append(1 << assignment[node[1]])
                    dependencies.append(set())
                    continue
                left_support = supports[node[1]]
                right_support = supports[node[2]]
                cells = set(dependencies[node[1]])
                cells.update(dependencies[node[2]])
                for left in range(self.domain_size):
                    if not left_support & (1 << left):
                        continue
                    for right in range(self.domain_size):
                        if right_support & (1 << right):
                            cells.add(self.domain_size * left + right)
                dependencies.append(cells)
                # Under the initially unconstrained table, every operation
                # output may be any domain value.
                supports.append(self.full_domain)
            cells = dependencies[compiled[1]] | dependencies[compiled[2]]
            frozen = tuple(sorted(cells))
            by_assignment.append(frozen)
            for cell in frozen:
                by_cell[cell].add(assignment_id)
        return tuple(by_assignment), tuple(
            tuple(sorted(indices)) for indices in by_cell
        )

    @staticmethod
    def assignment_shape(assignment):
        names = {}
        return tuple(
            names.setdefault(value, len(names)) for value in assignment
        )

    def rank_target_assignments(self):
        assignments = list(
            product(
                range(self.domain_size),
                repeat=len(self.target_compiled[3]),
            )
        )
        legacy_asymmetry = structural_distance(
            self.target[0], self.target[1]
        )

        def key(assignment):
            dependencies = set()
            supports = []
            direct_cells = []
            nodes = self.target_compiled[0]
            for node in nodes:
                if node[0] == "variable":
                    supports.append(1 << assignment[node[1]])
                    direct_cells.append(None)
                    continue
                left_support = supports[node[1]]
                right_support = supports[node[2]]
                cell = None
                if (
                    singleton_value(left_support) is not None
                    and singleton_value(right_support) is not None
                ):
                    cell = (
                        self.domain_size * singleton_value(left_support)
                        + singleton_value(right_support)
                    )
                    dependencies.add(cell)
                supports.append(self.full_domain)
                direct_cells.append(cell)
            left_id, right_id = self.target_compiled[1:3]
            left_support = supports[left_id]
            right_support = supports[right_id]
            support_asymmetry = (left_support ^ right_support).bit_count()
            direct_exposure = sum(cell is not None for cell in direct_cells)
            direct_root = (
                direct_cells[left_id] is not None
                or direct_cells[right_id] is not None
            )
            if not self.diverse_witnesses:
                return (
                    len(set(assignment)),
                    len(dependencies),
                    -legacy_asymmetry,
                    assignment,
                )
            return (
                len(set(assignment)),
                len(dependencies),
                -direct_exposure,
                -support_asymmetry,
                -int(direct_root),
                -(len(assignment) - len(set(assignment))),
                assignment,
            )

        assignments.sort(key=key)
        if self.diverse_witnesses:
            # With a blank table, assignments with the same equality pattern
            # are related by an element relabelling. Keep one deterministic
            # representative and interleave cardinalities so a small witness
            # budget does not collapse onto a single pattern size.
            representatives = {}
            for assignment in assignments:
                representatives.setdefault(
                    self.assignment_shape(assignment), assignment
                )
            buckets = {}
            for assignment in representatives.values():
                buckets.setdefault(len(set(assignment)), []).append(assignment)
            assignments = []
            offset = 0
            while any(offset < len(bucket) for bucket in buckets.values()):
                for cardinality in range(1, self.domain_size + 1):
                    bucket = buckets.get(cardinality, ())
                    if offset < len(bucket):
                        assignments.append(bucket[offset])
                offset += 1
        return tuple(assignments)

    def source_holds_complete(self, table):
        for assignment in self.source_assignments:
            self.source_assignments_evaluated += 1
            left, right = evaluate_compiled(
                self.source_compiled,
                assignment,
                table,
                self.domain_size,
            )
            if left != right:
                self.early_source_prunes += 1
                return False
        return True

    def target_witness(self, table, required=None):
        assignments = (
            (required,) if required is not None else self.target_assignments
        )
        for assignment in assignments:
            self.target_witnesses_tested += 1
            left, right = evaluate_compiled(
                self.target_compiled,
                assignment,
                table,
                self.domain_size,
            )
            if left != right:
                return tuple(assignment)
        return None

    def retain_source_model(self, table):
        if self.first_source_model_seconds is None:
            self.first_source_model_seconds = (
                time.monotonic() - self.search_started
            )
        started = time.monotonic()
        canonical = self.canonicalize(table)
        self.canonicalization_seconds += time.monotonic() - started
        if canonical in self.model_keys:
            self.symmetry_duplicates += 1
            return
        self.model_keys.add(canonical)
        if len(self.model_bank) < self.maximum_models:
            self.model_bank.append(canonical)

    def restrict_domain(self, domains, cell, allowed):
        previous = domains[cell]
        restricted = previous & allowed
        if restricted == previous:
            return True, False
        if restricted == 0:
            return False, False
        if self.reversible_trail:
            self.trail.append((cell, previous))
        domains[cell] = restricted
        self.changed_cells.add(cell)
        self.domain_reductions += previous.bit_count() - restricted.bit_count()
        if singleton_value(restricted) is not None and (
            singleton_value(previous) is None
        ):
            self.forced_assignments += 1
        return True, True

    def evaluate_supports(self, compiled, assignment, domains):
        """Sound over-approximating supports for one compiled term DAG."""
        values = []
        self.term_support_evaluations += len(compiled[0])
        for node in compiled[0]:
            if node[0] == "variable":
                values.append((1 << assignment[node[1]], None))
                continue
            self.support_cache_hits += 2
            left_domain = values[node[1]][0]
            right_domain = values[node[2]][0]
            output_domain = 0
            left_singleton = singleton_value(left_domain)
            right_singleton = singleton_value(right_domain)
            root_cell = None
            for left in range(self.domain_size):
                if not left_domain & (1 << left):
                    continue
                row = self.domain_size * left
                for right in range(self.domain_size):
                    if right_domain & (1 << right):
                        output_domain |= domains[row + right]
            if left_singleton is not None and right_singleton is not None:
                root_cell = (
                    self.domain_size * left_singleton + right_singleton
                )
            values.append((output_domain, root_cell))
        return values

    def restrict_root_support(
        self, compiled, values, root_id, required, domains
    ):
        support, direct_cell = values[root_id]
        required &= support
        if direct_cell is not None:
            return self.restrict_domain(domains, direct_cell, required)
        node = compiled[0][root_id]
        if node[0] != "operation":
            return True, False
        left_support = values[node[1]][0]
        right_support = values[node[2]][0]
        candidates = []
        for left in range(self.domain_size):
            if not left_support & (1 << left):
                continue
            for right in range(self.domain_size):
                if not right_support & (1 << right):
                    continue
                cell = self.domain_size * left + right
                if domains[cell] & required:
                    candidates.append(cell)
                    if len(candidates) > 1:
                        return True, False
        if len(candidates) == 1:
            return self.restrict_domain(domains, candidates[0], required)
        return False, False

    def propagate_equality(self, domains, left, right):
        left_domain, left_cell = left
        right_domain, right_cell = right
        common = left_domain & right_domain
        if common == 0:
            return False, False
        changed = False
        if left_cell is not None:
            valid, reduced = self.restrict_domain(
                domains, left_cell, common
            )
            if not valid:
                return False, False
            changed |= reduced
        if right_cell is not None:
            valid, reduced = self.restrict_domain(
                domains, right_cell, common
            )
            if not valid:
                return False, False
            changed |= reduced
        return True, changed

    def propagate_equality_support(
        self, domains, compiled, values
    ):
        left_id, right_id = compiled[1:3]
        left_domain, left_cell = values[left_id]
        right_domain, right_cell = values[right_id]
        common = left_domain & right_domain
        if common == 0:
            self.support_disjoint_contradictions += 1
            return False, False
        changed = False
        for root_id, root_cell in (
            (left_id, left_cell),
            (right_id, right_cell),
        ):
            if root_cell is not None or self.support_propagation:
                valid, reduced = self.restrict_root_support(
                    compiled, values, root_id, common, domains
                )
                if not valid:
                    return False, False
                changed |= reduced
        return True, changed

    def propagate_disequality(self, domains, assignment):
        values = self.evaluate_supports(
            self.target_compiled, assignment, domains
        )
        left = values[self.target_compiled[1]]
        right = values[self.target_compiled[2]]
        left_domain, left_cell = left
        right_domain, right_cell = right
        if left_domain & right_domain == 0:
            self.target_support_disjoint_guaranteed += 1
            return True, False
        if left_cell is not None and left_cell == right_cell:
            return False, False
        left_value = singleton_value(left_domain)
        right_value = singleton_value(right_domain)
        if left_value is not None and right_value is not None:
            return left_value != right_value, False
        if left_cell is not None and right_value is not None:
            return self.restrict_domain(
                domains, left_cell, self.full_domain ^ (1 << right_value)
            )
        if right_cell is not None and left_value is not None:
            return self.restrict_domain(
                domains, right_cell, self.full_domain ^ (1 << left_value)
            )
        return True, False

    def evaluate_source_constraint(self, domains, assignment_id):
        self.constraint_evaluations += 1
        self.source_assignments_evaluated += 1
        assignment = self.source_assignments[assignment_id]
        if self.support_propagation:
            values = self.evaluate_supports(
                self.source_compiled, assignment, domains
            )
            return self.propagate_equality_support(
                domains, self.source_compiled, values
            )
        left, right = evaluate_compiled_domains(
            self.source_compiled,
            assignment,
            domains,
            self.domain_size,
        )
        return self.propagate_equality(domains, left, right)

    def propagate_incremental(self, domains, target_assignment):
        queue = deque(range(len(self.source_assignments)))
        queued = set(queue)
        target_pending = target_assignment is not None
        while queue or target_pending:
            self.propagation_rounds += 1
            while queue:
                assignment_id = queue.popleft()
                queued.discard(assignment_id)
                self.changed_cells.clear()
                valid, _ = self.evaluate_source_constraint(
                    domains, assignment_id
                )
                if not valid:
                    self.early_source_prunes += 1
                    self.source_contradictions += 1
                    return False, "source"
                for cell in self.changed_cells:
                    for affected in self.cell_source_constraints[cell]:
                        if affected not in queued:
                            queued.add(affected)
                            queue.append(affected)
                    target_pending = target_assignment is not None
            if target_pending:
                target_pending = False
                self.changed_cells.clear()
                self.constraint_evaluations += 1
                valid, _ = self.propagate_disequality(
                    domains, target_assignment
                )
                if not valid:
                    self.target_contradictions += 1
                    return False, "target"
                for cell in self.changed_cells:
                    for affected in self.cell_source_constraints[cell]:
                        if affected not in queued:
                            queued.add(affected)
                            queue.append(affected)
        return True, None

    def propagate(self, domains, target_assignment=None):
        """Reach a fixed point using only sound equality/disequality rules."""
        started = time.monotonic()
        if self.incremental_propagation:
            result = self.propagate_incremental(
                domains, target_assignment
            )
            self.propagation_seconds += time.monotonic() - started
            return result
        changed = True
        while changed:
            self.propagation_rounds += 1
            changed = False
            for assignment_id in range(len(self.source_assignments)):
                valid, reduced = self.evaluate_source_constraint(
                    domains, assignment_id
                )
                if not valid:
                    self.early_source_prunes += 1
                    self.source_contradictions += 1
                    self.propagation_seconds += time.monotonic() - started
                    return False, "source"
                changed |= reduced
            if target_assignment is not None:
                valid, reduced = self.propagate_disequality(
                    domains, target_assignment
                )
                if not valid:
                    self.target_contradictions += 1
                    self.propagation_seconds += time.monotonic() - started
                    return False, "target"
                changed |= reduced
        self.propagation_seconds += time.monotonic() - started
        return True, None

    def choose_cell(self, domains, target_assignment=None):
        started = time.monotonic()
        if self.support_branching:
            target_pressure = [0] * len(domains)
            if target_assignment is not None:
                values = self.evaluate_supports(
                    self.target_compiled, target_assignment, domains
                )
                for node_id, node in enumerate(self.target_compiled[0]):
                    if node[0] != "operation":
                        continue
                    left_support = values[node[1]][0]
                    right_support = values[node[2]][0]
                    for left in range(self.domain_size):
                        if not left_support & (1 << left):
                            continue
                        for right in range(self.domain_size):
                            if right_support & (1 << right):
                                target_pressure[
                                    self.domain_size * left + right
                                ] += 1
            candidates = [
                cell for cell, domain in enumerate(domains)
                if domain.bit_count() > 1
            ]
            selected = min(
                candidates,
                key=lambda cell: (
                    domains[cell].bit_count(),
                    -len(self.cell_source_constraints[cell]),
                    -target_pressure[cell],
                    -self.static_cell_frequency[cell],
                    -self.nogood_conflict_activity[cell],
                    -self.contradiction_activity[cell],
                    cell,
                ),
            )
            self.activity_seconds += time.monotonic() - started
            return selected
        source_activity = list(self.static_cell_frequency)
        target_activity = list(self.target_cell_frequency)
        for assignment in self.source_assignments:
            left, right = evaluate_compiled_domains(
                self.source_compiled,
                assignment,
                domains,
                self.domain_size,
            )
            for value in (left, right):
                if value[1] is not None:
                    source_activity[value[1]] += 8
        if target_assignment is not None:
            left, right = evaluate_compiled_domains(
                self.target_compiled,
                target_assignment,
                domains,
                self.domain_size,
            )
            for value in (left, right):
                if value[1] is not None:
                    target_activity[value[1]] += 64
        candidates = [
            cell for cell, domain in enumerate(domains)
            if domain.bit_count() > 1
        ]
        selected = min(
            candidates,
            key=lambda cell: (
                domains[cell].bit_count(),
                -source_activity[cell],
                -target_activity[cell],
                cell,
            ),
        )
        first = min(candidates)
        if (
            selected != first
            or domains[selected].bit_count()
            < self.full_domain.bit_count()
        ):
            self.mrv_reductions += 1
        self.activity_seconds += time.monotonic() - started
        return selected

    def order_branch_values(self, domains, cell, target_assignment):
        values = [
            value for value in range(self.domain_size)
            if domains[cell] & (1 << value)
        ]
        if not self.support_branching:
            return values
        previous = domains[cell]
        scored = []
        for value in values:
            domains[cell] = 1 << value
            target_overlap = self.domain_size + 1
            target_disjoint = 0
            if target_assignment is not None:
                target_values = self.evaluate_supports(
                    self.target_compiled, target_assignment, domains
                )
                left = target_values[self.target_compiled[1]][0]
                right = target_values[self.target_compiled[2]][0]
                target_overlap = (left & right).bit_count()
                target_disjoint = int((left & right) == 0)
            source_disjoint = 0
            source_intersection = 0
            for assignment_id in self.cell_source_constraints[cell][:32]:
                supports = self.evaluate_supports(
                    self.source_compiled,
                    self.source_assignments[assignment_id],
                    domains,
                )
                left = supports[self.source_compiled[1]][0]
                right = supports[self.source_compiled[2]][0]
                intersection = (left & right).bit_count()
                source_disjoint += int(intersection == 0)
                source_intersection += intersection
            scored.append((
                -target_disjoint,
                target_overlap,
                source_disjoint,
                -source_intersection,
                value,
            ))
        domains[cell] = previous
        scored.sort()
        return [item[-1] for item in scored]

    def assigned_facts(self, domains):
        return frozenset(
            (cell, value)
            for cell, domain in enumerate(domains)
            for value in (singleton_value(domain),)
            if value is not None
        )

    def nogood_applies(self, facts, target_assignment):
        started = time.monotonic()
        candidate_ids = set(self.empty_nogoods)
        for fact in facts:
            candidate_ids.update(self.nogood_index.get(fact, ()))
        for record_id in sorted(candidate_ids):
            scope, nogood, _ = self.nogoods[record_id]
            if scope is not None and scope != target_assignment:
                continue
            if nogood <= facts:
                self.nogoods_reused += 1
                for cell, _ in nogood:
                    self.nogood_conflict_activity[cell] += 1
                self.nogood_seconds += time.monotonic() - started
                return True
        self.nogood_seconds += time.monotonic() - started
        return False

    def minimize_nogood(self, facts, scope):
        if (
            self.nogood_minimization_remaining <= 0
            or len(facts) < 2
            or len(facts) > 8
        ):
            return facts
        minimized = set(facts)
        for literal in sorted(facts):
            if self.nogood_minimization_remaining <= 0:
                break
            self.nogood_minimization_remaining -= 1
            trial = minimized - {literal}
            domains = [self.full_domain] * (self.domain_size ** 2)
            for cell, value in trial:
                domains[cell] = 1 << value
            previous_trail = self.reversible_trail
            self.reversible_trail = False
            valid, _ = self.propagate(domains, scope)
            self.reversible_trail = previous_trail
            if not valid:
                minimized = trial
                self.nogoods_minimized += 1
        return frozenset(minimized)

    def learn_nogood(self, facts, scope, cause="domain"):
        if self.support_propagation:
            facts = self.minimize_nogood(facts, scope)
        record = (scope, facts, cause)
        key = (scope, facts)
        if (
            len(self.nogoods) < self.maximum_nogoods
            and key not in self.nogood_records
        ):
            record_id = len(self.nogoods)
            self.nogoods.append(record)
            self.nogood_records.add(key)
            self.nogoods_learned += 1
            if cause in self.nogood_causes:
                self.nogood_causes[cause] += 1
            for literal in facts:
                self.literal_frequency[literal] = (
                    self.literal_frequency.get(literal, 0) + 1
                )
            if facts:
                rarest = min(
                    facts,
                    key=lambda literal: (
                        self.literal_frequency.get(literal, 0),
                        literal,
                    ),
                )
                self.nogood_index.setdefault(rarest, []).append(record_id)
            else:
                self.empty_nogoods.append(record_id)
            for cell, _ in facts:
                self.contradiction_activity[cell] += 1

    def relabel_domains(self, domains, permutation):
        transformed = [self.full_domain] * len(domains)
        for left in range(self.domain_size):
            for right in range(self.domain_size):
                old_cell = self.domain_size * left + right
                new_cell = (
                    self.domain_size * permutation[left]
                    + permutation[right]
                )
                new_domain = 0
                for value in range(self.domain_size):
                    if domains[old_cell] & (1 << value):
                        new_domain |= 1 << permutation[value]
                transformed[new_cell] = new_domain
        return tuple(transformed)

    def partial_symmetry_prunable(self, domains, target_assignment):
        started = time.monotonic()
        if not self.symmetry_enabled:
            return False
        constrained = {
            cell for cell, domain in enumerate(domains)
            if domain != self.full_domain
        }
        if not constrained:
            self.symmetry_seconds += time.monotonic() - started
            return False
        current = tuple(domains)
        used = set(target_assignment or ())
        for permutation in permutations(range(self.domain_size)):
            self.symmetry_permutations_tested += 1
            if any(permutation[value] != value for value in used):
                continue
            mapped_cells = {
                self.domain_size * permutation[cell // self.domain_size]
                + permutation[cell % self.domain_size]
                for cell in constrained
            }
            # Only compare within the stabilizer of the current constrained
            # cell set. This avoids unsafe canonical-prefix assumptions.
            if mapped_cells != constrained:
                continue
            if self.relabel_domains(domains, permutation) < current:
                self.symmetry_branch_prunes += 1
                self.symmetry_seconds += time.monotonic() - started
                return True
        self.symmetry_seconds += time.monotonic() - started
        return False

    def domains_to_table(self, domains):
        table = tuple(singleton_value(domain) for domain in domains)
        return table if all(value is not None for value in table) else None

    def rollback_domains(self, domains, mark):
        while len(self.trail) > mark:
            cell, previous = self.trail.pop()
            domains[cell] = previous

    def branch(self, domains, target_assignment=None, depth=0):
        if self.expired():
            self.exhaustion = "timeout"
            return None
        if self.partial_states >= self.maximum_states:
            self.exhaustion = "partial state budget exhausted"
            return None
        self.partial_states += 1
        self.maximum_depth = max(self.maximum_depth, depth)
        mark = len(self.trail)
        current = domains if self.reversible_trail else list(domains)
        result = None
        try:
            facts_before = self.assigned_facts(current)
            if self.nogood_applies(facts_before, target_assignment):
                return None
            disjoint_before = self.support_disjoint_contradictions
            valid, contradiction = self.propagate(
                current, target_assignment
            )
            if not valid:
                scope = (
                    None if contradiction == "source"
                    else target_assignment
                )
                cause = contradiction
                if (
                    contradiction == "source"
                    and self.support_disjoint_contradictions
                    > disjoint_before
                ):
                    cause = "support"
                self.learn_nogood(
                    self.assigned_facts(current), scope, cause
                )
                return None
            if self.partial_symmetry_prunable(current, target_assignment):
                self.nogood_causes["symmetry"] += 1
                return None
            complete = self.domains_to_table(current)
            if complete is not None:
                self.complete_tables += 1
                if not self.source_holds_complete(complete):
                    return None
                self.source_models += 1
                self.retain_source_model(complete)
                witness = self.target_witness(
                    complete, target_assignment
                )
                if witness is not None:
                    self.target_falsifying_models += 1
                    result = (complete, witness)
                return result
            cell = self.choose_cell(current, target_assignment)
            values = self.order_branch_values(
                current, cell, target_assignment
            )
            self.branch_choices += 1
            self.branch_values += len(values)
            for value in values:
                value_mark = len(self.trail)
                if self.reversible_trail:
                    self.trail.append((cell, current[cell]))
                    current[cell] = 1 << value
                    branch = current
                else:
                    branch = list(current)
                    branch[cell] = 1 << value
                found = self.branch(
                    branch, target_assignment, depth=depth + 1
                )
                if self.reversible_trail:
                    self.rollback_domains(current, value_mark)
                if found is not None:
                    result = found
                    return result
                if self.exhaustion is not None:
                    return None
            self.learn_nogood(
                self.assigned_facts(current),
                target_assignment,
                "domain",
            )
            return None
        finally:
            if self.reversible_trail:
                self.rollback_domains(current, mark)

    def search_target_guided(self):
        for assignment in self.target_assignments:
            if self.expired() or self.partial_states >= self.maximum_states:
                break
            self.target_witnesses_tested += 1
            found = self.branch(
                [self.full_domain] * (self.domain_size ** 2),
                assignment,
            )
            if found is not None:
                return found
            if self.exhaustion is not None:
                break
            self.target_witnesses_fully_searched += 1
        return None

    def search_partial_source_models(self):
        found = self.branch(
            [self.full_domain] * (self.domain_size ** 2)
        )
        if found is None and self.exhaustion is None:
            self.complete = True
        return found

    def search_complete_enumeration(self, canonical_only=True):
        table_count = self.domain_size ** (self.domain_size ** 2)
        for encoded in range(table_count):
            if self.expired():
                self.exhaustion = "complete enumeration deadline exhausted"
                return None
            value = encoded
            table = []
            for _ in range(self.domain_size ** 2):
                table.append(value % self.domain_size)
                value //= self.domain_size
            table = tuple(table)
            if canonical_only and self.canonicalize(table) != table:
                self.symmetry_duplicates += 1
                continue
            self.complete_tables += 1
            if not self.source_holds_complete(table):
                continue
            self.source_models += 1
            self.retain_source_model(table)
            witness = self.target_witness(table)
            if witness is not None:
                self.target_falsifying_models += 1
                return table, witness
        self.complete = True
        return None

    def canonicalize(self, table):
        return canonical_table(table, self.domain_size)

    def replay(self, table, witness):
        serialized = serialize_flat_table(table, self.domain_size)
        return replay_countermodel(
            self.source,
            self.target,
            table,
            self.domain_size,
            witness,
            serialized,
        )

    def emit_certificate(self, table):
        return emit_fin_certificate(table, self.domain_size)


def find_finite_countermodel(
    domain_size, source, target, deadline, canonical_only=False
):
    """Generic complete reference route used by the tiny Fin 2 stage."""
    search = FiniteModelEngine(
        domain_size, source, target, deadline, 0, 16
    )
    return search.search_complete_enumeration(
        canonical_only=canonical_only
    )


def finish_finite_candidate(source, target, search, found, engine):
    if found is None:
        report_finite_model(search, engine, False)
        return False
    table, witness = found
    replay_start = time.monotonic()
    replayed = search.replay(table, witness)
    replay_seconds = time.monotonic() - replay_start
    if not replayed:
        report_finite_model(
            search, engine, False, replay_seconds=replay_seconds
        )
        return False
    code = search.emit_certificate(table)
    code_bytes = len(code.encode("utf-8"))
    report_finite_model(
        search, engine, True, replay_seconds=replay_seconds,
        certificate_bytes=code_bytes,
    )
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("false", code).get("status") == "accepted"


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


def emit_fin_certificate(table, order=None):
    if order is None:
        order = len(table)
        flat_table = tuple(value for row in table for value in row)
    else:
        flat_table = tuple(table)
    compact = serialize_flat_table(flat_table, order)
    depth_option = (
        "set_option maxRecDepth 100000 in\n"
        if order >= 7
        else ""
    )
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        + depth_option
        + "def submission : Goal := by\n"
        "  let candidateMagma : Magma (Fin "
        + str(order)
        + ") := {\n"
        '    op := finOpTable "'
        + compact
        + '"\n'
        "  }\n"
        "  refine ⟨Fin "
        + str(order)
        + ", candidateMagma, ?_⟩\n"
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


def term_depth(term):
    if term[0] == "var":
        return 0
    return 1 + max(term_depth(term[1]), term_depth(term[2]))


def term_repetition_penalty(term):
    counts = {}
    for variable in term_variables(term):
        counts[variable] = 0

    def count(node):
        if node[0] == "var":
            counts[node[1]] = counts.get(node[1], 0) + 1
        else:
            count(node[1])
            count(node[2])

    count(term)
    return sum(max(0, value - 1) for value in counts.values())


def normalization_order_key(term, ordering="size"):
    common = (
        term_repetition_penalty(term),
        len(term_variables(term)),
        render_term(term),
    )
    if ordering == "depth":
        return (term_depth(term), term_size(term)) + common
    return (term_size(term), term_depth(term)) + common


def alpha_canonical_term(term, names=None):
    names = {} if names is None else names
    if term[0] == "var":
        if term[1] not in names:
            names[term[1]] = chr(ord("a") + len(names))
        return ("var", names[term[1]])
    return (
        "op",
        alpha_canonical_term(term[1], names),
        alpha_canonical_term(term[2], names),
    )


def match_rule(pattern, concrete, mapping):
    if pattern[0] == "var":
        previous = mapping.get(pattern[1])
        if previous is None:
            mapping[pattern[1]] = concrete
            return True
        return previous == concrete
    return (
        concrete[0] == "op"
        and match_rule(pattern[1], concrete[1], mapping)
        and match_rule(pattern[2], concrete[2], mapping)
    )


def substitute_known(term, mapping):
    if term[0] == "var":
        if term[1] not in mapping:
            raise ValueError("unbound normalization-rule variable")
        return mapping[term[1]]
    return (
        "op",
        substitute_known(term[1], mapping),
        substitute_known(term[2], mapping),
    )


def substitute_partial(term, mapping):
    if term[0] == "var":
        return mapping.get(term[1], term)
    return (
        "op",
        substitute_partial(term[1], mapping),
        substitute_partial(term[2], mapping),
    )


def match_selected_variables(pattern, concrete, variables, mapping):
    if pattern[0] == "var":
        if pattern[1] not in variables:
            return pattern == concrete
        previous = mapping.get(pattern[1])
        if previous is None:
            mapping[pattern[1]] = concrete
            return True
        return previous == concrete
    return (
        concrete[0] == "op"
        and match_selected_variables(
            pattern[1], concrete[1], variables, mapping
        )
        and match_selected_variables(
            pattern[2], concrete[2], variables, mapping
        )
    )


def instantiate_rule_rhs(term, variables, mapping):
    if term[0] == "var":
        if term[1] in variables:
            if term[1] not in mapping:
                raise ValueError("unbound normalization-rule variable")
            return mapping[term[1]]
        return term
    return (
        "op",
        instantiate_rule_rhs(term[1], variables, mapping),
        instantiate_rule_rhs(term[2], variables, mapping),
    )


def apply_unifier(term, mapping):
    if term[0] == "var":
        replacement = mapping.get(term[1])
        if replacement is None:
            return term
        return apply_unifier(replacement, mapping)
    return (
        "op",
        apply_unifier(term[1], mapping),
        apply_unifier(term[2], mapping),
    )


def occurs_in(variable, term, mapping):
    resolved = apply_unifier(term, mapping)
    if resolved[0] == "var":
        return resolved[1] == variable
    return (
        occurs_in(variable, resolved[1], mapping)
        or occurs_in(variable, resolved[2], mapping)
    )


def unify_terms(left, right):
    mapping = {}
    pending = [(left, right)]
    while pending:
        first, second = pending.pop()
        first = apply_unifier(first, mapping)
        second = apply_unifier(second, mapping)
        if first == second:
            continue
        if first[0] == "var":
            if occurs_in(first[1], second, mapping):
                return None
            mapping[first[1]] = second
            continue
        if second[0] == "var":
            if occurs_in(second[1], first, mapping):
                return None
            mapping[second[1]] = first
            continue
        if first[0] != "op" or second[0] != "op":
            return None
        pending.append((first[1], second[1]))
        pending.append((first[2], second[2]))
    return {
        variable: apply_unifier(value, mapping)
        for variable, value in mapping.items()
    }


class NormalizationRule:
    __slots__ = (
        "lhs", "rhs", "node_id", "origin", "variables", "proof_cost",
        "provenance", "support",
    )

    def __init__(
        self, lhs, rhs, node_id, origin, proof_cost, provenance, support=1
    ):
        self.lhs = lhs
        self.rhs = rhs
        self.node_id = node_id
        self.origin = origin
        self.variables = tuple(sorted(term_variables(lhs)))
        self.proof_cost = proof_cost
        self.provenance = provenance
        self.support = support


class EquationalNormalizer:
    """Bounded proof-producing canonicalization under source consequences."""

    def __init__(self, source, target, deadline, configuration):
        self.source = source
        self.target = target
        self.deadline = deadline
        self.configuration = configuration
        self.ordering = configuration.get("ordering", "size")
        self.selector = configuration.get("selector", "coverage")
        self.nodes = []
        self.rules = []
        self.selected_rules = []
        self.source_instances_generated = 0
        self.congruence_candidates = 0
        self.overlap_candidates = 0
        self.composed_consequences = 0
        self.replayed_candidates = 0
        self.replay_failures = 0
        self.decreasing_rules = 0
        self.nonorientable_equalities = 0
        self.alpha_duplicates_removed = 0
        self.subsumed_rules_removed = 0
        self.local_critical_pairs = 0
        self.joined_critical_pairs = 0
        self.unresolved_critical_pairs = 0
        self.left_steps = 0
        self.right_steps = 0
        self.normal_form_hits = 0
        self.distinct_normal_forms = 0
        self.normalization_budget_exits = 0
        self.consequence_budget_exits = 0
        self.exhaustion = None

    def expired(self):
        return time.monotonic() >= self.deadline

    def add_source_instance(self, mapping, origin):
        if (
            self.expired()
            or len(self.nodes) >= self.configuration["candidate_equalities"]
        ):
            self.consequence_budget_exits += 1
            self.exhaustion = (
                "timeout" if self.expired()
                else "consequence budget exhausted"
            )
            return None
        sl, sr, source_vars = self.source
        if tuple(mapping) != source_vars:
            return None
        lhs = substitute(sl, mapping)
        rhs = substitute(sr, mapping)
        maximum = self.configuration["maximum_term_size"]
        if max(term_size(lhs), term_size(rhs)) > maximum:
            return None
        node_id = len(self.nodes)
        self.nodes.append(EqualityNode(
            lhs,
            rhs,
            "source instance",
            substitution=tuple((v, mapping[v]) for v in source_vars),
            constructor="equational-normalization-" + origin,
        ))
        self.source_instances_generated += 1
        return node_id

    def vocabulary(self):
        source_vars = [("var", value) for value in self.source[2]]
        target_vars = [("var", value) for value in self.target[2]]
        target_terms = list(walk_subterms(self.target[0])) + list(
            walk_subterms(self.target[1])
        )
        values = []
        for term in source_vars + target_vars + target_terms:
            if term not in values and term_size(term) <= 7:
                values.append(term)
        atoms = [term for term in values if term[0] == "var"][:4]
        for left in atoms:
            for right in atoms:
                term = ("op", left, right)
                if term not in values:
                    values.append(term)
        return values[:24]

    def generate_consequences(self):
        source_vars = self.source[2]
        vocabulary = self.vocabulary()
        maximum = self.configuration["source_substitutions"]
        attempts = 0
        seen = set()

        def add(values, origin):
            nonlocal attempts
            if attempts >= maximum or self.expired():
                return False
            attempts += 1
            mapping = dict(zip(source_vars, values))
            signature = tuple(mapping[v] for v in source_vars)
            if signature in seen:
                return True
            seen.add(signature)
            self.add_source_instance(mapping, origin)
            return True

        # Exact source-side matches at target subterms are the compact local
        # compilation boundary: they are equation-driven and label-blind.
        target_subterms = list(walk_subterms(self.target[0])) + list(
            walk_subterms(self.target[1])
        )
        for pattern in self.source[:2]:
            for concrete in target_subterms:
                mapping = {}
                if (
                    match_term(pattern, concrete, mapping)
                    and all(variable in mapping for variable in source_vars)
                ):
                    add(
                        tuple(mapping[variable] for variable in source_vars),
                        "target-subterm-instance",
                    )

        # Identity and variable-identification consequences come first.
        canonical = [
            ("var", value)
            for value in tuple(dict.fromkeys(
                self.target[2] + self.source[2]
            ))[:4]
        ]
        if not canonical:
            canonical = [("var", source_vars[0])]
        for width in range(1, min(len(canonical), len(source_vars)) + 1):
            for indexes in product(range(width), repeat=len(source_vars)):
                if width > 1 and set(indexes) != set(range(width)):
                    continue
                if not add(
                    tuple(canonical[index] for index in indexes),
                    "variable-identification",
                ):
                    break
            if attempts >= maximum or self.expired():
                break

        # Fair bounded substitutions from the target-relevant vocabulary.
        for layer in range(len(vocabulary)):
            if attempts >= maximum or self.expired():
                break
            for indexes in product(
                range(layer + 1), repeat=len(source_vars)
            ):
                if layer and max(indexes) != layer:
                    continue
                if not add(
                    tuple(vocabulary[index] for index in indexes),
                    "source-instance",
                ):
                    break

        # Proper, exact non-variable overlaps between bounded instances.
        # These consequences are candidates only; they must replay and orient
        # decreasingly before they can enter a rulebook.
        overlap_limit = min(
            self.configuration.get("overlap_candidates", 0),
            max(
                0,
                (
                    self.configuration["candidate_equalities"]
                    - len(self.nodes)
                ) // 6,
            ),
        )
        overlap_snapshot = list(range(len(self.nodes)))
        overlap_snapshot.sort(key=lambda node_id: (
            min(
                structural_distance(
                    self.nodes[node_id].lhs, self.target[0]
                ),
                structural_distance(
                    self.nodes[node_id].lhs, self.target[1]
                ),
                structural_distance(
                    self.nodes[node_id].rhs, self.target[0]
                ),
                structural_distance(
                    self.nodes[node_id].rhs, self.target[1]
                ),
            ),
            term_size(self.nodes[node_id].lhs)
            + term_size(self.nodes[node_id].rhs),
            node_id,
        ))

        def oriented(node_id, reverse):
            if not reverse:
                return node_id
            node = self.nodes[node_id]
            new_id = len(self.nodes)
            self.nodes.append(EqualityNode(
                node.rhs, node.lhs, "symmetry", parents=(node_id,),
                constructor="equational-normalization-overlap",
            ))
            return new_id

        def wrap(parent_id, root, path):
            current_id = parent_id
            for index in range(len(path) - 1, -1, -1):
                current = self.nodes[current_id]
                previous_id = current_id
                context = get_subterm(root, path[:index])
                if path[index] == "L":
                    sibling = context[2]
                    lhs = ("op", current.lhs, sibling)
                    rhs = ("op", current.rhs, sibling)
                    kind = "congruence on left child"
                    record = ("left", sibling)
                else:
                    sibling = context[1]
                    lhs = ("op", sibling, current.lhs)
                    rhs = ("op", sibling, current.rhs)
                    kind = "congruence on right child"
                    record = ("right", sibling)
                current_id = len(self.nodes)
                self.nodes.append(EqualityNode(
                    lhs, rhs, kind, parents=(previous_id,),
                    context=record,
                    constructor="equational-normalization-overlap",
                ))
            return current_id

        # Standard one-step critical consequences. The inner source instance
        # is alpha-renamed before unification so distinct quantified variables
        # cannot collide accidentally.
        used_names = set(self.source[2]) | set(self.target[2])
        fresh_names = [
            name for name in reversed("abcdefghijklmnopqrstuvwxyz")
            if name not in used_names
        ]
        if len(fresh_names) >= len(source_vars):
            renamed = dict(zip(source_vars, fresh_names))

            def rename(term):
                if term[0] == "var":
                    return ("var", renamed[term[1]])
                return ("op", rename(term[1]), rename(term[2]))

            renamed_sides = (
                rename(self.source[0]), rename(self.source[1])
            )
            critical_cap = min(overlap_limit, 32)
            critical_added = 0
            for outer_side in (0, 1):
                if critical_added >= critical_cap:
                    break
                outer_pattern = self.source[outer_side]
                outer_other_pattern = self.source[1 - outer_side]
                for path in nonvariable_positions(
                    outer_pattern, maximum_depth=5, include_root=False
                ):
                    selected_pattern = get_subterm(outer_pattern, path)
                    for inner_side in (0, 1):
                        if critical_added >= critical_cap:
                            break
                        unifier = unify_terms(
                            selected_pattern,
                            renamed_sides[inner_side],
                        )
                        if unifier is None:
                            continue
                        outer_mapping = {
                            variable: apply_unifier(
                                ("var", variable), unifier
                            )
                            for variable in source_vars
                        }
                        inner_mapping = {
                            variable: apply_unifier(
                                ("var", renamed[variable]), unifier
                            )
                            for variable in source_vars
                        }
                        outer_node = self.add_source_instance(
                            outer_mapping, "critical-overlap"
                        )
                        inner_node = self.add_source_instance(
                            inner_mapping, "critical-overlap"
                        )
                        if outer_node is None or inner_node is None:
                            continue
                        outer_equality = self.nodes[outer_node]
                        outer_term = (
                            outer_equality.lhs
                            if outer_side == 0 else outer_equality.rhs
                        )
                        other = (
                            outer_equality.rhs
                            if outer_side == 0 else outer_equality.lhs
                        )
                        inner_equality = self.nodes[inner_node]
                        before = (
                            inner_equality.lhs
                            if inner_side == 0 else inner_equality.rhs
                        )
                        after = (
                            inner_equality.rhs
                            if inner_side == 0 else inner_equality.lhs
                        )
                        if get_subterm(outer_term, path) != before:
                            continue
                        changed = replace_subterm(
                            outer_term, path, after
                        )
                        if max(
                            term_size(other), term_size(changed)
                        ) > self.configuration["maximum_term_size"]:
                            continue
                        outer_oriented = oriented(
                            outer_node, outer_side == 0
                        )
                        inner_oriented = oriented(
                            inner_node, inner_side == 1
                        )
                        lifted = wrap(
                            inner_oriented, outer_term, path
                        )
                        left = self.nodes[outer_oriented]
                        right = self.nodes[lifted]
                        if left.rhs != right.lhs:
                            continue
                        self.nodes.append(EqualityNode(
                            left.lhs,
                            right.rhs,
                            "transitivity",
                            parents=(outer_oriented, lifted),
                            constructor="equational-normalization-overlap",
                        ))
                        self.overlap_candidates += 1
                        critical_added += 1

        overlap_added = 0
        for outer_id in overlap_snapshot:
            if overlap_added >= overlap_limit or self.expired():
                break
            outer = self.nodes[outer_id]
            for outer_reverse in (False, True):
                outer_term = outer.rhs if outer_reverse else outer.lhs
                other = outer.lhs if outer_reverse else outer.rhs
                for path in nonvariable_positions(
                    outer_term, maximum_depth=4, include_root=False
                ):
                    if overlap_added >= overlap_limit:
                        break
                    selected = get_subterm(outer_term, path)
                    for inner_id in overlap_snapshot:
                        if overlap_added >= overlap_limit:
                            break
                        inner = self.nodes[inner_id]
                        for inner_reverse in (False, True):
                            before = (
                                inner.rhs if inner_reverse else inner.lhs
                            )
                            after = (
                                inner.lhs if inner_reverse else inner.rhs
                            )
                            self.overlap_candidates += 1
                            if selected != before:
                                continue
                            changed = replace_subterm(
                                outer_term, path, after
                            )
                            if max(
                                term_size(other), term_size(changed)
                            ) > self.configuration["maximum_term_size"]:
                                continue
                            # other = outer_term = changed
                            outer_to_selected = oriented(
                                outer_id, not outer_reverse
                            )
                            inner_oriented = oriented(
                                inner_id, inner_reverse
                            )
                            lifted = wrap(
                                inner_oriented, outer_term, path
                            )
                            left = self.nodes[outer_to_selected]
                            right = self.nodes[lifted]
                            if left.rhs != right.lhs:
                                continue
                            self.nodes.append(EqualityNode(
                                left.lhs,
                                right.rhs,
                                "transitivity",
                                parents=(outer_to_selected, lifted),
                                constructor="equational-normalization-overlap",
                            ))
                            overlap_added += 1
                            break

        # Exact endpoint composition only; this is not transitive closure.
        starts = {}
        ends = {}
        initial_count = len(self.nodes)
        for node_id, node in enumerate(self.nodes[:initial_count]):
            for start, end, reverse in (
                (node.lhs, node.rhs, False),
                (node.rhs, node.lhs, True),
            ):
                starts.setdefault(start, []).append(
                    (node_id, reverse, start, end)
                )
                ends.setdefault(end, []).append(
                    (node_id, reverse, start, end)
                )
        composition_cap = min(
            self.configuration.get("composition_candidates", 0),
            self.configuration["candidate_equalities"] - len(self.nodes),
        )
        for middle in sorted(
            set(starts) & set(ends), key=render_term
        ):
            if composition_cap <= 0 or self.expired():
                break
            for (
                left_id, left_reverse, left_start, left_end
            ) in ends[middle]:
                for (
                    right_id, right_reverse, right_start, right_end
                ) in starts[middle]:
                    if left_id >= right_id or composition_cap <= 0:
                        continue
                    if left_end != middle or right_start != middle:
                        continue
                    if max(
                        term_size(left_start), term_size(right_end)
                    ) > self.configuration["maximum_term_size"]:
                        continue
                    oriented_left = left_id
                    if left_reverse:
                        left = self.nodes[left_id]
                        oriented_left = len(self.nodes)
                        self.nodes.append(EqualityNode(
                            left.rhs, left.lhs, "symmetry",
                            parents=(left_id,),
                            constructor="equational-normalization-composition",
                        ))
                    oriented_right = right_id
                    if right_reverse:
                        right = self.nodes[right_id]
                        oriented_right = len(self.nodes)
                        self.nodes.append(EqualityNode(
                            right.rhs, right.lhs, "symmetry",
                            parents=(right_id,),
                            constructor="equational-normalization-composition",
                        ))
                    self.nodes.append(EqualityNode(
                        left_start,
                        right_end,
                        "transitivity",
                        parents=(oriented_left, oriented_right),
                        constructor="equational-normalization-composition",
                    ))
                    self.composed_consequences += 1
                    composition_cap -= 1
        return self.nodes

    def replay_consequence(self, node_id):
        ok = replay_dag(
            self.source,
            self.nodes,
            node_id,
            maximum_term_size=self.configuration["maximum_term_size"],
        )
        if ok:
            self.replayed_candidates += 1
        else:
            self.replay_failures += 1
        return ok

    def proof_cost(self, node_id, seen=None):
        seen = set() if seen is None else seen
        if node_id in seen:
            return 0
        seen.add(node_id)
        return 1 + sum(
            self.proof_cost(parent, seen)
            for parent in self.nodes[node_id].parents
        )

    def orient(self):
        by_alpha = {}
        maximum_rules = self.configuration["replayed_rules"]
        for node_id, node in enumerate(self.nodes):
            if self.expired() or len(by_alpha) >= maximum_rules:
                break
            if not self.replay_consequence(node_id):
                continue
            left_key = normalization_order_key(node.lhs, self.ordering)
            right_key = normalization_order_key(node.rhs, self.ordering)
            if left_key == right_key:
                self.nonorientable_equalities += 1
                continue
            if right_key < left_key:
                lhs, rhs, proof_id = node.lhs, node.rhs, node_id
            else:
                lhs, rhs = node.rhs, node.lhs
                proof_id = len(self.nodes)
                self.nodes.append(EqualityNode(
                    lhs, rhs, "symmetry", parents=(node_id,),
                    constructor="equational-normalization-orientation",
                ))
            if lhs[0] == "var":
                self.nonorientable_equalities += 1
                continue
            source_argument_variables = set()
            stack = [proof_id]
            visited = set()
            while stack:
                current = stack.pop()
                if current in visited:
                    continue
                visited.add(current)
                proof = self.nodes[current]
                if proof.kind == "source instance":
                    for _, value in proof.substitution:
                        source_argument_variables |= term_variables(value)
                stack.extend(proof.parents)
            schematic = (
                term_variables(rhs) <= term_variables(lhs)
                and source_argument_variables <= term_variables(lhs)
            )
            # A replayed symbolic critical consequence can contain auxiliary
            # proof parameters which cancel from both endpoints.  Such a rule
            # remains universally specializable: compilation fills the
            # internal parameters with an arbitrary matched target term.
            if (
                not schematic
                and term_variables(rhs) <= term_variables(lhs)
                and term_variables(lhs)
            ):
                schematic = True
            if schematic:
                names = {}
                alpha = (
                    alpha_canonical_term(lhs, names),
                    alpha_canonical_term(rhs, names),
                    "schematic",
                )
            else:
                alpha = (lhs, rhs, "target-concrete")
            cost = self.proof_cost(proof_id)
            existing = by_alpha.get(alpha)
            if existing is not None:
                existing.support += 1
                self.alpha_duplicates_removed += 1
                if cost >= existing.proof_cost:
                    continue
            provenance = (
                render_term(alpha[0]) + "->" + render_term(alpha[1])
            )
            rule = NormalizationRule(
                lhs, rhs, proof_id, node.constructor or node.kind,
                cost, provenance,
                support=(existing.support if existing else 1),
            )
            if not schematic:
                rule.variables = ()
            by_alpha[alpha] = rule
        self.rules = list(by_alpha.values())
        self.decreasing_rules = len(self.rules)
        return self.rules

    def rule_target_occurrences(self, rule):
        count = 0
        for target in self.target[:2]:
            for subterm in walk_subterms(target):
                mapping = {}
                if match_selected_variables(
                    rule.lhs, subterm, set(rule.variables), mapping
                ):
                    count += 1
        return count

    def select_rulebook(self):
        scored = []
        for rule in self.rules:
            occurrences = self.rule_target_occurrences(rule)
            reduction = (
                term_size(rule.lhs) - term_size(rule.rhs),
                term_depth(rule.lhs) - term_depth(rule.rhs),
            )
            if self.selector == "reduction":
                score = (
                    -reduction[0], -reduction[1], -occurrences,
                    rule.proof_cost, rule.provenance,
                )
            else:
                score = (
                    -occurrences, -rule.support, -reduction[0],
                    -reduction[1], rule.proof_cost, rule.provenance,
                )
            scored.append((score, rule))
        scored.sort(key=lambda item: item[0])
        self.selected_rules = [
            rule for _, rule in scored[
                :self.configuration["selected_rules"]
            ]
        ]
        self.audit_critical_pairs()
        return self.selected_rules

    def applicable(self, term, rule):
        mapping = {}
        variables = set(rule.variables)
        if not match_selected_variables(
            rule.lhs, term, variables, mapping
        ):
            return None
        if not set(rule.variables) <= set(mapping):
            return None
        try:
            replacement = instantiate_rule_rhs(
                rule.rhs, variables, mapping
            )
        except ValueError:
            return None
        return mapping, replacement

    def rewrite_candidates(self, term):
        paths = []

        def visit(node, path):
            if node[0] == "op":
                visit(node[1], path + ("L",))
                visit(node[2], path + ("R",))
            paths.append(path)

        visit(term, ())
        candidates = []
        for path in paths:
            subterm = get_subterm(term, path)
            for index, rule in enumerate(self.selected_rules):
                result = self.applicable(subterm, rule)
                if result is None:
                    continue
                mapping, replacement = result
                after = replace_subterm(term, path, replacement)
                if normalization_order_key(
                    after, self.ordering
                ) >= normalization_order_key(term, self.ordering):
                    continue
                reduction = term_size(term) - term_size(after)
                candidates.append((
                    -len(path), -reduction, rule.proof_cost, index,
                    path, rule, mapping, after,
                ))
        candidates.sort(key=lambda item: item[:4])
        return candidates

    def normalize(self, term):
        current = term
        trace = []
        for _ in range(self.configuration["normalization_steps"]):
            candidates = self.rewrite_candidates(current)
            if not candidates:
                return current, trace, False
            _, _, _, _, path, rule, mapping, after = candidates[0]
            trace.append({
                "before": current,
                "path": tuple(path),
                "rule": rule,
                "substitution": tuple(sorted(mapping.items())),
                "after": after,
            })
            current = after
        if self.rewrite_candidates(current):
            self.normalization_budget_exits += 1
            return current, trace, True
        return current, trace, False

    def replay_trace(self, start, trace, expected):
        current = start
        for step in trace:
            if step["before"] != current:
                return False
            rule = step["rule"]
            try:
                selected = get_subterm(current, step["path"])
            except (TypeError, ValueError):
                return False
            mapping = {}
            variables = set(rule.variables)
            if not match_selected_variables(
                rule.lhs, selected, variables, mapping
            ):
                return False
            if tuple(sorted(mapping.items())) != step["substitution"]:
                return False
            try:
                replacement = instantiate_rule_rhs(
                    rule.rhs, variables, mapping
                )
                after = replace_subterm(current, step["path"], replacement)
            except (TypeError, ValueError):
                return False
            if after != step["after"]:
                return False
            if normalization_order_key(
                after, self.ordering
            ) >= normalization_order_key(current, self.ordering):
                return False
            if not self.replay_consequence(rule.node_id):
                return False
            current = after
        return current == expected

    def instantiate_proof(self, node_id, mapping, output, cache):
        mapping = dict(mapping)
        stack = [node_id]
        visited = set()
        internal_variables = set()
        while stack:
            current = stack.pop()
            if current in visited:
                continue
            visited.add(current)
            proof = self.nodes[current]
            internal_variables |= term_variables(proof.lhs)
            internal_variables |= term_variables(proof.rhs)
            stack.extend(proof.parents)
        fallback = next(
            iter(mapping.values()),
            ("var", self.target[2][0]),
        )
        for variable in internal_variables:
            mapping.setdefault(variable, fallback)
        key = (node_id, tuple(sorted(mapping.items())))
        if key in cache:
            return cache[key]
        node = self.nodes[node_id]
        parents = tuple(
            self.instantiate_proof(parent, mapping, output, cache)
            for parent in node.parents
        )
        lhs = substitute_partial(node.lhs, mapping)
        rhs = substitute_partial(node.rhs, mapping)
        if node.kind == "source instance":
            substitution = tuple(
                (variable, substitute_partial(value, mapping))
                for variable, value in node.substitution
            )
            new = EqualityNode(
                lhs, rhs, "source instance",
                substitution=substitution,
                orientation=node.orientation,
                constructor="equational-normalization",
            )
        elif node.kind == "symmetry":
            new = EqualityNode(
                lhs, rhs, "symmetry", parents=parents,
                constructor="equational-normalization",
            )
        elif node.kind == "transitivity":
            new = EqualityNode(
                lhs, rhs, "transitivity", parents=parents,
                constructor="equational-normalization",
            )
        elif node.kind in (
            "congruence on left child",
            "congruence on right child",
        ):
            side, sibling = node.context
            new = EqualityNode(
                lhs,
                rhs,
                node.kind,
                parents=parents,
                context=(side, substitute_partial(sibling, mapping)),
                constructor="equational-normalization",
            )
        else:
            raise ValueError("unsupported normalization proof node")
        result = len(output)
        output.append(new)
        cache[key] = result
        return result

    def lift_context(self, output, parent_id, root, path):
        parent = output[parent_id]
        if get_subterm(root, path) != parent.lhs:
            raise ValueError("normalization context mismatch")
        current_id = parent_id
        for index in range(len(path) - 1, -1, -1):
            current = output[current_id]
            previous_id = current_id
            context = get_subterm(root, path[:index])
            if path[index] == "L":
                sibling = context[2]
                lhs = ("op", current.lhs, sibling)
                rhs = ("op", current.rhs, sibling)
                kind = "congruence on left child"
                record = ("left", sibling)
            else:
                sibling = context[1]
                lhs = ("op", sibling, current.lhs)
                rhs = ("op", sibling, current.rhs)
                kind = "congruence on right child"
                record = ("right", sibling)
            current_id = len(output)
            output.append(EqualityNode(
                lhs, rhs, kind, parents=(previous_id,),
                context=record, constructor="equational-normalization",
            ))
        return current_id

    def compile_trace(self, start, trace, output):
        if not trace:
            node_id = len(output)
            output.append(EqualityNode(start, start, "reflexivity"))
            return node_id
        cache = {}
        root = None
        for step in trace:
            mapping = dict(step["substitution"])
            rule_id = self.instantiate_proof(
                step["rule"].node_id, mapping, output, cache
            )
            lifted = self.lift_context(
                output, rule_id, step["before"], step["path"]
            )
            if root is None:
                root = lifted
            else:
                left = output[root]
                right = output[lifted]
                if left.rhs != right.lhs:
                    raise ValueError("normalization trace is discontinuous")
                previous_root = root
                root = len(output)
                output.append(EqualityNode(
                    left.lhs, right.rhs, "transitivity",
                    parents=(previous_root, lifted),
                    constructor="equational-normalization",
                ))
        return root

    def audit_critical_pairs(self):
        # Bounded root/applicability ambiguity audit. It is a quality metric,
        # not a confluence claim or an acceptance condition.
        for left_index, left in enumerate(self.selected_rules):
            for right in self.selected_rules[left_index + 1:]:
                mapping_left = {}
                mapping_right = {}
                if not (
                    match_rule(left.lhs, right.lhs, mapping_left)
                    or match_rule(right.lhs, left.lhs, mapping_right)
                ):
                    continue
                self.local_critical_pairs += 1
                # Identical alpha-normalized right sides are trivially joined.
                names_left = {}
                names_right = {}
                if (
                    alpha_canonical_term(left.rhs, names_left)
                    == alpha_canonical_term(right.rhs, names_right)
                ):
                    self.joined_critical_pairs += 1
                else:
                    self.unresolved_critical_pairs += 1

    def solve(self):
        self.generate_consequences()
        self.orient()
        self.select_rulebook()
        left_nf, left_trace, left_exhausted = self.normalize(self.target[0])
        right_nf, right_trace, right_exhausted = self.normalize(self.target[1])
        self.left_steps = len(left_trace)
        self.right_steps = len(right_trace)
        if left_exhausted or right_exhausted:
            return None
        if not self.replay_trace(self.target[0], left_trace, left_nf):
            self.replay_failures += 1
            return None
        if not self.replay_trace(self.target[1], right_trace, right_nf):
            self.replay_failures += 1
            return None
        if left_nf != right_nf:
            self.distinct_normal_forms += 1
            return None
        self.normal_form_hits += 1
        proof_nodes = []
        try:
            left_root = self.compile_trace(
                self.target[0], left_trace, proof_nodes
            )
            right_root = self.compile_trace(
                self.target[1], right_trace, proof_nodes
            )
            right_node = proof_nodes[right_root]
            symmetric_right = len(proof_nodes)
            proof_nodes.append(EqualityNode(
                right_node.rhs,
                right_node.lhs,
                "symmetry",
                parents=(right_root,),
                constructor="equational-normalization",
            ))
            left_node = proof_nodes[left_root]
            if left_node.rhs != proof_nodes[symmetric_right].lhs:
                return None
            root = len(proof_nodes)
            proof_nodes.append(EqualityNode(
                left_node.lhs,
                proof_nodes[symmetric_right].rhs,
                "transitivity",
                parents=(left_root, symmetric_right),
                constructor="equational-normalization",
            ))
        except (KeyError, TypeError, ValueError):
            self.replay_failures += 1
            return None
        if (
            proof_nodes[root].lhs != self.target[0]
            or proof_nodes[root].rhs != self.target[1]
            or not replay_dag(
                self.source,
                proof_nodes,
                root,
                maximum_term_size=self.configuration["maximum_term_size"],
                maximum_nodes=self.configuration["maximum_proof_nodes"],
            )
        ):
            self.replay_failures += 1
            return None
        return proof_nodes, root


class BridgeIR:
    """Bounded source-derived representation changes followed by normalization."""

    def __init__(self, source, target, deadline, configuration):
        self.source = source
        self.target = target
        self.deadline = deadline
        self.configuration = configuration
        normalizer_configuration = dict(configuration["normalizer"])
        normalizer_configuration["seconds"] = configuration["seconds"]
        self.normalizer = EquationalNormalizer(
            source, target, deadline, normalizer_configuration
        )
        self.bridge_equalities = []
        self.bridge_equality_candidates = 0
        self.replayed_bridge_equalities = 0
        self.bridge_replay_failures = 0
        self.bridge_matches_attempted = 0
        self.repeated_variable_rejections = 0
        self.unbound_variable_rejections = 0
        self.bridge_states_created = 0
        self.bridge_states_deduplicated = 0
        self.bridge_states_pruned_no_activation = 0
        self.bridge_cycles_suppressed = 0
        self.reverse_rule_expansions = 0
        self.nonorientable_bridges = 0
        self.anti_unification_proposals = 0
        self.anti_unification_replayed = 0
        self.maximum_bridge_depth = 0
        self.maximum_term_growth = 0
        self.initial_normalizer_matches = 0
        self.post_bridge_normalizer_matches = 0
        self.no_match_activations = 0
        self.normalization_steps_after_activation = 0
        self.shared_normal_form_hits = 0
        self.activated_distinct_normal_forms = 0
        self.proof_dag_nodes = 0
        self.winning_states = None
        self.deadline_exits = 0
        self.state_budget_exits = 0
        self.exhaustion = None

    def expired(self):
        return time.monotonic() >= self.deadline

    def bridge_vocabulary(self):
        values = []
        terms = (
            [("var", variable) for variable in self.target[2]]
            + list(walk_subterms(self.target[0]))
            + list(walk_subterms(self.target[1]))
            + [("var", variable) for variable in self.source[2]]
        )
        for term in terms:
            if (
                term not in values
                and term_size(term) <= self.configuration["vocabulary_term_size"]
            ):
                values.append(term)
        values.sort(key=lambda term: (
            term_size(term), term_depth(term), render_term(term)
        ))
        return values[:self.configuration["vocabulary_terms"]]

    def collect_bridge_equalities(self):
        self.normalizer.generate_consequences()
        self.normalizer.orient()
        self.normalizer.select_rulebook()
        maximum = self.configuration["bridge_equalities"]
        selected = set(id(rule) for rule in self.normalizer.selected_rules)
        ordered_rules = sorted(
            self.normalizer.rules,
            key=lambda rule: (
                0 if id(rule) in selected else 1,
                -self.normalizer.rule_target_occurrences(rule),
                rule.proof_cost,
                rule.provenance,
            ),
        )
        seen = set()

        def add(
            pattern, replacement, node_id, variables, proof_reverse,
            origin, expansion=False, nonorientable=False,
        ):
            if len(self.bridge_equalities) >= maximum:
                return
            signature = (
                pattern, replacement, node_id, tuple(variables), proof_reverse
            )
            if signature in seen or pattern == replacement:
                return
            seen.add(signature)
            self.bridge_equality_candidates += 1
            if not self.normalizer.replay_consequence(node_id):
                self.bridge_replay_failures += 1
                return
            self.replayed_bridge_equalities += 1
            self.bridge_equalities.append({
                "pattern": pattern,
                "replacement": replacement,
                "node_id": node_id,
                "variables": tuple(variables),
                "proof_reverse": proof_reverse,
                "origin": origin,
                "expansion": expansion,
                "nonorientable": nonorientable,
                "proof_cost": self.normalizer.proof_cost(node_id),
            })

        for rule in ordered_rules:
            if len(self.bridge_equalities) >= maximum or self.expired():
                break
            add(
                rule.lhs,
                rule.rhs,
                rule.node_id,
                rule.variables,
                False,
                rule.origin,
            )
            if self.configuration["reverse_expansion"]:
                add(
                    rule.rhs,
                    rule.lhs,
                    rule.node_id,
                    rule.variables,
                    True,
                    rule.origin,
                    expansion=True,
                )

        if self.configuration["nonorientable_evidence"]:
            candidates = []
            for node_id, node in enumerate(self.normalizer.nodes):
                if node.lhs == node.rhs:
                    continue
                if normalization_order_key(
                    node.lhs, self.normalizer.ordering
                ) != normalization_order_key(
                    node.rhs, self.normalizer.ordering
                ):
                    continue
                distance = min(
                    structural_distance(node.lhs, self.target[0]),
                    structural_distance(node.lhs, self.target[1]),
                    structural_distance(node.rhs, self.target[0]),
                    structural_distance(node.rhs, self.target[1]),
                )
                candidates.append((distance, node_id, node))
            candidates.sort(key=lambda item: (
                item[0],
                term_size(item[2].lhs) + term_size(item[2].rhs),
                item[1],
            ))
            for _, node_id, node in candidates:
                if len(self.bridge_equalities) >= maximum or self.expired():
                    break
                # These target-derived instances are deliberately concrete.
                add(
                    node.lhs, node.rhs, node_id, (), False,
                    "nonorientable-evidence", nonorientable=True,
                )
                add(
                    node.rhs, node.lhs, node_id, (), True,
                    "nonorientable-evidence", nonorientable=True,
                )

        # Anti-unification is proposal-only. A proposal is retained only when
        # its alpha pattern is already represented by a replayed equality.
        if self.configuration["anti_unification"]:
            alpha_index = {}
            for equality in self.bridge_equalities:
                names = {}
                key = (
                    alpha_canonical_term(equality["pattern"], names),
                    alpha_canonical_term(equality["replacement"], names),
                )
                alpha_index[key] = equality
            for left_index, left in enumerate(self.bridge_equalities[:16]):
                for right in self.bridge_equalities[left_index + 1:16]:
                    self.anti_unification_proposals += 1
                    names_left = {}
                    names_right = {}
                    key_left = (
                        alpha_canonical_term(left["pattern"], names_left),
                        alpha_canonical_term(left["replacement"], names_left),
                    )
                    key_right = (
                        alpha_canonical_term(right["pattern"], names_right),
                        alpha_canonical_term(right["replacement"], names_right),
                    )
                    if key_left == key_right and key_left in alpha_index:
                        self.anti_unification_replayed += 1
        return self.bridge_equalities

    def count_matches(self, term):
        return len(self.normalizer.rewrite_candidates(term))

    def initial_state(self, term):
        normal_form, trace, exhausted = self.normalizer.normalize(term)
        if exhausted or not self.normalizer.replay_trace(
            term, trace, normal_form
        ):
            return None
        return {
            "current": normal_form,
            "initial_trace": trace,
            "bridge_steps": [],
            "depth": 0,
            "activations": 0,
            "proof_cost": len(trace),
            "maximum_growth": 0,
        }

    def paths(self, term):
        output = []

        def visit(node, path):
            if node[0] == "op":
                visit(node[1], path + ("L",))
                visit(node[2], path + ("R",))
            output.append(path)

        visit(term, ())
        return output

    def complete_mappings(self, equality, selected):
        variables = set(equality["variables"])
        mapping = {}
        if not match_selected_variables(
            equality["pattern"], selected, variables, mapping
        ):
            return []
        missing = sorted(variables - set(mapping))
        if not missing:
            return [mapping]
        vocabulary = self.bridge_vocabulary()
        if not vocabulary:
            return []
        maximum = self.configuration["missing_variable_substitutions"]
        output = []
        for values in product(vocabulary, repeat=len(missing)):
            candidate = dict(mapping)
            candidate.update(zip(missing, values))
            output.append(candidate)
            if len(output) >= maximum:
                break
        return output

    def replay_bridge_step(self, before, step):
        if step["before"] != before:
            return False
        equality = step["equality"]
        try:
            selected = get_subterm(before, step["path"])
        except (TypeError, ValueError):
            return False
        variables = set(equality["variables"])
        mapping = {}
        if not match_selected_variables(
            equality["pattern"], selected, variables, mapping
        ):
            return False
        recorded = dict(step["substitution"])
        if not set(mapping) <= set(recorded):
            return False
        if any(mapping[key] != recorded[key] for key in mapping):
            return False
        if set(recorded) != variables:
            return False
        try:
            replacement = instantiate_rule_rhs(
                equality["replacement"], variables, recorded
            )
            bridged = replace_subterm(before, step["path"], replacement)
        except (TypeError, ValueError):
            return False
        if bridged != step["bridged"]:
            return False
        if not self.normalizer.replay_consequence(equality["node_id"]):
            return False
        if not self.normalizer.replay_trace(
            bridged, step["normalization_trace"], step["after"]
        ):
            return False
        return True

    def replay_state(self, start, state):
        initial = start
        if state["initial_trace"]:
            initial = state["initial_trace"][-1]["after"]
        if not self.normalizer.replay_trace(
            start, state["initial_trace"], initial
        ):
            return False
        current = initial
        for step in state["bridge_steps"]:
            if not self.replay_bridge_step(current, step):
                return False
            current = step["after"]
        return current == state["current"]

    def candidate_states(self, state, opposite_terms):
        before = state["current"]
        before_matches = self.count_matches(before)
        original_size = max(1, term_size(before))
        output = []
        for path in self.paths(before):
            if self.expired():
                self.deadline_exits += 1
                self.exhaustion = "timeout"
                break
            selected = get_subterm(before, path)
            for equality in self.bridge_equalities:
                self.bridge_matches_attempted += 1
                mappings = self.complete_mappings(equality, selected)
                if not mappings:
                    continue
                for mapping in mappings:
                    try:
                        replacement = instantiate_rule_rhs(
                            equality["replacement"],
                            set(equality["variables"]),
                            mapping,
                        )
                        bridged = replace_subterm(before, path, replacement)
                    except (TypeError, ValueError):
                        self.unbound_variable_rejections += 1
                        continue
                    if bridged == before:
                        self.bridge_cycles_suppressed += 1
                        continue
                    growth = term_size(bridged) - term_size(before)
                    if (
                        growth > self.configuration["maximum_growth_per_step"]
                        or term_size(bridged)
                        > int(original_size * self.configuration["maximum_ratio"])
                        or term_size(bridged)
                        > self.normalizer.configuration["maximum_term_size"]
                    ):
                        continue
                    raw_matches = self.count_matches(bridged)
                    normal_form, trace, exhausted = self.normalizer.normalize(
                        bridged
                    )
                    if exhausted or not self.normalizer.replay_trace(
                        bridged, trace, normal_form
                    ):
                        continue
                    previous_distance = min(
                        (
                            structural_distance(before, opposite)
                            for opposite in opposite_terms
                        ),
                        default=10 ** 9,
                    )
                    new_distance = min(
                        (
                            structural_distance(normal_form, opposite)
                            for opposite in opposite_terms
                        ),
                        default=10 ** 9,
                    )
                    activated = before_matches == 0 and raw_matches > 0
                    useful = (
                        activated
                        or raw_matches > before_matches
                        or new_distance < previous_distance
                        or normal_form in opposite_terms
                    )
                    if not useful:
                        self.bridge_states_pruned_no_activation += 1
                        continue
                    step = {
                        "before": before,
                        "path": tuple(path),
                        "equality": equality,
                        "substitution": tuple(sorted(mapping.items())),
                        "bridged": bridged,
                        "normalization_trace": trace,
                        "after": normal_form,
                        "before_matches": before_matches,
                        "post_bridge_matches": raw_matches,
                        "activated": activated,
                    }
                    candidate = {
                        "current": normal_form,
                        "initial_trace": state["initial_trace"],
                        "bridge_steps": state["bridge_steps"] + [step],
                        "depth": state["depth"] + 1,
                        "activations":
                            state["activations"] + int(activated),
                        "proof_cost": (
                            state["proof_cost"]
                            + equality["proof_cost"]
                            + len(path) + len(trace) + 1
                        ),
                        "maximum_growth": max(
                            state["maximum_growth"], growth
                        ),
                    }
                    if not self.replay_state(
                        self.target[0]
                        if state.get("side") == "left"
                        else self.target[1],
                        {**candidate, "side": state.get("side")},
                    ):
                        self.bridge_replay_failures += 1
                        continue
                    candidate["side"] = state.get("side")
                    self.bridge_states_created += 1
                    self.post_bridge_normalizer_matches += raw_matches
                    if activated:
                        self.no_match_activations += 1
                        self.normalization_steps_after_activation += len(trace)
                    if equality["expansion"]:
                        self.reverse_rule_expansions += 1
                    if equality["nonorientable"]:
                        self.nonorientable_bridges += 1
                    self.maximum_bridge_depth = max(
                        self.maximum_bridge_depth, candidate["depth"]
                    )
                    self.maximum_term_growth = max(
                        self.maximum_term_growth,
                        candidate["maximum_growth"],
                    )
                    output.append(candidate)
                    if (
                        self.bridge_states_created
                        >= self.configuration["maximum_states"]
                    ):
                        self.state_budget_exits += 1
                        self.exhaustion = "state budget exhausted"
                        return output
        return output

    def state_rank(self, state, opposite_terms):
        distance = min(
            (
                structural_distance(state["current"], opposite)
                for opposite in opposite_terms
            ),
            default=10 ** 9,
        )
        exact = state["current"] in opposite_terms
        activation_key = -state["activations"]
        if self.configuration["ranking"] == "distance":
            primary = (0 if exact else 1, distance, activation_key)
        else:
            primary = (0 if exact else 1, activation_key, distance)
        return primary + (
            state["maximum_growth"],
            state["proof_cost"],
            render_term(state["current"]),
        )

    def retain_states(self, candidates, opposite_terms):
        best = {}
        for state in candidates:
            key = (state["current"], state["depth"])
            existing = best.get(key)
            if existing is None or self.state_rank(
                state, opposite_terms
            ) < self.state_rank(existing, opposite_terms):
                if existing is not None:
                    self.bridge_states_deduplicated += 1
                best[key] = state
            else:
                self.bridge_states_deduplicated += 1
        return sorted(
            best.values(),
            key=lambda state: self.state_rank(state, opposite_terms),
        )[:self.configuration["beam"]]

    def compile_side(self, start, state, output):
        root = self.normalizer.compile_trace(
            start, state["initial_trace"], output
        )
        for step in state["bridge_steps"]:
            mapping = dict(step["substitution"])
            proof = self.normalizer.instantiate_proof(
                step["equality"]["node_id"], mapping, output, {}
            )
            if step["equality"]["proof_reverse"]:
                node = output[proof]
                previous = proof
                proof = len(output)
                output.append(EqualityNode(
                    node.rhs, node.lhs, "symmetry", parents=(previous,),
                    constructor="bridge-ir",
                ))
            lifted = self.normalizer.lift_context(
                output, proof, step["before"], step["path"]
            )
            segment = lifted
            if step["normalization_trace"]:
                normalized = self.normalizer.compile_trace(
                    step["bridged"], step["normalization_trace"], output
                )
                left = output[lifted]
                right = output[normalized]
                if left.rhs != right.lhs:
                    raise ValueError("bridge normalization discontinuity")
                segment = len(output)
                output.append(EqualityNode(
                    left.lhs, right.rhs, "transitivity",
                    parents=(lifted, normalized), constructor="bridge-ir",
                ))
            left = output[root]
            right = output[segment]
            if left.rhs != right.lhs:
                raise ValueError("bridge trace discontinuity")
            previous_root = root
            root = len(output)
            output.append(EqualityNode(
                left.lhs, right.rhs, "transitivity",
                parents=(previous_root, segment), constructor="bridge-ir",
            ))
        return root

    def compile_solution(self, left_state, right_state):
        if not (
            self.replay_state(self.target[0], left_state)
            and self.replay_state(self.target[1], right_state)
            and left_state["current"] == right_state["current"]
        ):
            self.bridge_replay_failures += 1
            return None
        output = []
        try:
            left_root = self.compile_side(
                self.target[0], left_state, output
            )
            right_root = self.compile_side(
                self.target[1], right_state, output
            )
            right = output[right_root]
            symmetric = len(output)
            output.append(EqualityNode(
                right.rhs, right.lhs, "symmetry", parents=(right_root,),
                constructor="bridge-ir",
            ))
            left = output[left_root]
            if left.rhs != output[symmetric].lhs:
                return None
            root = len(output)
            output.append(EqualityNode(
                left.lhs, output[symmetric].rhs, "transitivity",
                parents=(left_root, symmetric), constructor="bridge-ir",
            ))
        except (KeyError, TypeError, ValueError):
            self.bridge_replay_failures += 1
            return None
        target_variables = set(self.target[2])
        used_variables = set()
        for node_id in proof_node_ids(output, root):
            node = output[node_id]
            used_variables |= term_variables(node.lhs)
            used_variables |= term_variables(node.rhs)
            for _, value in node.substitution:
                used_variables |= term_variables(value)
            if node.context is not None:
                used_variables |= term_variables(node.context[1])
        if not used_variables <= target_variables:
            self.unbound_variable_rejections += 1
            return None
        if (
            len(output) > self.configuration["maximum_proof_nodes"]
            or not replay_dag(
                self.source,
                output,
                root,
                maximum_term_size=
                    self.normalizer.configuration["maximum_term_size"],
                maximum_nodes=self.configuration["maximum_proof_nodes"],
            )
        ):
            self.bridge_replay_failures += 1
            return None
        self.proof_dag_nodes = len(proof_node_ids(output, root))
        return output, root

    def solve(self):
        self.collect_bridge_equalities()
        left = self.initial_state(self.target[0])
        right = self.initial_state(self.target[1])
        if left is None or right is None:
            return None
        left["side"] = "left"
        right["side"] = "right"
        # A depth-zero convergence belongs to the standalone normalizer and
        # is not evidence that a representation bridge added capability.
        if left["current"] == right["current"]:
            return None
        self.initial_normalizer_matches = (
            self.count_matches(self.target[0])
            + self.count_matches(self.target[1])
        )
        left_states = [left]
        right_states = [right]
        all_left = [left]
        all_right = [right]
        for _ in range(self.configuration["maximum_depth"]):
            if self.expired():
                self.deadline_exits += 1
                self.exhaustion = "timeout"
                break
            left_terms = [state["current"] for state in all_left]
            right_terms = [state["current"] for state in all_right]
            new_left = []
            for state in left_states:
                new_left.extend(self.candidate_states(state, right_terms))
            new_right = []
            for state in right_states:
                new_right.extend(self.candidate_states(state, left_terms))
            left_states = self.retain_states(new_left, right_terms)
            right_states = self.retain_states(new_right, left_terms)
            all_left.extend(left_states)
            all_right.extend(right_states)
            hits = [
                (left_state, right_state)
                for left_state in all_left
                for right_state in all_right
                if (
                    left_state["current"] == right_state["current"]
                    and (
                        left_state["bridge_steps"]
                        or right_state["bridge_steps"]
                    )
                )
            ]
            hits.sort(key=lambda pair: (
                pair[0]["proof_cost"] + pair[1]["proof_cost"],
                pair[0]["depth"] + pair[1]["depth"],
                render_term(pair[0]["current"]),
            ))
            for left_state, right_state in hits:
                found = self.compile_solution(left_state, right_state)
                if found is not None:
                    self.shared_normal_form_hits += 1
                    self.winning_states = (left_state, right_state)
                    return found
            activated = [
                state for state in left_states + right_states
                if state["activations"]
            ]
            if activated and not hits:
                self.activated_distinct_normal_forms += len(activated)
            if not left_states and not right_states:
                break
        return None


class QuotientMatcher:
    """Instantiate the source law by matching modulo replayed equalities."""

    def __init__(self, source, target, deadline, edge_cap=256):
        self.source = source
        self.target = target
        self.deadline = deadline
        self.configuration = NORMALIZATION_PORTFOLIO[1]
        self.normalizer = EquationalNormalizer(
            source, target, deadline, dict(self.configuration)
        )
        self.normalizer.generate_consequences()
        self.normalizer.orient()
        self.normalizer.select_rulebook()
        self.nodes = self.normalizer.nodes
        if not self.nodes or not replay_dag(
            source, self.nodes, 0,
            maximum_term_size=self.configuration["maximum_term_size"],
        ):
            raise ValueError("normalizer proof DAG did not replay")
        self.parent = {}
        self.members = defaultdict(set)
        self.adjacency = defaultdict(list)
        self.matches = 0
        self.quotient_only = 0
        self.instances = 0
        self.generations = 0
        self.replay_failures = 0
        self.max_term_size = self.configuration["maximum_term_size"]
        self.max_derivation_nodes = 5000
        target_variables = set(target[2])
        for node_id, node in enumerate(self.nodes[:edge_cap]):
            if (
                set(term_variables(node.lhs)) <= target_variables
                and set(term_variables(node.rhs)) <= target_variables
            ):
                self.add_edge(node.lhs, node.rhs, node_id)
        for side in target[:2]:
            for term in walk_subterms(side):
                self.find(term)
        self.rebuild_members()

    def expired(self):
        return time.monotonic() >= self.deadline

    def find(self, term):
        self.parent.setdefault(term, term)
        if self.parent[term] != term:
            self.parent[term] = self.find(self.parent[term])
        return self.parent[term]

    def union(self, left, right):
        left_root, right_root = self.find(left), self.find(right)
        if left_root == right_root:
            return
        if render_term(left_root) > render_term(right_root):
            left_root, right_root = right_root, left_root
        self.parent[right_root] = left_root

    def add_edge(self, left, right, node_id):
        self.adjacency[left].append((right, node_id, False))
        self.adjacency[right].append((left, node_id, True))
        self.union(left, right)

    def rebuild_members(self):
        self.members = defaultdict(set)
        for term in list(self.parent):
            self.members[self.find(term)].add(term)

    def class_members(self, term):
        return self.members.get(self.find(term), {term})

    def path_proof(self, start, goal):
        if start == goal:
            node_id = len(self.nodes)
            self.nodes.append(EqualityNode(start, goal, "reflexivity"))
            return node_id
        queue = deque([start])
        previous = {start: None}
        while queue:
            current = queue.popleft()
            for neighbor, node_id, reverse in self.adjacency.get(current, ()):
                if neighbor in previous:
                    continue
                previous[neighbor] = (current, node_id, reverse)
                if neighbor == goal:
                    queue.clear()
                    break
                queue.append(neighbor)
        if goal not in previous:
            return None
        edges = []
        cursor = goal
        while cursor != start:
            prior, node_id, reverse = previous[cursor]
            edges.append((node_id, reverse))
            cursor = prior
        edges.reverse()
        oriented = []
        for node_id, reverse in edges:
            if reverse:
                node = self.nodes[node_id]
                new_id = len(self.nodes)
                self.nodes.append(EqualityNode(
                    node.rhs, node.lhs, "symmetry", parents=(node_id,),
                    constructor="quotient-matcher",
                ))
                oriented.append(new_id)
            else:
                oriented.append(node_id)
        root = oriented[0]
        for node_id in oriented[1:]:
            left, right = self.nodes[root], self.nodes[node_id]
            if left.rhs != right.lhs:
                return None
            new_root = len(self.nodes)
            self.nodes.append(EqualityNode(
                left.lhs, right.rhs, "transitivity",
                parents=(root, node_id), constructor="quotient-matcher",
            ))
            root = new_root
        return root

    def ematch(self, pattern, concrete, mapping):
        if pattern[0] == "var":
            variable = pattern[1]
            value = self.find(concrete)
            if variable in mapping and mapping[variable] != value:
                return []
            result = dict(mapping)
            result[variable] = value
            return [(result, ("var", concrete))]
        output = []
        for candidate in self.class_members(concrete):
            if candidate[0] != "op":
                continue
            for left_map, left_witness in self.ematch(
                pattern[1], candidate[1], mapping
            ):
                for right_map, right_witness in self.ematch(
                    pattern[2], candidate[2], left_map
                ):
                    output.append((
                        right_map,
                        ("op", concrete, candidate, left_witness, right_witness),
                    ))
        return output

    def representative_mapping(self, mapping):
        return {
            variable: min(
                self.members.get(eclass, {eclass}),
                key=lambda term: (term_size(term), render_term(term)),
            )
            for variable, eclass in mapping.items()
        }

    def compile_witness(self, pattern, witness, representatives):
        if pattern[0] == "var":
            return self.path_proof(witness[1], representatives[pattern[1]])
        _, concrete, candidate, left_witness, right_witness = witness
        prefix = self.path_proof(concrete, candidate)
        left = self.compile_witness(pattern[1], left_witness, representatives)
        right = self.compile_witness(
            pattern[2], right_witness, representatives
        )
        if prefix is None or left is None or right is None:
            return None
        left_node = self.nodes[left]
        left_lift = len(self.nodes)
        self.nodes.append(EqualityNode(
            ("op", left_node.lhs, candidate[2]),
            ("op", left_node.rhs, candidate[2]),
            "congruence on left child", parents=(left,),
            context=("left", candidate[2]), constructor="quotient-matcher",
        ))
        right_node = self.nodes[right]
        right_lift = len(self.nodes)
        self.nodes.append(EqualityNode(
            ("op", left_node.rhs, right_node.lhs),
            ("op", left_node.rhs, right_node.rhs),
            "congruence on right child", parents=(right,),
            context=("right", left_node.rhs), constructor="quotient-matcher",
        ))
        middle = len(self.nodes)
        self.nodes.append(EqualityNode(
            self.nodes[left_lift].lhs, self.nodes[right_lift].rhs,
            "transitivity", parents=(left_lift, right_lift),
            constructor="quotient-matcher",
        ))
        if self.nodes[prefix].lhs == self.nodes[prefix].rhs:
            return middle
        root = len(self.nodes)
        self.nodes.append(EqualityNode(
            self.nodes[prefix].lhs, self.nodes[middle].rhs,
            "transitivity", parents=(prefix, middle),
            constructor="quotient-matcher",
        ))
        return root

    def target_paths(self):
        for side_name, root in (
            ("left", self.target[0]), ("right", self.target[1])
        ):
            stack = [(root, ())]
            while stack:
                term, path = stack.pop()
                yield side_name, root, term, path
                if term[0] == "op":
                    stack.append((term[2], path + ("R",)))
                    stack.append((term[1], path + ("L",)))

    def collect_candidates(self, maximum=4096):
        candidates = []
        seen = set()
        target_variables = set(self.target[2])
        for orientation, pattern, replacement, reverse in (
            ("forward", self.source[0], self.source[1], False),
            ("reverse", self.source[1], self.source[0], True),
        ):
            for side_name, root, concrete, path in self.target_paths():
                if self.expired():
                    return candidates
                exact_mapping = {}
                exact = match_term(pattern, concrete, exact_mapping)
                for mapping, witness in self.ematch(pattern, concrete, {}):
                    if self.expired():
                        return candidates
                    if set(mapping) != set(self.source[2]):
                        continue
                    self.matches += 1
                    if exact and set(exact_mapping) == set(self.source[2]):
                        continue
                    self.quotient_only += 1
                    representatives = self.representative_mapping(mapping)
                    if any(
                        not set(term_variables(term)) <= target_variables
                        for term in representatives.values()
                    ):
                        continue
                    replacement_term = substitute(replacement, representatives)
                    after = replace_subterm(root, path, replacement_term)
                    opposite = (
                        self.target[1] if side_name == "left"
                        else self.target[0]
                    )
                    key = (
                        side_name, path, replacement_term,
                        tuple(sorted(representatives.items())),
                    )
                    if key in seen:
                        continue
                    seen.add(key)
                    connects = int(
                        self.find(after) == self.find(opposite)
                        or self.find(replacement_term) == self.find(opposite)
                    )
                    score = (
                        -connects,
                        structural_distance(after, opposite),
                        term_size(after), len(path), render_term(after),
                        orientation,
                    )
                    candidates.append((
                        score, pattern, replacement, reverse, root, concrete,
                        path, representatives, witness,
                    ))
                    if len(candidates) >= maximum:
                        return candidates
        return candidates

    def one_generation(self, maximum_instances=128):
        added = []
        candidates = self.collect_candidates()
        candidates.sort(key=lambda item: item[0])
        for (
            _, pattern, replacement, reverse, root, concrete, path,
            representatives, witness,
        ) in candidates:
            if self.expired():
                break
            candidate_start = len(self.nodes)
            pattern_proof = self.compile_witness(
                pattern, witness, representatives
            )
            if pattern_proof is None:
                del self.nodes[candidate_start:]
                continue
            instantiated_pattern = substitute(pattern, representatives)
            instantiated_replacement = substitute(replacement, representatives)
            if self.nodes[pattern_proof].rhs != instantiated_pattern:
                del self.nodes[candidate_start:]
                continue
            source_id = len(self.nodes)
            self.nodes.append(EqualityNode(
                instantiated_pattern, instantiated_replacement,
                "source instance",
                substitution=tuple(
                    (variable, representatives[variable])
                    for variable in self.source[2]
                ),
                orientation=reverse, constructor="quotient-matcher",
            ))
            segment = len(self.nodes)
            self.nodes.append(EqualityNode(
                concrete, instantiated_replacement, "transitivity",
                parents=(pattern_proof, source_id),
                constructor="quotient-matcher",
            ))
            lifted = self.normalizer.lift_context(
                self.nodes, segment, root, path
            )
            node = self.nodes[lifted]
            if max(term_size(node.lhs), term_size(node.rhs)) > self.max_term_size:
                del self.nodes[candidate_start:]
                continue
            if not replay_dag(
                self.source, self.nodes, lifted,
                maximum_term_size=self.max_term_size,
            ):
                self.replay_failures += 1
                del self.nodes[candidate_start:]
                continue
            self.add_edge(node.lhs, node.rhs, lifted)
            added.append(lifted)
            self.instances += 1
            if len(added) >= maximum_instances:
                break
        self.rebuild_members()
        return added

    def solve(self, generations=2):
        for generation in range(generations):
            self.generations = generation + 1
            self.one_generation()
            if self.find(self.target[0]) == self.find(self.target[1]):
                root = self.path_proof(self.target[0], self.target[1])
                if root is not None and replay_dag(
                    self.source, self.nodes, root,
                    maximum_term_size=self.max_term_size,
                ):
                    return self.nodes, root
            if self.expired():
                break
        return None


class Recipe:
    __slots__ = ("lhs", "rhs", "kind", "parents", "data", "cost")

    def __init__(self, lhs, rhs, kind, parents=(), data=None):
        self.lhs = lhs
        self.rhs = rhs
        self.kind = kind
        self.parents = tuple(parents)
        self.data = data
        self.cost = 1 + sum(parent.cost for parent in self.parents)


class CompactSuperposition:
    def __init__(self, module, source, target, deadline, limits):
        self.m = module
        self.source = source
        self.target = target
        self.deadline = deadline
        self.limits = limits
        self.clauses = []
        self.signatures = set()
        self.generated = 0
        self.superpositions = 0
        self.reductions = 0
        self.rounds = 0
        self.maximum_recipe_cost = 0
        identity = {
            variable: ("var", variable) for variable in source[2]
        }
        base = Recipe(
            source[0],
            source[1],
            "source",
            data=(tuple(identity.items()), False),
        )
        self.add_clause(base)

    def expired(self):
        return time.monotonic() >= self.deadline

    def key(self, term):
        return self.m.normalization_order_key(term, "size")

    def orient(self, recipe):
        left_variables = self.m.term_variables(recipe.lhs)
        right_variables = self.m.term_variables(recipe.rhs)
        if (
            recipe.lhs[0] != "var"
            and right_variables <= left_variables
            and self.key(recipe.rhs) < self.key(recipe.lhs)
        ):
            return recipe
        if (
            recipe.rhs[0] != "var"
            and left_variables <= right_variables
            and self.key(recipe.lhs) < self.key(recipe.rhs)
        ):
            return Recipe(
                recipe.rhs, recipe.lhs, "symmetry", (recipe,)
            )
        return None

    def alpha_signature(self, lhs, rhs):
        names = {}
        return (
            self.m.alpha_canonical_term(lhs, names),
            self.m.alpha_canonical_term(rhs, names),
        )

    def add_clause(self, recipe):
        if (
            recipe.lhs == recipe.rhs
            or max(
                self.m.term_size(recipe.lhs),
                self.m.term_size(recipe.rhs),
            ) > self.limits["maximum_term_size"]
        ):
            return False
        oriented = self.orient(recipe)
        if oriented is None:
            candidates = (recipe,)
        else:
            candidates = (oriented,)
        added = False
        for candidate in candidates:
            signature = self.alpha_signature(
                candidate.lhs, candidate.rhs
            )
            reverse = self.alpha_signature(
                candidate.rhs, candidate.lhs
            )
            if signature in self.signatures or reverse in self.signatures:
                continue
            self.signatures.add(signature)
            self.clauses.append(candidate)
            self.maximum_recipe_cost = max(
                self.maximum_recipe_cost, candidate.cost
            )
            self.generated += 1
            added = True
        return added

    def instantiate(self, recipe, mapping):
        lhs = self.m.substitute_partial(recipe.lhs, mapping)
        rhs = self.m.substitute_partial(recipe.rhs, mapping)
        if lhs == recipe.lhs and rhs == recipe.rhs:
            return recipe
        return Recipe(
            lhs,
            rhs,
            "instantiate",
            (recipe,),
            tuple(sorted(mapping.items())),
        )

    def lift(self, recipe, root, path):
        if self.m.get_subterm(root, path) != recipe.lhs:
            raise ValueError("recipe context mismatch")
        current = recipe
        for index in range(len(path) - 1, -1, -1):
            context = self.m.get_subterm(root, path[:index])
            if path[index] == "L":
                sibling = context[2]
                lhs = ("op", current.lhs, sibling)
                rhs = ("op", current.rhs, sibling)
                data = ("left", sibling)
            else:
                sibling = context[1]
                lhs = ("op", sibling, current.lhs)
                rhs = ("op", sibling, current.rhs)
                data = ("right", sibling)
            current = Recipe(lhs, rhs, "congruence", (current,), data)
        return current

    def target_score(self, recipe):
        targets = self.target[:2]
        occurrence = 0
        for target in targets:
            for subterm in self.m.walk_subterms(target):
                mapping = {}
                if self.m.match_term(recipe.lhs, subterm, mapping):
                    occurrence += 1
        return (
            -occurrence,
            min(
                self.m.structural_distance(recipe.lhs, targets[0]),
                self.m.structural_distance(recipe.lhs, targets[1]),
                self.m.structural_distance(recipe.rhs, targets[0]),
                self.m.structural_distance(recipe.rhs, targets[1]),
            ),
            self.m.term_size(recipe.lhs) + self.m.term_size(recipe.rhs),
            recipe.cost,
            self.m.render_term(recipe.lhs),
        )

    def rules(self):
        output = []
        for clause in self.clauses:
            oriented = self.orient(clause)
            if oriented is not None:
                output.append(oriented)
            else:
                if clause.lhs[0] != "var":
                    output.append(clause)
                if clause.rhs[0] != "var":
                    output.append(Recipe(
                        clause.rhs,
                        clause.lhs,
                        "symmetry",
                        (clause,),
                    ))
        output.sort(key=self.target_score)
        return output[:self.limits["maximum_rules"]]

    def rewrite_once(self, term, rules, excluded=None):
        candidates = []
        for path in self.m.nonvariable_positions(
            term,
            maximum_depth=self.limits["maximum_depth"],
            include_root=True,
        ):
            selected = self.m.get_subterm(term, path)
            for index, rule in enumerate(rules):
                if rule is excluded:
                    continue
                mapping = {}
                if not self.m.match_term(rule.lhs, selected, mapping):
                    continue
                if not self.m.term_variables(rule.lhs) <= set(mapping):
                    continue
                replacement = self.m.substitute_partial(rule.rhs, mapping)
                after = self.m.replace_subterm(term, path, replacement)
                if self.key(after) >= self.key(term):
                    continue
                candidates.append((
                    -len(path),
                    self.key(after),
                    rule.cost,
                    index,
                    path,
                    rule,
                    mapping,
                    after,
                ))
        if not candidates:
            return None
        candidates.sort(key=lambda item: item[:4])
        _, _, _, _, path, rule, mapping, after = candidates[0]
        proof = self.instantiate(rule, mapping)
        return after, self.lift(proof, term, path)

    def normalize(self, term, rules, excluded=None):
        current = term
        proof = None
        for _ in range(self.limits["normalization_steps"]):
            step = self.rewrite_once(current, rules, excluded)
            if step is None:
                return current, proof
            after, step_proof = step
            proof = (
                step_proof
                if proof is None
                else Recipe(
                    proof.lhs,
                    step_proof.rhs,
                    "transitivity",
                    (proof, step_proof),
                )
            )
            current = after
            self.reductions += 1
        return current, proof

    def interreduce(self, recipe, rules):
        left, left_proof = self.normalize(recipe.lhs, rules, recipe)
        right, right_proof = self.normalize(recipe.rhs, rules, recipe)
        result = recipe
        if left_proof is not None:
            reverse = Recipe(
                left_proof.rhs,
                left_proof.lhs,
                "symmetry",
                (left_proof,),
            )
            result = Recipe(
                left,
                result.rhs,
                "transitivity",
                (reverse, result),
            )
        if right_proof is not None:
            result = Recipe(
                result.lhs,
                right,
                "transitivity",
                (result, right_proof),
            )
        return result

    def freshen(self, recipe, prefix):
        mapping = {
            variable: ("var", f"_{prefix}{index}")
            for index, variable in enumerate(
                sorted(
                    self.m.term_variables(recipe.lhs)
                    | self.m.term_variables(recipe.rhs)
                )
            )
        }
        return self.instantiate(recipe, mapping)

    def critical_pair(self, outer, inner, outer_index, inner_index, path):
        left = self.freshen(outer, f"o{outer_index}_")
        right = self.freshen(inner, f"i{inner_index}_")
        selected = self.m.get_subterm(left.lhs, path)
        unifier = self.m.unify_terms(selected, right.lhs)
        if unifier is None:
            return None
        left = self.instantiate(left, unifier)
        right = self.instantiate(right, unifier)
        changed = self.m.replace_subterm(left.lhs, path, right.rhs)
        if changed == left.rhs:
            return None
        reverse_left = Recipe(
            left.rhs, left.lhs, "symmetry", (left,)
        )
        lifted = self.lift(right, left.lhs, path)
        return Recipe(
            left.rhs,
            changed,
            "transitivity",
            (reverse_left, lifted),
        )

    def target_proof(self, rules):
        collapse = self.collapse_proof()
        if collapse is not None:
            return collapse
        left, left_proof = self.normalize(self.target[0], rules)
        right, right_proof = self.normalize(self.target[1], rules)
        if left != right:
            return None
        if left_proof is None:
            left_proof = Recipe(
                self.target[0], self.target[0], "reflexivity"
            )
        if right_proof is None:
            right_proof = Recipe(
                self.target[1], self.target[1], "reflexivity"
            )
        reverse_right = Recipe(
            right_proof.rhs,
            right_proof.lhs,
            "symmetry",
            (right_proof,),
        )
        return Recipe(
            self.target[0],
            self.target[1],
            "transitivity",
            (left_proof, reverse_right),
        )

    def collapse_proof(self):
        """Close any goal from a replayed universal bare-variable collapse."""
        for clause in sorted(self.clauses, key=self.target_score):
            for variable_side, common_side in (
                (clause.lhs, clause.rhs),
                (clause.rhs, clause.lhs),
            ):
                if (
                    variable_side[0] != "var"
                    or variable_side[1] in self.m.term_variables(common_side)
                ):
                    continue
                distinguished = variable_side[1]
                variables = sorted(
                    self.m.term_variables(clause.lhs)
                    | self.m.term_variables(clause.rhs)
                )
                anchor = ("var", self.target[2][0])
                base = {variable: anchor for variable in variables}
                left_mapping = dict(base)
                right_mapping = dict(base)
                left_mapping[distinguished] = self.target[0]
                right_mapping[distinguished] = self.target[1]
                left = self.instantiate(clause, left_mapping)
                right = self.instantiate(clause, right_mapping)
                if variable_side is clause.rhs:
                    left = Recipe(
                        left.rhs, left.lhs, "symmetry", (left,)
                    )
                    right = Recipe(
                        right.rhs, right.lhs, "symmetry", (right,)
                    )
                reverse_right = Recipe(
                    right.rhs, right.lhs, "symmetry", (right,)
                )
                proof = Recipe(
                    left.lhs,
                    reverse_right.rhs,
                    "transitivity",
                    (left, reverse_right),
                )
                if (
                    proof.lhs == self.target[0]
                    and proof.rhs == self.target[1]
                ):
                    return proof
        return None

    def solve(self):
        processed = 0
        for round_index in range(self.limits["maximum_rounds"]):
            self.rounds = round_index + 1
            rules = self.rules()
            goal = self.target_proof(rules)
            if goal is not None:
                return goal
            snapshot = rules
            proposals = []
            for outer_index, outer in enumerate(snapshot):
                for inner_index, inner in enumerate(snapshot):
                    for path in self.m.nonvariable_positions(
                        outer.lhs,
                        maximum_depth=self.limits["maximum_depth"],
                        include_root=True,
                    ):
                        if self.expired():
                            return None
                        proposal = self.critical_pair(
                            outer, inner, outer_index, inner_index, path
                        )
                        if proposal is None:
                            continue
                        proposal = self.interreduce(proposal, rules)
                        proposals.append((
                            self.target_score(proposal), proposal
                        ))
            proposals.sort(key=lambda item: item[0])
            added = 0
            for _, proposal in proposals:
                if self.add_clause(proposal):
                    self.superpositions += 1
                    added += 1
                    if added >= self.limits["new_clauses_per_round"]:
                        break
            processed += len(proposals)
            if not added or len(self.clauses) >= self.limits[
                "maximum_clauses"
            ]:
                break
        return self.target_proof(self.rules())

    def compile(self, recipe):
        nodes = []
        cache = {}

        def transform(term, environment):
            return self.m.substitute_partial(term, environment)

        def visit(current, environment):
            key = (id(current), tuple(sorted(environment.items())))
            if key in cache:
                return cache[key]
            if current.kind == "instantiate":
                mapping = {
                    variable: transform(value, environment)
                    for variable, value in current.data
                }
                for variable, value in environment.items():
                    mapping.setdefault(variable, value)
                result = visit(current.parents[0], mapping)
                cache[key] = result
                return result
            parents = tuple(
                visit(parent, environment) for parent in current.parents
            )
            lhs = transform(current.lhs, environment)
            rhs = transform(current.rhs, environment)
            if current.kind == "source":
                substitution, reverse = current.data
                substitution = tuple(
                    (variable, transform(value, environment))
                    for variable, value in substitution
                )
                node = self.m.EqualityNode(
                    lhs,
                    rhs,
                    "source instance",
                    substitution=substitution,
                    orientation=reverse,
                    constructor="compact-superposition",
                )
            elif current.kind == "congruence":
                side, sibling = current.data
                kind = (
                    "congruence on left child"
                    if side == "left"
                    else "congruence on right child"
                )
                node = self.m.EqualityNode(
                    lhs,
                    rhs,
                    kind,
                    parents=parents,
                    context=(side, transform(sibling, environment)),
                    constructor="compact-superposition",
                )
            else:
                node = self.m.EqualityNode(
                    lhs,
                    rhs,
                    current.kind,
                    parents=parents,
                    constructor="compact-superposition",
                )
            result = len(nodes)
            nodes.append(node)
            cache[key] = result
            return result

        # Variables introduced only to standardize schematic parents apart
        # are universal proof parameters.  If they disappear from the final
        # equality, specialize them to an in-scope target variable rather
        # than leaking synthetic names into Lean.
        internal_variables = set()
        stack = [recipe]
        visited = set()
        while stack:
            current = stack.pop()
            if id(current) in visited:
                continue
            visited.add(id(current))
            internal_variables |= self.m.term_variables(current.lhs)
            internal_variables |= self.m.term_variables(current.rhs)
            stack.extend(current.parents)
        target_variables = set(self.target[2])
        fallback = ("var", self.target[2][0])
        environment = {
            variable: fallback
            for variable in internal_variables
            if variable not in target_variables
        }
        root = visit(recipe, environment)
        return nodes, root


COMPACT_SUPERPOSITION_PROBE = {
    "seconds": 0.20,
    "maximum_term_size": 35,
    "maximum_replay_term_size": 80,
    "maximum_depth": 7,
    "maximum_rules": 96,
    "maximum_rounds": 8,
    "new_clauses_per_round": 64,
    "maximum_clauses": 512,
    "normalization_steps": 64,
    "maximum_proof_nodes": 8000,
}


NORMALIZATION_PORTFOLIO = (
    {
        "name": "norm-probe",
        "seconds": 0.20,
        "ordering": "size",
        "selector": "coverage",
        "candidate_equalities": 250,
        "replayed_rules": 32,
        "selected_rules": 8,
        "source_substitutions": 200,
        "overlap_candidates": 100,
        "composition_candidates": 32,
        "normalization_steps": 24,
        "maximum_term_size": 15,
        "maximum_proof_nodes": 256,
    },
    {
        "name": "norm-fast",
        "seconds": 0.75,
        "ordering": "size",
        "selector": "coverage",
        "candidate_equalities": 800,
        "replayed_rules": 64,
        "selected_rules": 16,
        "source_substitutions": 600,
        "overlap_candidates": 500,
        "composition_candidates": 96,
        "normalization_steps": 48,
        "maximum_term_size": 17,
        "maximum_proof_nodes": 512,
    },
    {
        "name": "norm-medium",
        "seconds": 3.0,
        "ordering": "size",
        "selector": "coverage",
        "candidate_equalities": 2000,
        "replayed_rules": 128,
        "selected_rules": 24,
        "source_substitutions": 1500,
        "overlap_candidates": 2000,
        "composition_candidates": 256,
        "normalization_steps": 96,
        "maximum_term_size": 19,
        "maximum_proof_nodes": 1000,
    },
    {
        "name": "norm-deep-diagnostic",
        "seconds": 15.0,
        "ordering": "size",
        "selector": "coverage",
        "candidate_equalities": 4000,
        "replayed_rules": 256,
        "selected_rules": 48,
        "source_substitutions": 3000,
        "overlap_candidates": 4000,
        "composition_candidates": 512,
        "normalization_steps": 192,
        "maximum_term_size": 21,
        "maximum_proof_nodes": 2000,
        "production_eligible": False,
    },
)

SYMBOLIC_SUPERPOSITION = {
    "name": "symbolic-superposition",
    "seconds": 0.35,
    "ordering": "size",
    "selector": "coverage",
    # Preserve the candidate budget for symbolic critical pairs.  Concrete
    # source instances are already covered by the earlier equality routes.
    "candidate_equalities": 1200,
    "replayed_rules": 400,
    "selected_rules": 128,
    "source_substitutions": 0,
    "overlap_candidates": 800,
    "composition_candidates": 512,
    "normalization_steps": 96,
    "maximum_term_size": 27,
    "maximum_proof_nodes": 3000,
}

# One symbolic generation gained three public TRUE cases and four of forty
# label-hidden external TRUE opportunities, with no candidate on forty matched
# FALSE controls.  The earlier concrete normalization portfolios remain off.
PROMOTED_NORMALIZATION_PORTFOLIO = (SYMBOLIC_SUPERPOSITION,)

BRIDGE_IR_PORTFOLIO = (
    {
        "name": "bridge-probe",
        "seconds": 0.20,
        "maximum_depth": 1,
        "bridge_equalities": 64,
        "beam": 8,
        "maximum_states": 128,
        "maximum_growth_per_step": 3,
        "maximum_ratio": 1.5,
        "maximum_proof_nodes": 256,
        "missing_variable_substitutions": 16,
        "vocabulary_terms": 8,
        "vocabulary_term_size": 5,
        "ranking": "activation",
        "nonorientable_evidence": False,
        "reverse_expansion": True,
        "anti_unification": False,
        "normalizer": NORMALIZATION_PORTFOLIO[0],
    },
    {
        "name": "bridge-fast",
        "seconds": 0.75,
        "maximum_depth": 2,
        "bridge_equalities": 192,
        "beam": 16,
        "maximum_states": 1000,
        "maximum_growth_per_step": 4,
        "maximum_ratio": 2.0,
        "maximum_proof_nodes": 512,
        "missing_variable_substitutions": 32,
        "vocabulary_terms": 10,
        "vocabulary_term_size": 7,
        "ranking": "activation",
        "nonorientable_evidence": False,
        "reverse_expansion": True,
        "anti_unification": False,
        "normalizer": NORMALIZATION_PORTFOLIO[1],
    },
    {
        "name": "bridge-medium",
        "seconds": 3.0,
        "maximum_depth": 2,
        "bridge_equalities": 512,
        "beam": 32,
        "maximum_states": 5000,
        "maximum_growth_per_step": 5,
        "maximum_ratio": 2.5,
        "maximum_proof_nodes": 1000,
        "missing_variable_substitutions": 64,
        "vocabulary_terms": 12,
        "vocabulary_term_size": 9,
        "ranking": "activation",
        "nonorientable_evidence": False,
        "reverse_expansion": True,
        "anti_unification": False,
        "normalizer": NORMALIZATION_PORTFOLIO[2],
        "production_eligible": False,
    },
    {
        "name": "bridge-deep-diagnostic",
        "seconds": 15.0,
        "maximum_depth": 3,
        "bridge_equalities": 1024,
        "beam": 48,
        "maximum_states": 25000,
        "maximum_growth_per_step": 6,
        "maximum_ratio": 3.0,
        "maximum_proof_nodes": 2000,
        "missing_variable_substitutions": 96,
        "vocabulary_terms": 16,
        "vocabulary_term_size": 11,
        "ranking": "activation",
        "nonorientable_evidence": True,
        "reverse_expansion": True,
        "anti_unification": True,
        "normalizer": NORMALIZATION_PORTFOLIO[3],
        "production_eligible": False,
    },
)

# Frozen only after development selection and a sealed external TRUE audit.
PROMOTED_BRIDGE_IR_PORTFOLIO = ()


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

CONTEXTUAL_PORTFOLIO = (
    {
        "name": "target-narrowing",
        "kind": "target-narrowing",
        "seconds": 3.0,
        "maximum_depth": 3,
        "maximum_context_depth": 5,
        "branching": 20,
        "maximum_terms": 750,
        "limits": {
            "max_term_size": 19,
            "max_pool_terms": 40,
            "max_core_terms": 9,
            "max_source_attempts": 12000,
            "max_source_edges": 1000,
            "max_derivation_nodes": 3000,
            "max_graph_edges": 2800,
            "max_congruence_rounds": 0,
        },
    },
    {
        "name": "contextual-light",
        "kind": "contextual-overlap",
        "seconds": 1.0,
        "maximum_overlap_depth": 1,
        "maximum_context_depth": 3,
        "maximum_source_instances": 300,
        "maximum_candidates": 1000,
        "maximum_new_nodes": 1500,
        "limits": {
            "max_term_size": 17,
            "max_pool_terms": 40,
            "max_core_terms": 8,
            "max_source_attempts": 12000,
            "max_source_edges": 300,
            "max_derivation_nodes": 2000,
            "max_graph_edges": 1800,
            "max_congruence_rounds": 0,
        },
    },
    {
        "name": "contextual-medium",
        "kind": "contextual-overlap",
        "seconds": 5.0,
        "maximum_overlap_depth": 2,
        "maximum_context_depth": 5,
        "maximum_source_instances": 800,
        "maximum_candidates": 4000,
        "maximum_new_nodes": 6000,
        "limits": {
            "max_term_size": 21,
            "max_pool_terms": 48,
            "max_core_terms": 10,
            "max_source_attempts": 30000,
            "max_source_edges": 800,
            "max_derivation_nodes": 6500,
            "max_graph_edges": 6200,
            "max_congruence_rounds": 0,
        },
    },
)

# Development added five accepted TRUE cases through target narrowing, while
# both overlap configurations added no marginal win. The untouched holdout then
# added zero. The preregistered promotion rule therefore keeps the constructor
# implemented and regression-tested but disables it in the production route.
PROMOTED_CONTEXTUAL_PORTFOLIO = ()

FINITE_MODEL_PORTFOLIO = (
    {
        "name": "fin3-fast",
        "domain_size": 3,
        "kind": "target-guided",
        "seconds": 0.5,
        "maximum_states": 25000,
        "maximum_models": 16,
    },
    {
        "name": "fin3-medium",
        "domain_size": 3,
        "kind": "partial-source",
        "seconds": 2.0,
        "maximum_states": 150000,
        "maximum_models": 64,
    },
    {
        "name": "fin3-complete-bounded",
        "domain_size": 3,
        "kind": "complete-enumeration",
        "seconds": 3.0,
        "maximum_states": 0,
        "maximum_models": 64,
    },
)

FINITE_MODEL_PROTOTYPES = (
    {
        "name": "fin4-prototype",
        "domain_size": 4,
        "kind": "target-guided",
        "seconds": 1.0,
        "maximum_states": 50000,
        "maximum_models": 16,
    },
)

FIN4_ENGINE_OPTIONS = {
    "support_propagation": True,
    "incremental_propagation": True,
    "reversible_trail": True,
    "diverse_witnesses": True,
    "support_branching": True,
    "symmetry_enabled": True,
    "nogood_minimization_budget": 16,
}

FIN4_PORTFOLIO = (
    {
        "name": "fin4-probe",
        "domain_size": 4,
        "kind": "target-guided",
        "seconds": 0.20,
        "maximum_states": 10000,
        "maximum_models": 4,
        "options": {
            **FIN4_ENGINE_OPTIONS,
            "target_witness_limit": 16,
        },
    },
    {
        "name": "fin4-fast",
        "domain_size": 4,
        "kind": "target-guided",
        "seconds": 0.75,
        "maximum_states": 75000,
        "maximum_models": 16,
        "options": {
            **FIN4_ENGINE_OPTIONS,
            "target_witness_limit": 64,
        },
    },
    {
        "name": "fin4-medium",
        "domain_size": 4,
        "kind": "target-guided",
        "seconds": 3.0,
        "maximum_states": 400000,
        "maximum_models": 64,
        "options": {
            **FIN4_ENGINE_OPTIONS,
            "target_witness_limit": 256,
        },
    },
    {
        "name": "fin4-deep-diagnostic",
        "domain_size": 4,
        "kind": "target-guided",
        "seconds": 15.0,
        "maximum_states": 2000000,
        "maximum_models": 256,
        "options": {
            **FIN4_ENGINE_OPTIONS,
            "target_witness_limit": 256,
        },
        "production_eligible": False,
    },
)

# The original content-hash holdout contained no remaining FALSE
# opportunities. A later sealed external audit over 40 previously unused
# order->=4 FALSE opportunities and 40 matched TRUE controls promoted the
# frozen probe without changing its configuration. Fast added external audit
# recall, but no production gain, so the minimization rule keeps it diagnostic.
PROMOTED_FIN4_PORTFOLIO = (FIN4_PORTFOLIO[0],)

# Order five is routed only to the structurally compressed 3-source-variable
# / 2-target-variable phenotype.  It uses the same generic engine, replay, and
# certificate path as Fin 2--4; only the table dimension changes.
PROMOTED_FIN5_PORTFOLIO = ({
    "name": "fin5-compression",
    "domain_size": 5,
    "seconds": 60.0,
    "maximum_states": 5000000,
    "maximum_models": 128,
    "options": {
        **FIN4_ENGINE_OPTIONS,
        "target_witness_limit": 8,
    },
},)

# Development gains were both found by fast. Medium and complete enumeration
# added no marginal accepted case, so only the target-guided engine advances
# to untouched holdout.
PROMOTED_FINITE_MODEL_PORTFOLIO = (FINITE_MODEL_PORTFOLIO[0],)


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
    if isinstance(search, ContextualSearch):
        payload.update({
            "narrowing_successors": search.narrowing_successors,
            "overlap_candidates": search.overlap_candidates,
            "overlaps_added": search.overlaps_added,
            "overlap_depths": search.overlap_depth_counts,
            "missing_target_introduced": search.missing_target_introduced,
            "components_joined": search.components_joined,
            "term_size_rejections": search.term_size_rejections,
            "variable_overlap_suppressed": search.variable_overlap_suppressed,
        })
    print(
        "MATHGRAPH_METRICS " + json.dumps(payload, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )


def report_normalization(
    search, portfolio, found, replay_seconds=0.0, certificate_bytes=0,
    proof_nodes=0,
):
    payload = {
        "portfolio": portfolio,
        "found": bool(found),
        "source_instances_generated": search.source_instances_generated,
        "congruence_candidates": search.congruence_candidates,
        "overlap_candidates": search.overlap_candidates,
        "composed_consequences": search.composed_consequences,
        "replayed_candidate_equalities": search.replayed_candidates,
        "replay_failures": search.replay_failures,
        "decreasing_rules": search.decreasing_rules,
        "nonorientable_equalities": search.nonorientable_equalities,
        "alpha_duplicates_removed": search.alpha_duplicates_removed,
        "subsumed_rules_removed": search.subsumed_rules_removed,
        "selected_rules": len(search.selected_rules),
        "local_critical_pairs": search.local_critical_pairs,
        "joined_critical_pairs": search.joined_critical_pairs,
        "unresolved_critical_pairs": search.unresolved_critical_pairs,
        "left_normalization_steps": search.left_steps,
        "right_normalization_steps": search.right_steps,
        "maximum_trace_length": max(search.left_steps, search.right_steps),
        "normal_form_equality_hits": search.normal_form_hits,
        "distinct_normal_form_abstentions": search.distinct_normal_forms,
        "normalization_budget_exits": search.normalization_budget_exits,
        "consequence_budget_exits": search.consequence_budget_exits,
        "proof_dag_nodes": proof_nodes,
        "certificate_bytes": certificate_bytes,
        "replay_seconds": round(replay_seconds, 6),
        "exhaustion": search.exhaustion,
    }
    print(
        "MATHGRAPH_METRICS " + json.dumps(payload, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )


def report_bridge_ir(
    search, portfolio, found, replay_seconds=0.0, certificate_bytes=0,
    proof_nodes=0,
):
    attempts = search.bridge_states_created
    payload = {
        "portfolio": portfolio,
        "found": bool(found),
        "bridge_equality_candidates": search.bridge_equality_candidates,
        "replayed_bridge_equalities": search.replayed_bridge_equalities,
        "bridge_replay_failures": search.bridge_replay_failures,
        "bridge_matches_attempted": search.bridge_matches_attempted,
        "repeated_variable_rejections":
            search.repeated_variable_rejections,
        "unbound_variable_rejections": search.unbound_variable_rejections,
        "bridge_states_created": attempts,
        "bridge_states_deduplicated": search.bridge_states_deduplicated,
        "bridge_states_pruned_no_activation":
            search.bridge_states_pruned_no_activation,
        "bridge_cycles_suppressed": search.bridge_cycles_suppressed,
        "reverse_rule_expansions": search.reverse_rule_expansions,
        "nonorientable_equality_bridges": search.nonorientable_bridges,
        "anti_unification_proposals": search.anti_unification_proposals,
        "anti_unification_replayed": search.anti_unification_replayed,
        "maximum_bridge_depth": search.maximum_bridge_depth,
        "maximum_term_growth": search.maximum_term_growth,
        "initial_normalizer_matches": search.initial_normalizer_matches,
        "post_bridge_normalizer_matches":
            search.post_bridge_normalizer_matches,
        "no_match_to_match_activations": search.no_match_activations,
        "normalization_steps_after_activation":
            search.normalization_steps_after_activation,
        "exact_shared_normal_form_hits": search.shared_normal_form_hits,
        "activated_distinct_normal_forms":
            search.activated_distinct_normal_forms,
        "activation_to_proof_rate": round(
            search.shared_normal_form_hits / search.no_match_activations, 6
        ) if search.no_match_activations else 0.0,
        "proof_dag_nodes": proof_nodes,
        "certificate_bytes": certificate_bytes,
        "replay_seconds": round(replay_seconds, 6),
        "deadline_exits": search.deadline_exits,
        "state_budget_exits": search.state_budget_exits,
        "exhaustion": search.exhaustion,
    }
    print(
        "MATHGRAPH_METRICS " + json.dumps(payload, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )


def report_finite_model(
    search, engine, found, replay_seconds=0.0, certificate_bytes=0
):
    payload = {
        "portfolio": engine,
        "domain_size": search.domain_size,
        "found": bool(found),
        "complete_tables": search.complete_tables,
        "partial_states": search.partial_states,
        "source_assignments_evaluated": search.source_assignments_evaluated,
        "early_source_prunes": search.early_source_prunes,
        "target_witnesses_tested": search.target_witnesses_tested,
        "symmetry_duplicates": search.symmetry_duplicates,
        "source_models": search.source_models,
        "target_falsifying_models": search.target_falsifying_models,
        "retained_models": len(search.model_bank),
        "propagation_rounds": search.propagation_rounds,
        "domain_reductions": search.domain_reductions,
        "mrv_reductions": search.mrv_reductions,
        "nogoods_learned": search.nogoods_learned,
        "nogoods_reused": search.nogoods_reused,
        "symmetry_branch_prunes": search.symmetry_branch_prunes,
        "branch_choices": search.branch_choices,
        "branch_values": search.branch_values,
        "mean_branch_factor": round(
            search.branch_values / search.branch_choices, 6
        ) if search.branch_choices else 0.0,
        "maximum_depth": search.maximum_depth,
        "constraint_evaluations": search.constraint_evaluations,
        "term_support_evaluations": search.term_support_evaluations,
        "support_cache_hits": search.support_cache_hits,
        "forced_assignments": search.forced_assignments,
        "support_disjoint_contradictions":
            search.support_disjoint_contradictions,
        "source_contradictions": search.source_contradictions,
        "target_contradictions": search.target_contradictions,
        "target_support_disjoint_guaranteed":
            search.target_support_disjoint_guaranteed,
        "nogoods_minimized": search.nogoods_minimized,
        "nogood_causes": search.nogood_causes,
        "symmetry_permutations_tested":
            search.symmetry_permutations_tested,
        "symmetry_seconds": round(search.symmetry_seconds, 6),
        "propagation_seconds": round(search.propagation_seconds, 6),
        "activity_seconds": round(search.activity_seconds, 6),
        "nogood_seconds": round(search.nogood_seconds, 6),
        "canonicalization_seconds":
            round(search.canonicalization_seconds, 6),
        "first_source_model_seconds": (
            round(search.first_source_model_seconds, 6)
            if search.first_source_model_seconds is not None else None
        ),
        "target_witnesses_fully_searched":
            search.target_witnesses_fully_searched,
        "complete": search.complete,
        "exhaustion": search.exhaustion,
        "replay_seconds": round(replay_seconds, 6),
        "certificate_bytes": certificate_bytes,
    }
    print(
        "MATHGRAPH_METRICS " + json.dumps(payload, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )


def proof_node_ids(nodes, root):
    needed = set()
    stack = [root]
    while stack:
        node_id = stack.pop()
        if node_id in needed:
            continue
        needed.add(node_id)
        stack.extend(nodes[node_id].parents)
    return needed


def finish_dag_candidate(
    source, target, search, found, portfolio, required_constructor=None
):
    if found is None:
        report_search(search, portfolio, False)
        return False
    nodes, root = found
    needed = proof_node_ids(nodes, root)
    if required_constructor is not None and not any(
        nodes[node_id].constructor == required_constructor
        for node_id in needed
    ):
        report_search(search, portfolio, False)
        return False
    replay_start = time.monotonic()
    replayed = replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=search.max_term_size,
        maximum_nodes=search.max_derivation_nodes,
    )
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


def finish_normalization_candidate(source, target, search, found, portfolio):
    if found is None:
        report_normalization(search, portfolio, False)
        return False
    nodes, root = found
    replay_start = time.monotonic()
    replayed = replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=search.configuration["maximum_term_size"],
        maximum_nodes=search.configuration["maximum_proof_nodes"],
    )
    replay_seconds = time.monotonic() - replay_start
    if not replayed or (nodes[root].lhs, nodes[root].rhs) != target[:2]:
        report_normalization(
            search, portfolio, False, replay_seconds,
            proof_nodes=len(proof_node_ids(nodes, root)),
        )
        return False
    code, proof_nodes = make_dag_certificate(target, nodes, root)
    code_bytes = len(code.encode("utf-8"))
    report_normalization(
        search, portfolio, True, replay_seconds, code_bytes, proof_nodes
    )
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("true", code).get("status") == "accepted"


def finish_compact_superposition_candidate(source, target, search, recipe):
    if recipe is None:
        return False
    try:
        nodes, root = search.compile(recipe)
    except (KeyError, MemoryError, RecursionError, TypeError, ValueError):
        return False
    replayed = replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=search.limits.get(
            "maximum_replay_term_size",
            search.limits["maximum_term_size"],
        ),
        maximum_nodes=search.limits["maximum_proof_nodes"],
    )
    if not replayed or (nodes[root].lhs, nodes[root].rhs) != target[:2]:
        return False
    code, proof_nodes = make_dag_certificate(target, nodes, root)
    code_bytes = len(code.encode("utf-8"))
    print(
        "MATHGRAPH_METRICS " + json.dumps({
            "portfolio": "compact-superposition-probe",
            "found": True,
            "clauses": len(search.clauses),
            "rounds": search.rounds,
            "superpositions": search.superpositions,
            "reductions": search.reductions,
            "proof_nodes": proof_nodes,
            "certificate_bytes": code_bytes,
        }, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )
    # The official intake limit is 100 KB; retain the solver's stricter
    # historical 50 KB production margin.
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("true", code).get("status") == "accepted"


class RigidSuperpositionModule:
    """Make target variables rigid while retaining schematic source variables."""

    EqualityNode = EqualityNode

    @staticmethod
    def rigid(term):
        return term[0] == "var" and term[1].startswith("@")

    @classmethod
    def term_variables(cls, term):
        return {
            variable for variable in term_variables(term)
            if not variable.startswith("@")
        }

    @classmethod
    def substitute_partial(cls, term, mapping):
        if term[0] == "var":
            return term if cls.rigid(term) else mapping.get(term[1], term)
        return (
            "op",
            cls.substitute_partial(term[1], mapping),
            cls.substitute_partial(term[2], mapping),
        )

    @classmethod
    def apply(cls, term, substitution, visiting=None):
        visiting = set() if visiting is None else visiting
        if term[0] == "var":
            if cls.rigid(term) or term[1] not in substitution:
                return term
            if term[1] in visiting:
                return term
            return cls.apply(
                substitution[term[1]], substitution, visiting | {term[1]}
            )
        return (
            "op",
            cls.apply(term[1], substitution, visiting),
            cls.apply(term[2], substitution, visiting),
        )

    @classmethod
    def occurs(cls, variable, term, substitution):
        term = cls.apply(term, substitution)
        if term[0] == "var":
            return not cls.rigid(term) and term[1] == variable
        return (
            cls.occurs(variable, term[1], substitution)
            or cls.occurs(variable, term[2], substitution)
        )

    @classmethod
    def replace_variable(cls, term, variable, replacement):
        if term[0] == "var":
            return (
                replacement
                if not cls.rigid(term) and term[1] == variable
                else term
            )
        return (
            "op",
            cls.replace_variable(term[1], variable, replacement),
            cls.replace_variable(term[2], variable, replacement),
        )

    @classmethod
    def unify_terms(cls, left, right):
        substitution = {}
        pending = [(left, right)]
        while pending:
            first, second = pending.pop()
            first = cls.apply(first, substitution)
            second = cls.apply(second, substitution)
            if first == second:
                continue
            if first[0] == "var" and not cls.rigid(first):
                if cls.occurs(first[1], second, substitution):
                    return None
                substitution = {
                    variable: cls.replace_variable(
                        value, first[1], second
                    )
                    for variable, value in substitution.items()
                }
                substitution[first[1]] = second
                continue
            if second[0] == "var" and not cls.rigid(second):
                if cls.occurs(second[1], first, substitution):
                    return None
                substitution = {
                    variable: cls.replace_variable(
                        value, second[1], first
                    )
                    for variable, value in substitution.items()
                }
                substitution[second[1]] = first
                continue
            if first[0] != "op" or second[0] != "op":
                return None
            pending.extend(((first[1], second[1]), (first[2], second[2])))
        return substitution

    @classmethod
    def match_term(cls, pattern, concrete, mapping):
        if pattern[0] == "var":
            if cls.rigid(pattern):
                return pattern == concrete
            previous = mapping.get(pattern[1])
            if previous is None:
                mapping[pattern[1]] = concrete
                return True
            return previous == concrete
        return (
            concrete[0] == "op"
            and cls.match_term(pattern[1], concrete[1], mapping)
            and cls.match_term(pattern[2], concrete[2], mapping)
        )

    @classmethod
    def alpha_canonical_term(cls, term, names):
        if cls.rigid(term):
            return term
        if term[0] == "var":
            if term[1] not in names:
                names[term[1]] = "v" + str(len(names))
            return ("var", names[term[1]])
        return (
            "op",
            cls.alpha_canonical_term(term[1], names),
            cls.alpha_canonical_term(term[2], names),
        )

    def __getattr__(self, name):
        return globals()[name]


class TargetGroundedRefutation:
    """A bounded unit-superposition refutation of a rigid target disequality."""

    def __init__(self, source, target, deadline, limits):
        self.source = source
        self.target = target
        self.constants = {}
        self.reverse_constants = {}
        rigid_target = (
            self.name_target(target[0], "L"),
            self.name_target(target[1], "R"),
            target[2],
        )
        self.search = CompactSuperposition(
            RigidSuperpositionModule(),
            source,
            rigid_target,
            deadline,
            limits,
        )
        for constant, term in sorted(self.reverse_constants.items()):
            self.search.add_clause(Recipe(
                term, ("var", constant), "reflexivity"
            ))

    @classmethod
    def encode_rigid(cls, term):
        if term[0] == "var":
            return ("var", "@" + term[1])
        return (
            "op",
            cls.encode_rigid(term[1]),
            cls.encode_rigid(term[2]),
        )

    def name_target(self, term, prefix):
        encoded = self.encode_rigid(term)
        for index, subterm in enumerate(walk_subterms(encoded)):
            name = "@" + prefix + str(index)
            self.constants[subterm] = name
            self.reverse_constants[name] = subterm
        return ("var", self.constants[encoded])

    def inline(self, term):
        if term[0] == "var":
            if term[1] in self.reverse_constants:
                return self.inline(self.reverse_constants[term[1]])
            if term[1].startswith("@"):
                return ("var", term[1][1:])
            return term
        return ("op", self.inline(term[1]), self.inline(term[2]))

    def inline_recipe(self, recipe, cache=None):
        cache = {} if cache is None else cache
        if id(recipe) in cache:
            return cache[id(recipe)]
        parents = tuple(
            self.inline_recipe(parent, cache) for parent in recipe.parents
        )
        data = recipe.data
        if recipe.kind == "source":
            substitution, reverse = data
            data = (
                tuple(
                    (variable, self.inline(value))
                    for variable, value in substitution
                ),
                reverse,
            )
        elif recipe.kind == "instantiate":
            data = tuple(
                (variable, self.inline(value)) for variable, value in data
            )
        elif recipe.kind == "congruence":
            data = (data[0], self.inline(data[1]))
        result = Recipe(
            self.inline(recipe.lhs),
            self.inline(recipe.rhs),
            recipe.kind,
            parents,
            data,
        )
        cache[id(recipe)] = result
        return result

    def solve(self):
        recipe = self.search.solve()
        if recipe is None:
            return None
        recipe = self.inline_recipe(recipe)
        compiler = CompactSuperposition(
            sys.modules[__name__],
            self.source,
            self.target,
            time.monotonic() + 1,
            self.search.limits,
        )
        nodes, root = compiler.compile(recipe)
        if (
            (nodes[root].lhs, nodes[root].rhs) != self.target[:2]
            or not replay_dag(
                self.source,
                nodes,
                root,
                maximum_term_size=self.search.limits[
                    "maximum_replay_term_size"
                ],
                maximum_nodes=self.search.limits["maximum_proof_nodes"],
            )
        ):
            return None
        return nodes, root


def finish_target_grounded_candidate(source, target, engine, found):
    if found is None:
        return False
    nodes, root = found
    code, proof_nodes = make_dag_certificate(target, nodes, root)
    code_bytes = len(code.encode("utf-8"))
    print(
        "MATHGRAPH_METRICS " + json.dumps({
            "portfolio": "target-grounded-refutation",
            "found": True,
            "clauses": len(engine.search.clauses),
            "rounds": engine.search.rounds,
            "superpositions": engine.search.superpositions,
            "proof_nodes": proof_nodes,
            "certificate_bytes": code_bytes,
        }, separators=(",", ":")),
        file=sys.stderr,
        flush=True,
    )
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("true", code).get("status") == "accepted"


def finish_bridge_ir_candidate(source, target, search, found, portfolio):
    if found is None:
        report_bridge_ir(search, portfolio, False)
        return False
    nodes, root = found
    replay_start = time.monotonic()
    replayed = replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=
            search.normalizer.configuration["maximum_term_size"],
        maximum_nodes=search.configuration["maximum_proof_nodes"],
    )
    replay_seconds = time.monotonic() - replay_start
    proof_nodes = len(proof_node_ids(nodes, root))
    if not replayed or (nodes[root].lhs, nodes[root].rhs) != target[:2]:
        report_bridge_ir(
            search, portfolio, False, replay_seconds,
            proof_nodes=proof_nodes,
        )
        return False
    code, proof_nodes = make_dag_certificate(target, nodes, root)
    code_bytes = len(code.encode("utf-8"))
    report_bridge_ir(
        search, portfolio, True, replay_seconds, code_bytes, proof_nodes
    )
    if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("true", code).get("status") == "accepted"


def finish_quotient_matcher_candidate(source, target, search, found):
    if found is None:
        return False
    nodes, root = found
    if not replay_dag(
        source, nodes, root, maximum_term_size=search.max_term_size
    ):
        return False
    if (nodes[root].lhs, nodes[root].rhs) != target[:2]:
        return False
    needed = proof_node_ids(nodes, root)
    if not any(
        nodes[node_id].constructor == "quotient-matcher"
        for node_id in needed
    ):
        return False
    code, _ = make_dag_certificate(target, nodes, root)
    if len(code.encode("utf-8")) > EqualitySearch.MAX_CERTIFICATE_BYTES:
        return False
    return judge("true", code).get("status") == "accepted"


def run_contextual_portfolio(source, target, timeout):
    for configuration in PROMOTED_CONTEXTUAL_PORTFOLIO:
        seconds = min(
            configuration["seconds"], max(0.1, timeout / 20.0)
        )
        contextual_deadline = time.monotonic() + seconds
        try:
            search = ContextualSearch(
                source, target, contextual_deadline, configuration["limits"]
            )
            if configuration["kind"] == "target-narrowing":
                found = search.solve_target_narrowing(
                    configuration["maximum_depth"],
                    configuration["branching"],
                    configuration["maximum_terms"],
                    configuration["maximum_context_depth"],
                )
            else:
                found = search.solve_contextual_overlap(
                    configuration["maximum_overlap_depth"],
                    configuration["maximum_context_depth"],
                    configuration["maximum_source_instances"],
                    configuration["maximum_candidates"],
                    configuration["maximum_new_nodes"],
                )
        except (
            KeyError, IndexError, MemoryError, RecursionError, TypeError,
            ValueError,
        ):
            continue
        if found is not None and finish_dag_candidate(
            source,
            target,
            search,
            found,
            configuration["name"],
            required_constructor=configuration["kind"],
        ):
            return True
        if found is None:
            report_search(search, configuration["name"], False)
    return False


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

    collapsed = variable_omission_collapse(source, target)
    if collapsed is not None:
        nodes, root = collapsed
        code, _ = make_dag_certificate(target, nodes, root)
        if (
            len(code.encode("utf-8")) <= EqualitySearch.MAX_CERTIFICATE_BYTES
            and judge("true", code).get("status") == "accepted"
        ):
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

    compact_limits = dict(COMPACT_SUPERPOSITION_PROBE)
    compact_seconds = min(
        compact_limits["seconds"], max(0.05, timeout / 100.0)
    )
    try:
        compact_search = CompactSuperposition(
            sys.modules[__name__],
            source,
            target,
            time.monotonic() + compact_seconds,
            compact_limits,
        )
        compact_recipe = compact_search.solve()
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError,
        ValueError,
    ):
        compact_recipe = None
    if compact_recipe is not None and finish_compact_superposition_candidate(
        source, target, compact_search, compact_recipe
    ):
        return

    # BridgeIR is a TRUE-side representation constructor. Its production
    # portfolio remains empty unless a sealed external audit promotes it.
    for configuration in PROMOTED_BRIDGE_IR_PORTFOLIO:
        seconds = min(
            configuration["seconds"], max(0.1, timeout / 20.0)
        )
        try:
            search = BridgeIR(
                source,
                target,
                time.monotonic() + seconds,
                configuration,
            )
            found = search.solve()
        except (
            KeyError, IndexError, MemoryError, RecursionError, TypeError,
            ValueError,
        ):
            continue
        if finish_bridge_ir_candidate(
            source, target, search, found, configuration["name"]
        ):
            return

    # Fin 2 uses the same generic finite-model evaluator, replay, symmetry,
    # statistics, and certificate path as every larger domain.
    deadline = time.monotonic() + min(1.0, max(0.05, timeout / 20.0))
    try:
        fin2_search = FiniteModelEngine(
            2, source, target, deadline, 0, 16
        )
        fin2_found = fin2_search.search_complete_enumeration(
            canonical_only=False
        )
    except (KeyError, IndexError, RecursionError, TypeError, ValueError):
        return
    if fin2_found is not None:
        if finish_finite_candidate(
            source, target, fin2_search, fin2_found, "fin2-complete"
        ):
            return
    else:
        report_finite_model(fin2_search, "fin2-complete", False)

    # This hook precedes re-entry because that was the cheaper development
    # ordering. The frozen portfolio is empty after its zero-gain holdout.
    if run_contextual_portfolio(source, target, timeout):
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

    for configuration in PROMOTED_FINITE_MODEL_PORTFOLIO:
        seconds = min(
            configuration["seconds"], max(0.1, timeout / 20.0)
        )
        finite_deadline = time.monotonic() + seconds
        try:
            search = FiniteModelEngine(
                configuration["domain_size"],
                source,
                target,
                finite_deadline,
                configuration["maximum_states"],
                configuration["maximum_models"],
            )
            if configuration["kind"] == "target-guided":
                found = search.search_target_guided()
            elif configuration["kind"] == "partial-source":
                found = search.search_partial_source_models()
            else:
                found = search.search_complete_enumeration()
        except (
            KeyError, IndexError, MemoryError, RecursionError, TypeError,
            ValueError,
        ):
            continue
        if found is not None and finish_finite_candidate(
            source, target, search, found, configuration["name"]
        ):
            return
        if found is None:
            report_finite_model(search, configuration["name"], False)

    for configuration in PROMOTED_FIN4_PORTFOLIO:
        seconds = min(
            configuration["seconds"], max(0.1, timeout / 20.0)
        )
        finite_deadline = time.monotonic() + seconds
        try:
            search = FiniteModelEngine(
                configuration["domain_size"],
                source,
                target,
                finite_deadline,
                configuration["maximum_states"],
                configuration["maximum_models"],
                options=configuration["options"],
            )
            found = search.search_target_guided()
        except (
            KeyError, IndexError, MemoryError, RecursionError, TypeError,
            ValueError,
        ):
            continue
        if found is not None and finish_finite_candidate(
            source, target, search, found, configuration["name"]
        ):
            return
        if found is None:
            report_finite_model(search, configuration["name"], False)

    if len(source[2]) == 3 and len(target[2]) == 2:
        for configuration in PROMOTED_FIN5_PORTFOLIO:
            seconds = min(
                configuration["seconds"], max(0.1, timeout / 20.0)
            )
            try:
                search = FiniteModelEngine(
                    configuration["domain_size"],
                    source,
                    target,
                    time.monotonic() + seconds,
                    configuration["maximum_states"],
                    configuration["maximum_models"],
                    options=configuration["options"],
                )
                found = search.search_target_guided()
            except (
                KeyError, IndexError, MemoryError, RecursionError, TypeError,
                ValueError,
            ):
                continue
            if found is not None and finish_finite_candidate(
                source, target, search, found, configuration["name"]
            ):
                return
            if found is None:
                report_finite_model(search, configuration["name"], False)

    # A tiny equation-blind bank of crossed-coordinate finite geometries.
    # It runs after the cheaper promoted CSP routes so it cannot replace an
    # existing small certificate with a slower large-carrier certificate.
    try:
        structured_found = structured_model_candidate(source, target)
    except (IndexError, MemoryError, RecursionError, TypeError, ValueError):
        structured_found = None
    if finish_structured_model_candidate(
        source, target, structured_found
    ):
        return

    # Match source-law instances modulo replayed equality classes.  This route
    # remains bounded, reconstructs every representative replacement, and
    # independently replays the complete proof DAG before asking Lean.
    quotient_seconds = min(3.0, max(0.1, timeout / 20.0))
    try:
        quotient_search = QuotientMatcher(
            source, target, time.monotonic() + quotient_seconds
        )
        quotient_found = quotient_search.solve()
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError,
        ValueError,
    ):
        quotient_found = None
    if quotient_found is not None and finish_quotient_matcher_candidate(
        source, target, quotient_search, quotient_found
    ):
        return

    for configuration in PROMOTED_NORMALIZATION_PORTFOLIO:
        seconds = min(
            configuration["seconds"], max(0.1, timeout / 20.0)
        )
        try:
            search = EquationalNormalizer(
                source,
                target,
                time.monotonic() + seconds,
                configuration,
            )
            found = search.solve()
        except (
            KeyError, IndexError, MemoryError, RecursionError, TypeError,
            ValueError,
        ):
            continue
        if finish_normalization_candidate(
            source, target, search, found, configuration["name"]
        ):
            return

    # Ground the target disequality while keeping source variables schematic.
    # This is intentionally last: earlier proof and finite-model routes avoid
    # paying its bounded 0.5 second cost on already resolved implications.
    grounded_limits = dict(COMPACT_SUPERPOSITION_PROBE)
    grounded_limits.update({
        "seconds": 0.5,
        "maximum_term_size": 45,
        "maximum_replay_term_size": 160,
        "maximum_depth": 10,
        "maximum_rules": 192,
        "maximum_rounds": 16,
        "new_clauses_per_round": 128,
        "maximum_clauses": 2000,
        "normalization_steps": 96,
        "maximum_proof_nodes": 20000,
    })
    grounded_seconds = min(0.5, max(0.05, timeout / 100.0))
    grounded_search = None
    try:
        grounded_search = TargetGroundedRefutation(
            source,
            target,
            time.monotonic() + grounded_seconds,
            grounded_limits,
        )
        grounded_found = grounded_search.solve()
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError,
        ValueError,
    ):
        grounded_found = None
    if finish_target_grounded_candidate(
        source, target, grounded_search, grounded_found
    ):
        return


    stair_seconds = min(2.0, max(0.1, timeout / 50.0))
    stair_found = external_paramodulation_candidate(problem, stair_seconds)
    if finish_external_paramodulation_candidate(stair_found):
        return

    # Unresolved: EOF is intentional. Never guess and never ask an LLM.


def main():
    run_solo()


if __name__ == "__main__":
    main()
