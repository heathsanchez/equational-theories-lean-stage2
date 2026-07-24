"""Deterministic MathGraph Stage 2 solver.

The submission is deliberately fail-closed: it asks the official judge only
about certificates reconstructed from the incoming equation strings, and
exits without a verdict when no replayable certificate is available.
"""

import json
import sys
import time
import heapq
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
        self.full_domain = (1 << domain_size) - 1
        self.source_compiled = compile_equation(source)
        self.target_compiled = compile_equation(target)
        self.source_assignments = ordered_assignments(
            self.source_compiled, domain_size
        )
        self.target_assignments = self.rank_target_assignments()
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
        self.static_cell_frequency = self.cell_frequency(
            self.source_compiled, self.source_assignments
        )
        self.target_cell_frequency = self.cell_frequency(
            self.target_compiled, self.target_assignments
        )
        self.constraint_graph = self.build_constraints()

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

    def rank_target_assignments(self):
        assignments = list(
            product(
                range(self.domain_size),
                repeat=len(self.target_compiled[3]),
            )
        )
        asymmetry = structural_distance(self.target[0], self.target[1])

        def key(assignment):
            dependencies = set()
            nodes = self.target_compiled[0]
            for node in nodes:
                if node[0] != "operation":
                    continue
                left, right = nodes[node[1]], nodes[node[2]]
                if left[0] == "variable" and right[0] == "variable":
                    dependencies.add(
                        self.domain_size * assignment[left[1]]
                        + assignment[right[1]]
                    )
            return (
                len(set(assignment)),
                len(dependencies),
                -asymmetry,
                assignment,
            )

        assignments.sort(key=key)
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
        canonical = self.canonicalize(table)
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
        domains[cell] = restricted
        self.domain_reductions += previous.bit_count() - restricted.bit_count()
        return True, True

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

    def propagate_disequality(self, domains, assignment):
        left, right = evaluate_compiled_domains(
            self.target_compiled,
            assignment,
            domains,
            self.domain_size,
        )
        left_domain, left_cell = left
        right_domain, right_cell = right
        if left_domain & right_domain == 0:
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

    def propagate(self, domains, target_assignment=None):
        """Reach a fixed point using only sound equality/disequality rules."""
        changed = True
        while changed:
            self.propagation_rounds += 1
            changed = False
            for assignment in self.source_assignments:
                self.source_assignments_evaluated += 1
                left, right = evaluate_compiled_domains(
                    self.source_compiled,
                    assignment,
                    domains,
                    self.domain_size,
                )
                valid, reduced = self.propagate_equality(
                    domains, left, right
                )
                if not valid:
                    self.early_source_prunes += 1
                    return False, "source"
                changed |= reduced
            if target_assignment is not None:
                valid, reduced = self.propagate_disequality(
                    domains, target_assignment
                )
                if not valid:
                    return False, "target"
                changed |= reduced
        return True, None

    def choose_cell(self, domains, target_assignment=None):
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
        return selected

    def assigned_facts(self, domains):
        return frozenset(
            (cell, value)
            for cell, domain in enumerate(domains)
            for value in (singleton_value(domain),)
            if value is not None
        )

    def nogood_applies(self, facts, target_assignment):
        for scope, nogood in self.nogoods:
            if scope is not None and scope != target_assignment:
                continue
            if nogood <= facts:
                self.nogoods_reused += 1
                return True
        return False

    def learn_nogood(self, facts, scope):
        record = (scope, facts)
        if (
            len(self.nogoods) < self.maximum_nogoods
            and record not in self.nogoods
        ):
            self.nogoods.append(record)
            self.nogoods_learned += 1

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
        constrained = {
            cell for cell, domain in enumerate(domains)
            if domain != self.full_domain
        }
        if not constrained:
            return False
        current = tuple(domains)
        used = set(target_assignment or ())
        for permutation in permutations(range(self.domain_size)):
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
                return True
        return False

    def domains_to_table(self, domains):
        table = tuple(singleton_value(domain) for domain in domains)
        return table if all(value is not None for value in table) else None

    def branch(self, domains, target_assignment=None, depth=0):
        if self.expired():
            self.exhaustion = "timeout"
            return None
        if self.partial_states >= self.maximum_states:
            self.exhaustion = "partial state budget exhausted"
            return None
        self.partial_states += 1
        self.maximum_depth = max(self.maximum_depth, depth)
        current = list(domains)
        facts_before = self.assigned_facts(current)
        if self.nogood_applies(facts_before, target_assignment):
            return None
        valid, contradiction = self.propagate(current, target_assignment)
        if not valid:
            scope = None if contradiction == "source" else target_assignment
            self.learn_nogood(self.assigned_facts(current), scope)
            return None
        if self.partial_symmetry_prunable(current, target_assignment):
            return None
        complete = self.domains_to_table(current)
        if complete is not None:
            self.complete_tables += 1
            if not self.source_holds_complete(complete):
                return None
            self.source_models += 1
            self.retain_source_model(complete)
            witness = self.target_witness(complete, target_assignment)
            if witness is not None:
                self.target_falsifying_models += 1
                return complete, witness
            return None
        cell = self.choose_cell(current, target_assignment)
        values = [
            value for value in range(self.domain_size)
            if current[cell] & (1 << value)
        ]
        self.branch_choices += 1
        self.branch_values += len(values)
        for value in values:
            branch = list(current)
            branch[cell] = 1 << value
            found = self.branch(
                branch, target_assignment, depth=depth + 1
            )
            if found is not None:
                return found
            if self.exhaustion is not None:
                return None
        self.learn_nogood(self.assigned_facts(current), target_assignment)
        return None

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
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
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
        "maximum_depth": search.maximum_depth,
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

    # Unresolved: EOF is intentional. Never guess and never ask an LLM.


def main():
    run_solo()


if __name__ == "__main__":
    main()
