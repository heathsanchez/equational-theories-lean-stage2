#!/usr/bin/env python3
"""Research prototype: proof-producing source matching modulo verified classes."""

import argparse
import importlib.util
import json
import sys
import time
from collections import defaultdict, deque
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("quotient_matcher_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class QuotientMatcher:
    def __init__(self, module, source, target, deadline, edge_cap=256):
        self.m = module
        self.source = source
        self.target = target
        self.deadline = deadline
        config = dict(module.NORMALIZATION_PORTFOLIO[1])
        self.normalizer = module.EquationalNormalizer(
            source, target, deadline, config
        )
        self.normalizer.generate_consequences()
        self.normalizer.orient()
        self.normalizer.select_rulebook()
        self.nodes = self.normalizer.nodes
        self.base_nodes = len(self.nodes)
        if not self.nodes or not module.replay_dag(
            source, self.nodes, 0,
            maximum_term_size=config["maximum_term_size"],
        ):
            raise ValueError("normalizer proof DAG did not replay")
        self.edge_cap = min(edge_cap, len(self.nodes))
        self.parent = {}
        self.members = defaultdict(set)
        self.adjacency = defaultdict(list)
        self.matches = 0
        self.quotient_only = 0
        self.instances = 0
        self.generations = 0
        self.replay_failures = 0
        self.maximum_term_size = config["maximum_term_size"]
        self.frontiers = {
            "left": {target[0]},
            "right": {target[1]},
        }
        target_variables = set(self.target[2])
        for node_id, node in enumerate(self.nodes[:self.edge_cap]):
            if (
                set(self.m.term_variables(node.lhs)) <= target_variables
                and set(self.m.term_variables(node.rhs)) <= target_variables
            ):
                self.add_edge(node.lhs, node.rhs, node_id)
        for side in target[:2]:
            for term in module.walk_subterms(side):
                self.find(term)
        self.rebuild_members()

    def find(self, term):
        self.parent.setdefault(term, term)
        if self.parent[term] != term:
            self.parent[term] = self.find(self.parent[term])
        return self.parent[term]

    def union(self, left, right):
        a, b = self.find(left), self.find(right)
        if a == b:
            return
        if self.m.render_term(a) > self.m.render_term(b):
            a, b = b, a
        self.parent[b] = a

    def add_edge(self, left, right, node_id):
        self.adjacency[left].append((right, node_id, False))
        self.adjacency[right].append((left, node_id, True))
        self.union(left, right)

    def rebuild_members(self):
        self.members = defaultdict(set)
        for term in list(self.parent):
            self.members[self.find(term)].add(term)

    def class_members(self, term):
        root = self.find(term)
        return self.members.get(root, {term})

    def path_proof(self, start, goal):
        if start == goal:
            node_id = len(self.nodes)
            self.nodes.append(self.m.EqualityNode(start, goal, "reflexivity"))
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
                self.nodes.append(self.m.EqualityNode(
                    node.rhs, node.lhs, "symmetry", parents=(node_id,),
                    constructor="quotient-matcher-representative",
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
            self.nodes.append(self.m.EqualityNode(
                left.lhs, right.rhs, "transitivity",
                parents=(root, node_id),
                constructor="quotient-matcher-representative",
            ))
            root = new_root
        return root

    def ematch(self, pattern, concrete, mapping):
        if pattern[0] == "var":
            name = pattern[1]
            value = self.find(concrete)
            if name in mapping and mapping[name] != value:
                return []
            result = dict(mapping)
            result[name] = value
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
                key=lambda term: (
                    self.m.term_size(term), self.m.render_term(term)
                ),
            )
            for variable, eclass in mapping.items()
        }

    def compile_witness(self, pattern, witness, representatives):
        if pattern[0] == "var":
            return self.path_proof(witness[1], representatives[pattern[1]])
        _, concrete, candidate, left_witness, right_witness = witness
        prefix = self.path_proof(concrete, candidate)
        left = self.compile_witness(
            pattern[1], left_witness, representatives
        )
        right = self.compile_witness(
            pattern[2], right_witness, representatives
        )
        if prefix is None or left is None or right is None:
            return None
        left_node = self.nodes[left]
        left_lift = len(self.nodes)
        self.nodes.append(self.m.EqualityNode(
            ("op", left_node.lhs, candidate[2]),
            ("op", left_node.rhs, candidate[2]),
            "congruence on left child", parents=(left,),
            context=("left", candidate[2]),
            constructor="quotient-matcher",
        ))
        right_node = self.nodes[right]
        right_lift = len(self.nodes)
        self.nodes.append(self.m.EqualityNode(
            ("op", left_node.rhs, right_node.lhs),
            ("op", left_node.rhs, right_node.rhs),
            "congruence on right child", parents=(right,),
            context=("right", left_node.rhs),
            constructor="quotient-matcher",
        ))
        middle = len(self.nodes)
        self.nodes.append(self.m.EqualityNode(
            self.nodes[left_lift].lhs, self.nodes[right_lift].rhs,
            "transitivity", parents=(left_lift, right_lift),
            constructor="quotient-matcher",
        ))
        if self.nodes[prefix].lhs == self.nodes[prefix].rhs:
            return middle
        root = len(self.nodes)
        self.nodes.append(self.m.EqualityNode(
            self.nodes[prefix].lhs, self.nodes[middle].rhs,
            "transitivity", parents=(prefix, middle),
            constructor="quotient-matcher",
        ))
        return root

    def target_paths(self):
        for side_name in ("left", "right"):
            roots = sorted(
                self.frontiers[side_name],
                key=lambda term: (self.m.term_size(term), self.m.render_term(term)),
            )[:32]
            for root in roots:
                stack = [(root, ())]
                while stack:
                    term, path = stack.pop()
                    yield side_name, root, term, path
                    if term[0] == "op":
                        stack.append((term[2], path + ("R",)))
                        stack.append((term[1], path + ("L",)))

    def one_generation(self, maximum_instances=128):
        added = []
        candidates = []
        seen_candidates = set()
        for orientation, pattern, replacement, reverse in (
            ("forward", self.source[0], self.source[1], False),
            ("reverse", self.source[1], self.source[0], True),
        ):
            for side_name, root, concrete, path in self.target_paths():
                if time.monotonic() >= self.deadline:
                    self.rebuild_members()
                    return added
                exact_mapping = {}
                exact = self.m.match_term(pattern, concrete, exact_mapping)
                for mapping, witness in self.ematch(pattern, concrete, {}):
                    if time.monotonic() >= self.deadline:
                        self.rebuild_members()
                        return added
                    if set(mapping) != set(self.source[2]):
                        continue
                    self.matches += 1
                    if exact and set(exact_mapping) == set(self.source[2]):
                        continue
                    self.quotient_only += 1
                    representatives = self.representative_mapping(mapping)
                    target_variables = set(self.target[2])
                    if any(
                        not set(self.m.term_variables(term)) <= target_variables
                        for term in representatives.values()
                    ):
                        continue
                    instantiated_replacement = self.m.substitute(
                        replacement, representatives
                    )
                    after = self.m.replace_subterm(
                        root, path, instantiated_replacement
                    )
                    opposite = (
                        self.target[1] if side_name == "left"
                        else self.target[0]
                    )
                    key = (
                        side_name, path, instantiated_replacement,
                        tuple(sorted(representatives.items())),
                    )
                    if key in seen_candidates:
                        continue
                    seen_candidates.add(key)
                    connects_component = int(
                        self.find(after) == self.find(opposite)
                        or self.find(instantiated_replacement)
                        == self.find(opposite)
                    )
                    score = (
                        -connects_component,
                        self.m.structural_distance(after, opposite),
                        self.m.term_size(after),
                        len(path),
                        self.m.render_term(after),
                        orientation,
                    )
                    candidates.append((
                        score, side_name, pattern, replacement, reverse, root,
                        concrete, path, representatives, witness,
                    ))
                    if len(candidates) >= 4096:
                        break
                if len(candidates) >= 4096:
                    break
            if len(candidates) >= 4096:
                break
        candidates.sort(key=lambda item: item[0])
        for (
            _, side_name, pattern, replacement, reverse, root, concrete,
            path, representatives, witness,
        ) in candidates:
                    if time.monotonic() >= self.deadline:
                        self.rebuild_members()
                        return added
                    candidate_start = len(self.nodes)
                    pattern_proof = self.compile_witness(
                        pattern, witness, representatives
                    )
                    if pattern_proof is None:
                        del self.nodes[candidate_start:]
                        continue
                    instantiated_pattern = self.m.substitute(
                        pattern, representatives
                    )
                    instantiated_replacement = self.m.substitute(
                        replacement, representatives
                    )
                    if self.nodes[pattern_proof].rhs != instantiated_pattern:
                        del self.nodes[candidate_start:]
                        continue
                    source_id = len(self.nodes)
                    self.nodes.append(self.m.EqualityNode(
                        instantiated_pattern,
                        instantiated_replacement,
                        "source instance",
                        substitution=tuple(
                            (variable, representatives[variable])
                            for variable in self.source[2]
                        ),
                        orientation=reverse,
                        constructor="quotient-matcher",
                    ))
                    segment = len(self.nodes)
                    self.nodes.append(self.m.EqualityNode(
                        concrete, instantiated_replacement, "transitivity",
                        parents=(pattern_proof, source_id),
                        constructor="quotient-matcher",
                    ))
                    lifted = self.normalizer.lift_context(
                        self.nodes, segment, root, path
                    )
                    node = self.nodes[lifted]
                    if max(
                        self.m.term_size(node.lhs), self.m.term_size(node.rhs)
                    ) > self.maximum_term_size:
                        del self.nodes[candidate_start:]
                        continue
                    if not self.m.replay_dag(
                        self.source, self.nodes, lifted,
                        maximum_term_size=self.maximum_term_size,
                    ):
                        self.replay_failures += 1
                        del self.nodes[candidate_start:]
                        continue
                    self.add_edge(node.lhs, node.rhs, lifted)
                    self.frontiers[side_name].add(node.rhs)
                    added.append(lifted)
                    self.instances += 1
                    if len(added) >= maximum_instances:
                        self.rebuild_members()
                        return added
        self.rebuild_members()
        return added

    def solve(self, generations=2, maximum_instances=128):
        for generation in range(generations):
            self.generations = generation + 1
            self.one_generation(maximum_instances)
            if self.find(self.target[0]) == self.find(self.target[1]):
                root = self.path_proof(self.target[0], self.target[1])
                if root is not None and self.m.replay_dag(
                    self.source, self.nodes, root,
                    maximum_term_size=self.maximum_term_size,
                ):
                    return self.nodes, root
            if time.monotonic() >= self.deadline:
                break
        return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--id")
    parser.add_argument("--input", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--seconds", type=float, default=5.0)
    parser.add_argument("--generations", type=int, default=2)
    parser.add_argument("--instances", type=int, default=128)
    parser.add_argument("--edge-cap", type=int, default=256)
    args = parser.parse_args()
    module = load_solver()
    if args.input:
        payload = json.loads(args.input.read_text())
        rows = payload["rows"] if isinstance(payload, dict) else payload
        rows = [
            row for row in rows
            if args.id is None or row["id"] == args.id
        ]
    else:
        rows = json.loads(
            (ROOT / "examples/problems/sample_200.json").read_text()
        )
        baseline = json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "normalization_baseline_manifest.json").read_text()
        )["sample_200_accepted"]
        rows = [
            row for row in rows
            if row["id"].startswith("true_") and row["id"] not in baseline
            and (args.id is None or row["id"] == args.id)
        ]
    results = []
    for index, row in enumerate(rows, 1):
        print(f"[{index}/{len(rows)}] {row['id']}", flush=True)
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        started = time.monotonic()
        try:
            search = QuotientMatcher(
                module, source, target, started + args.seconds,
                edge_cap=args.edge_cap,
            )
            found = search.solve(args.generations, args.instances)
        except Exception as error:
            results.append({"id": row["id"], "error": repr(error)})
            continue
        record = {
            "id": row["id"],
            "found": found is not None,
            "seconds": round(time.monotonic() - started, 6),
            "matches": search.matches,
            "quotient_only": search.quotient_only,
            "instances": search.instances,
            "generations": search.generations,
            "replay_failures": search.replay_failures,
        }
        if found:
            nodes, root = found
            code, proof_nodes = module.make_dag_certificate(target, nodes, root)
            record["proof_nodes"] = proof_nodes
            record["certificate_bytes"] = len(code.encode())
            record["code"] = code
        results.append(record)
        print(json.dumps({k: v for k, v in record.items() if k != "code"}))
    payload = {"diagnostic_only": False, "rows": results}
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
