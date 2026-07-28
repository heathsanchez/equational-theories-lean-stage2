#!/usr/bin/env python3
"""Diagnostic proof-producing interreduction of symbolic consequences."""

import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def load_solver():
    path = ROOT / "submissions/mathgraph/solver.py"
    spec = importlib.util.spec_from_file_location("mathgraph_solver", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def read_rows(path):
    text = path.read_text()
    if path.suffix == ".jsonl":
        return [json.loads(line) for line in text.splitlines() if line.strip()]
    payload = json.loads(text)
    return payload["rows"] if isinstance(payload, dict) else payload


def make_search(module):
    class GoalDirectedNormalizer(module.EquationalNormalizer):
        def clone_proof(self, node_id, variable_mapping, unifier, cache):
            key = (node_id, tuple(sorted(variable_mapping)))
            if key in cache:
                return cache[key]

            def transform(term):
                return module.apply_unifier(
                    module.substitute(term, variable_mapping), unifier
                )

            node = self.nodes[node_id]
            parents = tuple(
                self.clone_proof(
                    parent, variable_mapping, unifier, cache
                )
                for parent in node.parents
            )
            context = node.context
            if context:
                context = (context[0], transform(context[1]))
            clone = module.EqualityNode(
                transform(node.lhs),
                transform(node.rhs),
                node.kind,
                parents=parents,
                substitution=tuple(
                    (variable, transform(value))
                    for variable, value in node.substitution
                ),
                orientation=node.orientation,
                context=context,
                constructor="goal-directed-superposition",
            )
            result = len(self.nodes)
            self.nodes.append(clone)
            cache[key] = result
            return result

        def add_critical_pairs(self):
            def proof_variables(node_id):
                variables = set()
                stack = [node_id]
                visited = set()
                while stack:
                    current = stack.pop()
                    if current in visited:
                        continue
                    visited.add(current)
                    node = self.nodes[current]
                    variables |= module.term_variables(node.lhs)
                    variables |= module.term_variables(node.rhs)
                    stack.extend(node.parents)
                return variables

            rules = sorted(
                self.rules,
                key=lambda rule: (
                    -self.rule_target_occurrences(rule),
                    rule.proof_cost,
                    module.term_size(rule.lhs),
                    rule.provenance,
                ),
            )[:self.configuration["superposition_rules"]]
            signatures = {
                (node.lhs, node.rhs) for node in self.nodes
            }
            added = 0
            for outer_index, outer in enumerate(rules):
                if self.expired():
                    break
                for inner_index, inner in enumerate(rules):
                    if (
                        self.expired()
                        or added >= self.configuration[
                            "superposition_candidates"
                        ]
                    ):
                        break
                    outer_map = {
                        variable: (
                            "var", f"_go{outer_index}_{offset}"
                        )
                        for offset, variable in enumerate(
                            sorted(proof_variables(outer.node_id))
                        )
                    }
                    inner_map = {
                        variable: (
                            "var", f"_gi{inner_index}_{offset}"
                        )
                        for offset, variable in enumerate(
                            sorted(proof_variables(inner.node_id))
                        )
                    }
                    outer_lhs = module.substitute(outer.lhs, outer_map)
                    outer_rhs = module.substitute(outer.rhs, outer_map)
                    inner_lhs = module.substitute(inner.lhs, inner_map)
                    inner_rhs = module.substitute(inner.rhs, inner_map)
                    for path in module.nonvariable_positions(
                        outer_lhs, maximum_depth=7, include_root=True
                    ):
                        selected = module.get_subterm(outer_lhs, path)
                        unifier = module.unify_terms(selected, inner_lhs)
                        if unifier is None:
                            continue
                        concrete_lhs = module.apply_unifier(
                            outer_lhs, unifier
                        )
                        concrete_other = module.apply_unifier(
                            outer_rhs, unifier
                        )
                        concrete_replacement = module.apply_unifier(
                            inner_rhs, unifier
                        )
                        changed = module.replace_subterm(
                            concrete_lhs, path, concrete_replacement
                        )
                        if (
                            concrete_other == changed
                            or max(
                                module.term_size(concrete_other),
                                module.term_size(changed),
                            ) > self.configuration["maximum_term_size"]
                            or (concrete_other, changed) in signatures
                            or (changed, concrete_other) in signatures
                        ):
                            continue
                        start = len(self.nodes)
                        outer_id = self.clone_proof(
                            outer.node_id, outer_map, unifier, {}
                        )
                        inner_id = self.clone_proof(
                            inner.node_id, inner_map, unifier, {}
                        )
                        outer_reverse = len(self.nodes)
                        self.nodes.append(module.EqualityNode(
                            self.nodes[outer_id].rhs,
                            self.nodes[outer_id].lhs,
                            "symmetry",
                            parents=(outer_id,),
                            constructor="goal-directed-superposition",
                        ))
                        try:
                            lifted = self.lift_context(
                                self.nodes, inner_id, concrete_lhs, path
                            )
                        except ValueError:
                            del self.nodes[start:]
                            continue
                        root = len(self.nodes)
                        self.nodes.append(module.EqualityNode(
                            concrete_other,
                            changed,
                            "transitivity",
                            parents=(outer_reverse, lifted),
                            constructor="goal-directed-superposition",
                        ))
                        if not module.replay_dag(
                            self.source,
                            self.nodes,
                            root,
                            maximum_term_size=self.configuration[
                                "maximum_term_size"
                            ],
                            maximum_nodes=self.configuration[
                                "maximum_proof_nodes"
                            ],
                        ):
                            del self.nodes[start:]
                            continue
                        signatures.add((concrete_other, changed))
                        added += 1
                        if added >= self.configuration[
                            "superposition_candidates"
                        ]:
                            break
            return added

        def append_interreduced(self, node_id):
            node = self.nodes[node_id]
            left_nf, left_trace, left_exhausted = self.normalize(node.lhs)
            right_nf, right_trace, right_exhausted = self.normalize(node.rhs)
            if left_exhausted or right_exhausted:
                return False
            if left_nf == node.lhs and right_nf == node.rhs:
                return False
            start = len(self.nodes)
            try:
                left_root = self.compile_trace(
                    node.lhs, left_trace, self.nodes
                )
                right_root = self.compile_trace(
                    node.rhs, right_trace, self.nodes
                )
                left_reverse = len(self.nodes)
                self.nodes.append(module.EqualityNode(
                    left_nf,
                    node.lhs,
                    "symmetry",
                    parents=(left_root,),
                    constructor="goal-directed-interreduction",
                ))
                prefix = len(self.nodes)
                self.nodes.append(module.EqualityNode(
                    left_nf,
                    node.rhs,
                    "transitivity",
                    parents=(left_reverse, node_id),
                    constructor="goal-directed-interreduction",
                ))
                root = len(self.nodes)
                self.nodes.append(module.EqualityNode(
                    left_nf,
                    right_nf,
                    "transitivity",
                    parents=(prefix, right_root),
                    constructor="goal-directed-interreduction",
                ))
            except (KeyError, TypeError, ValueError):
                del self.nodes[start:]
                return False
            if (
                left_nf == right_nf
                or not module.replay_dag(
                    self.source,
                    self.nodes,
                    root,
                    maximum_term_size=self.configuration[
                        "maximum_term_size"
                    ],
                    maximum_nodes=self.configuration[
                        "maximum_proof_nodes"
                    ],
                )
            ):
                del self.nodes[start:]
                return False
            return True

        def generate_consequences(self):
            super().generate_consequences()
            seen = {(node.lhs, node.rhs) for node in self.nodes}
            for _ in range(self.configuration.get("interreduce_rounds", 3)):
                if self.expired():
                    break
                self.orient()
                self.select_rulebook()
                snapshot = list(range(len(self.nodes)))
                snapshot.sort(key=lambda node_id: (
                    min(
                        module.structural_distance(
                            self.nodes[node_id].lhs, self.target[0]
                        ),
                        module.structural_distance(
                            self.nodes[node_id].lhs, self.target[1]
                        ),
                        module.structural_distance(
                            self.nodes[node_id].rhs, self.target[0]
                        ),
                        module.structural_distance(
                            self.nodes[node_id].rhs, self.target[1]
                        ),
                    ),
                    self.proof_cost(node_id),
                    node_id,
                ))
                added = 0
                for node_id in snapshot:
                    if self.expired() or added >= self.configuration[
                        "interreduce_candidates"
                    ]:
                        break
                    before = len(self.nodes)
                    if not self.append_interreduced(node_id):
                        continue
                    result = self.nodes[-1]
                    signature = (result.lhs, result.rhs)
                    reverse = (result.rhs, result.lhs)
                    if signature in seen or reverse in seen:
                        del self.nodes[before:]
                        continue
                    seen.add(signature)
                    added += 1
                if not added:
                    if not self.add_critical_pairs():
                        break
                else:
                    self.add_critical_pairs()
            self.rules = []
            self.selected_rules = []
            return self.nodes

    return GoalDirectedNormalizer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--id")
    parser.add_argument("--answer", choices=("true", "false"))
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/mathgraph-goal-superposition.json"),
    )
    args = parser.parse_args()
    module = load_solver()
    search_type = make_search(module)
    rows = read_rows(args.input)
    if args.id:
        rows = [row for row in rows if row["id"] == args.id]
    if args.answer:
        expected = args.answer == "true"
        rows = [row for row in rows if row.get("answer") is expected]
    records = []
    for index, row in enumerate(rows, 1):
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        configuration = dict(module.SYMBOLIC_SUPERPOSITION)
        configuration.update(
            seconds=10.0,
            candidate_equalities=5000,
            replayed_rules=512,
            selected_rules=256,
            overlap_candidates=1200,
            composition_candidates=800,
            normalization_steps=128,
            maximum_term_size=35,
            maximum_proof_nodes=8000,
            interreduce_rounds=3,
            interreduce_candidates=96,
            superposition_rules=24,
            superposition_candidates=24,
        )
        started = time.monotonic()
        search = search_type(
            source, target, started + configuration["seconds"], configuration
        )
        found = search.solve()
        record = {
            "id": row["id"],
            "answer": row.get("answer"),
            "found": found is not None,
            "seconds": round(time.monotonic() - started, 6),
            "nodes": len(search.nodes),
            "rules": len(search.rules),
            "left_steps": search.left_steps,
            "right_steps": search.right_steps,
            "replay_failures": search.replay_failures,
        }
        if found:
            nodes, root = found
            code, proof_nodes = module.make_dag_certificate(
                target, nodes, root
            )
            record.update(
                proof_nodes=proof_nodes,
                certificate_bytes=len(code.encode()),
                replay=module.replay_dag(
                    source,
                    nodes,
                    root,
                    maximum_term_size=configuration["maximum_term_size"],
                    maximum_nodes=configuration["maximum_proof_nodes"],
                ),
                code=code,
            )
        records.append(record)
        print(
            f"[{index}/{len(rows)}] "
            + json.dumps({k: v for k, v in record.items() if k != "code"}),
            flush=True,
        )
    args.output.write_text(
        json.dumps({"diagnostic_only": True, "rows": records}, indent=2)
    )


if __name__ == "__main__":
    main()
