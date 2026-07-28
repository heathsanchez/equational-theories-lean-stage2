#!/usr/bin/env python3
"""Replayable symbolic-critical-pair specialization diagnostic."""

import importlib.util
import argparse
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


def current_residuals():
    rows = json.loads((ROOT / "examples/problems/sample_200.json").read_text())
    accepted = set(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "normalization_baseline_manifest.json").read_text()
        )["sample_200_accepted"]
    )
    accepted.update(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "quotient_matcher_promotion_summary.json").read_text()
        )["public_hits"]
    )
    accepted.update(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "variable_omission_collapse_summary.json").read_text()
        )["sample_200"]["new_hits"]
    )
    return [
        row for row in rows
        if row["id"].startswith("true_") and row["id"] not in accepted
    ]


def make_normalizer(module):
    class SymbolicNormalizer(module.EquationalNormalizer):
        def clone_proof(self, node_id, variable_mapping, unifier, cache):
            key = (node_id, tuple(sorted(variable_mapping)))
            if key in cache:
                return cache[key]

            def transform(term):
                renamed = module.substitute(term, variable_mapping)
                return module.apply_unifier(renamed, unifier)

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
                constructor="symbolic-superposition-generation-2",
            )
            result = len(self.nodes)
            self.nodes.append(clone)
            cache[key] = result
            return result

        def generate_second_generation(self, maximum=96):
            first_rules = sorted(
                self.rules,
                key=lambda rule: (
                    -self.rule_target_occurrences(rule),
                    rule.proof_cost,
                    module.term_size(rule.lhs),
                    rule.provenance,
                ),
            )[:48]
            added = 0
            signatures = {
                (node.lhs, node.rhs) for node in self.nodes
            }
            for outer_index, outer in enumerate(first_rules):
                if added >= maximum or self.expired():
                    break
                for inner_index, inner in enumerate(first_rules):
                    if added >= maximum or self.expired():
                        break
                    outer_variables = set()
                    inner_variables = set()
                    for node_id, destination in (
                        (outer.node_id, outer_variables),
                        (inner.node_id, inner_variables),
                    ):
                        stack = [node_id]
                        visited = set()
                        while stack:
                            current = stack.pop()
                            if current in visited:
                                continue
                            visited.add(current)
                            node = self.nodes[current]
                            destination |= module.term_variables(node.lhs)
                            destination |= module.term_variables(node.rhs)
                            stack.extend(node.parents)
                    outer_map = {
                        variable: ("var", f"_g2o{outer_index}_{offset}")
                        for offset, variable in enumerate(
                            sorted(outer_variables)
                        )
                    }
                    inner_map = {
                        variable: ("var", f"_g2i{inner_index}_{offset}")
                        for offset, variable in enumerate(
                            sorted(inner_variables)
                        )
                    }
                    outer_lhs = module.substitute(outer.lhs, outer_map)
                    outer_rhs = module.substitute(outer.rhs, outer_map)
                    inner_lhs = module.substitute(inner.lhs, inner_map)
                    inner_rhs = module.substitute(inner.rhs, inner_map)
                    for path in module.nonvariable_positions(
                        outer_lhs, maximum_depth=6, include_root=True
                    ):
                        selected = module.get_subterm(outer_lhs, path)
                        unifier = module.unify_terms(selected, inner_lhs)
                        if unifier is None:
                            continue
                        concrete_outer_lhs = module.apply_unifier(
                            outer_lhs, unifier
                        )
                        concrete_outer_rhs = module.apply_unifier(
                            outer_rhs, unifier
                        )
                        concrete_inner_rhs = module.apply_unifier(
                            inner_rhs, unifier
                        )
                        changed = module.replace_subterm(
                            concrete_outer_lhs, path, concrete_inner_rhs
                        )
                        if (
                            concrete_outer_rhs == changed
                            or max(
                                module.term_size(concrete_outer_rhs),
                                module.term_size(changed),
                            ) > self.configuration["maximum_term_size"]
                            or (concrete_outer_rhs, changed) in signatures
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
                            constructor="symbolic-superposition-generation-2",
                        ))
                        try:
                            lifted = self.lift_context(
                                self.nodes, inner_id,
                                concrete_outer_lhs, path,
                            )
                        except ValueError:
                            del self.nodes[start:]
                            continue
                        root = len(self.nodes)
                        self.nodes.append(module.EqualityNode(
                            concrete_outer_rhs,
                            changed,
                            "transitivity",
                            parents=(outer_reverse, lifted),
                            constructor="symbolic-superposition-generation-2",
                        ))
                        if not module.replay_dag(
                            self.source, self.nodes, root,
                            maximum_term_size=self.configuration[
                                "maximum_term_size"
                            ],
                        ):
                            del self.nodes[start:]
                            continue
                        signatures.add((concrete_outer_rhs, changed))
                        added += 1
                        if added >= maximum:
                            break
            return added

        def generate_consequences(self):
            result = super().generate_consequences()
            self.orient()
            self.generate_second_generation()
            self.rules = []
            return result

        def orient(self):
            rules = super().orient()
            for rule in rules:
                lhs_variables = module.term_variables(rule.lhs)
                if (
                    rule.variables == ()
                    and module.term_variables(rule.rhs) <= lhs_variables
                    and lhs_variables
                ):
                    # Internal proof parameters that disappear from both
                    # endpoints can be specialized arbitrarily at compilation.
                    rule.variables = tuple(sorted(lhs_variables))
            return rules

        def instantiate_proof(self, node_id, mapping, output, cache):
            expanded = dict(mapping)
            stack = [node_id]
            seen = set()
            internal = set()
            while stack:
                current = stack.pop()
                if current in seen:
                    continue
                seen.add(current)
                node = self.nodes[current]
                internal |= module.term_variables(node.lhs)
                internal |= module.term_variables(node.rhs)
                stack.extend(node.parents)
            fallback = next(
                iter(expanded.values()),
                ("var", self.target[2][0]),
            )
            for variable in internal:
                expanded.setdefault(variable, fallback)
            return super().instantiate_proof(
                node_id, expanded, output, cache
            )

    return SymbolicNormalizer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path)
    parser.add_argument("--id")
    parser.add_argument("--output", type=Path, default=Path(
        "/tmp/mathgraph-symbolic-superposition.json"
    ))
    args = parser.parse_args()
    module = load_solver()
    normalizer_type = make_normalizer(module)
    output = []
    rows = current_residuals()
    if args.input:
        payload = json.loads(args.input.read_text())
        rows = payload["rows"] if isinstance(payload, dict) else payload
    if args.id:
        rows = [row for row in rows if row["id"] == args.id]
    for index, row in enumerate(rows, 1):
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        configuration = dict(module.NORMALIZATION_PORTFOLIO[3])
        configuration.update(
            source_substitutions=0,
            seconds=3.0,
            candidate_equalities=1200,
            overlap_candidates=800,
            selected_rules=128,
            replayed_rules=400,
            maximum_term_size=27,
            maximum_proof_nodes=3000,
        )
        started = time.monotonic()
        search = normalizer_type(
            source, target, started + configuration["seconds"], configuration
        )
        found = search.solve()
        record = {
            "id": row["id"],
            "found": found is not None,
            "seconds": round(time.monotonic() - started, 6),
            "consequences": len(search.nodes),
            "overlaps": search.overlap_candidates,
            "rules": len(search.rules),
            "selected_rules": len(search.selected_rules),
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
                    source, nodes, root, maximum_term_size=27
                ),
                code=code,
            )
        output.append(record)
        print(
            f"[{index}/{len(rows)}] "
            + json.dumps({k: v for k, v in record.items() if k != "code"}),
            flush=True,
        )
    args.output.write_text(
        json.dumps({"diagnostic_only": True, "rows": output}, indent=2)
    )


if __name__ == "__main__":
    main()
