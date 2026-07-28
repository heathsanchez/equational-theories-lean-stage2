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
