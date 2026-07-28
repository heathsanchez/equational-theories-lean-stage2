#!/usr/bin/env python3
"""Proof-producing variable-position critical-overlap diagnostic."""

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


def variable_paths(term, variable, path=()):
    if term[0] == "var":
        return [path] if term[1] == variable else []
    return (
        variable_paths(term[1], variable, path + ("L",))
        + variable_paths(term[2], variable, path + ("R",))
    )


def ground(module, term, unifier, fallback):
    value = module.apply_unifier(term, unifier)
    if value[0] == "var" and value[1].startswith("_"):
        return fallback
    if value[0] == "op":
        return (
            "op",
            ground(module, value[1], unifier, fallback),
            ground(module, value[2], unifier, fallback),
        )
    return value


def try_row(module, row):
    source = module.parse_equation(row["equation1"])
    target = module.parse_equation(row["equation2"])
    sl, sr, source_vars = source
    target_left, target_right = target[:2]
    fallback = ("var", target[2][0])
    for outer_side, pattern, other in ((0, sl, sr), (1, sr, sl)):
        counts = {
            variable: len(variable_paths(pattern, variable))
            for variable in source_vars
        }
        for repeated, count in counts.items():
            if count < 2:
                continue
            for chosen_path in variable_paths(pattern, repeated):
                for inner_side, inner_before0, inner_after0 in (
                    (0, sl, sr), (1, sr, sl)
                ):
                    renamed = {
                        variable: ("var", f"_i_{variable}")
                        for variable in source_vars
                    }
                    inner_before = module.substitute(inner_before0, renamed)
                    inner_after = module.substitute(inner_after0, renamed)
                    outer_mapping = {
                        variable: (
                            inner_before if variable == repeated
                            else ("var", f"_o_{variable}")
                        )
                        for variable in source_vars
                    }
                    outer_term = module.substitute(pattern, outer_mapping)
                    outer_other = module.substitute(other, outer_mapping)
                    changed = module.replace_subterm(
                        outer_term, chosen_path, inner_after
                    )
                    pair_pattern = ("op", outer_other, changed)
                    pair_target = ("op", target_left, target_right)
                    unifier = module.unify_terms(pair_pattern, pair_target)
                    reverse_goal = False
                    if unifier is None:
                        pair_target = ("op", target_right, target_left)
                        unifier = module.unify_terms(pair_pattern, pair_target)
                        reverse_goal = unifier is not None
                    if unifier is None:
                        continue
                    outer_concrete = {
                        variable: ground(
                            module, value, unifier, fallback
                        )
                        for variable, value in outer_mapping.items()
                    }
                    inner_concrete = {
                        variable: ground(
                            module, renamed[variable], unifier, fallback
                        )
                        for variable in source_vars
                    }
                    nodes = []
                    outer_lhs = module.substitute(sl, outer_concrete)
                    outer_rhs = module.substitute(sr, outer_concrete)
                    nodes.append(module.EqualityNode(
                        outer_lhs, outer_rhs, "source instance",
                        substitution=tuple(outer_concrete.items()),
                        constructor="variable-overlap",
                    ))
                    outer_id = 0
                    if outer_side == 0:
                        nodes.append(module.EqualityNode(
                            outer_rhs, outer_lhs, "symmetry", parents=(0,),
                            constructor="variable-overlap",
                        ))
                        outer_id = 1
                    inner_lhs = module.substitute(sl, inner_concrete)
                    inner_rhs = module.substitute(sr, inner_concrete)
                    inner_id = len(nodes)
                    nodes.append(module.EqualityNode(
                        inner_lhs, inner_rhs, "source instance",
                        substitution=tuple(inner_concrete.items()),
                        constructor="variable-overlap",
                    ))
                    if inner_side == 1:
                        old = inner_id
                        inner_id = len(nodes)
                        nodes.append(module.EqualityNode(
                            inner_rhs, inner_lhs, "symmetry", parents=(old,),
                            constructor="variable-overlap",
                        ))
                    search = module.ContextualSearch(
                        source, target, time.monotonic() + 1,
                        {"max_term_size": 80, "max_derivation_nodes": 1000},
                    )
                    search.nodes = nodes
                    lifted = search.wrap_context(
                        inner_id, nodes[outer_id].rhs, chosen_path,
                        "variable-overlap", 1,
                    )
                    nodes = search.nodes
                    if lifted is None:
                        continue
                    root = len(nodes)
                    nodes.append(module.EqualityNode(
                        nodes[outer_id].lhs, nodes[lifted].rhs,
                        "transitivity", parents=(outer_id, lifted),
                        constructor="variable-overlap",
                    ))
                    if reverse_goal:
                        old = root
                        root = len(nodes)
                        nodes.append(module.EqualityNode(
                            nodes[old].rhs, nodes[old].lhs,
                            "symmetry", parents=(old,),
                            constructor="variable-overlap",
                        ))
                    if (
                        (nodes[root].lhs, nodes[root].rhs) == target[:2]
                        and module.replay_dag(
                            source, nodes, root, maximum_term_size=80
                        )
                    ):
                        code, proof_nodes = module.make_dag_certificate(
                            target, nodes, root
                        )
                        return {
                            "found": True,
                            "repeated_variable": repeated,
                            "path": chosen_path,
                            "outer_side": outer_side,
                            "inner_side": inner_side,
                            "proof_nodes": proof_nodes,
                            "certificate_bytes": len(code.encode()),
                            "code": code,
                        }
    return {"found": False}


def main():
    module = load_solver()
    wanted = {
        "true_2135_2128", "true_2074_2082",
        "true_2771_2775", "true_674_668",
    }
    rows = json.loads((ROOT / "examples/problems/sample_200.json").read_text())
    output = []
    for row in rows:
        if row["id"] not in wanted:
            continue
        result = {"id": row["id"], **try_row(module, row)}
        output.append(result)
        print(json.dumps({k: v for k, v in result.items() if k != "code"}))
    Path("/tmp/mathgraph-variable-overlap.json").write_text(
        json.dumps({"diagnostic_only": True, "rows": output}, indent=2)
    )


if __name__ == "__main__":
    main()
