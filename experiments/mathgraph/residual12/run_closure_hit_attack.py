#!/usr/bin/env python3
"""Attack compact-superposition census hits with budget and surface controls."""

import argparse
import ast
import hashlib
import importlib.util
import json
import string
import sys
import time
from pathlib import Path


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = Path(__file__).with_name("released_residuals_unlabelled.json")
HIT_IDS = ("evaluation_order5_0022", "evaluation_order5_0040")
EXPECTED_SOLVER_SHA256 = (
    "a92eae8cce4fdf7c787c3218fa4f7eb1158c92a6b57f2920199ddbe6e7726a08"
)


def load_solver(path):
    spec = importlib.util.spec_from_file_location(
        "mathgraph_residual12_hit_attack_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def map_term(term, mapping=None, mirror=False):
    if term[0] == "var":
        return ("var", mapping.get(term[1], term[1]) if mapping else term[1])
    left = map_term(term[1], mapping, mirror)
    right = map_term(term[2], mapping, mirror)
    return ("op", right, left) if mirror else ("op", left, right)


def transform_equation(solver, equation, mapping=None, mirror=False):
    return (
        map_term(equation[0], mapping, mirror),
        map_term(equation[1], mapping, mirror),
        tuple(mapping.get(v, v) for v in equation[2]) if mapping
        else equation[2],
    )


def equation_text(solver, equation):
    return solver.render_term(equation[0]) + " = " + solver.render_term(
        equation[1]
    )


def officially_verify(problem, code):
    from judge.verify import verify_answer

    proxy_tree = ast.parse(
        (ROOT / "pipeline/proxy.py").read_text(encoding="utf-8")
    )
    policy = None
    for node in proxy_tree.body:
        if (
            isinstance(node, ast.Assign)
            and any(
                isinstance(target, ast.Name)
                and target.id == "DEFAULT_PROOF_POLICY"
                for target in node.targets
            )
        ):
            policy = ast.literal_eval(node.value)
            break
    if policy is None:
        raise RuntimeError("DEFAULT_PROOF_POLICY not found")
    problem = {**problem, "proof_policy": policy}

    answer = json.dumps({"verdict": "true", "code": code})
    result = verify_answer(problem, answer)
    return result.get("status", "unparsed")


def run_once(solver, source, target, seconds, problem_id):
    configuration = dict(solver.COMPACT_SUPERPOSITION_FAST)
    configuration["seconds"] = seconds
    started = time.monotonic()
    search = solver.CompactSuperposition(
        solver, source, target, started + seconds, configuration
    )
    recipe = search.solve()
    record = {
        "seconds_budget": seconds,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "found": recipe is not None,
        "clauses": len(search.clauses),
        "rounds": search.rounds,
        "superpositions": search.superpositions,
        "replayed": False,
        "root_matches": False,
        "certificate_bytes": 0,
        "judge_status": None,
    }
    if recipe is None:
        return record
    nodes, root = search.compile(recipe)
    record["root_matches"] = (nodes[root].lhs, nodes[root].rhs) == target[:2]
    record["replayed"] = solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=configuration["maximum_replay_term_size"],
        maximum_nodes=configuration["maximum_proof_nodes"],
    )
    code, proof_nodes = solver.make_dag_certificate(target, nodes, root)
    record["proof_nodes"] = proof_nodes
    record["certificate_bytes"] = len(code.encode("utf-8"))
    if record["root_matches"] and record["replayed"]:
        problem = {
            "id": problem_id,
            "eq1_id": 990001,
            "eq2_id": 990002,
            "equation1": equation_text(solver, source),
            "equation2": equation_text(solver, target),
        }
        record["judge_status"] = officially_verify(problem, code)
    return record


def variants(solver, source, target):
    variables = tuple(dict.fromkeys(source[2] + target[2]))
    fresh = [
        name for name in reversed(string.ascii_lowercase)
        if name not in variables
    ]
    mapping = dict(zip(variables, fresh))
    return {
        "alpha-renamed": (
            transform_equation(solver, source, mapping=mapping),
            transform_equation(solver, target, mapping=mapping),
        ),
        "operation-dual": (
            transform_equation(solver, source, mirror=True),
            transform_equation(solver, target, mirror=True),
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if hashlib.sha256(args.solver.read_bytes()).hexdigest() != (
        EXPECTED_SOLVER_SHA256
    ):
        raise SystemExit("solver hash differs from frozen attack")
    rows = json.loads(args.input.read_text(encoding="utf-8"))
    assert all("answer" not in row for row in rows)
    by_id = {row["id"]: row for row in rows}
    assert set(HIT_IDS) <= set(by_id)
    solver = load_solver(args.solver)
    output = []
    for hit_index, hit_id in enumerate(HIT_IDS):
        row = by_id[hit_id]
        source = solver.parse_equation(row["equation1"])
        target = solver.parse_equation(row["equation2"])
        original = {}
        for seconds in (3.0, 5.0):
            original[str(int(seconds))] = [
                run_once(
                    solver, source, target, seconds,
                    f"{hit_id}_original_{int(seconds)}_{repeat}",
                )
                for repeat in range(3)
            ]
        transformed = {}
        for variant_index, (name, pair) in enumerate(
            variants(solver, source, target).items()
        ):
            changed_source, changed_target = pair
            # Reparse the rendered form exactly as the official intake does.
            changed_source = solver.parse_equation(
                equation_text(solver, changed_source)
            )
            changed_target = solver.parse_equation(
                equation_text(solver, changed_target)
            )
            transformed[name] = run_once(
                solver, changed_source, changed_target, 5.0,
                f"{hit_id}_{name}_{hit_index}_{variant_index}",
            )
        output.append({
            "id": hit_id,
            "original": original,
            "transformed": transformed,
        })
    result = {
        "schema": "mathgraph.verified-residual-12-closure-hit-attack-results.v1",
        "solver_sha256": EXPECTED_SOLVER_SHA256,
        "label_fields_available_to_runner": [],
        "rows": output,
    }
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "hits": len(output),
        "original_attempts": sum(
            len(attempts) for row in output
            for attempts in row["original"].values()
        ),
        "metamorphic_attempts": sum(
            len(row["transformed"]) for row in output
        ),
        "official_acceptances": sum(
            attempt.get("judge_status") == "accepted"
            for row in output
            for attempts in row["original"].values()
            for attempt in attempts
        ) + sum(
            attempt.get("judge_status") == "accepted"
            for row in output
            for attempt in row["transformed"].values()
        ),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
