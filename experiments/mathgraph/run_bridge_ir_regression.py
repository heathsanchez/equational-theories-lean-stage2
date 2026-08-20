#!/usr/bin/env python3
"""Official BridgeIR proxy/judge regression with fail-closed controls."""

import argparse
import copy
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
CASES = ROOT / "experiments/mathgraph/regressions/bridge_ir_cases.json"


def load_solver():
    spec = importlib.util.spec_from_file_location("bridge_regression", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def judge(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    started = time.monotonic()
    answer = json.dumps({"verdict": "true", "code": code})
    result = verify_answer(_to_judge_problem(problem), answer)
    return result.get("status", "unparsed"), time.monotonic() - started


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    module = load_solver()
    cases = json.loads(CASES.read_text())
    records = []
    positive_acceptances = 0
    negative_judge_calls = 0
    largest_proof = 0
    largest_certificate = 0
    corrupted_path_rejected = False
    corrupted_substitution_rejected = False
    for index, problem in enumerate(cases, 1):
        print(f"[{index}/{len(cases)}] {problem['id']}", flush=True)
        source = module.parse_equation(problem["equation1"])
        target = module.parse_equation(problem["equation2"])
        configuration = {
            **module.BRIDGE_IR_PORTFOLIO[1], "seconds": 1.5
        }
        started = time.monotonic()
        search = module.BridgeIR(
            source, target, started + configuration["seconds"], configuration
        )
        found = search.solve()
        record = {
            "id": problem["id"],
            "expect_true": problem["expect_true"],
            "found": found is not None,
            "engine_seconds": round(time.monotonic() - started, 6),
            "activations": search.no_match_activations,
            "bridge_states": search.bridge_states_created,
            "maximum_depth": search.maximum_bridge_depth,
            "replay_failures": search.bridge_replay_failures,
        }
        if problem["expect_true"]:
            if found is None:
                raise AssertionError(f"BridgeIR missed {problem['id']}")
            nodes, root = found
            if not module.replay_dag(
                source,
                nodes,
                root,
                maximum_term_size=
                    search.normalizer.configuration["maximum_term_size"],
                maximum_nodes=configuration["maximum_proof_nodes"],
            ):
                raise AssertionError(f"replay failed for {problem['id']}")
            code, proof_nodes = module.make_dag_certificate(
                target, nodes, root
            )
            status, judge_seconds = judge(problem, code)
            if status != "accepted":
                raise AssertionError(
                    f"official judge rejected {problem['id']}: {status}"
                )
            positive_acceptances += 1
            largest_proof = max(largest_proof, proof_nodes)
            largest_certificate = max(
                largest_certificate, len(code.encode())
            )
            record.update({
                "judge_status": status,
                "judge_seconds": round(judge_seconds, 6),
                "proof_nodes": proof_nodes,
                "certificate_bytes": len(code.encode()),
            })
            if (
                not corrupted_path_rejected
                and search.winning_states is not None
            ):
                for side_index, start in (
                    (0, target[0]), (1, target[1])
                ):
                    state = search.winning_states[side_index]
                    if not state["bridge_steps"]:
                        continue
                    corrupted = copy.deepcopy(state)
                    corrupted["bridge_steps"][0]["path"] = ("L", "L", "L")
                    corrupted_path_rejected = not search.replay_state(
                        start, corrupted
                    )
                    corrupted = copy.deepcopy(state)
                    step = corrupted["bridge_steps"][0]
                    if step["substitution"]:
                        key, _ = step["substitution"][0]
                        step["substitution"] = (
                            (key, ("var", "__invalid_bridge_variable__")),
                        ) + step["substitution"][1:]
                    else:
                        step["substitution"] = (
                            ("__extra_bridge_variable__", ("var", "x")),
                        )
                    corrupted_substitution_rejected = (
                        not search.replay_state(start, corrupted)
                    )
                    break
        else:
            if found is not None:
                negative_judge_calls += 1
                raise AssertionError(
                    f"FALSE control produced BridgeIR proof: {problem['id']}"
                )
        records.append(record)
    if not corrupted_path_rejected or not corrupted_substitution_rejected:
        raise AssertionError("independent BridgeIR corruption controls failed")
    summary = {
        "solver_sha256": hashlib.sha256(SOLVER.read_bytes()).hexdigest(),
        "cases": len(cases),
        "positive_official_acceptances": positive_acceptances,
        "negative_true_judge_calls": negative_judge_calls,
        "corrupted_path_rejected": corrupted_path_rejected,
        "corrupted_substitution_rejected":
            corrupted_substitution_rejected,
        "largest_proof_nodes": largest_proof,
        "largest_certificate_bytes": largest_certificate,
        "records": records,
    }
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(
        f"BridgeIR regression: {positive_acceptances} accepted TRUE, "
        f"{len(cases) - positive_acceptances} abstention/corruption controls, "
        "zero FALSE-control judge calls"
    )


if __name__ == "__main__":
    main()
