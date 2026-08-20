#!/usr/bin/env python3
"""Label-blind baseline profiling for the frozen generic Fin-4 engine."""

import argparse
import hashlib
import importlib.util
import json
import resource
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
FROZEN_SOLVER = ROOT / "experiments/mathgraph/regressions/solver_fb671c7.py"
LIVE_SOLVER = ROOT / "submissions/mathgraph/solver.py"
PROBLEMS = ROOT / "examples/problems/sample_200.json"
BASELINE = ROOT / "experiments/mathgraph/results/fin3_final/sample_200.json"
OBSTRUCTIONS = (
    ROOT / "experiments/mathgraph/results/fin3_frozen/residual_obstructions.json"
)


def load_solver(path):
    spec = importlib.util.spec_from_file_location("profile_fin4_solver", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def content_digest(problem):
    payload = (
        problem["equation1"].strip()
        + "\0"
        + problem["equation2"].strip()
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def content_split(problems):
    ordered = sorted(
        problems,
        key=lambda row: (
            content_digest(row),
            row["equation1"],
            row["equation2"],
        ),
    )
    return ordered[: len(ordered) // 2], ordered[len(ordered) // 2 :]


def node_depths(compiled):
    depths = []
    for node in compiled[0]:
        if node[0] == "variable":
            depths.append(0)
        else:
            depths.append(1 + max(depths[node[1]], depths[node[2]]))
    return depths


class ProfileEngineMixin:
    def initialize_profile(self):
        self.profile_started = time.monotonic()
        self.first_source_model_seconds = None
        self.profile_time = {
            "propagate": 0.0,
            "activity": 0.0,
            "nogood": 0.0,
            "symmetry": 0.0,
            "canonicalize": 0.0,
            "replay": 0.0,
            "certificate": 0.0,
        }

    def retain_source_model(self, table):
        if self.first_source_model_seconds is None:
            self.first_source_model_seconds = (
                time.monotonic() - self.profile_started
            )
        return super().retain_source_model(table)

    def propagate(self, domains, target_assignment=None):
        started = time.monotonic()
        result = super().propagate(domains, target_assignment)
        self.profile_time["propagate"] += time.monotonic() - started
        return result

    def choose_cell(self, domains, target_assignment=None):
        started = time.monotonic()
        result = super().choose_cell(domains, target_assignment)
        self.profile_time["activity"] += time.monotonic() - started
        return result

    def nogood_applies(self, facts, target_assignment):
        started = time.monotonic()
        result = super().nogood_applies(facts, target_assignment)
        self.profile_time["nogood"] += time.monotonic() - started
        return result

    def partial_symmetry_prunable(self, domains, target_assignment):
        started = time.monotonic()
        result = super().partial_symmetry_prunable(
            domains, target_assignment
        )
        self.profile_time["symmetry"] += time.monotonic() - started
        return result

    def canonicalize(self, table):
        started = time.monotonic()
        result = super().canonicalize(table)
        self.profile_time["canonicalize"] += time.monotonic() - started
        return result

    def replay(self, table, witness):
        started = time.monotonic()
        result = super().replay(table, witness)
        self.profile_time["replay"] += time.monotonic() - started
        return result

    def emit_certificate(self, table):
        started = time.monotonic()
        result = super().emit_certificate(table)
        self.profile_time["certificate"] += time.monotonic() - started
        return result


def make_profile_engine(solver):
    return type(
        "ProfileFiniteModelEngine",
        (ProfileEngineMixin, solver.FiniteModelEngine),
        {},
    )


def initial_support_profile(solver, engine):
    domains = [engine.full_domain] * (engine.domain_size ** 2)
    categories = {"known": 0, "root_cell": 0, "multi_cell": 0}
    deepest = 0
    depths = node_depths(engine.source_compiled)
    for assignment in engine.source_assignments:
        roots = solver.evaluate_compiled_domains(
            engine.source_compiled,
            assignment,
            domains,
            engine.domain_size,
        )
        for root_id, (support, cell) in zip(
            engine.source_compiled[1:3], roots
        ):
            if solver.singleton_value(support) is not None:
                categories["known"] += 1
            elif cell is not None:
                categories["root_cell"] += 1
            else:
                categories["multi_cell"] += 1
                deepest = max(deepest, depths[root_id])
    total = sum(categories.values()) or 1
    return {
        "counts": categories,
        "fractions": {
            name: round(count / total, 6)
            for name, count in categories.items()
        },
        "deepest_unresolved_term": deepest,
        "cells_without_direct_activity": sum(
            not source and not target
            for source, target in engine.constraint_graph
        ),
    }


def run_attempt(solver, engine_type, problem, configuration):
    source = solver.parse_equation(problem["equation1"])
    target = solver.parse_equation(problem["equation2"])
    started = time.monotonic()
    before_memory = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    arguments = (
        4,
        source,
        target,
        started + configuration["seconds"],
        configuration["maximum_states"],
        configuration["maximum_models"],
    )
    if "options" in configuration:
        engine = engine_type(
            *arguments, options=configuration["options"]
        )
    else:
        engine = engine_type(*arguments)
    engine.target_assignments = engine.target_assignments[
        : configuration["target_witness_limit"]
    ]
    engine.initialize_profile()
    supports = initial_support_profile(solver, engine)
    found = engine.search_target_guided()
    elapsed = time.monotonic() - started
    after_memory = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    replay = found is not None and engine.replay(*found)
    certificate_bytes = (
        len(engine.emit_certificate(found[0]).encode("utf-8"))
        if replay
        else 0
    )
    return {
        "id": problem["id"],
        "content_sha256": content_digest(problem),
        "configuration": configuration["name"],
        "found": found is not None,
        "replay": bool(replay),
        "target_witnesses_considered": engine.target_witnesses_tested,
        "partial_states": engine.partial_states,
        "propagation_rounds": engine.propagation_rounds,
        "domain_reductions": engine.domain_reductions,
        "branch_choices": engine.branch_choices,
        "branch_values": engine.branch_values,
        "maximum_depth": engine.maximum_depth,
        "first_source_model_seconds": engine.first_source_model_seconds,
        "source_models": engine.source_models,
        "nogoods_learned": engine.nogoods_learned,
        "nogoods_reused": engine.nogoods_reused,
        "symmetry_prunes": engine.symmetry_branch_prunes,
        "timeout_or_exhaustion": engine.exhaustion,
        "elapsed_seconds": round(elapsed, 6),
        "memory_highwater_delta": max(0, after_memory - before_memory),
        "certificate_bytes": certificate_bytes,
        "initial_supports": supports,
        "phase_times": {
            name: round(value, 6)
            for name, value in engine.profile_time.items()
        },
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--candidate", action="store_true")
    args = parser.parse_args()
    solver_path = LIVE_SOLVER if args.candidate else FROZEN_SOLVER
    solver = load_solver(solver_path)
    engine_type = make_profile_engine(solver)
    problems = json.loads(PROBLEMS.read_text(encoding="utf-8"))
    by_id = {problem["id"]: problem for problem in problems}
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    unresolved_ids = {
        row["id"] for row in baseline if not row.get("solved")
    }
    development, _ = content_split(problems)
    development_unresolved = [
        problem for problem in development if problem["id"] in unresolved_ids
    ]
    all_unresolved = [
        problem for problem in problems if problem["id"] in unresolved_ids
    ]
    diverse = sorted(all_unresolved, key=content_digest)[::4]
    obstruction_ids = {
        row["id"]
        for row in json.loads(OBSTRUCTIONS.read_text(encoding="utf-8"))[
            "residual_false"
        ]
    }
    configurations = {
        "probe": {
            "name": "baseline-probe",
            "seconds": 0.2,
            "maximum_states": 10000,
            "maximum_models": 4,
            "target_witness_limit": 16,
        },
        "fast": {
            "name": "baseline-fast",
            "seconds": 0.75,
            "maximum_states": 75000,
            "maximum_models": 16,
            "target_witness_limit": 64,
        },
        "medium": {
            "name": "baseline-medium",
            "seconds": 3.0,
            "maximum_states": 400000,
            "maximum_models": 64,
            "target_witness_limit": 256,
        },
        "deep": {
            "name": "baseline-deep",
            "seconds": 15.0,
            "maximum_states": 2000000,
            "maximum_models": 256,
            "target_witness_limit": 256,
        },
    }
    work = []
    if args.candidate:
        base_options = {
            "support_propagation": True,
            "incremental_propagation": True,
            "reversible_trail": True,
            "diverse_witnesses": True,
            "support_branching": True,
            "symmetry_enabled": True,
            "nogood_minimization_budget": 16,
        }
        variants = []
        for name, changes in (
            ("support-incremental", {}),
            ("support-full-scan", {"incremental_propagation": False}),
            ("support-legacy-branch", {"support_branching": False}),
            ("support-no-symmetry", {"symmetry_enabled": False}),
            ("root-only-incremental", {"support_propagation": False}),
        ):
            options = dict(base_options)
            options.update(changes)
            variants.append({
                "name": name,
                "seconds": 0.2,
                "maximum_states": 10000,
                "maximum_models": 4,
                "target_witness_limit": 16,
                "options": options,
            })
        fast = {
            "name": "support-incremental-fast",
            "seconds": 0.75,
            "maximum_states": 75000,
            "maximum_models": 16,
            "target_witness_limit": 64,
            "options": dict(base_options),
        }
        for problem in development_unresolved:
            for configuration in variants:
                work.append((problem, configuration, "development"))
            work.append((problem, fast, "development"))
    else:
        for problem in development_unresolved:
            work.append((problem, configurations["probe"], "development"))
            work.append((problem, configurations["fast"], "development"))
        for problem in diverse:
            work.append((problem, configurations["medium"], "diverse"))
        for problem_id in sorted(obstruction_ids):
            work.append(
                (by_id[problem_id], configurations["deep"], "residual")
            )
    rows = []
    for index, (problem, configuration, cohort) in enumerate(work, 1):
        print(
            f"[{index}/{len(work)}] {configuration['name']} "
            f"{problem['id']}",
            flush=True,
        )
        row = run_attempt(solver, engine_type, problem, configuration)
        row["cohort"] = cohort
        rows.append(row)
    payload = {
        "solver_sha256": hashlib.sha256(solver_path.read_bytes()).hexdigest(),
        "candidate": args.candidate,
        "development_unresolved_count": len(development_unresolved),
        "diverse_selection": "every fourth content-hash-ordered unresolved row",
        "diverse_count": len(diverse),
        "residual_diagnostic_count": len(obstruction_ids),
        "attempts": rows,
    }
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
