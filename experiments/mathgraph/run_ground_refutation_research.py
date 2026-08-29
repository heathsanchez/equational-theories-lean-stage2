#!/usr/bin/env python3
"""Replayable target-grounded unit-superposition research constructor."""

import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def load_solver():
    path = ROOT / "submissions/mathgraph/solver.py"
    spec = importlib.util.spec_from_file_location(
        "mathgraph_ground_refutation_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class RigidModule:
    """Adapter making ``@``-prefixed variables rigid during proof search."""

    def __init__(self, module):
        self.module = module
        self.EqualityNode = module.EqualityNode

    @staticmethod
    def rigid(term):
        return term[0] == "var" and term[1].startswith("@")

    def term_variables(self, term):
        return {
            variable for variable in self.module.term_variables(term)
            if not variable.startswith("@")
        }

    def substitute_partial(self, term, mapping):
        if term[0] == "var":
            return term if self.rigid(term) else mapping.get(term[1], term)
        return (
            "op",
            self.substitute_partial(term[1], mapping),
            self.substitute_partial(term[2], mapping),
        )

    def apply(self, term, substitution, visiting=None):
        if visiting is None:
            visiting = set()
        if term[0] == "var":
            if self.rigid(term) or term[1] not in substitution:
                return term
            if term[1] in visiting:
                return term
            return self.apply(
                substitution[term[1]],
                substitution,
                visiting | {term[1]},
            )
        return (
            "op",
            self.apply(term[1], substitution, visiting),
            self.apply(term[2], substitution, visiting),
        )

    def occurs(self, variable, term, substitution):
        term = self.apply(term, substitution)
        if term[0] == "var":
            return not self.rigid(term) and term[1] == variable
        return (
            self.occurs(variable, term[1], substitution)
            or self.occurs(variable, term[2], substitution)
        )

    def replace_variable(self, term, variable, replacement):
        if term[0] == "var":
            if not self.rigid(term) and term[1] == variable:
                return replacement
            return term
        return (
            "op",
            self.replace_variable(term[1], variable, replacement),
            self.replace_variable(term[2], variable, replacement),
        )

    def unify_terms(self, left, right):
        substitution = {}
        pending = [(left, right)]
        while pending:
            first, second = pending.pop()
            first = self.apply(first, substitution)
            second = self.apply(second, substitution)
            if first == second:
                continue
            if first[0] == "var" and not self.rigid(first):
                if self.occurs(first[1], second, substitution):
                    return None
                substitution = {
                    variable: self.replace_variable(
                        value, first[1], second
                    )
                    for variable, value in substitution.items()
                }
                substitution[first[1]] = second
                continue
            if second[0] == "var" and not self.rigid(second):
                if self.occurs(second[1], first, substitution):
                    return None
                substitution = {
                    variable: self.replace_variable(
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

    def match_term(self, pattern, concrete, mapping):
        if pattern[0] == "var":
            if self.rigid(pattern):
                return pattern == concrete
            previous = mapping.get(pattern[1])
            if previous is None:
                mapping[pattern[1]] = concrete
                return True
            return previous == concrete
        if concrete[0] != "op":
            return False
        return (
            self.match_term(pattern[1], concrete[1], mapping)
            and self.match_term(pattern[2], concrete[2], mapping)
        )

    def alpha_canonical_term(self, term, names):
        if self.rigid(term):
            return term
        if term[0] == "var":
            if term[1] not in names:
                names[term[1]] = "v" + str(len(names))
            return ("var", names[term[1]])
        return (
            "op",
            self.alpha_canonical_term(term[1], names),
            self.alpha_canonical_term(term[2], names),
        )

    def __getattr__(self, name):
        return getattr(self.module, name)


class GroundRefutation:
    def __init__(self, module, source, target, deadline, limits):
        self.module = module
        self.rigid_module = RigidModule(module)
        self.source = source
        self.target = target
        self.constants = {}
        self.reverse_constants = {}
        rigid_left = self.name_target(target[0], "L")
        rigid_right = self.name_target(target[1], "R")
        rigid_target = (rigid_left, rigid_right, target[2])
        self.search = module.CompactSuperposition(
            self.rigid_module,
            source,
            rigid_target,
            deadline,
            limits,
        )
        for constant, term in sorted(self.reverse_constants.items()):
            self.search.add_clause(module.Recipe(
                term,
                ("var", constant),
                "reflexivity",
            ))

    def encode_rigid(self, term):
        if term[0] == "var":
            return ("var", "@" + term[1])
        return (
            "op",
            self.encode_rigid(term[1]),
            self.encode_rigid(term[2]),
        )

    def name_target(self, term, prefix):
        encoded = self.encode_rigid(term)
        for index, subterm in enumerate(self.module.walk_subterms(encoded)):
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
        if cache is None:
            cache = {}
        if id(recipe) in cache:
            return cache[id(recipe)]
        parents = tuple(
            self.inline_recipe(parent, cache) for parent in recipe.parents
        )
        data = recipe.data
        if recipe.kind in ("source",):
            substitution, reverse = data
            data = (
                tuple((variable, self.inline(value))
                      for variable, value in substitution),
                reverse,
            )
        elif recipe.kind == "instantiate":
            data = tuple(
                (variable, self.inline(value)) for variable, value in data
            )
        elif recipe.kind == "congruence":
            data = (data[0], self.inline(data[1]))
        cloned = self.module.Recipe(
            self.inline(recipe.lhs),
            self.inline(recipe.rhs),
            recipe.kind,
            parents,
            data,
        )
        cache[id(recipe)] = cloned
        return cloned

    def solve(self):
        recipe = self.search.solve()
        if recipe is None:
            return None
        inlined = self.inline_recipe(recipe)
        compiler = self.module.CompactSuperposition(
            self.module,
            self.source,
            self.target,
            time.monotonic() + 1,
            self.search.limits,
        )
        nodes, root = compiler.compile(inlined)
        if (
            (nodes[root].lhs, nodes[root].rhs) != self.target[:2]
            or not self.module.replay_dag(
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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3)
    arguments = parser.parse_args()
    module = load_solver()
    text = arguments.input.read_text()
    rows = (
        json.loads(text)
        if text.lstrip().startswith("[")
        else [json.loads(line) for line in text.splitlines() if line.strip()]
    )
    limits = dict(module.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds": arguments.seconds,
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
    results = []
    for index, row in enumerate(rows, 1):
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        started = time.monotonic()
        engine = GroundRefutation(
            module,
            source,
            target,
            time.monotonic() + arguments.seconds,
            limits,
        )
        found = engine.solve()
        code = None
        nodes = 0
        if found is not None:
            dag, root = found
            code, nodes = module.make_dag_certificate(target, dag, root)
        record = {
            "id": row["id"],
            "found": found is not None,
            "seconds": round(time.monotonic() - started, 6),
            "clauses": len(engine.search.clauses),
            "rounds": engine.search.rounds,
            "superpositions": engine.search.superpositions,
            "proof_nodes": nodes,
            "certificate_bytes": len(code.encode()) if code else 0,
            "code": code,
        }
        results.append(record)
        print(
            f"[{index}/{len(rows)}] "
            + json.dumps({k: v for k, v in record.items() if k != "code"}),
            flush=True,
        )
    arguments.output.write_text(json.dumps(results, separators=(",", ":")))


if __name__ == "__main__":
    main()
