#!/usr/bin/env python3
"""Compact proof-recipe unit superposition diagnostic.

Search retains immutable proof recipes.  Concrete EqualityNode DAGs are
materialized only for a winning target trace.
"""

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


class Recipe:
    __slots__ = ("lhs", "rhs", "kind", "parents", "data", "cost")

    def __init__(self, lhs, rhs, kind, parents=(), data=None):
        self.lhs = lhs
        self.rhs = rhs
        self.kind = kind
        self.parents = tuple(parents)
        self.data = data
        self.cost = 1 + sum(parent.cost for parent in self.parents)


class CompactSuperposition:
    def __init__(self, module, source, target, deadline, limits):
        self.m = module
        self.source = source
        self.target = target
        self.deadline = deadline
        self.limits = limits
        self.clauses = []
        self.signatures = set()
        self.generated = 0
        self.superpositions = 0
        self.reductions = 0
        self.rounds = 0
        self.maximum_recipe_cost = 0
        identity = {
            variable: ("var", variable) for variable in source[2]
        }
        base = Recipe(
            source[0],
            source[1],
            "source",
            data=(tuple(identity.items()), False),
        )
        self.add_clause(base)

    def expired(self):
        return time.monotonic() >= self.deadline

    def key(self, term):
        return self.m.normalization_order_key(term, "size")

    def orient(self, recipe):
        left_variables = self.m.term_variables(recipe.lhs)
        right_variables = self.m.term_variables(recipe.rhs)
        if (
            recipe.lhs[0] != "var"
            and right_variables <= left_variables
            and self.key(recipe.rhs) < self.key(recipe.lhs)
        ):
            return recipe
        if (
            recipe.rhs[0] != "var"
            and left_variables <= right_variables
            and self.key(recipe.lhs) < self.key(recipe.rhs)
        ):
            return Recipe(
                recipe.rhs, recipe.lhs, "symmetry", (recipe,)
            )
        return None

    def alpha_signature(self, lhs, rhs):
        names = {}
        return (
            self.m.alpha_canonical_term(lhs, names),
            self.m.alpha_canonical_term(rhs, names),
        )

    def add_clause(self, recipe):
        if (
            recipe.lhs == recipe.rhs
            or max(
                self.m.term_size(recipe.lhs),
                self.m.term_size(recipe.rhs),
            ) > self.limits["maximum_term_size"]
        ):
            return False
        oriented = self.orient(recipe)
        if oriented is None:
            candidates = (recipe,)
        else:
            candidates = (oriented,)
        added = False
        for candidate in candidates:
            signature = self.alpha_signature(
                candidate.lhs, candidate.rhs
            )
            reverse = self.alpha_signature(
                candidate.rhs, candidate.lhs
            )
            if signature in self.signatures or reverse in self.signatures:
                continue
            self.signatures.add(signature)
            self.clauses.append(candidate)
            self.maximum_recipe_cost = max(
                self.maximum_recipe_cost, candidate.cost
            )
            self.generated += 1
            added = True
        return added

    def instantiate(self, recipe, mapping):
        lhs = self.m.substitute_partial(recipe.lhs, mapping)
        rhs = self.m.substitute_partial(recipe.rhs, mapping)
        if lhs == recipe.lhs and rhs == recipe.rhs:
            return recipe
        return Recipe(
            lhs,
            rhs,
            "instantiate",
            (recipe,),
            tuple(sorted(mapping.items())),
        )

    def lift(self, recipe, root, path):
        if self.m.get_subterm(root, path) != recipe.lhs:
            raise ValueError("recipe context mismatch")
        current = recipe
        for index in range(len(path) - 1, -1, -1):
            context = self.m.get_subterm(root, path[:index])
            if path[index] == "L":
                sibling = context[2]
                lhs = ("op", current.lhs, sibling)
                rhs = ("op", current.rhs, sibling)
                data = ("left", sibling)
            else:
                sibling = context[1]
                lhs = ("op", sibling, current.lhs)
                rhs = ("op", sibling, current.rhs)
                data = ("right", sibling)
            current = Recipe(lhs, rhs, "congruence", (current,), data)
        return current

    def target_score(self, recipe):
        targets = self.target[:2]
        occurrence = 0
        for target in targets:
            for subterm in self.m.walk_subterms(target):
                mapping = {}
                if self.m.match_term(recipe.lhs, subterm, mapping):
                    occurrence += 1
        return (
            -occurrence,
            min(
                self.m.structural_distance(recipe.lhs, targets[0]),
                self.m.structural_distance(recipe.lhs, targets[1]),
                self.m.structural_distance(recipe.rhs, targets[0]),
                self.m.structural_distance(recipe.rhs, targets[1]),
            ),
            self.m.term_size(recipe.lhs) + self.m.term_size(recipe.rhs),
            recipe.cost,
            self.m.render_term(recipe.lhs),
        )

    def rules(self):
        output = []
        for clause in self.clauses:
            oriented = self.orient(clause)
            if oriented is not None:
                output.append(oriented)
        output.sort(key=self.target_score)
        return output[:self.limits["maximum_rules"]]

    def rewrite_once(self, term, rules, excluded=None):
        candidates = []
        for path in self.m.nonvariable_positions(
            term,
            maximum_depth=self.limits["maximum_depth"],
            include_root=True,
        ):
            selected = self.m.get_subterm(term, path)
            for index, rule in enumerate(rules):
                if rule is excluded:
                    continue
                mapping = {}
                if not self.m.match_term(rule.lhs, selected, mapping):
                    continue
                if not self.m.term_variables(rule.lhs) <= set(mapping):
                    continue
                replacement = self.m.substitute_partial(rule.rhs, mapping)
                after = self.m.replace_subterm(term, path, replacement)
                if self.key(after) >= self.key(term):
                    continue
                candidates.append((
                    -len(path),
                    self.key(after),
                    rule.cost,
                    index,
                    path,
                    rule,
                    mapping,
                    after,
                ))
        if not candidates:
            return None
        candidates.sort(key=lambda item: item[:4])
        _, _, _, _, path, rule, mapping, after = candidates[0]
        proof = self.instantiate(rule, mapping)
        return after, self.lift(proof, term, path)

    def normalize(self, term, rules, excluded=None):
        current = term
        proof = None
        for _ in range(self.limits["normalization_steps"]):
            step = self.rewrite_once(current, rules, excluded)
            if step is None:
                return current, proof
            after, step_proof = step
            proof = (
                step_proof
                if proof is None
                else Recipe(
                    proof.lhs,
                    step_proof.rhs,
                    "transitivity",
                    (proof, step_proof),
                )
            )
            current = after
            self.reductions += 1
        return current, proof

    def interreduce(self, recipe, rules):
        left, left_proof = self.normalize(recipe.lhs, rules, recipe)
        right, right_proof = self.normalize(recipe.rhs, rules, recipe)
        result = recipe
        if left_proof is not None:
            reverse = Recipe(
                left_proof.rhs,
                left_proof.lhs,
                "symmetry",
                (left_proof,),
            )
            result = Recipe(
                left,
                result.rhs,
                "transitivity",
                (reverse, result),
            )
        if right_proof is not None:
            result = Recipe(
                result.lhs,
                right,
                "transitivity",
                (result, right_proof),
            )
        return result

    def freshen(self, recipe, prefix):
        mapping = {
            variable: ("var", f"_{prefix}{index}")
            for index, variable in enumerate(
                sorted(
                    self.m.term_variables(recipe.lhs)
                    | self.m.term_variables(recipe.rhs)
                )
            )
        }
        return self.instantiate(recipe, mapping)

    def critical_pair(self, outer, inner, outer_index, inner_index, path):
        left = self.freshen(outer, f"o{outer_index}_")
        right = self.freshen(inner, f"i{inner_index}_")
        selected = self.m.get_subterm(left.lhs, path)
        unifier = self.m.unify_terms(selected, right.lhs)
        if unifier is None:
            return None
        left = self.instantiate(left, unifier)
        right = self.instantiate(right, unifier)
        changed = self.m.replace_subterm(left.lhs, path, right.rhs)
        if changed == left.rhs:
            return None
        reverse_left = Recipe(
            left.rhs, left.lhs, "symmetry", (left,)
        )
        lifted = self.lift(right, left.lhs, path)
        return Recipe(
            left.rhs,
            changed,
            "transitivity",
            (reverse_left, lifted),
        )

    def target_proof(self, rules):
        left, left_proof = self.normalize(self.target[0], rules)
        right, right_proof = self.normalize(self.target[1], rules)
        if left != right:
            return None
        if left_proof is None:
            left_proof = Recipe(
                self.target[0], self.target[0], "reflexivity"
            )
        if right_proof is None:
            right_proof = Recipe(
                self.target[1], self.target[1], "reflexivity"
            )
        reverse_right = Recipe(
            right_proof.rhs,
            right_proof.lhs,
            "symmetry",
            (right_proof,),
        )
        return Recipe(
            self.target[0],
            self.target[1],
            "transitivity",
            (left_proof, reverse_right),
        )

    def solve(self):
        processed = 0
        for round_index in range(self.limits["maximum_rounds"]):
            self.rounds = round_index + 1
            rules = self.rules()
            goal = self.target_proof(rules)
            if goal is not None:
                return goal
            snapshot = rules
            proposals = []
            for outer_index, outer in enumerate(snapshot):
                for inner_index, inner in enumerate(snapshot):
                    for path in self.m.nonvariable_positions(
                        outer.lhs,
                        maximum_depth=self.limits["maximum_depth"],
                        include_root=True,
                    ):
                        if self.expired():
                            return None
                        proposal = self.critical_pair(
                            outer, inner, outer_index, inner_index, path
                        )
                        if proposal is None:
                            continue
                        proposal = self.interreduce(proposal, rules)
                        proposals.append((
                            self.target_score(proposal), proposal
                        ))
            proposals.sort(key=lambda item: item[0])
            added = 0
            for _, proposal in proposals:
                if self.add_clause(proposal):
                    self.superpositions += 1
                    added += 1
                    if added >= self.limits["new_clauses_per_round"]:
                        break
            processed += len(proposals)
            if not added or len(self.clauses) >= self.limits[
                "maximum_clauses"
            ]:
                break
        return self.target_proof(self.rules())

    def compile(self, recipe):
        nodes = []
        cache = {}

        def transform(term, environment):
            return self.m.substitute_partial(term, environment)

        def visit(current, environment):
            key = (id(current), tuple(sorted(environment.items())))
            if key in cache:
                return cache[key]
            if current.kind == "instantiate":
                mapping = {
                    variable: transform(value, environment)
                    for variable, value in current.data
                }
                for variable, value in environment.items():
                    mapping.setdefault(variable, value)
                result = visit(current.parents[0], mapping)
                cache[key] = result
                return result
            parents = tuple(
                visit(parent, environment) for parent in current.parents
            )
            lhs = transform(current.lhs, environment)
            rhs = transform(current.rhs, environment)
            if current.kind == "source":
                substitution, reverse = current.data
                substitution = tuple(
                    (variable, transform(value, environment))
                    for variable, value in substitution
                )
                node = self.m.EqualityNode(
                    lhs,
                    rhs,
                    "source instance",
                    substitution=substitution,
                    orientation=reverse,
                    constructor="compact-superposition",
                )
            elif current.kind == "congruence":
                side, sibling = current.data
                kind = (
                    "congruence on left child"
                    if side == "left"
                    else "congruence on right child"
                )
                node = self.m.EqualityNode(
                    lhs,
                    rhs,
                    kind,
                    parents=parents,
                    context=(side, transform(sibling, environment)),
                    constructor="compact-superposition",
                )
            else:
                node = self.m.EqualityNode(
                    lhs,
                    rhs,
                    current.kind,
                    parents=parents,
                    constructor="compact-superposition",
                )
            result = len(nodes)
            nodes.append(node)
            cache[key] = result
            return result

        # Variables introduced only to standardize schematic parents apart
        # are universal proof parameters.  If they disappear from the final
        # equality, specialize them to an in-scope target variable rather
        # than leaking synthetic names into Lean.
        internal_variables = set()
        stack = [recipe]
        visited = set()
        while stack:
            current = stack.pop()
            if id(current) in visited:
                continue
            visited.add(id(current))
            internal_variables |= self.m.term_variables(current.lhs)
            internal_variables |= self.m.term_variables(current.rhs)
            stack.extend(current.parents)
        target_variables = set(self.target[2])
        fallback = ("var", self.target[2][0])
        environment = {
            variable: fallback
            for variable in internal_variables
            if variable not in target_variables
        }
        root = visit(recipe, environment)
        return nodes, root


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--id")
    parser.add_argument("--answer", choices=("true", "false"))
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/mathgraph-compact-superposition.json"),
    )
    args = parser.parse_args()
    module = load_solver()
    rows = read_rows(args.input)
    if args.id:
        rows = [row for row in rows if row["id"] == args.id]
    if args.answer:
        expected = args.answer == "true"
        rows = [row for row in rows if row.get("answer") is expected]
    limits = {
        "seconds": 0.20,
        "maximum_term_size": 35,
        "maximum_depth": 7,
        "maximum_rules": 96,
        "maximum_rounds": 8,
        "new_clauses_per_round": 64,
        "maximum_clauses": 512,
        "normalization_steps": 64,
        "maximum_proof_nodes": 8000,
    }
    records = []
    for index, row in enumerate(rows, 1):
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        started = time.monotonic()
        search = CompactSuperposition(
            module,
            source,
            target,
            started + limits["seconds"],
            limits,
        )
        recipe = search.solve()
        found = recipe is not None
        record = {
            "id": row["id"],
            "answer": row.get("answer"),
            "found": found,
            "seconds": round(time.monotonic() - started, 6),
            "clauses": len(search.clauses),
            "rounds": search.rounds,
            "superpositions": search.superpositions,
            "reductions": search.reductions,
            "maximum_recipe_cost": search.maximum_recipe_cost,
        }
        if found:
            nodes, root = search.compile(recipe)
            replay = module.replay_dag(
                source,
                nodes,
                root,
                maximum_term_size=limits["maximum_term_size"],
                maximum_nodes=limits["maximum_proof_nodes"],
            )
            code, proof_nodes = module.make_dag_certificate(
                target, nodes, root
            )
            record.update(
                replay=replay,
                proof_nodes=proof_nodes,
                certificate_bytes=len(code.encode()),
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
