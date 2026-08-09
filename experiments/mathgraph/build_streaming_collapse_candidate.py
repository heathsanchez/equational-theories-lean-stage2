#!/usr/bin/env python3
import argparse
from pathlib import Path


STREAMING_METHOD = r'''
    def solve_streaming(self, age_every=2):
        """Incremental given-clause saturation that never discards a partial round."""
        processed = set()
        active = []
        tick = 0
        while not self.expired() and len(self.clauses) < self.limits["maximum_clauses"]:
            available = [
                index for index in range(len(self.clauses))
                if index not in processed
            ]
            if not available:
                break
            tick += 1
            self.rounds = tick
            if tick % age_every == 0:
                clause_index = available[0]
            else:
                clause_index = min(
                    available,
                    key=lambda index: (
                        self.m.term_size(self.clauses[index].lhs)
                        + self.m.term_size(self.clauses[index].rhs),
                        self.clauses[index].cost,
                        index,
                    ),
                )
            processed.add(clause_index)
            clause = self.clauses[clause_index]
            oriented = self.orient(clause)
            if oriented is not None:
                given_rules = [oriented]
            else:
                given_rules = []
                if clause.lhs[0] != "var":
                    given_rules.append(clause)
                if clause.rhs[0] != "var":
                    given_rules.append(Recipe(
                        clause.rhs, clause.lhs, "symmetry", (clause,)
                    ))
            simplifying_rules = active + given_rules
            pending = []
            for given in given_rules:
                for prior_index, prior in enumerate(active + [given]):
                    for outer, inner, outer_index, inner_index in (
                        (given, prior, tick, prior_index),
                        (prior, given, prior_index, tick),
                    ):
                        for path in self.m.nonvariable_positions(
                            outer.lhs,
                            maximum_depth=self.limits["maximum_depth"],
                            include_root=True,
                        ):
                            if self.expired():
                                break
                            proposal = self.critical_pair(
                                outer, inner, outer_index, inner_index, path
                            )
                            if proposal is None:
                                continue
                            if max(
                                self.m.term_size(proposal.lhs),
                                self.m.term_size(proposal.rhs),
                            ) > self.limits["maximum_term_size"]:
                                continue
                            proposal = self.interreduce(
                                proposal, simplifying_rules
                            )
                            if max(
                                self.m.term_size(proposal.lhs),
                                self.m.term_size(proposal.rhs),
                            ) <= self.limits["maximum_term_size"]:
                                pending.append(proposal)
                        if self.expired():
                            break
                    if self.expired():
                        break
                if self.expired():
                    break
            pending.sort(key=lambda proposal: (
                self.m.term_size(proposal.lhs)
                + self.m.term_size(proposal.rhs),
                proposal.cost,
                self.target_score(proposal),
            ))
            for proposal in pending:
                if self.add_clause(proposal):
                    self.superpositions += 1
            active.extend(given_rules)
            goal = self.target_proof(self.rules())
            if goal is not None:
                return goal
        return self.target_proof(self.rules())
'''


HELPERS = r'''

def variable_occurrence_count(term):
    if term[0] == "var":
        return 1
    return variable_occurrence_count(term[1]) + variable_occurrence_count(term[2])


def streaming_singleton_shape(source, target):
    source_left, source_right, source_variables = source
    target_left, target_right, target_variables = target
    return (
        source_left[0] == "var"
        and target_left[0] == "var"
        and source_left[1] in term_variables(source_right)
        and target_left[1] in term_variables(target_right)
        and 7 <= term_size(source_right) <= 15
        and 7 <= term_size(target_right) <= 15
        and variable_occurrence_count(source_right) > len(source_variables)
        and variable_occurrence_count(target_right) > len(target_variables)
    )


def make_universal_recipe_certificate(source, target, root):
    order = []
    seen = set()

    def visit(recipe):
        if id(recipe) in seen:
            return
        for parent in recipe.parents:
            visit(parent)
        seen.add(id(recipe))
        order.append(recipe)

    visit(root)
    names = {id(recipe): "q" + str(index) for index, recipe in enumerate(order)}

    def recipe_variables(recipe):
        return sorted(term_variables(recipe.lhs) | term_variables(recipe.rhs))

    variable_sets = {
        id(recipe): recipe_variables(recipe) for recipe in order
    }

    def render_under(term, current_variables, renaming, anchor):
        mapping = {
            variable: ("var", renaming[variable])
            for variable in current_variables
        }
        for variable in term_variables(term):
            if variable not in mapping:
                mapping[variable] = ("var", anchor)
        return render_term(substitute_partial(term, mapping))

    def parent_application(parent, current, renaming, explicit=None):
        current_variables = set(recipe_variables(current))
        anchor = (
            renaming[recipe_variables(current)[0]]
            if recipe_variables(current)
            else target[2][0]
        )
        explicit = dict(explicit or ())
        arguments = []
        for parent_variable in variable_sets[id(parent)]:
            term = explicit.get(parent_variable, ("var", parent_variable))
            arguments.append(render_under(
                term, current_variables, renaming, anchor
            ))
        return names[id(parent)] + "".join(
            " (" + argument + ")" for argument in arguments
        )

    lines = [
        "import JudgeProblem",
        "",
        "def submission : Goal := by",
        "  intro G _ h",
    ]
    if target[2]:
        lines.append("  intro " + " ".join(target[2]))
    maximum_formula_chars = 0
    for recipe in order:
        variables = recipe_variables(recipe)
        renaming = {
            variable: "v" + str(index)
            for index, variable in enumerate(variables)
        }
        anchor = (
            renaming[variables[0]] if variables else target[2][0]
        )
        lhs = render_under(recipe.lhs, set(variables), renaming, anchor)
        rhs = render_under(recipe.rhs, set(variables), renaming, anchor)
        maximum_formula_chars = max(
            maximum_formula_chars, len(lhs) + len(rhs)
        )
        if recipe.kind == "source":
            substitution, reverse = recipe.data
            mapping = dict(substitution)
            arguments = [
                render_under(
                    mapping[variable], set(variables), renaming, anchor
                )
                for variable in source[2]
            ]
            expression = "h" + "".join(
                " (" + argument + ")" for argument in arguments
            )
            if reverse:
                expression = "Eq.symm (" + expression + ")"
        elif recipe.kind == "instantiate":
            expression = parent_application(
                recipe.parents[0], recipe, renaming, recipe.data
            )
        elif recipe.kind == "symmetry":
            expression = "Eq.symm (" + parent_application(
                recipe.parents[0], recipe, renaming
            ) + ")"
        elif recipe.kind == "transitivity":
            expression = "Eq.trans (" + parent_application(
                recipe.parents[0], recipe, renaming
            ) + ") (" + parent_application(
                recipe.parents[1], recipe, renaming
            ) + ")"
        elif recipe.kind == "congruence":
            side, sibling = recipe.data
            sibling_text = render_under(
                sibling, set(variables), renaming, anchor
            )
            function = (
                "fun _t => _t ◇ " + sibling_text
                if side == "left"
                else "fun _t => " + sibling_text + " ◇ _t"
            )
            expression = "congrArg (" + function + ") (" + parent_application(
                recipe.parents[0], recipe, renaming
            ) + ")"
        elif recipe.kind == "reflexivity":
            expression = "rfl"
        else:
            return None, 0, 0
        if variables:
            binder_names = " ".join(renaming[v] for v in variables)
            lines.append(
                "  have " + names[id(recipe)] + " : ∀ ("
                + binder_names + " : G), " + lhs + " = " + rhs + " := by"
            )
            lines.append("    intro " + binder_names)
            lines.append("    exact " + expression)
        else:
            lines.append(
                "  have " + names[id(recipe)] + " : " + lhs + " = "
                + rhs + " := " + expression
            )
    root_variables = recipe_variables(root)
    root_mapping = {"x": target[0], "y": target[1]}
    root_arguments = [
        render_term(root_mapping.get(variable, target[0]))
        for variable in root_variables
    ]
    lines.append(
        "  exact " + names[id(root)] + "".join(
            " (" + argument + ")" for argument in root_arguments
        )
    )
    code = "\n".join(lines) + "\n"
    return code, len(order), maximum_formula_chars


def try_streaming_singleton_candidate(source, target, timeout):
    if not streaming_singleton_shape(source, target):
        return False
    singleton = parse_equation("x = y")
    total_seconds = min(2.5, max(0.15, timeout / 40.0))
    started = time.monotonic()
    attempts = ((25, min(2.1, total_seconds)), (30, 0.35))
    for maximum_term_size, allowance in attempts:
        remaining = total_seconds - (time.monotonic() - started)
        seconds = min(allowance, remaining)
        if seconds <= 0.02:
            break
        limits = dict(COMPACT_SUPERPOSITION_PROBE)
        limits.update({
            "maximum_term_size": maximum_term_size,
            "maximum_replay_term_size": 10000,
            "maximum_depth": 12,
            "maximum_rules": 700,
            "maximum_rounds": 10000,
            "new_clauses_per_round": 10000,
            "maximum_clauses": 7000,
            "normalization_steps": 64,
            "maximum_proof_nodes": 50000,
        })
        engine = TargetGroundedRefutation(
            source, singleton, time.monotonic() + seconds, limits
        )
        recipe = engine.search.solve_streaming(age_every=2)
        if recipe is None:
            continue
        recipe = engine.inline_recipe(recipe)
        if (recipe.lhs, recipe.rhs) != singleton[:2]:
            continue
        code, proof_nodes, maximum_formula_chars = (
            make_universal_recipe_certificate(source, target, recipe)
        )
        if not code:
            continue
        code_bytes = len(code.encode("utf-8"))
        print(
            "MATHGRAPH_METRICS " + json.dumps({
                "portfolio": "streaming-singleton-collapse",
                "found": True,
                "maximum_term_size": maximum_term_size,
                "clauses": len(engine.search.clauses),
                "rounds": engine.search.rounds,
                "superpositions": engine.search.superpositions,
                "reductions": engine.search.reductions,
                "proof_nodes": proof_nodes,
                "certificate_bytes": code_bytes,
                "maximum_formula_chars": maximum_formula_chars,
            }, separators=(",", ":")),
            file=sys.stderr,
            flush=True,
        )
        if code_bytes > EqualitySearch.MAX_CERTIFICATE_BYTES:
            continue
        if judge("true", code).get("status") == "accepted":
            return True
    return False
'''


ROUTE = r'''
    # Discover whether the source law itself collapses every two carrier
    # elements.  Streaming saturation commits useful critical pairs as soon as
    # they are found; the certificate remains schematic until Lean checks it.
    if try_streaming_singleton_candidate(source, target, timeout):
        return

'''


def build(baseline, output):
    text = Path(baseline).read_text()
    method_marker = "        return self.target_proof(self.rules())\n\n    def compile(self, recipe):"
    if method_marker not in text:
        raise SystemExit("CompactSuperposition insertion marker not found")
    text = text.replace(
        method_marker,
        "        return self.target_proof(self.rules())\n\n"
        + STREAMING_METHOD
        + "\n    def compile(self, recipe):",
        1,
    )
    helper_marker = "\ndef finish_bridge_ir_candidate(source, target, search, found, portfolio):"
    if helper_marker not in text:
        raise SystemExit("helper insertion marker not found")
    text = text.replace(helper_marker, HELPERS + helper_marker, 1)
    route_marker = "    stair_seconds = min(2.0, max(0.1, timeout / 50.0))\n"
    if route_marker not in text:
        raise SystemExit("route insertion marker not found")
    text = text.replace(route_marker, ROUTE + route_marker, 1)
    Path(output).write_text(text)
    print(f"candidate_bytes={Path(output).stat().st_size}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", default="submissions/mathgraph/solver.py")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    build(args.baseline, args.output)


if __name__ == "__main__":
    main()
