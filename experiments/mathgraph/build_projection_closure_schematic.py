#!/usr/bin/env python3
"""Upgrade projection-closure emission with schematic lemma sharing."""

import build_projection_closure_specialist as base

COMPACT = r'''    def compact_certificate(recipe):
        """Share learned schematic consequences while preserving DAG replay."""
        helper = {id(search.clauses[0]): ("h", tuple(source[2]))}
        lines = ["import JudgeProblem", "", "def submission : Goal := by", "  intro G _ h"]

        def clause_variables(clause):
            return tuple(sorted(term_variables(clause.lhs) | term_variables(clause.rhs)))

        def transform(term, environment):
            return substitute_partial(term, environment)

        def close_term(term, allowed, anchor):
            if term[0] == "var":
                return term if term[1] in allowed else ("var", anchor)
            return (
                "op",
                close_term(term[1], allowed, anchor),
                close_term(term[2], allowed, anchor),
            )

        def rendered(term, allowed, anchor):
            return render_term(close_term(term, allowed, anchor))

        def expression(current, environment, allowed, anchor):
            known = helper.get(id(current))
            if known is not None:
                name, binders = known
                arguments = [
                    rendered(transform(("var", variable), environment), allowed, anchor)
                    for variable in binders
                ]
                return name + "".join(" (" + arg + ")" for arg in arguments)
            if current.kind == "instantiate":
                mapping = {
                    variable: transform(value, environment)
                    for variable, value in current.data
                }
                for variable, value in environment.items():
                    mapping.setdefault(variable, value)
                return expression(current.parents[0], mapping, allowed, anchor)
            if current.kind == "symmetry":
                return "Eq.symm (" + expression(
                    current.parents[0], environment, allowed, anchor
                ) + ")"
            if current.kind == "transitivity":
                return "Eq.trans (" + expression(
                    current.parents[0], environment, allowed, anchor
                ) + ") (" + expression(
                    current.parents[1], environment, allowed, anchor
                ) + ")"
            if current.kind == "congruence":
                side, sibling = current.data
                sibling = rendered(transform(sibling, environment), allowed, anchor)
                parent = expression(current.parents[0], environment, allowed, anchor)
                if side == "left":
                    return "congrArg (fun _mg_t => _mg_t ◇ " + sibling + ") (" + parent + ")"
                return "congrArg (fun _mg_t => " + sibling + " ◇ _mg_t) (" + parent + ")"
            if current.kind == "reflexivity":
                return "rfl"
            if current.kind == "source":
                substitution, reverse = current.data
                mapping = {
                    variable: transform(value, environment)
                    for variable, value in substitution
                }
                arguments = [
                    rendered(mapping.get(variable, ("var", anchor)), allowed, anchor)
                    for variable in source[2]
                ]
                result = "h" + "".join(" (" + arg + ")" for arg in arguments)
                return "Eq.symm (" + result + ")" if reverse else result
            raise ValueError("unsupported compact recipe kind " + str(current.kind))

        for index, clause in enumerate(search.clauses[1:], 1):
            variables = clause_variables(clause)
            safe = tuple("v" + str(i) for i in range(len(variables)))
            if not safe:
                return None
            mapping = {
                variable: ("var", safe[i]) for i, variable in enumerate(variables)
            }
            allowed = set(safe)
            anchor = safe[0]
            lhs = render_term(substitute_partial(clause.lhs, mapping))
            rhs = render_term(substitute_partial(clause.rhs, mapping))
            body = expression(clause, mapping, allowed, anchor)
            name = "L" + str(index)
            lines.append(
                "  have " + name + " : ∀ (" + " ".join(safe) + " : G), "
                + lhs + " = " + rhs + " := by"
            )
            lines.append("    intro " + " ".join(safe))
            lines.append("    exact " + body)
            helper[id(clause)] = (name, variables)

        target_vars = tuple(target[2])
        if not target_vars:
            return None
        lines.append("  intro " + " ".join(target_vars))
        environment = {variable: ("var", variable) for variable in target_vars}
        lines.append(
            "  exact " + expression(
                recipe, environment, set(target_vars), target_vars[0]
            )
        )
        return "\n".join(lines) + "\n"

'''

OLD = '''        code, proof_nodes = make_dag_certificate(target, nodes, root)\n        if "_mg_elide_have_types" in globals():\n            old_lines = code.splitlines()\n            new_lines = _mg_elide_have_types(code).splitlines()\n            code = "\\n".join(\n                old if ":=" in old and old.rstrip().endswith(":= rfl") else new\n                for old, new in zip(old_lines, new_lines)\n            ) + "\\n"\n        code_bytes = len(code.encode("utf-8"))\n'''
NEW = '''        proof_nodes = len(proof_node_ids(nodes, root))\n        code = compact_certificate(recipe)\n        if code is None:\n            return False\n        code_bytes = len(code.encode("utf-8"))\n'''

if base.SPECIALIST.count("    def finish(recipe):\n") != 1:
    raise SystemExit("finish marker not unique")
if base.SPECIALIST.count(OLD) != 1:
    raise SystemExit("expanded certificate block not unique")
base.SPECIALIST = base.SPECIALIST.replace("    def finish(recipe):\n", COMPACT + "    def finish(recipe):\n", 1)
base.SPECIALIST = base.SPECIALIST.replace(OLD, NEW, 1)
base.main()
