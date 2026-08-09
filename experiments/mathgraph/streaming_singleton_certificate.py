#!/usr/bin/env python3
import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path


def load_solver(path):
    spec = importlib.util.spec_from_file_location("mg_streaming_solver", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def oriented_rules(search, clause):
    oriented = search.orient(clause)
    if oriented is not None:
        return [oriented]
    module = search.m
    out = []
    if clause.lhs[0] != "var":
        out.append(clause)
    if clause.rhs[0] != "var":
        out.append(module.Recipe(clause.rhs, clause.lhs, "symmetry", (clause,)))
    return out


def discover_singleton(module, source, seconds, max_term, age_every=2):
    singleton = module.parse_equation("x = y")
    limits = dict(module.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "maximum_term_size": max_term,
        "maximum_depth": 12,
        "maximum_rules": 700,
        "maximum_clauses": 7000,
        "normalization_steps": 64,
    })
    engine = module.TargetGroundedRefutation(
        source, singleton, time.monotonic() + seconds, limits
    )
    search = engine.search
    processed = set()
    active = []
    tick = 0
    found = None
    started = time.monotonic()
    while time.monotonic() < search.deadline:
        available = [i for i in range(len(search.clauses)) if i not in processed]
        if not available:
            break
        tick += 1
        if tick % age_every == 0:
            index = available[0]
        else:
            index = min(
                available,
                key=lambda i: (
                    module.term_size(search.clauses[i].lhs)
                    + module.term_size(search.clauses[i].rhs),
                    search.clauses[i].cost,
                    i,
                ),
            )
        processed.add(index)
        given_rules = oriented_rules(search, search.clauses[index])
        simplifying_rules = active + given_rules
        pending = []
        for given in given_rules:
            for prior_index, prior in enumerate(active + [given]):
                for outer, inner, oi, ii in (
                    (given, prior, tick, prior_index),
                    (prior, given, prior_index, tick),
                ):
                    for path in module.nonvariable_positions(
                        outer.lhs, maximum_depth=12, include_root=True
                    ):
                        if time.monotonic() >= search.deadline:
                            break
                        try:
                            proposal = search.critical_pair(outer, inner, oi, ii, path)
                        except Exception:
                            proposal = None
                        if proposal is None:
                            continue
                        if max(
                            module.term_size(proposal.lhs),
                            module.term_size(proposal.rhs),
                        ) > max_term:
                            continue
                        try:
                            proposal = search.interreduce(proposal, simplifying_rules)
                        except Exception:
                            continue
                        if max(
                            module.term_size(proposal.lhs),
                            module.term_size(proposal.rhs),
                        ) <= max_term:
                            pending.append(proposal)
                    if time.monotonic() >= search.deadline:
                        break
                if time.monotonic() >= search.deadline:
                    break
            if time.monotonic() >= search.deadline:
                break
        pending.sort(
            key=lambda q: (
                module.term_size(q.lhs) + module.term_size(q.rhs),
                q.cost,
                search.target_score(q),
            )
        )
        for proposal in pending:
            search.add_clause(proposal)
        active.extend(given_rules)
        found = search.target_proof(search.rules())
        if found is not None:
            break
    elapsed = time.monotonic() - started
    if found is None:
        return None, {
            "found": False,
            "elapsed": elapsed,
            "clauses": len(search.clauses),
            "processed": len(processed),
            "reductions": search.reductions,
        }
    root = engine.inline_recipe(found)
    return root, {
        "found": True,
        "elapsed": elapsed,
        "clauses": len(search.clauses),
        "processed": len(processed),
        "reductions": search.reductions,
        "max_recipe_cost": search.maximum_recipe_cost,
    }


def emit_universal_certificate(module, source, actual, root):
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
    names = {id(recipe): f"q{i}" for i, recipe in enumerate(order)}

    def rvars(recipe):
        return sorted(module.term_variables(recipe.lhs) | module.term_variables(recipe.rhs))

    varsets = {id(recipe): rvars(recipe) for recipe in order}

    def render_under(term, current_vars, renaming, anchor):
        mapping = {v: ("var", renaming[v]) for v in current_vars}
        for variable in module.term_variables(term):
            if variable not in mapping:
                mapping[variable] = ("var", anchor)
        return module.render_term(module.substitute_partial(term, mapping))

    def parent_app(parent, current, renaming, explicit=None):
        current_vars = set(rvars(current))
        anchor = renaming[rvars(current)[0]] if rvars(current) else "x"
        explicit = dict(explicit or ())
        args = []
        for parent_var in varsets[id(parent)]:
            term = explicit.get(parent_var, ("var", parent_var))
            args.append(render_under(term, current_vars, renaming, anchor))
        return names[id(parent)] + "".join(f" ({arg})" for arg in args)

    target_vars = list(actual[2])
    lines = [
        "import JudgeProblem",
        "",
        "def submission : Goal := by",
        "  intro G _ h",
    ]
    if target_vars:
        lines.append("  intro " + " ".join(target_vars))
    max_formula_chars = 0
    for recipe in order:
        variables = rvars(recipe)
        renaming = {v: f"v{i}" for i, v in enumerate(variables)}
        anchor = renaming[variables[0]] if variables else (target_vars[0] if target_vars else "x")
        lhs = render_under(recipe.lhs, set(variables), renaming, anchor)
        rhs = render_under(recipe.rhs, set(variables), renaming, anchor)
        max_formula_chars = max(max_formula_chars, len(lhs) + len(rhs))
        binders = (
            "∀ (" + " ".join(renaming[v] for v in variables) + " : G), "
            if variables
            else ""
        )
        if recipe.kind == "source":
            substitution, reverse = recipe.data
            mapping = dict(substitution)
            args = [
                render_under(mapping[v], set(variables), renaming, anchor)
                for v in source[2]
            ]
            expression = "h" + "".join(f" ({arg})" for arg in args)
            if reverse:
                expression = f"Eq.symm ({expression})"
        elif recipe.kind == "instantiate":
            expression = parent_app(recipe.parents[0], recipe, renaming, recipe.data)
        elif recipe.kind == "symmetry":
            expression = f"Eq.symm ({parent_app(recipe.parents[0], recipe, renaming)})"
        elif recipe.kind == "transitivity":
            expression = (
                f"Eq.trans ({parent_app(recipe.parents[0], recipe, renaming)}) "
                f"({parent_app(recipe.parents[1], recipe, renaming)})"
            )
        elif recipe.kind == "congruence":
            side, sibling = recipe.data
            sibling_text = render_under(sibling, set(variables), renaming, anchor)
            function = (
                f"fun _t => _t ◇ {sibling_text}"
                if side == "left"
                else f"fun _t => {sibling_text} ◇ _t"
            )
            expression = (
                f"congrArg ({function}) "
                f"({parent_app(recipe.parents[0], recipe, renaming)})"
            )
        elif recipe.kind == "reflexivity":
            expression = "rfl"
        else:
            raise ValueError(f"unsupported recipe kind {recipe.kind}")
        if variables:
            lines.append(
                f"  have {names[id(recipe)]} : {binders}{lhs} = {rhs} := by"
            )
            lines.append("    intro " + " ".join(renaming[v] for v in variables))
            lines.append(f"    exact {expression}")
        else:
            lines.append(
                f"  have {names[id(recipe)]} : {lhs} = {rhs} := {expression}"
            )

    root_vars = rvars(root)
    root_mapping = {"x": actual[0], "y": actual[1]}
    root_args = [
        module.render_term(root_mapping.get(v, actual[0])) for v in root_vars
    ]
    lines.append(
        "  exact " + names[id(root)] + "".join(f" ({arg})" for arg in root_args)
    )
    code = "\n".join(lines) + "\n"
    return code, {
        "recipe_nodes": len(order),
        "code_bytes": len(code.encode()),
        "max_formula_chars": max_formula_chars,
        "root_vars": root_vars,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", default="submissions/mathgraph/solver.py")
    parser.add_argument("--source", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--stats", required=True)
    parser.add_argument("--seconds", type=float, default=8.0)
    parser.add_argument("--max-term", type=int, default=30)
    parser.add_argument("--age-every", type=int, default=2)
    args = parser.parse_args()
    module = load_solver(args.solver)
    source = module.parse_equation(args.source)
    target = module.parse_equation(args.target)
    root, search_stats = discover_singleton(
        module, source, args.seconds, args.max_term, args.age_every
    )
    if root is None:
        Path(args.stats).write_text(json.dumps(search_stats, indent=2) + "\n")
        raise SystemExit("singleton collapse not found")
    code, certificate_stats = emit_universal_certificate(module, source, target, root)
    Path(args.output).write_text(code)
    stats = {**search_stats, **certificate_stats}
    Path(args.stats).write_text(json.dumps(stats, indent=2) + "\n")
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
