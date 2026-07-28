#!/usr/bin/env python3
"""Independent replay helpers for the external Stair-climber component audit.

This module deliberately does not import the external proof-plan compiler.
It checks its compact equality plans with a separate parser and rewriting
implementation.  The official Lean judge remains the final verifier.
"""

from __future__ import annotations

import re


TOKEN = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*|\(|\)|◇|\*)")


def parse_term(text):
    text = text.strip()
    tokens = []
    position = 0
    while position < len(text):
        match = TOKEN.match(text, position)
        if match is None:
            raise ValueError("invalid term")
        tokens.append("◇" if match.group(1) == "*" else match.group(1))
        position = match.end()
    cursor = 0

    def atom():
        nonlocal cursor
        if cursor >= len(tokens):
            raise ValueError("missing atom")
        token = tokens[cursor]
        if token == "(":
            cursor += 1
            result = term()
            if cursor >= len(tokens) or tokens[cursor] != ")":
                raise ValueError("missing close parenthesis")
            cursor += 1
            return result
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", token):
            cursor += 1
            return ("var", token)
        raise ValueError("invalid atom")

    def term():
        nonlocal cursor
        result = atom()
        while cursor < len(tokens) and tokens[cursor] == "◇":
            cursor += 1
            result = ("op", result, atom())
        return result

    parsed = term()
    if cursor != len(tokens):
        raise ValueError("trailing term input")
    return parsed


def parse_equation(text):
    left, separator, right = text.partition("=")
    if not separator or "=" in right:
        raise ValueError("invalid equation")
    return parse_term(left), parse_term(right)


def variables_in_order(text):
    output = []
    for variable in re.findall(r"[a-z]", text):
        if variable not in output:
            output.append(variable)
    return output


def substitute(term, substitution):
    if term[0] == "var":
        return substitution[term[1]]
    return (
        "op",
        substitute(term[1], substitution),
        substitute(term[2], substitution),
    )


def concretize(term, keep, fallback):
    if term[0] == "var":
        return term if term[1] in keep else ("var", fallback)
    return (
        "op",
        concretize(term[1], keep, fallback),
        concretize(term[2], keep, fallback),
    )


def subterm_at(term, path):
    current = term
    for direction in path:
        if current[0] != "op" or direction not in "LR":
            raise ValueError("invalid context path")
        current = current[1 if direction == "L" else 2]
    return current


def replace_at(term, path, replacement):
    if not path:
        return replacement
    if term[0] != "op":
        raise ValueError("context traverses a variable")
    if path[0] == "L":
        return ("op", replace_at(term[1], path[1:], replacement), term[2])
    if path[0] == "R":
        return ("op", term[1], replace_at(term[2], path[1:], replacement))
    raise ValueError("invalid context direction")


def replay_steps(start, steps, rules, keep, fallback):
    current = concretize(start, keep, fallback)
    for step in steps:
        rule = rules.get(step.get("rule", "h"))
        if rule is None:
            raise ValueError("unknown rule")
        left, right, variables = rule
        arguments = [
            concretize(parse_term(value), keep, fallback)
            for value in step["args"]
        ]
        if len(arguments) != len(variables):
            raise ValueError("incorrect rule arity")
        substitution = dict(zip(variables, arguments))
        instantiated_left = substitute(left, substitution)
        instantiated_right = substitute(right, substitution)
        if step["kind"] == "fwd":
            before, after = instantiated_left, instantiated_right
        elif step["kind"] == "rev":
            before, after = instantiated_right, instantiated_left
        else:
            raise ValueError("unsupported step kind")
        path = step.get("path", "")
        if subterm_at(current, path) != before:
            raise ValueError("rewrite source mismatch")
        current = replace_at(current, path, after)
    return current


def replay_plan(spec):
    source_left, source_right = parse_equation(spec["equation1"])
    target_left, target_right = parse_equation(spec["equation2"])
    rules = {
        "h": (
            source_left,
            source_right,
            variables_in_order(spec["equation1"]),
        )
    }
    target_variables = variables_in_order(spec["equation2"])
    target_fallback = target_variables[0] if target_variables else "x"
    for lemma in spec.get("lemmas", []):
        left = parse_term(lemma["lhs"])
        right = parse_term(lemma["rhs"])
        parameters = list(lemma["params"])
        fallback = parameters[0] if parameters else target_fallback
        if replay_steps(
            left, lemma["steps"], rules, set(parameters), fallback
        ) != concretize(right, set(parameters), fallback):
            raise ValueError("lemma endpoint mismatch")
        rules[lemma["name"]] = (left, right, parameters)
    if replay_steps(
        target_left,
        spec["goal_steps"],
        rules,
        set(target_variables),
        target_fallback,
    ) != target_right:
        raise ValueError("goal endpoint mismatch")
    return True


def evaluate(term, environment, table, order):
    if term[0] == "var":
        return environment[term[1]]
    return table[
        evaluate(term[1], environment, table, order) * order
        + evaluate(term[2], environment, table, order)
    ]
