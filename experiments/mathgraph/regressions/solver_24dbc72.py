"""Deterministic MathGraph Stage 2 solver.

The submission is deliberately fail-closed: it asks the official judge only
about certificates reconstructed from the incoming equation strings, and
exits without a verdict when no replayable certificate is available.
"""

import json
import sys
import time
from itertools import product


class ParseError(ValueError):
    pass


class Parser:
    """Full-consumption parser for the official single-operation equation DSL."""

    def __init__(self, text):
        self.tokens = self._tokenize(text)
        self.pos = 0

    @staticmethod
    def _tokenize(text):
        if not isinstance(text, str):
            raise ParseError("equation is not text")
        out = []
        i = 0
        while i < len(text):
            c = text[i]
            if c.isspace():
                i += 1
            elif c in "()=◇*":
                out.append("◇" if c == "*" else c)
                i += 1
            elif "a" <= c <= "z":
                # The official judge binds single lowercase variable names.
                if i + 1 < len(text) and text[i + 1].isalnum():
                    raise ParseError("variables must be single lowercase letters")
                out.append(c)
                i += 1
            else:
                raise ParseError("unexpected character")
        return out

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise ParseError("unexpected token")
        self.pos += 1
        return token

    def atom(self):
        token = self.peek()
        if token == "(":
            self.take("(")
            term = self.term()
            self.take(")")
            return term
        if token is not None and len(token) == 1 and "a" <= token <= "z":
            self.take()
            return ("var", token)
        raise ParseError("expected a variable or parenthesized term")

    def term(self):
        # Lean parses this operator left-associatively when parentheses are
        # omitted. Official data parenthesizes every nontrivial ambiguity.
        node = self.atom()
        while self.peek() == "◇":
            self.take("◇")
            node = ("op", node, self.atom())
        return node

    def equation(self):
        lhs = self.term()
        self.take("=")
        rhs = self.term()
        if self.peek() is not None:
            raise ParseError("trailing input")
        variables = []
        seen = set()
        for token in self.tokens:
            if len(token) == 1 and "a" <= token <= "z" and token not in seen:
                seen.add(token)
                variables.append(token)
        if not variables:
            raise ParseError("equation has no variables")
        return lhs, rhs, tuple(variables)


def parse_equation(text):
    return Parser(text).equation()


def render_term(term):
    if term[0] == "var":
        return term[1]
    return "(" + render_term(term[1]) + " ◇ " + render_term(term[2]) + ")"


def match_term(pattern, concrete, substitution):
    """Match a source term against a target term, extending substitution."""
    if pattern[0] == "var":
        name = pattern[1]
        previous = substitution.get(name)
        if previous is None:
            substitution[name] = concrete
            return True
        return previous == concrete
    return (
        concrete[0] == "op"
        and match_term(pattern[1], concrete[1], substitution)
        and match_term(pattern[2], concrete[2], substitution)
    )


def source_instance(source, target):
    """Return (arguments, symmetric) if target is one source instance."""
    sl, sr, source_vars = source
    tl, tr, _ = target
    for left, right, symmetric in ((tl, tr, False), (tr, tl, True)):
        substitution = {}
        if match_term(sl, left, substitution) and match_term(sr, right, substitution):
            if all(v in substitution for v in source_vars):
                return [substitution[v] for v in source_vars], symmetric
    return None


def eval_term(term, assignment, table):
    if term[0] == "var":
        return assignment[term[1]]
    return table[eval_term(term[1], assignment, table)][
        eval_term(term[2], assignment, table)
    ]


def equation_holds(equation, table):
    lhs, rhs, variables = equation
    n = len(table)
    for values in product(range(n), repeat=len(variables)):
        assignment = dict(zip(variables, values))
        if eval_term(lhs, assignment, table) != eval_term(rhs, assignment, table):
            return False
    return True


def find_fin2_countermodel(source, target, deadline):
    """Exhaust all 16 binary operations on Fin 2 and revalidate the winner."""
    for encoded in range(16):
        if time.monotonic() >= deadline:
            return None
        table = [
            [(encoded >> (2 * row + col)) & 1 for col in range(2)]
            for row in range(2)
        ]
        if equation_holds(source, table) and not equation_holds(target, table):
            # Deliberate second replay before certificate generation.
            if equation_holds(source, table) and not equation_holds(target, table):
                return table
    return None


def make_true_certificate(target, instance):
    _, _, target_vars = target
    arguments, symmetric = instance
    binders = " ".join(target_vars)
    applied = "h" + "".join(" (" + render_term(arg) + ")" for arg in arguments)
    if symmetric:
        applied = "(" + applied + ").symm"
    intro = "  intro " + binders + "\n" if binders else ""
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        + intro
        + "  exact "
        + applied
        + "\n"
    )


def make_false_certificate(table):
    compact = json.dumps(table, separators=(",", ":"))
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
        "  let candidateMagma : Magma (Fin 2) := {\n"
        '    op := finOpTable "'
        + compact
        + '"\n'
        "  }\n"
        "  refine ⟨Fin 2, candidateMagma, ?_⟩\n"
        "  decideFin!\n"
    )


def read_message():
    line = sys.stdin.readline()
    if not line:
        return None
    try:
        value = json.loads(line)
    except (json.JSONDecodeError, ValueError):
        return None
    return value if isinstance(value, dict) else None


def judge(verdict, code):
    print(json.dumps({"call": "judge", "verdict": verdict, "code": code}), flush=True)
    response = read_message()
    return response if response is not None else {}


def run_solo():
    startup = read_message()
    if startup is None:
        return
    problem = startup.get("problem")
    budget = startup.get("budget")
    if not isinstance(problem, dict) or not isinstance(budget, dict):
        return
    try:
        source = parse_equation(problem.get("equation1"))
        target = parse_equation(problem.get("equation2"))
    except (ParseError, TypeError, RecursionError):
        return

    instance = source_instance(source, target)
    if instance is not None:
        code = make_true_certificate(target, instance)
        if judge("true", code).get("status") == "accepted":
            return

    # Fin 2 is tiny, but retain an explicit hard local deadline so malformed
    # or unexpectedly large incoming terms cannot turn this stage unbounded.
    timeout = budget.get("timeout_seconds", 0)
    if not isinstance(timeout, (int, float)) or timeout <= 0:
        return
    deadline = time.monotonic() + min(1.0, max(0.05, timeout / 20.0))
    try:
        table = find_fin2_countermodel(source, target, deadline)
    except (KeyError, IndexError, RecursionError, TypeError):
        return
    if table is not None:
        code = make_false_certificate(table)
        judge("false", code)
    # Unresolved: EOF is intentional. Never guess and never ask an LLM.


def main():
    run_solo()


if __name__ == "__main__":
    main()
