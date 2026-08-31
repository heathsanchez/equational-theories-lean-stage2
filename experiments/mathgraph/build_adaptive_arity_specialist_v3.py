#!/usr/bin/env python3
"""Build isolated adaptive arity with an AST-exact champion invariant.

V2 correctly separated adaptive arity into a second top-level function, but its
textual invariant accidentally sliced from the champion function through the
next `run_solo` definition.  Because the new standalone adaptive function lives
between those definitions, the invariant reported a false modification.

This wrapper keeps the V2 architecture and replaces only the invariant slicer:
it extracts exactly the `run_behavioural_future_fallback` FunctionDef using
Python's AST `lineno`/`end_lineno` boundaries.  The champion function must still
be byte-for-byte identical within those exact source lines.
"""

import argparse
import ast
from pathlib import Path

import build_adaptive_arity_specialist as v2


def _exact_function(text: str) -> str:
    tree = ast.parse(text)
    node = next(
        n for n in tree.body
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
        and n.name == "run_behavioural_future_fallback"
    )
    lines = text.splitlines(keepends=True)
    return "".join(lines[node.lineno - 1:node.end_lineno])


# V2's build() resolves this global at call time, so replace only the faulty
# boundary detector while retaining all generation and non-regression checks.
v2._champion_function = _exact_function


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default=str(v2.DEFAULT_BASE))
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    v2.build(Path(args.base), Path(args.output))


if __name__ == "__main__":
    main()
