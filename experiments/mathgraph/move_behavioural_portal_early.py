#!/usr/bin/env python3
"""Move the injected developmental fallback to an early diagnostic gate.

Experimental only: the same problem-blind portal is run immediately after
input/budget validation, before legacy portfolios can censor the measurement.
The late duplicate call inserted by the builder is removed.
"""

import argparse
from pathlib import Path

EARLY = '''    if not isinstance(timeout, (int, float)) or timeout <= 0:\n        return\n\n'''
LATE = '''    # Verified developmental fallback: preserve only distinctions that\n    # change reachable future proof behaviour, then replay before judging.\n    if run_behavioural_future_fallback(source, target, timeout):\n        return\n\n'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("solver")
    args = ap.parse_args()
    p = Path(args.solver)
    s = p.read_text()
    if s.count(EARLY) != 1:
        raise SystemExit(f"expected one early marker, found {s.count(EARLY)}")
    if s.count(LATE) != 1:
        raise SystemExit(f"expected one late fallback, found {s.count(LATE)}")
    s = s.replace(
        EARLY,
        EARLY + '''    # Experimental developmental gate: measure the representation\n    # portal before legacy routes can consume the row budget.\n    if run_behavioural_future_fallback(source, target, timeout):\n        return\n\n''',
        1,
    )
    s = s.replace(LATE, "", 1)
    compile(s, str(p), "exec")
    p.write_text(s)
    print(f"moved developmental portal early in {p}")


if __name__ == "__main__":
    main()
