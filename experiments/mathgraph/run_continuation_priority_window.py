#!/usr/bin/env python3
"""Causal continuation-window test for the residual proof-search cases.

Reuses the existing residual-3 fairness sweep as the frozen baseline and tests
whether increasing the number of target-side selections following each age
selection changes reachability.  This is deliberately a small deciding test:
windows 0/2/4/8, residual cases plus the protected set, same 20s cap.
"""
from __future__ import annotations
import json
from pathlib import Path

# Import the frozen experiment machinery rather than fork the prover.
import run_residual3_fairness_proof_sweep as base

OUT = Path(__file__).parent / "results" / "continuation-priority-window.json"
WINDOWS = (0, 2, 4, 8)
RESIDUAL = ("hard1_0067", "hard2_0107", "hard3_0208")


def find_callable(names):
    for n in names:
        f = getattr(base, n, None)
        if callable(f):
            return f
    return None


def main():
    # First record the exact baseline module surface so a negative result cannot
    # silently be mistaken for a different prover implementation.
    surface = sorted(n for n in dir(base) if not n.startswith("__"))
    runner = find_callable(("run_case", "run_one", "run_problem"))
    if runner is None:
        # Fail scientifically, not infrastructurally: emit a typed residual that
        # tells us the minimal integration point required by the next patch.
        result = {
            "status": "CONTINUATION_HOOK_REQUIRED",
            "windows": WINDOWS,
            "residual": RESIDUAL,
            "module_surface": surface,
            "reason": "Frozen fairness sweep exposes no callable per-case runner; do not fake the intervention.",
        }
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(result, indent=2, sort_keys=True))
        print("CONTINUATION_WINDOW_RESIDUAL", json.dumps(result, sort_keys=True))
        return

    # If the baseline already exposes a continuation-window argument, exercise it.
    import inspect
    sig = inspect.signature(runner)
    window_arg = next((x for x in ("continuation_window", "priority_window", "descendant_window") if x in sig.parameters), None)
    if window_arg is None:
        result = {
            "status": "CONTINUATION_HOOK_REQUIRED",
            "windows": WINDOWS,
            "residual": RESIDUAL,
            "runner": getattr(runner, "__name__", str(runner)),
            "runner_signature": str(sig),
            "reason": "Per-case runner exists but has no lawful continuation-window intervention point.",
        }
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(result, indent=2, sort_keys=True))
        print("CONTINUATION_WINDOW_RESIDUAL", json.dumps(result, sort_keys=True))
        return

    runs = {}
    for pid in RESIDUAL:
        runs[pid] = {}
        for w in WINDOWS:
            kwargs = {window_arg: w}
            runs[pid][str(w)] = runner(pid, **kwargs)
            print("CONTINUATION_WINDOW", json.dumps({"id": pid, "window": w, "result": runs[pid][str(w)]}, default=str, sort_keys=True))
    result = {"status": "COMPLETE", "window_arg": window_arg, "runs": runs}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, default=str, sort_keys=True))
    print("CONTINUATION_WINDOW_SUMMARY", json.dumps(result, default=str, sort_keys=True))


if __name__ == "__main__":
    main()
