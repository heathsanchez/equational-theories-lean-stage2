#!/usr/bin/env python3
"""Finite Stage-2 approximation to MSI BehEq with the *full* continuation key.

A reachable continuation in this superposition interface is determined by the
probe, parent direction, orientations, and redex path.  Lean's BehEq quantifies
pointwise over the whole action m, so the observation coordinate must preserve
all of those components.  Search/inference budgets are unchanged.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / 'run_798_msi_minimal_repair_effect.py'
s = SRC.read_text()
marker = "s = SRC.read_text()\n"
inject = '''s = SRC.read_text()
# Preserve the complete finite continuation/action coordinate.
s = s.replace("for A,B in ((rule,p),(p,rule)):", "for di,(A,B) in enumerate(((rule,p),(p,rule))):", 1)
s = s.replace("calls+=1; out.add(sig_of(z))", "calls+=1; out.add((pi,di,ar,br,tuple(path),sig_of(z)))", 1)
'''
if marker not in s:
    raise SystemExit('source injection marker not found')
s = s.replace(marker, inject, 1)
s = s.replace("'msi-minimal-repair-effect-class'", "'msi-full-continuation-congruence'", 1)

g = {'__name__': '__main__', '__file__': str(SRC)}
exec(compile(s, str(SRC), 'exec'), g, g)
