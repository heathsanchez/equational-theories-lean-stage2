#!/usr/bin/env python3
"""Faithful finite approximation to MSI BehaviouralCongruence.BehEq.

The previous effect-class probe compared the union of all future observations.
Lean's BehEq is pointwise in the continuation: for every m, observations after
m must agree.  This wrapper preserves the probe/continuation index in every
future observation, so effects cannot be spuriously identified by swapping
which continuation produced them.

No proof IDs, hidden traces, named intermediates, or row-specific lemmas.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / 'run_798_msi_minimal_repair_effect.py'
s = SRC.read_text()
marker = "s = SRC.read_text()\n"
inject = "s = SRC.read_text()\n# MSI BehEq is pointwise in m: preserve the continuation index in the observation.\ns = s.replace(\"calls+=1; out.add(sig_of(z))\", \"calls+=1; out.add((pi,sig_of(z)))\", 1)\n"
if marker not in s:
    raise SystemExit('source injection marker not found')
s = s.replace(marker, inject, 1)
s = s.replace("'msi-minimal-repair-effect-class'", "'msi-indexed-continuation-congruence'", 1)

g = {'__name__': '__main__', '__file__': str(SRC)}
exec(compile(s, str(SRC), 'exec'), g, g)
