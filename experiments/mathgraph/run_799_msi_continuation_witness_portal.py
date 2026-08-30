#!/usr/bin/env python3
"""MSI continuation-witness portal.

The adaptive depth-2 test already established that the one-step quotient merges
rules that composed continuations can distinguish. The prior repair retained
representatives of those split classes. This ablation instead reifies the
actual depth-2 continuation witnesses as first-class rules and gives only those
witnesses the same bounded closure opportunity.

This changes representation/attachment, not generic search volume. It uses no
proof IDs, hidden proof traces, named intermediates, or row-specific lemmas.
"""
import subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_799_msi_adaptive_compositional_separator.py'


def main():
    s = SRC.read_text()

    old = "        fresh_separators=[]; split_mult=[]; depth3_split_mult=[]\n"
    new = "        fresh_separators=[]; split_mult=[]; depth3_split_mult=[]\n        depth2_witnesses={}\n"
    if old not in s:
        raise SystemExit('fresh-separator marker not found')
    s = s.replace(old, new, 1)

    old = "            first=first_children(rule,{a.child_width})\n            if target_recipe is not None: return (('TARGET',),)\n"
    new = "            first=first_children(rule,{a.child_width})\n            depth2_witnesses[id(rule)]=list(first)\n            if target_recipe is not None: return (('TARGET',),)\n"
    if old not in s:
        raise SystemExit('depth2 witness marker not found')
    s = s.replace(old, new, 1)

    old = "                    for vals in buckets.values(): fresh_separators.append(min(vals,key=lambda x:x[0]))\n"
    new = "                    # Portal: retain the continuation contexts that witnessed the split,\n                    # not the class representatives that happened to be distinguished.\n                    for vals in buckets.values():\n                        for _,member in vals:\n                            fresh_separators.extend(depth2_witnesses.get(id(member),()))\n"
    if old not in s:
        raise SystemExit('depth2 promotion marker not found')
    s = s.replace(old, new, 1)

    s = s.replace("'mode':'msi-adaptive-compositional-separator'",
                  "'mode':'msi-continuation-witness-portal'", 1)
    s = s.replace("'fresh_separators':len(fresh_separators),",
                  "'fresh_separators':len(fresh_separators),'portal_witness_candidates':len(fresh_separators),", 1)

    with tempfile.NamedTemporaryFile(mode='w', suffix='_msi_witness_portal.py',
                                     prefix='_mg_', dir=SRC.parent, delete=False) as fh:
        fh.write(s)
        patched = Path(fh.name)
    try:
        raise SystemExit(subprocess.call([sys.executable, str(patched), *sys.argv[1:]], cwd=ROOT))
    finally:
        patched.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
