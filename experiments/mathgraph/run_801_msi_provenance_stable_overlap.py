#!/usr/bin/env python3
"""Map provenance-only splits onto the frozen depth-3-stable collision set.

This is a measurement-only wrapper around run_800_msi_provenance_edge_ablation.py.
It does not change search depth, candidates, probes, ranking, closure, or judge logic.
It records which original one-step collision classes split under each provenance
projection, then intersects those indices with the classes that remain merged
through the existing frozen depth-2 test and advance to depth 3.
"""
import subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_800_msi_provenance_edge_ablation.py'


def main():
    s = SRC.read_text()

    old = "        provenance_split_classes={{k:0 for k in provenance_modes}}\n        provenance_domain_split_classes={{k:0 for k in provenance_modes}}\n"
    new = "        provenance_split_classes={{k:0 for k in provenance_modes}}\n        provenance_split_indices={{k:set() for k in provenance_modes}}\n        provenance_domain_split_classes={{k:0 for k in provenance_modes}}\n        provenance_collision_index_by_member={{}}\n"
    if old not in s:
        raise SystemExit('provenance metric marker not found')
    s = s.replace(old, new, 1)

    old = "        for cls_i,cls in enumerate(collision_classes):\n            members=sorted(cls,key=lambda x:x[0])[:{a.collision_members}]\n"
    new = "        for cls_i,cls in enumerate(collision_classes):\n            members=sorted(cls,key=lambda x:x[0])[:{a.collision_members}]\n            for _,q0 in members: provenance_collision_index_by_member[id(q0)]=cls_i\n"
    if old not in s:
        raise SystemExit('collision census marker not found')
    s = s.replace(old, new, 1)

    old = "                if len(set(map(str,full_sigs)))>1:\n                    provenance_split_classes[mode]+=1\n"
    new = "                if len(set(map(str,full_sigs)))>1:\n                    provenance_split_classes[mode]+=1\n                    provenance_split_indices[mode].add(cls_i)\n"
    if old not in s:
        raise SystemExit('split-index marker not found')
    s = s.replace(old, new, 1)

    marker = "        def depth3_signature(rule):\n"
    block = """        provenance_depth3_stable_indices=set()\n        for members0 in depth2_remaining:\n            if members0:\n                ci=provenance_collision_index_by_member.get(id(members0[0][1]))\n                if ci is not None: provenance_depth3_stable_indices.add(ci)\n        provenance_stable_overlap={k:len(v & provenance_depth3_stable_indices) for k,v in provenance_split_indices.items()}\n        provenance_stable_overlap_indices={k:sorted(v & provenance_depth3_stable_indices) for k,v in provenance_split_indices.items()}\n        provenance_depth3_stable_count=len(provenance_depth3_stable_indices)\n\n        def depth3_signature(rule):\n"""
    if marker not in s:
        raise SystemExit('depth3 marker not found')
    s = s.replace(marker, block, 1)

    seam = "\"'provenance_examples':provenance_examples,\"\n"
    injected = (seam +
        "        \"'provenance_split_indices':{k:sorted(v) for k,v in provenance_split_indices.items()},\"\n"
        "        \"'provenance_depth3_stable_count':provenance_depth3_stable_count,\"\n"
        "        \"'provenance_stable_overlap':provenance_stable_overlap,\"\n"
        "        \"'provenance_stable_overlap_indices':provenance_stable_overlap_indices,\"\n")
    if seam not in s:
        raise SystemExit('output injection marker not found')
    s = s.replace(seam, injected, 1)
    s = s.replace("'mode':'msi-provenance-edge-ablation'", "'mode':'msi-provenance-stable-overlap'", 1)

    with tempfile.NamedTemporaryFile(mode='w', suffix='_msi_overlap.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
        fh.write(s)
        patched = Path(fh.name)
    try:
        raise SystemExit(subprocess.call([sys.executable, str(patched), *sys.argv[1:]], cwd=ROOT))
    finally:
        patched.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
