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

    # run_800 is itself a source-generating wrapper. Patch its generated
    # adaptive source after the provenance block has been inserted, instead of
    # trying to find depth3_signature in the wrapper text itself.
    wrapper_seam = "    s = s.replace(marker, block, 1)\n\n    # Patch only the stable field seam"
    wrapper_insert = '''    s = s.replace(marker, block, 1)\n\n    overlap_marker = "        def depth3_signature(rule):\\n"\n    overlap_block = """        provenance_depth3_stable_indices=set()\n        for members0 in depth2_remaining:\n            if members0:\n                ci=provenance_collision_index_by_member.get(id(members0[0][1]))\n                if ci is not None: provenance_depth3_stable_indices.add(ci)\n        provenance_stable_overlap=dict((k,len(v & provenance_depth3_stable_indices)) for k,v in provenance_split_indices.items())\n        provenance_stable_overlap_indices=dict((k,sorted(v & provenance_depth3_stable_indices)) for k,v in provenance_split_indices.items())\n        provenance_depth3_stable_count=len(provenance_depth3_stable_indices)\n\n        def depth3_signature(rule):\n"""\n    if overlap_marker not in s:\n        raise SystemExit('generated depth3 marker not found')\n    s = s.replace(overlap_marker, overlap_block, 1)\n\n    # Patch only the stable field seam'''
    if wrapper_seam not in s:
        raise SystemExit('run800 post-provenance seam not found')
    s = s.replace(wrapper_seam, wrapper_insert, 1)

    seam = "        \"'provenance_examples':provenance_examples,\"\n"
    injected = (seam +
        "        \"'provenance_split_indices':dict((k,sorted(v)) for k,v in provenance_split_indices.items()),\"\n"
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
