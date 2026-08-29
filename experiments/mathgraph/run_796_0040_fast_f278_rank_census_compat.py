#!/usr/bin/env python3
"""Compatibility launcher adding a post-hoc f278 promotion-rank census.

The autonomous closure policy is unchanged. We record the already-sorted proposal
lists generically, then identify f278 only after all generation and promotion
choices are complete. This isolates whether the 64-wide beam loses f278 by rank.
"""
import subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_fast_f278_census.py'
s = SRC.read_text()

old = 'new = "        closure_enum=0; closure_rounds_completed=0; closure_generated=[]; closure_all=[]; closure_promoted=[]\\\\n"'
new = 'new = "        closure_enum=0; closure_rounds_completed=0; closure_generated=[]; closure_all=[]; closure_promoted=[]; closure_ranked=[]\\\\n"'
if old not in s:
    raise SystemExit('closure counter marker not found')
s = s.replace(old, new, 1)

old = 'new = "                frontier=[q for _,q in proposals[:{a.closure_new_per_round}]]\\\\n                closure_promoted.extend((closure_round+1,q) for q in frontier)\\\\n                closure_generated.append(len(frontier))\\\\n"'
new = 'new = "                closure_ranked.extend((closure_round+1,score,q) for score,q in proposals)\\\\n                frontier=[q for _,q in proposals[:{a.closure_new_per_round}]]\\\\n                closure_promoted.extend((closure_round+1,q) for q in frontier)\\\\n                closure_generated.append(len(frontier))\\\\n"'
if old not in s:
    raise SystemExit('promotion marker not found')
s = s.replace(old, new, 1)

old = "        f278_census={'posthoc_hidden_trace_only':True,'generated_hits':f278_generated,'generated_count':len(f278_generated),'promoted_hits':f278_promoted,'promoted_count':len(f278_promoted)}\n"
new = """        f278_ranked=[]
        by_round={}
        for rnd,score,q in closure_ranked:
            by_round.setdefault(rnd,[]).append((score,q))
        for rnd,items in by_round.items():
            cutoff=items[min(63,len(items)-1)][0] if items else None
            for rank,(score,q) in enumerate(items,1):
                if is_f278(q):
                    f278_ranked.append({'round':rnd,'rank':rank,'score':score,'beam_cutoff_score':cutoff,'proposal_count':len(items)})
        f278_census={'posthoc_hidden_trace_only':True,'generated_hits':f278_generated,'generated_count':len(f278_generated),'promoted_hits':f278_promoted,'promoted_count':len(f278_promoted),'ranked_hits':f278_ranked}
"""
if old not in s:
    raise SystemExit('f278 census marker not found')
s = s.replace(old, new, 1)

# Preserve the proven compatibility fix for literal braces in the post-hoc block.
needle = 'new = posthoc + "\'\'\'\\n"'
replacement = 'posthoc = posthoc.replace("{", "{{").replace("}", "}}")\nnew = posthoc + "\'\'\'\\n"'
if needle not in s:
    raise SystemExit('posthoc assembly marker not found')
s = s.replace(needle, replacement, 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_rank_compat.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s)
    patched = Path(fh.name)
try:
    raise SystemExit(subprocess.call([sys.executable, str(patched), *sys.argv[1:]], cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)
