#!/usr/bin/env python3
"""Generic retention-rank diagnostic for 0040.

This wrapper does not load hidden proof IDs. It instruments the existing
behavioural selector so every shortlisted candidate reports whether it adds a
new one-step continuation signature and whether it is retained by the greedy
interface. This localizes admission vs retention without steering selection.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'

ap = argparse.ArgumentParser()
ap.add_argument('--input', required=True)
ap.add_argument('--output', required=True)
ap.add_argument('--frontier-seconds', type=float, default=30)
ap.add_argument('--given-seconds', type=float, default=10)
ap.add_argument('--frontier-rounds', type=int, default=3)
ap.add_argument('--given-steps', type=int, default=16)
ap.add_argument('--candidate-budget', type=int, default=512)
ap.add_argument('--behavioural-keep', type=int, default=512)
ap.add_argument('--probe-partners', type=int, default=64)
a = ap.parse_args()

s = SRC.read_text()
s = s.replace(
    "        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None\n",
    "        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None\n        candidate_retention=[]; retained_candidate_ranks=[]\n",
    1,
)
s = s.replace(
    "        for _,q in candidates:\n            fp,child,n=future_signature(q); behavioural_tests+=1; future_calls+=n\n            novelty=fp-current\n            if not novelty:continue\n            retained.append(q); novelty_sizes.append(len(novelty)); current.update(fp)\n",
    "        for candidate_rank,(_,q) in enumerate(candidates,1):\n            fp,child,n=future_signature(q); behavioural_tests+=1; future_calls+=n\n            novelty=fp-current\n            candidate_retention.append({'rank':candidate_rank,'future_signatures':len(fp),'novelty':len(novelty),'target_child':child is not None,'retained':bool(novelty)})\n            if not novelty:continue\n            retained.append(q); retained_candidate_ranks.append(candidate_rank); novelty_sizes.append(len(novelty)); current.update(fp)\n",
    1,
)
needle = "        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\\n'); print('BEHAVIOURAL_SEPARATOR_EXCHANGE',json.dumps(out,sort_keys=True),flush=True)\n"
replacement = "        out['candidate_retention']=candidate_retention; out['retained_candidate_ranks']=retained_candidate_ranks\n        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\\n'); print('RETENTION_RANK_DIAGNOSTIC',json.dumps(out,sort_keys=True),flush=True)\n"
if needle not in s:
    raise SystemExit('output marker not found')
s = s.replace(needle, replacement, 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_retention_runtime.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s)
    patched = Path(fh.name)
try:
    cmd = [sys.executable, str(patched),
           '--input', a.input, '--output', a.output,
           '--frontier-seconds', str(a.frontier_seconds),
           '--given-seconds', str(a.given_seconds),
           '--frontier-rounds', str(a.frontier_rounds),
           '--given-steps', str(a.given_steps),
           '--candidate-budget', str(a.candidate_budget),
           '--behavioural-keep', str(a.behavioural_keep),
           '--probe-partners', str(a.probe_partners)]
    raise SystemExit(subprocess.call(cmd, cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)
