#!/usr/bin/env python3
"""Fast post-hoc localization of the 0040 bridge in the full raw cross pool.

This is NOT an autonomy result. Candidate/world generation runs unchanged and
without hidden intermediate identities. Only after *all* raw cross inferences
have been generated, target-scored, sorted, deduplicated, and shortlisted do we
load the known Vampire trace for diagnosis.

The decisive question is whether f259 is:
  (A) absent from the full raw cross language,
  (B) generated but ranked outside the bounded shortlist, or
  (C) already in the shortlist (which would contradict the prior diagnostic).
We also diagnose whether the known parent capabilities f217/f258 and downstream
f15 are live in the independently generated worlds.
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
ap.add_argument('--candidate-budget', type=int, default=192)
ap.add_argument('--behavioural-keep', type=int, default=32)
ap.add_argument('--probe-partners', type=int, default=10)
a = ap.parse_args()

s = SRC.read_text()
needle = """        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None\n"""
inject = r"""        # POST-HOC ONLY: raw generation, target sorting, deduplication and
        # shortlist construction are complete before hidden trace identities load.
        TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        rigid=m.RigidSuperpositionModule(); defs={}; wanted={}
        for block in h.fof_blocks(proof):
            parsed=h.parse_fof(block)
            if not parsed:continue
            fid,kind,formula,_=parsed
            try:eq=h.formula_equality(formula)
            except Exception:eq=None
            if eq is None:continue
            x,y=eq
            if kind=='definition':
                if x[0]=='var' and x[1].startswith('sF'):defs[x[1]]=y
                elif y[0]=='var' and y[1].startswith('sF'):defs[y[1]]=x
            elif fid in {'f15','f217','f258','f259','f278'}:
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        def alpha_pair(a,b):
            names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names); return min((x,y),(y,x))
        wsig={fid:alpha_pair(*eq) for fid,eq in wanted.items()}
        def inline_pair(r,eng):return (h.inline_engine_names(r.lhs,eng.reverse_constants),h.inline_engine_names(r.rhs,eng.reverse_constants))
        def diag_match(r,fid,eng=ef):
            if fid not in wsig:return False
            try:return alpha_pair(*inline_pair(r,eng))==wsig[fid]
            except Exception:return False

        # Full raw rank: raw is already target-score sorted but not deduplicated.
        raw_hits=[]
        for rank,(score,q) in enumerate(raw,1):
            if diag_match(q,'f259',ef):raw_hits.append((rank,score,q))

        # Full deduplicated rank across the entire raw pool, without the 192 cap.
        unique_rank=None; unique_score=None; unique_total=0; seen_all=set()
        for score,q in raw:
            k=(sf.alpha_signature(q.lhs,q.rhs),q.lhs,q.rhs)
            if k in seen_all:continue
            seen_all.add(k); unique_total+=1
            if unique_rank is None and diag_match(q,'f259',ef):
                unique_rank=unique_total; unique_score=score

        shortlist_rank=next((i for i,(_,q) in enumerate(candidates,1) if diag_match(q,'f259',ef)),None)
        def world_hits(clauses,exp,eng,fid):
            return [i for i,c0 in enumerate(clauses) if diag_match(exp(c0),fid,eng)]
        frontier_hits={fid:world_hits(sf.clauses,expf,ef,fid) for fid in ('f15','f217','f258','f259')}
        given_hits={fid:world_hits(sg.clauses,expg,eg,fid) for fid in ('f15','f217','f258','f259')}

        # Inspect the provenance of the first f259 raw hit, if any, without using
        # it to change generation or ranking.
        parent_labels=[]
        if raw_hits:
            q=raw_hits[0][2]
            for p in q.parents:
                labels=[]
                for fid in ('f217','f258'):
                    if diag_match(p,fid,ef) or diag_match(p,fid,eg):labels.append(fid)
                parent_labels.append(labels)

        diag={
            'posthoc_hidden_trace_only':True,
            'cross_enumerated':cross_enum,
            'raw_cross_count':len(raw),
            'unique_cross_count':unique_total,
            'candidate_budget':len(candidates),
            'f259_in_full_raw':bool(raw_hits),
            'f259_raw_first_rank':raw_hits[0][0] if raw_hits else None,
            'f259_raw_hit_count':len(raw_hits),
            'f259_raw_first_score':raw_hits[0][1] if raw_hits else None,
            'f259_unique_rank':unique_rank,
            'f259_unique_score':unique_score,
            'f259_shortlist_rank':shortlist_rank,
            'f259_first_raw_parent_labels':parent_labels,
            'frontier_hits':frontier_hits,
            'given_hits':given_hits,
            'frontier_clauses':len(sf.clauses),
            'given_clauses':len(sg.clauses),
            'frontier_enumerated':enumf,
            'given_enumerated':enumg,
            'given_steps':givens,
        }
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(diag,indent=2,sort_keys=True)+'\n')
        print('FULL_RAW_BRIDGE_SCAN',json.dumps(diag,sort_keys=True),flush=True)
        return

        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None
"""
if needle not in s:
    raise SystemExit('post-candidate marker not found')
s=s.replace(needle,inject,1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_full_raw_bridge_runtime.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s); patched=Path(fh.name)
try:
    cmd=[sys.executable,str(patched),
         '--input',a.input,'--output',a.output,
         '--frontier-seconds',str(a.frontier_seconds),
         '--given-seconds',str(a.given_seconds),
         '--frontier-rounds',str(a.frontier_rounds),
         '--given-steps',str(a.given_steps),
         '--candidate-budget',str(a.candidate_budget),
         '--behavioural-keep',str(a.behavioural_keep),
         '--probe-partners',str(a.probe_partners)]
    raise SystemExit(subprocess.call(cmd,cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)
