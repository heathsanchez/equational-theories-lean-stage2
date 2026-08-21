#!/usr/bin/env python3
"""K3 intervention for evaluation_order5_0014: cut-distance reduction.

K1 (opposite provenance mixing) and K2 (anchored opposite-structure insertion)
were both instantiable but insufficient.  The K2 outputs show that attachment
alone is too weak: many rewrites stay attached while exploding away from the
opposite residual component.

K3 is therefore derived from the residual geometry itself:
  a useful anchored extension should reduce structural distance from its new
  endpoint to the opposite frozen residual component.

The metric is fixed before candidate selection.  For a term t and frozen
component C, d(t,C) is the minimum recursive binary-tree edit cost to one of the
shortest distinct terms in C.  Candidate progress is
  delta = d(anchor,C_opp) - d(rewritten,C_opp).
Positive delta means genuine contraction toward the opposite component.

Matched arms:
 A frozen post-development state
 B anchored rewrites with delta <= 0 (matched control)
 C anchored rewrites with delta > 0, ranked by delta then size
If C closes while A/B fail, C is rerun without K3 for ablation.

No Vampire trace, target-specific identity, answer label, or new trusted axiom is
used.  Target sides define only the frozen residual components.  Every installed
rewrite is produced by the existing context-lift constructor and replayed to the
original source equation.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py';ACC=ROOT/'experiments/mathgraph/run_anchored_cut_contraction_gate.py'
OUT=ROOT/'experiments/mathgraph/results/cut-distance-reduction-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def tdist(a,b,memo=None):
 if memo is None:memo={}
 k=(a,b)
 if k in memo:return memo[k]
 if a==b:r=0
 elif a[0]=='var' and b[0]=='var':r=1
 elif a[0]=='op' and b[0]=='op':r=tdist(a[1],b[1],memo)+tdist(a[2],b[2],memo)
 else:r=m.term_size(a)+m.term_size(b)
 memo[k]=r;return r

def component_distance(m,t,terms):
 if not terms:return 10**9
 return min(tdist(t,u,{}) for u in terms)

def uniq_short(m,xs,limit=48):
 seen=set();out=[]
 for t in sorted(xs,key=lambda z:(m.term_size(z),m.render_term(z))):
  k=m.alpha_canonical_term(t,{})
  if k in seen:continue
  seen.add(k);out.append(t)
  if len(out)>=limit:break
 return out

def build_candidates(m,sym,selfm,op,r,cp,acc,source,target):
 state,s,roots=acc.make_search(m,sym,selfm,op,r,cp,source,target,30);tl,tr=target[:2];comps=s.components();lc,rc=comps.get(tl),comps.get(tr)
 terms={}
 for n in s.nodes:
  for t in (n.lhs,n.rhs):
   c=comps.get(t)
   if c in (lc,rc):terms.setdefault(c,[]).append(t)
 LA=uniq_short(m,terms.get(lc,[]),40);RA=uniq_short(m,terms.get(rc,[]),40)
 opp_terms={'L':uniq_short(m,terms.get(rc,[]),48),'R':uniq_short(m,terms.get(lc,[]),48)}
 items=[item for item,q in roots]
 extra=[]
 for i,n in enumerate(s.nodes):
  if n.kind in ('source instance','source reentry') and m.term_size(n.lhs)+m.term_size(n.rhs)<=30:
   extra.append(acc.proof_item_from_root(m,s,i,'source'))
   if len(extra)>=100:break
 items+=extra
 cand=[];seen=set()
 for side,anchors in (('L',LA),('R',RA)):
  ots=opp_terms[side]
  for A in anchors:
   d0=component_distance(m,A,ots)
   for it in items:
    for rev in (False,True):
     x=acc.derive(m,source,target,it,A,rev,max_size=140)
     if not x:continue
     u,v,_=x['schema'];key=(m.alpha_canonical_term(u,{}),m.alpha_canonical_term(v,{}))
     if key in seen:continue
     seen.add(key);d1=component_distance(m,v,ots);delta=d0-d1
     x.update(anchor_side=side,d_before=d0,d_after=d1,delta=delta,size=m.term_size(v));cand.append(x)
     if len(cand)>=2200:break
    if len(cand)>=2200:break
   if len(cand)>=2200:break
  if len(cand)>=2200:break
 return s,lc,rc,cand,LA,RA

def run_arm(m,sym,selfm,op,r,cp,acc,source,target,mode):
 s,lc,rc,cand,LA,RA=build_candidates(m,sym,selfm,op,r,cp,acc,source,target);tl,tr=target[:2]
 if lc==rc:return {'closure':True,'base_joined':True,'nodes':len(s.nodes)}
 pos=[x for x in cand if x['delta']>0];non=[x for x in cand if x['delta']<=0]
 pos.sort(key=lambda x:(-x['delta'],x['d_after'],x['size']))
 # matched controls favor similar size but explicitly do not contract the cut
 non.sort(key=lambda x:(x['size'],abs(x['delta']),x['d_after']))
 chosen=[]
 if mode=='control':chosen=non[:96]
 elif mode=='k3':chosen=pos[:96]
 for x in chosen:acc.install(m,s,x,'cut-distance-installed')
 if chosen:
  pool=s.make_pool();s.instantiate_sources(pool);outer=list(range(max(0,len(s.nodes)-min(len(s.nodes),5200)),len(s.nodes)));cs=s.collect_overlap_candidates(outer,outer,4,14000)
  for q in cs[:8000]:
   if time.monotonic()>=s.deadline:break
   s.apply_overlap(q,1)
 fin=s.components();closed=fin.get(tl)==fin.get(tr)
 return {'closure':closed,'nodes':len(s.nodes),'graph_edges':s.graph_edges,'candidate_count':len(cand),'distance_reducing_candidates':len(pos),'nonreducing_candidates':len(non),'installed':len(chosen),'lhs_anchors':len(LA),'rhs_anchors':len(RA),'best_delta':(pos[0]['delta'] if pos else None),'best_after':(pos[0]['d_after'] if pos else None),'top_k3':[{'anchor_side':x['anchor_side'],'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'d_before':x['d_before'],'d_after':x['d_after'],'delta':x['delta'],'size':x['size']} for x in pos[:16]]}

def main():
 m=load(SOLVER,'mg_k3');sym=load(SYM,'sym_k3');selfm=load(SELF,'self_k3');op=load(OPC,'op_k3');r=load(REIFY,'reify_k3');cp=load(CP,'cp_k3');acc=load(ACC,'acc_k3');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 A=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'base');B=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'control');C=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'k3');ab=None
 if C.get('closure'):ab=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'base')
 decision='K3_CLOSES_WITH_ABLATION' if C.get('closure') and not A.get('closure') and not B.get('closure') and ab and not ab.get('closure') else ('K3_CLOSES' if C.get('closure') else ('K3_INSTANTIABLE_NO_CLOSURE' if C.get('distance_reducing_candidates',0)>0 else 'NO_DISTANCE_REDUCING_ANCHORED_REWRITES'))
 out={'schema':'mathgraph.cut-distance-reduction.v1','id':RID,'K3':'a useful anchored extension should reduce structural distance from its rewritten endpoint to the opposite frozen residual component','metric':'minimum recursive binary-tree edit cost to 48 shortest distinct terms of opposite frozen component','protocol':{'derived_from_K2_negative':True,'no_external_proof_trace':True,'target_only_defines_residual_cut':True,'all_extensions_replay_to_source':True,'matched_nonreducing_control':True},'arms':{'A_frozen':A,'B_nonreducing_control':B,'C_distance_reducing':C,'C_ablation':ab},'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
