#!/usr/bin/env python3
"""Apply the previously promoted bare-variable collapse activation to O5-0014.

A and C share exactly one CompactSuperposition search. A uses the current target
proof path. C scans only clauses already derived by that search for V=C where V
is absent from C, then uses the historical promoted activation: instantiate that
same derived clause twice with the two target sides, symmetry, transitivity, and
compile/replay from the original source. No external proof trace is consumed.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2];SOLVER=ROOT/'submissions/mathgraph/solver.py';OUT=ROOT/'experiments/mathgraph/results/order5-0014-compact-collapse-activation-gate.json';RID='evaluation_order5_0014';SECONDS=20.0
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def replay(m,e,recipe):
 if recipe is None:return {'closure':False}
 try:
  r=e.inline_recipe(recipe);c=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+5.0,e.search.limits);nodes,root=c.compile(r);ok=(nodes[root].lhs==e.target[0] and nodes[root].rhs==e.target[1] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes']));rec={'closure':bool(ok),'proof_nodes':len(nodes) if ok else None};
  if ok:
   code,pn=m.make_dag_certificate(e.target,nodes,root);rec.update(certificate_bytes=len(code.encode()),certificate_proof_nodes=pn)
  return rec
 except Exception as ex:return {'closure':False,'error':repr(ex)}
def collapse(m,e):
 hits=[]
 for idx,cl in enumerate(sorted(e.search.clauses,key=e.search.target_score)):
  for reverse,(vs,common) in enumerate(((cl.lhs,cl.rhs),(cl.rhs,cl.lhs))):
   if vs[0]!='var' or vs[1] in m.term_variables(common):continue
   distinguished=vs[1];variables=sorted(m.term_variables(cl.lhs)|m.term_variables(cl.rhs));anchor=('var',e.target[2][0]);base={v:anchor for v in variables};lm=dict(base);rm=dict(base);lm[distinguished]=e.target[0];rm[distinguished]=e.target[1];left=e.search.instantiate(cl,lm);right=e.search.instantiate(cl,rm)
   if reverse:
    left=m.Recipe(left.rhs,left.lhs,'symmetry',(left,));right=m.Recipe(right.rhs,right.lhs,'symmetry',(right,))
   rr=m.Recipe(right.rhs,right.lhs,'symmetry',(right,));proof=m.Recipe(left.lhs,rr.rhs,'transitivity',(left,rr));hits.append({'rank':idx,'variable':distinguished,'clause_lhs':m.render_term(cl.lhs),'clause_rhs':m.render_term(cl.rhs),'common_side':m.render_term(common),'common_size':m.term_size(common),'proof':proof})
   if proof.lhs==e.target[0] and proof.rhs==e.target[1]:return hits,proof
 return hits,None
def main():
 m=load(SOLVER,'mg_collapse0014');row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update(seconds=SECONDS,maximum_term_size=65,maximum_replay_term_size=260,maximum_depth=12,maximum_rules=1024,maximum_rounds=96,new_clauses_per_round=384,maximum_clauses=12000,normalization_steps=256,maximum_proof_nodes=80000);e=m.TargetGroundedRefutation(source,target,time.monotonic()+SECONDS,limits);started=time.monotonic();base=e.search.solve();elapsed=time.monotonic()-started;A=replay(m,e,base);hits,proof=collapse(m,e);C=replay(m,e,proof);show=[{k:v for k,v in h.items() if k!='proof'} for h in hits[:12]];out={'schema':'mathgraph.order5-0014-compact-collapse-activation.v1','id':RID,'protocol':{'same_search_A_C':True,'activation_previously_promoted_and_externally_audited':True,'C_uses_only_already_derived_clause':True,'no_external_proof_trace':True,'final_source_replay_required':True},'search':{'elapsed':elapsed,'clauses':len(e.search.clauses),'rounds':getattr(e.search,'rounds',None),'superpositions':getattr(e.search,'superpositions',None),'reductions':getattr(e.search,'reductions',None)},'A':A,'collapse_candidates':len(hits),'top_candidates':show,'C':C,'decision':'PASS' if C.get('closure') and not A.get('closure') else 'BASELINE_ALREADY_CLOSES' if A.get('closure') else 'COLLAPSE_FOUND_REPLAY_FAILED' if proof else 'NO_DERIVED_COLLAPSE_CLAUSE'};OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
