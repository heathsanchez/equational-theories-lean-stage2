#!/usr/bin/env python3
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'; SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'; RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py'; EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py'; CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py'; PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-commitment-router-v2.json'; OUT=ROOT/'experiments/mathgraph/results/normal0040-commitment-router-v2-gate.json'; RID='evaluation_normal_0040'
def load(p,n): s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def md(m,t,S): return min((m.structural_distance(t,u) for u in S),default=999)
def main():
 proto=json.loads(PROTO.read_text()); m=load(SOLVER,'mgr2'); sym=load(SYM,'symr2'); selfm=load(SELF,'selfr2'); op=load(OPC,'opr2'); op.selfmod=selfm; rhs=load(RHS,'rhsr2'); rhs.selfm=selfm; ep=load(EP,'epr2'); cut=load(CUT,'cutr2')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target); s3,_=ep.frontier(m,sym,source,target,frozen,20.0); _,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes); c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3); good=[x for x in c3 if x['cross_distance']<3]; best=min(x['cross_distance'] for x in good); step=[x for x in good if x['cross_distance']==best]; assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]]; s2,_=ep.frontier(m,sym,source,target,prior,25.0); _,_,L,R,_,_,d=cut.components(m,target,s2.nodes); assert d==2
 shellL=[t for t in L if md(m,t,R)==2]; shellR=[t for t in R if md(m,t,L)==2]; assert len(shellL)==len(shellR)==1
 # Probe only the already-built verified rewrite/equality regime. No new inference package is installed.
 Norm=sym.make_normalizer(m); cfg=dict(m.NORMALIZATION_PORTFOLIO[3]); cfg.update(source_substitutions=0,seconds=20.0,candidate_equalities=8000,overlap_candidates=7500,selected_rules=1100,replayed_rules=4500,maximum_term_size=110,maximum_proof_nodes=130000)
 n=Norm(source,target,time.monotonic()+20.0,cfg)
 for item in prior: ep.append_proof(m,n.nodes,item['proof'],item.get('name','prior'))
 n.solve()
 # Use the normalizer's verified rules to reduce the two exact shells to fixed points.
 def reduce_fp(t):
  cur=t; seen=set(); trace=[]
  for _ in range(64):
   k=m.alpha_canonical_term(cur,{})
   if k in seen: break
   seen.add(k); changed=False
   for r in list(n.rules):
    try:
     nxt=n.rewrite_once(cur,r)
    except Exception:
     nxt=None
    if nxt is not None and nxt!=cur:
     trace.append((m.render_term(cur),m.render_term(nxt))); cur=nxt; changed=True; break
   if not changed: break
  return cur,trace
 nl,tl=reduce_fp(shellL[0]); nr,tr=reduce_fp(shellR[0]); before=m.structural_distance(shellL[0],shellR[0]); after=m.structural_distance(nl,nr); equal=m.alpha_canonical_term(nl,{})==m.alpha_canonical_term(nr,{})
 yes=bool(equal or after<before)
 decision='DEVELOP_CAPABILITY:quotient-normalization-constructor' if yes else 'PROBE:P_depth3'
 out={'schema':'mathgraph.normal0040-commitment-router.v2','id':RID,'protocol':proto,'verified_geometry':{'distance':d,'lhs_shell':m.render_term(shellL[0]),'rhs_shell':m.render_term(shellR[0])},'probe':{'name':'P_normalize_shells','before_distance':before,'lhs_normal':m.render_term(nl),'rhs_normal':m.render_term(nr),'after_distance':after,'representatives_equal':equal,'lhs_steps':len(tl),'rhs_steps':len(tr),'lhs_trace':tl[:20],'rhs_trace':tr[:20],'outcome':'YES' if yes else 'NO'},'router':{'decision':decision,'surviving_worlds':['H_normal_form_identification'] if yes else ['H_deeper_composition']},'decision':'ROUTER_COMMON_ACTION_IDENTIFIED' if yes else 'ROUTER_NEXT_PROBE_REQUIRED'}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
