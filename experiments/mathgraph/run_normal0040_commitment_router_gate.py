#!/usr/bin/env python3
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'; SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'; RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py'; EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py'; CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py'; PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-commitment-router-v1.json'; OUT=ROOT/'experiments/mathgraph/results/normal0040-commitment-router-gate.json'; RID='evaluation_normal_0040'
def load(p,n): s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def md(m,t,S): return min((m.structural_distance(t,u) for u in S),default=999)
def paths(t,p=()):
 yield p,t
 if t[0]=='op':
  yield from paths(t[1],p+('L',)); yield from paths(t[2],p+('R',))
def compatible(a,b):
 for k in set(a)&set(b):
  if a[k]!=b[k]: return False
 return True
def main():
 proto=json.loads(PROTO.read_text()); m=load(SOLVER,'mgr'); sym=load(SYM,'symr'); selfm=load(SELF,'selfr'); op=load(OPC,'opr'); op.selfmod=selfm; rhs=load(RHS,'rhsr'); rhs.selfm=selfm; ep=load(EP,'epr'); cut=load(CUT,'cutr')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target); s3,_=ep.frontier(m,sym,source,target,frozen,20.0); _,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes); c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3); good=[x for x in c3 if x['cross_distance']<3]; best=min(x['cross_distance'] for x in good); step=[x for x in good if x['cross_distance']==best]
 assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]]; s2,_=ep.frontier(m,sym,source,target,prior,25.0); _,_,L,R,_,_,d=cut.components(m,target,s2.nodes); assert d==2
 shellL=[t for t in L if md(m,t,R)==2]; shellR=[t for t in R if md(m,t,L)==2]; assert len(shellL)==len(shellR)==1
 lhs,rhs0=source[0],source[1]
 matches=[]
 for side_name,pat in [('lhs',lhs),('rhs',rhs0)]:
  for shell_name,shell in [('L',shellL[0]),('R',shellR[0])]:
   for path,subterm in paths(shell):
    if not path: continue
    mp={}
    if m.match_term(pat,subterm,mp): matches.append({'side':side_name,'shell':shell_name,'path':path,'subterm':subterm,'subst':mp})
 pairs=[]
 for i,a in enumerate(matches):
  for b in matches[i+1:]:
   if a['shell']==b['shell']: continue
   if compatible(a['subst'],b['subst']): pairs.append((a,b))
 joint=bool(pairs)
 # Commitment-router outcome map frozen by protocol semantics.
 if joint:
  surviving=['H_joint_substitution','H_overlap_generation']; common=['overlap-unification-constructor']; next_action='DEVELOP_CAPABILITY:overlap-unification-constructor'
 else:
  surviving=['H_normal_form_identification','H_deeper_composition']; common=[]; next_action='PROBE:P_normalize_shells'
 def show(x): return {'side':x['side'],'shell':x['shell'],'path':list(x['path']),'subterm':m.render_term(x['subterm']),'subst':{k:m.render_term(v) for k,v in x['subst'].items()}}
 out={'schema':'mathgraph.normal0040-commitment-router.v1','id':RID,'protocol':proto,'verified_geometry':{'distance':d,'lhs_shell':m.render_term(shellL[0]),'rhs_shell':m.render_term(shellR[0])},'probe':{'name':'P_joint_unify','matches':len(matches),'compatible_cross_shell_pairs':len(pairs),'outcome':'YES' if joint else 'NO','examples':[{'a':show(a),'b':show(b)} for a,b in pairs[:20]]},'router':{'surviving_worlds':surviving,'common_lawful_actions':common,'decision':next_action},'decision':'ROUTER_COMMON_ACTION_IDENTIFIED' if common else 'ROUTER_NEXT_PROBE_REQUIRED'}
 OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
