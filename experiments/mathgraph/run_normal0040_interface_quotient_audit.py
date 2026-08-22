#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from collections import defaultdict
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-interface-quotient-audit-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-interface-quotient-audit.json';RID='evaluation_normal_0040'
def load(p,n):s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def md(m,t,S):return min((m.structural_distance(t,u) for u in S),default=999)
def bucket(d):return 0 if d<=0 else 1 if d==1 else 2 if d==2 else 3 if d<=4 else 5
def canon(m,t):return repr(m.alpha_canonical_term(t,{}))
def subst_pattern(m,mp,vars_):
 vals=[canon(m,mp[v]) for v in vars_ if v in mp];ids={};out=[]
 for x in vals:
  if x not in ids:ids[x]=len(ids)
  out.append(ids[x])
 return tuple(out)
def shared_nontrivial(m,t,shell):
 a={canon(m,x) for x in m.walk_subterms(t) if m.term_size(x)>=2};b={canon(m,x) for x in m.walk_subterms(shell) if m.term_size(x)>=2};return bool(a&b)
def main():
 p=json.loads(PROTO.read_text());m=load(SOLVER,'mgqa');sym=load(SYM,'symqa');selfm=load(SELF,'selfqa');op=load(OPC,'opqa');op.selfmod=selfm;rhs=load(RHS,'rhsqa');rhs.selfm=selfm;ep=load(EP,'epqa');cut=load(CUT,'cutqa');rou=load(ROU,'rouqa');rou.epmod=ep
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);good=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in good);step=[x for x in good if x['cross_distance']==best];assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes);assert d==2
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2];assert len(shellL)==len(shellR)==1
 fillers=rou.source_atoms(m,source)[:6];vars_=list(source[2]);cap=96;maxt=150
 def interactions(term,origin):
  oppshell=shellR[0] if origin=='L' else shellL[0];out=[];seen=set()
  for side_name,pat in [('lhs',source[0]),('rhs',source[1])]:
   for path,sub in rou.paths(term):
    mp={}
    if not m.match_term(pat,sub,mp):continue
    missing=[v for v in vars_ if v not in mp]
    if len(missing)>2:continue
    for vals in itertools.product(fillers,repeat=len(missing)):
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'qa')
     if not it:continue
     endpoint=it['schema'][1]
     if m.term_size(endpoint)>maxt:continue
     k=canon(m,endpoint)
     if k in seen:continue
     seen.add(k);desc=(side_name,''.join(path) if path else 'ROOT',subst_pattern(m,full,vars_),bucket(md(m,endpoint,L)),bucket(md(m,endpoint,R)),shared_nontrivial(m,endpoint,oppshell));out.append((endpoint,desc))
     if len(out)>=cap:return out
  return out
 def iface(t,o):return tuple(sorted({d for _,d in interactions(t,o)}))
 def measure(order):
  ans={}
  for o in order:
   shell=shellL[0] if o=='L' else shellR[0];front=[];seen=set();edges=0
   for e,_ in interactions(shell,o):
    k=canon(m,e)
    if k not in seen:seen.add(k);front.append(e)
   by=defaultdict(int)
   for t in front:
    ints=interactions(t,o);edges+=len(ints)
    if edges>p['audit_rules']['matched_edge_budget_per_side']:break
    by[iface(t,o)]+=1
   ans[o]={'front_terms':len(front),'classes':len(by),'edges_used':min(edges,p['audit_rules']['matched_edge_budget_per_side'])}
  return ans
 a=measure(('L','R'));b=measure(('R','L'));same=(a['L']['classes']==b['L']['classes'] and a['R']['classes']==b['R']['classes'])
 if same and a['L']['classes']==5 and a['R']['classes']==5:decision='AUDIT_CONFIRMS_5x5'
 elif same:decision='AUDIT_OTHER_STABLE_QUOTIENT'
 else:decision='AUDIT_ORDER_DEPENDENT'
 out={'schema':'mathgraph.normal0040-interface-quotient-audit.v1','id':RID,'protocol':p,'frozen_distance':d,'L_then_R':a,'R_then_L':b,'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
