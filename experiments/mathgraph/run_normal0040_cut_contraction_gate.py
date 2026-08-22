#!/usr/bin/env python3
"""Prospective distance-3 cut-contraction gate for evaluation_normal_0040.

Protocol is frozen before this executable. Starting from the already validated
RHS-reification + endpoint-promotion state, synthesize only replay-valid direct
source-law instances anchored in one live target equality component. Rank by the
structural distance of the other endpoint to the opposite component.
"""
import importlib.util,itertools,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py'
EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-cut-contraction-v1.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-cut-contraction-gate.json'
RID='evaluation_normal_0040'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t):return m.alpha_canonical_term(t,{})
class UF:
 def __init__(self):self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a

def components(m,target,nodes):
 uf=UF();terms={}
 for n in nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk,rk=canon(m,target[0]),canon(m,target[1])
 if lk not in terms or rk not in terms:return uf,terms,[],[],None,None,None
 lr,rr=uf.find(lk),uf.find(rk)
 L=[t for k,t in terms.items() if uf.find(k)==lr];R=[t for k,t in terms.items() if uf.find(k)==rr]
 d=0 if lr==rr else min((m.structural_distance(a,b) for a in L for b in R),default=None)
 return uf,terms,L,R,lr,rr,d

def build_frozen(m,sym,selfm,op,rhs,ep,source,target):
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:
   sc=p['schema'];g1.append({'schema':sc,'proof':pr,'name':'g1','activation':selfm.activation(m,sc,target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128]
 diag,_=ep.frontier(m,sym,source,target,base,10.0)
 terms={}
 for n in diag.nodes:
  for side in (n.lhs,n.rhs):
   terms[canon(m,side)]=side
   for u in m.walk_subterms(side):terms.setdefault(canon(m,u),u)
 missing=rhs.rhs_missing(m,target,terms);proper=rhs.proper_rhs_missing(m,target,missing);focus=proper or missing
 if not focus:raise SystemExit('expected prior RHS residual')
 mk={canon(m,t) for t in missing}
 reif=rhs.generate_instances(m,source,target,focus,'cut-prior-reification',520)
 for x in reif:x['missing_hits']=rhs.hit_count(m,x,mk)
 reif.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 history=g1[:24]+g2[:56]+reif[:72]
 hs,_=ep.frontier(m,sym,source,target,history,12.0)
 rkey=canon(m,target[1]);reachable={}
 for n in hs.nodes:
  for side in (n.lhs,n.rhs):
   for u in m.walk_subterms(side):
    k=canon(m,u)
    if u[0]=='op' and k!=rkey:reachable[k]=u
 near=min(reachable.values(),key=lambda t:(m.structural_distance(t,target[1]),abs(m.term_size(t)-m.term_size(target[1])),m.term_size(t),m.render_term(t)))
 D=ep.generate_endpoint_instances(m,selfm,source,target,target[1],'cut-prior-endpoint',360)
 C=ep.generate_endpoint_instances(m,selfm,source,target,near,'cut-prior-nearmiss',360)
 D.sort(key=lambda x:(x['target_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 C.sort(key=lambda x:(x['target_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 n=min(96,len(D),len(C))
 return history+D[:n]

def synthesize(m,selfm,ep,source,target,L,R,base_dist):
 eps=ep.endpoint_variables(source)
 if not eps:raise SystemExit('no distinguished source endpoint variable')
 ev=eps[0];bare_left=(source[0][0]=='var' and source[0][1]==ev);bare_right=(source[1][0]=='var' and source[1][1]==ev)
 if not (bare_left or bare_right):raise SystemExit('endpoint variable is not a bare source side')
 fillers=ep.source_atoms(m,source)[:7];others=[v for v in source[2] if v!=ev]
 rows=[];seen=set()
 for side,A,B in [('L',L,R),('R',R,L)]:
  Bs=sorted(B,key=lambda t:(m.term_size(t),m.render_term(t)))[:120]
  for anchor in sorted(A,key=lambda t:(m.term_size(t),m.render_term(t)))[:100]:
   for vals in itertools.product(fillers,repeat=len(others)):
    mp={ev:anchor};mp.update(zip(others,vals));x=ep.make_instance(m,selfm,source,target,mp,'normal0040-cut-contractor')
    if not x:continue
    other=x['schema'][1] if bare_left else x['schema'][0]
    d=min((m.structural_distance(other,b) for b in Bs),default=999)
    k=ep.eqkey(m,x['schema'][0],x['schema'][1])
    if k in seen:continue
    seen.add(k);x['cross_distance']=d;x['anchor_side']=side;x['contracts']=d<base_dist;rows.append(x)
 rows.sort(key=lambda x:(x['cross_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return rows

def main():
 p=json.loads(PROTO.read_text())
 if not p.get('frozen_before_execution') or p.get('teacher_trace_used'):raise SystemExit('protocol invariant failed')
 m=load(SOLVER,'mg0040cc');sym=load(SYM,'sym0040cc');selfm=load(SELF,'self0040cc');op=load(OPC,'op0040cc');op.selfmod=selfm
 rhs=load(RHS,'rhs0040cc');rhs.selfm=selfm;ep=load(EP,'ep0040cc')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=build_frozen(m,sym,selfm,op,rhs,ep,source,target)
 s0,_=ep.frontier(m,sym,source,target,frozen,20.0);uf,terms,L,R,lr,rr,d0=components(m,target,s0.nodes)
 if d0 is None:raise SystemExit('post-endpoint cut not measurable')
 candidates=synthesize(m,selfm,ep,source,target,L,R,d0)
 good=[x for x in candidates if x['cross_distance']<d0]
 bad=[x for x in candidates if x['cross_distance']>=d0]
 n=min(96,len(good),len(bad)) if bad else min(96,len(good))
 A=ep.run_arm(m,sym,source,target,frozen,25.0,'A_frozen_endpoint_state')
 B=ep.run_arm(m,sym,source,target,frozen+bad[:n],25.0,'B_matched_noncontracting') if n and bad else {'closure':False,'cross_distance':d0,'tag':'B_matched_noncontracting','error':'no_control'}
 C=ep.run_arm(m,sym,source,target,frozen+good[:n],25.0,'C_cut_contractors') if n else {'closure':False,'cross_distance':d0,'tag':'C_cut_contractors','error':'no_contractors'}
 abl=ep.run_arm(m,sym,source,target,frozen,25.0,'C_ablation') if C.get('closure') else None
 strong=bool(C.get('closure') and not A.get('closure') and not B.get('closure') and abl and not abl.get('closure'))
 partial=bool(not C.get('closure') and C.get('cross_distance') is not None and C['cross_distance']<A.get('cross_distance',999))
 decision='PASS_STRONG' if strong else 'PASS_PARTIAL' if partial else 'JOINED_NO_TARGET' if C.get('joined') and not C.get('closure') else 'FALSIFIED_NO_CUT_CONTRACTION'
 def show(xs,k=20):return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'anchor_side':x['anchor_side'],'cross_distance':x['cross_distance'],'activation':x['activation']} for x in xs[:k]]
 out={'schema':'mathgraph.normal0040-cut-contraction-gate.v1','id':RID,'J':p['J'],'K_rho':p['K_rho'],'prediction':p['prediction'],'frozen_residual':{'lhs_component_size':len(L),'rhs_component_size':len(R),'cross_distance':d0,'nodes':len(s0.nodes),'rules':len(s0.rules),'overlaps':s0.overlap_candidates},'counts':{'all_anchored':len(candidates),'contractors':len(good),'noncontracting':len(bad),'exact_bridges':sum(x['cross_distance']==0 for x in candidates),'distance1':sum(x['cross_distance']==1 for x in candidates),'distance2':sum(x['cross_distance']==2 for x in candidates),'installed_per_arm':n},'arms':{'A':A,'B':B,'C':C,'C_ablation':abl},'best_contractors':show(good),'best_controls':show(bad),'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
