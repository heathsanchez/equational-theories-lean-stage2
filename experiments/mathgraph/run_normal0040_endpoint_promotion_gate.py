#!/usr/bin/env python3
"""Prospective endpoint-promotion gate for evaluation_normal_0040.

Protocol is frozen separately before this executable.  The experiment tests the
new residual distinction: target-RHS structured presence is not the same as
first-class equality-endpoint addressability.

A: G1/G2 base.
B: full history through residual-derived RHS reification, no endpoint promotion.
C: matched near-miss endpoint promotion.
D: target-RHS endpoint promotion.

All installed equalities are replay-valid direct instances of the source law.
"""
import importlib.util, itertools, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
RHSMOD=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-endpoint-promotion-v1.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-endpoint-promotion-gate.json'
RID='evaluation_normal_0040'

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def canon(m,t): return m.alpha_canonical_term(t,{})
def all_subterms(m,t): return list(m.walk_subterms(t))
def eqkey(m,a,b):
 names={};x=(m.alpha_canonical_term(a,names),m.alpha_canonical_term(b,names))
 names={};y=(m.alpha_canonical_term(b,names),m.alpha_canonical_term(a,names))
 return min(x,y)

def copy_nodes(m,src,dst,tag):
 off=len(dst)
 for n in src:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off

def append_proof(m,dst,proof,tag):
 ns,r=proof;off=copy_nodes(m,ns,dst,tag);return off+r

def frontier(m,sym,source,target,items,seconds=16.0):
 started=time.monotonic();Norm=sym.make_normalizer(m)
 cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=8000,overlap_candidates=7500,selected_rules=1100,replayed_rules=4500,maximum_term_size=110,maximum_proof_nodes=130000)
 s=Norm(source,target,started+seconds,cfg)
 for x in items: append_proof(m,s.nodes,x['proof'],x.get('name','endpoint-installed'))
 found=s.solve();return s,found

def source_atoms(m,source):
 vals={('var',v) for v in source[2]}
 for side in source[:2]:
  for t in all_subterms(m,side):
   if m.term_size(t)<=9: vals.add(t)
 return sorted(vals,key=lambda t:(m.term_size(t),m.render_term(t)))[:9]

def make_instance(m,selfm,source,target,mapping,tag):
 lhs=m.substitute(source[0],mapping);rhs=m.substitute(source[1],mapping)
 if max(m.term_size(lhs),m.term_size(rhs))>110:return None
 node=m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,mapping[v]) for v in source[2]),orientation=False,constructor=tag)
 if not m.replay_dag(source,[node],0,maximum_term_size=130,maximum_nodes=8):return None
 schema=(lhs,rhs,tuple(sorted(m.term_variables(lhs)|m.term_variables(rhs))))
 return {'schema':schema,'proof':([node],0),'name':tag,'activation':selfm.activation(m,schema,target)}

def endpoint_variables(source):
 out=[]
 for side in source[:2]:
  if side[0]=='var' and side[1] not in out: out.append(side[1])
 return out

def generate_endpoint_instances(m,selfm,source,target,special,tag,limit=360):
 eps=endpoint_variables(source)
 if not eps:return []
 fillers=source_atoms(m,source);out=[];seen=set();sk=canon(m,special)
 for focus in eps:
  others=[v for v in source[2] if v!=focus]
  for vals in itertools.product(fillers[:7],repeat=len(others)):
   mp={focus:special};mp.update(zip(others,vals));item=make_instance(m,selfm,source,target,mp,tag)
   if not item:continue
   # Enforce the scientific intervention: special is an actual equality endpoint.
   if sk not in (canon(m,item['schema'][0]),canon(m,item['schema'][1])):continue
   k=eqkey(m,item['schema'][0],item['schema'][1])
   if k in seen:continue
   seen.add(k);item['target_distance']=min(m.structural_distance(item['schema'][0],target[1]),m.structural_distance(item['schema'][1],target[1]));out.append(item)
   if len(out)>=limit:return out
 return out

def endpoint_metrics(m,target,s):
 rk=canon(m,target[1]);lk=canon(m,target[0]);endpoints={}
 parent={}
 def find(x):
  parent.setdefault(x,x)
  if parent[x]!=x:parent[x]=find(parent[x])
  return parent[x]
 def union(a,b):
  a=find(a);b=find(b)
  if a!=b:parent[b]=a
 for n in s.nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);endpoints[a]=n.lhs;endpoints[b]=n.rhs;union(a,b)
 rp=rk in endpoints;lp=lk in endpoints;joined=bool(rp and lp and find(rk)==find(lk))
 lsize=rsize=0;cross=None
 if lp:
  lr=find(lk);L=[t for k,t in endpoints.items() if find(k)==lr];lsize=len(L)
 else:L=[]
 if rp:
  rr=find(rk);R=[t for k,t in endpoints.items() if find(k)==rr];rsize=len(R)
 else:R=[]
 if L and R and not joined:
  L=sorted(L,key=lambda t:(m.term_size(t),m.render_term(t)))[:160];R=sorted(R,key=lambda t:(m.term_size(t),m.render_term(t)))[:160]
  cross=min(m.structural_distance(a,b) for a in L for b in R)
 rhs_struct={canon(m,u) for u in all_subterms(m,target[1]) if u[0]=='op'}
 present=set()
 for n in s.nodes:
  for side in (n.lhs,n.rhs):
   for u in all_subterms(m,side):
    if canon(m,u) in rhs_struct:present.add(canon(m,u))
 return {'rhs_endpoint_present':rp,'lhs_endpoint_present':lp,'joined':joined,'lhs_component_size':lsize,'rhs_component_size':rsize,'cross_distance':cross,'rhs_structured_present':len(present),'rhs_structured_total':len(rhs_struct)}

def run_arm(m,sym,source,target,items,seconds,tag):
 s,found=frontier(m,sym,source,target,items,seconds);ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=140,maximum_nodes=150000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 d={'closure':ok,'installed':len(items),'rules':len(s.rules),'overlaps':s.overlap_candidates,'nodes':len(s.nodes),'certificate_bytes':cert,'proof_nodes':pn,'tag':tag};d.update(endpoint_metrics(m,target,s));return d

def main():
 protocol=json.loads(PROTO.read_text())
 if not protocol.get('frozen_before_execution') or protocol.get('teacher_trace_used'):raise SystemExit('protocol invariant failed')
 m=load(SOLVER,'mg_ep0040');sym=load(SYM,'sym_ep0040');selfm=load(SELF,'self_ep0040');op=load(OPC,'op_ep0040');op.selfmod=selfm
 rhsmod=load(RHSMOD,'rhsmod_ep0040');rhsmod.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 # Reconstruct the same source-derived G1/G2 history.
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
 diag,_=frontier(m,sym,source,target,base,10.0)
 # Proper absent RHS motif used by the already-causal reification intervention.
 terms={}
 for n in diag.nodes:
  for side in (n.lhs,n.rhs):
   terms[canon(m,side)]=side
   for u in all_subterms(m,side):terms.setdefault(canon(m,u),u)
 missing=rhsmod.rhs_missing(m,target,terms);proper=rhsmod.proper_rhs_missing(m,target,missing);focus=proper or missing
 if not focus:raise SystemExit('expected residual RHS motif missing')
 miss_keys={canon(m,t) for t in missing}
 reif=rhsmod.generate_instances(m,source,target,focus,'endpoint-prior-reification',520)
 for x in reif:x['missing_hits']=rhsmod.hit_count(m,x,miss_keys)
 reif.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 history=g1[:24]+g2[:56]+reif[:72]
 # Choose a reachable structured near miss matched to the complete target RHS.
 hist_state,_=frontier(m,sym,source,target,history,12.0)
 rkey=canon(m,target[1]);reachable={}
 for n in hist_state.nodes:
  for side in (n.lhs,n.rhs):
   for u in all_subterms(m,side):
    k=canon(m,u)
    if u[0]=='op' and k!=rkey:reachable[k]=u
 near=min(reachable.values(),key=lambda t:(m.structural_distance(t,target[1]),abs(m.term_size(t)-m.term_size(target[1])),m.term_size(t),m.render_term(t)))
 Dall=generate_endpoint_instances(m,selfm,source,target,target[1],'endpoint-promotion-rhs',360)
 Call=generate_endpoint_instances(m,selfm,source,target,near,'endpoint-promotion-nearmiss',360)
 Dall.sort(key=lambda x:(x['target_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 Call.sort(key=lambda x:(x['target_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 n=min(96,len(Dall),len(Call))
 A=run_arm(m,sym,source,target,base,20.0,'A_base')
 B=run_arm(m,sym,source,target,history,20.0,'B_reified_no_endpoint')
 C=run_arm(m,sym,source,target,history+Call[:n],20.0,'C_nearmiss_endpoint') if n else {'closure':False,'error':'no_control_candidates'}
 D=run_arm(m,sym,source,target,history+Dall[:n],20.0,'D_rhs_endpoint') if n else {'closure':False,'error':'no_rhs_candidates'}
 ablation=run_arm(m,sym,source,target,history,20.0,'D_ablation') if D.get('closure') else None
 strong=bool(D.get('closure') and not B.get('closure') and not C.get('closure') and ablation and not ablation.get('closure'))
 endpoint_gain=bool(D.get('rhs_endpoint_present') and not B.get('rhs_endpoint_present') and not C.get('rhs_endpoint_present'))
 partial=endpoint_gain and not D.get('closure') and (D.get('joined') or D.get('cross_distance') is not None)
 decision='PASS_STRONG' if strong else 'PASS_PARTIAL' if partial else 'ENDPOINT_PROMOTED_NO_CONNECTION' if endpoint_gain else 'FALSIFIED_NO_ENDPOINT_ADVANTAGE'
 def show(xs,k=10):return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'target_distance':x['target_distance']} for x in xs[:k]]
 out={'schema':'mathgraph.normal0040-endpoint-promotion-gate.v1','id':RID,'J':protocol['J'],'K_rho':protocol['K_rho'],'prediction':protocol['prediction'],'endpoint_variables':endpoint_variables(source),'residual_objects':{'target_rhs':m.render_term(target[1]),'prior_rhs_motif':m.render_term(focus[0]),'near_control':m.render_term(near)},'counts':{'D_candidates':len(Dall),'C_candidates':len(Call),'installed_per_arm':n},'arms':{'A':A,'B':B,'C':C,'D':D,'D_ablation':ablation},'top_D':show(Dall),'top_C':show(Call),'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
