#!/usr/bin/env python3
"""RHS-directed residual reification for evaluation_normal_0040.

The prior bidirectional residual-cut gate found 120 terms in the target-LHS
component and zero terms in the target-RHS component. This gate tests the
representation-level hypothesis forced by that result: the next useful move is
not to bridge two existing components but to materialize the absent RHS region.

Matched arms:
 A: frozen G1+G2 developmental state.
 B: source instances using size/shape-matched reachable structured terms.
 C: source instances using only proper structured subterms of the target RHS
    that are absent from the frozen frontier.

Every new equality is a direct source-law instance and must replay to the
original axiom. A positive requires: C closes, A/B fail, and C ablation fails.
No external proof trace, case-specific theorem identity, or answer label enters
candidate generation.
"""
import importlib.util, itertools, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
OUT=ROOT/'experiments/mathgraph/results/normal0040-rhs-reification-gate.json'
RID='evaluation_normal_0040'


def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def copy_nodes(m,src,dst,tag):
 off=len(dst)
 for n in src:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off

def append_proof(m,dst,proof):
 ns,r=proof;off=copy_nodes(m,ns,dst,'normal0040-rhs-reification-installed');return off+r

def canon(m,t):return m.alpha_canonical_term(t,{})

def eqkey(m,a,b):
 names={};x=(m.alpha_canonical_term(a,names),m.alpha_canonical_term(b,names))
 names={};y=(m.alpha_canonical_term(b,names),m.alpha_canonical_term(a,names))
 return min(x,y)

def all_subterms(m,t):return list(m.walk_subterms(t))

def frontier(m,sym,source,target,items,seconds=10.0):
 started=time.monotonic();Norm=sym.make_normalizer(m)
 cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=7000,overlap_candidates=6500,selected_rules=1000,replayed_rules=4000,maximum_term_size=100,maximum_proof_nodes=100000)
 s=Norm(source,target,started+seconds,cfg)
 for x in items:append_proof(m,s.nodes,x['proof'])
 found=s.solve();terms={}
 for n in s.nodes:
  for side in (n.lhs,n.rhs):
   terms[canon(m,side)]=side
   for u in all_subterms(m,side):terms.setdefault(canon(m,u),u)
 return s,found,terms

def rhs_missing(m,target,terms):
 out=[];seen=set();rhs=target[1]
 for u in all_subterms(m,rhs):
  if u[0]!='op':continue
  k=canon(m,u)
  if k not in terms and k not in seen:seen.add(k);out.append(u)
 return sorted(out,key=lambda t:(-m.term_size(t),m.render_term(t)))

def proper_rhs_missing(m,target,missing):
 whole=canon(m,target[1])
 return [t for t in missing if canon(m,t)!=whole]

def source_atoms(m,source):
 vals={('var',v) for v in source[2]}
 for side in source[:2]:
  for t in all_subterms(m,side):
   if m.term_size(t)<=9:vals.add(t)
 return sorted(vals,key=lambda t:(m.term_size(t),m.render_term(t)))[:8]

def make_instance(m,source,target,mapping,tag):
 lhs=m.substitute(source[0],mapping);rhs=m.substitute(source[1],mapping)
 if max(m.term_size(lhs),m.term_size(rhs))>100:return None
 node=m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,mapping[v]) for v in source[2]),orientation=False,constructor=tag)
 if not m.replay_dag(source,[node],0,maximum_term_size=120,maximum_nodes=8):return None
 schema=(lhs,rhs,tuple(sorted(m.term_variables(lhs)|m.term_variables(rhs))))
 return {'schema':schema,'proof':([node],0),'name':tag,'activation':selfm.activation(m,schema,target)}

def generate_instances(m,source,target,specials,tag,limit=520):
 fillers=source_atoms(m,source);raw={};out=[];vars_=source[2]
 for special in specials:
  for focus in vars_:
   others=[v for v in vars_ if v!=focus]
   for vals in itertools.product(fillers[:6],repeat=len(others)):
    mp={focus:special};mp.update(zip(others,vals));item=make_instance(m,source,target,mp,tag)
    if not item:continue
    k=eqkey(m,item['schema'][0],item['schema'][1])
    if k in raw:continue
    raw[k]=item;out.append(item)
    if len(out)>=limit:return out
 return out

def hit_count(m,item,keys):
 hits=set()
 for side in item['schema'][:2]:
  for u in all_subterms(m,side):
   k=canon(m,u)
   if k in keys:hits.add(k)
 return len(hits)

def run_arm(m,sym,source,target,items,seconds,tag):
 s,found,terms=frontier(m,sym,source,target,items,seconds);ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=120,maximum_nodes=120000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 rhs_keys={canon(m,u) for u in all_subterms(m,target[1]) if u[0]=='op'}
 rhs_present=sum(k in terms for k in rhs_keys)
 return {'closure':ok,'installed':len(items),'rules':len(s.rules),'overlaps':s.overlap_candidates,'nodes':len(s.nodes),'seconds':seconds,'certificate_bytes':cert,'proof_nodes':pn,'rhs_structured_present':rhs_present,'rhs_structured_total':len(rhs_keys),'tag':tag}

def main():
 global selfm
 m=load(SOLVER,'mg_n0040_rhs');sym=load(SYM,'sym_n0040_rhs');selfm=load(SELF,'self_n0040_rhs');op=load(OPC,'op_n0040_rhs');op.selfmod=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:
   s=p['schema'];g1.append({'schema':s,'proof':pr,'name':'g1','activation':selfm.activation(m,s,target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128]
 diag,_,fterms=frontier(m,sym,source,target,base,10.0)
 missing=rhs_missing(m,target,fterms);proper=proper_rhs_missing(m,target,missing)
 focus=proper or missing
 miss_keys={canon(m,t) for t in missing}
 vals=[t for t in fterms.values() if t[0]=='op' and canon(m,t) not in miss_keys]
 vals.sort(key=lambda t:(min((m.structural_distance(t,q) for q in focus),default=999),abs(m.term_size(t)-(m.term_size(focus[0]) if focus else 1)),m.term_size(t),m.render_term(t)))
 near=[];seen=set()
 for t in vals:
  k=canon(m,t)
  if k in seen:continue
  seen.add(k);near.append(t)
  if len(near)>=max(1,len(focus)):break
 cC=generate_instances(m,source,target,focus,'normal0040-rhs-reification',520)
 cB=generate_instances(m,source,target,near,'normal0040-rhs-nearmiss-control',520)
 for x in cC:x['missing_hits']=hit_count(m,x,miss_keys)
 for x in cB:x['missing_hits']=hit_count(m,x,miss_keys)
 cC.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 cB.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 n=min(72,len(cC),len(cB)) if cB else min(72,len(cC))
 A=run_arm(m,sym,source,target,base,20.0,'A_frozen_g1_g2')
 B=run_arm(m,sym,source,target,g1[:24]+g2[:56]+cB[:n],20.0,'B_rhs_nearmiss_control') if n and cB else {'closure':False,'installed':0,'error':'no_control_candidates'}
 C=run_arm(m,sym,source,target,g1[:24]+g2[:56]+cC[:n],20.0,'C_rhs_reification') if n else {'closure':False,'installed':0,'error':'no_rhs_candidates'}
 abl=run_arm(m,sym,source,target,g1[:24]+g2[:56],20.0,'C_ablation') if C.get('closure') else None
 def show(xs,k=15):return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x['activation'],'missing_hits':x['missing_hits']} for x in xs[:k]]
 decision='PASS' if C.get('closure') and not A.get('closure') and not B.get('closure') and abl and not abl.get('closure') else 'RHS_REIFIED_NO_CLOSURE' if C.get('rhs_structured_present',0)>A.get('rhs_structured_present',0) else 'NO_RHS_REIFICATION'
 out={'schema':'mathgraph.normal0040-rhs-reification.v1','id':RID,'source':m.render_term(source[0])+' = '+m.render_term(source[1]),'target':m.render_term(target[0])+' = '+m.render_term(target[1]),'protocol':{'rhs_only_residual_objects':True,'direct_source_instances_only':True,'matched_runtime':True,'matched_candidate_count':True,'no_external_trace':True,'no_answer_label_in_generator':True},'frozen_frontier':{'nodes':len(diag.nodes),'rules':len(diag.rules),'overlaps':diag.overlap_candidates},'missing_rhs_subterms':[m.render_term(t) for t in missing],'proper_missing_rhs_subterms':[m.render_term(t) for t in proper],'near_control_terms':[m.render_term(t) for t in near],'counts':{'g1':len(g1),'g2':len(g2),'C_candidates':len(cC),'B_candidates':len(cB),'C_positive_missing':sum(x['missing_hits']>0 for x in cC),'B_positive_missing':sum(x['missing_hits']>0 for x in cB),'installed_new_per_arm':n},'arms':{'A':A,'B':B,'C':C,'C_ablation':abl},'top_C':show(cC),'top_B':show(cB),'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
