#!/usr/bin/env python3
"""Diagnose and repair the post-multisub cut-attachment residual on O5-0014.

The residual-derived multisubstitution family can create the missing target motifs,
but those operators had activation 0 and did not close.  This gate asks whether
that new structure is attached to either live target equality component.

It then synthesizes only direct replay-verified source instances whose endpoint is
already in a live component, with simultaneous substitutions allowed, and asks
whether any such attached instance crosses or contracts the cut.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/multisub-cut-attachment-gate.json';RID='evaluation_order5_0014'
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
def graph(m,nodes):
 uf=UF();terms={}
 for n in nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 return uf,terms
def match(p,t,env):
 if p[0]=='var':
  v=p[1]
  if v in env:return env[v]==t
  env[v]=t;return True
 if t[0]!='op' or p[0]!='op':return False
 return match(p[1],t[1],env) and match(p[2],t[2],env)
def direct_instance(m,source,target,env,tag):
 if any(v not in env for v in source[2]):return None
 a=m.substitute(source[0],env);b=m.substitute(source[1],env)
 if max(m.term_size(a),m.term_size(b))>160:return None
 node=m.EqualityNode(a,b,'source instance',substitution=tuple((v,env[v]) for v in source[2]),orientation=False,constructor=tag)
 if not m.replay_dag(source,[node],0,maximum_term_size=200,maximum_nodes=8):return None
 s=(a,b,tuple(sorted(m.term_variables(a)|m.term_variables(b))))
 return {'schema':s,'proof':([node],0),'name':tag,'activation':selfm.activation(m,s,target),'changed':sum(env[v]!=('var',v) for v in source[2])}
def build_post_state(m,sym,source,target,g1,g2):
 # Reification followed by tree completion, matching the prior component-boundary lineage.
 base=g1[:32]+g2[:128];_,_,t0=reify.frontier(m,sym,source,target,base,10.0);miss0=reify.target_missing(m,target,t0);proper=reify.proper_missing(m,target,miss0)
 c1=reify.generate_instances(m,source,target,proper,'retained-reification',520);k0={canon(m,t) for t in miss0}
 for x in c1:x['missing_hits']=reify.hit_count(m,x,k0)
 c1.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state1=g1[:24]+g2[:56]+c1[:72];_,_,t1=reify.frontier(m,sym,source,target,state1,15.0);miss1=reify.target_missing(m,target,t1);postkeys=set(t1)
 fill=[q for q in miss1 if q[0]=='op' and canon(m,q[1]) in postkeys and canon(m,q[2]) in postkeys]
 c2=reify.generate_instances(m,source,target,fill,'retained-tree-completion',520);k1={canon(m,t) for t in miss1}
 for x in c2:x['missing_hits']=reify.hit_count(m,x,k1)
 c2.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return g1[:20]+g2[:40]+c1[:48]+c2[:72]
def main():
 global selfm,reify
 m=load(SOLVER,'mg_mca');sym=load(SYM,'sym_mca');selfm=load(SELF,'self_mca');op=load(OPC,'op_mca');op.selfmod=selfm;reify=load(REIFY,'reify_mca');reify.selfm=selfm;ms=load(MS,'ms_mca');ms.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state=build_post_state(m,sym,source,target,g1,g2);s,_,terms0=reify.frontier(m,sym,source,target,state,20.0);uf,terms=graph(m,s.nodes);lk=canon(m,target[0]);rk=canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 L=[t for k,t in terms.items() if uf.find(k)==lr];R=[t for k,t in terms.items() if uf.find(k)==rr]
 # Recompute residual multisub family from this post-development frontier.
 missing=reify.target_missing(m,target,terms0);multi=ms.synthesize(m,source,target,missing)
 def cls(t):
  k=canon(m,t)
  return uf.find(k) if k in terms else None
 rows=[];exact=one=detached=subattach=0
 for x in multi:
  a,b,_=x['schema'];ca,cb=cls(a),cls(b);is_exact=(ca==lr and cb==rr) or (ca==rr and cb==lr);is_one=(ca in (lr,rr)) or (cb in (lr,rr));subs=set()
  for z in list(m.walk_subterms(a))+list(m.walk_subterms(b)):
   cz=cls(z)
   if cz in (lr,rr):subs.add('L' if cz==lr else 'R')
  if is_exact:exact+=1
  elif is_one:one+=1
  else:detached+=1
  if subs:subattach+=1
  rows.append({'lhs':m.render_term(a),'rhs':m.render_term(b),'lhs_component':str(ca),'rhs_component':str(cb),'exact_bridge':is_exact,'one_sided':is_one,'subterm_attachment':sorted(subs),'activation':x.get('activation',0)})
 # Synthesize direct source instances hard-constrained by endpoint membership.
 attached=[];bridges=[];seen=set()
 for side_name,component_terms,root in [('L',L,lr),('R',R,rr)]:
  other=rr if root==lr else lr
  for t in component_terms:
   for orient,pat in [(False,source[0]),(True,source[1])]:
    env={}
    if not match(pat,t,env) or any(v not in env for v in source[2]):continue
    item=direct_instance(m,source,target,env,'cut-attached-multisub-source-instance')
    if not item:continue
    a,b,_=item['schema'];u=b if not orient else a;cu=cls(u);key=(canon(m,a),canon(m,b))
    if key in seen:continue
    seen.add(key);rec=(item,side_name,cu==other)
    attached.append(rec)
    if cu==other:bridges.append(item)
 attached_items=[x[0] for x in attached]
 attached_items.sort(key=lambda x:(-x.get('changed',0),-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 bridges.sort(key=lambda x:(-x.get('changed',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 A=reify.run_arm(m,sym,source,target,state,25.0,'A_post_development')
 B=reify.run_arm(m,sym,source,target,state+attached_items[:64],25.0,'B_cut_attached_source_instances') if attached_items else {'closure':False,'installed':0,'tag':'B_cut_attached_source_instances'}
 C=reify.run_arm(m,sym,source,target,state+bridges[:32],25.0,'C_exact_cut_bridges') if bridges else {'closure':False,'installed':0,'tag':'C_exact_cut_bridges','error':'no_exact_bridge'}
 out={'schema':'mathgraph.multisub-cut-attachment.v1','id':RID,'component_state':{'lhs_size':len(L),'rhs_size':len(R),'already_joined':lr==rr,'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates},'multisub_attachment':{'candidates':len(multi),'exact_bridge':exact,'one_sided':one,'detached':detached,'subterm_attached':subattach,'rows':rows},'attached_synthesis':{'attached_candidates':len(attached_items),'exact_bridge_candidates':len(bridges)},'arms':{'A':A,'B':B,'C':C},'protocol':{'post_development_components_recomputed':True,'multisub_basis_residual_derived':True,'endpoint_attachment_is_generation_constraint':True,'all_new_equalities_direct_source_instances_and_replay_verified':True,'no_external_proof_trace':True},'decision':'PASS_EXACT_BRIDGE' if C.get('closure') and not A.get('closure') else 'ATTACHED_CLOSURE' if B.get('closure') and not A.get('closure') else 'EXACT_BRIDGE_EXISTS_NO_CLOSURE' if bridges else 'ATTACHED_NO_BRIDGE' if attached_items else 'ALL_RELEVANT_OPERATORS_DETACHED'}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
