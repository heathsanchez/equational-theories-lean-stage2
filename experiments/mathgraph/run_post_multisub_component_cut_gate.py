#!/usr/bin/env python3
"""After residual multisubstitution crosses the missing-structure boundary, diagnose
and attack the next obstruction as an equality-component cut.

The residual-unified multisubstitution family creates the previously absent target
subterms but does not close evaluation_order5_0014, even after one generic
verified composition generation.  This gate asks a stronger question:

  are the target sides still separated in the exact equality-endpoint graph of
  the expanded replay-verified frontier?

If so, every successful bounded derivation must contain a first equality edge
crossing that component cut.  We synthesize only source-law instances capable of
crossing the cut by jointly solving the source substitution against a term in the
left component and the target-side residual obligation.  No equality body is
supplied; candidates are accepted only if they replay to the original source law.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
MULTI=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/post-multisub-component-cut-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t):return m.alpha_canonical_term(t,{})

def match_bound(pat,term,mp):
 if pat[0]=='var':
  v=pat[1]
  if v in mp:return mp[v]==term
  mp[v]=term;return True
 if term[0]!='op':return False
 return match_bound(pat[1],term[1],mp) and match_bound(pat[2],term[2],mp)

def uf_components(m,nodes):
 parent={};term_by={}
 def add(t):
  k=canon(m,t);term_by.setdefault(k,t);parent.setdefault(k,k);return k
 def find(x):
  while parent[x]!=x:
   parent[x]=parent[parent[x]];x=parent[x]
  return x
 def union(a,b):
  a=find(a);b=find(b)
  if a!=b:parent[b]=a
 for n in nodes:union(add(n.lhs),add(n.rhs))
 comps={}
 for k,t in term_by.items():comps.setdefault(find(k),[]).append(t)
 return parent,term_by,find,comps

def target_overlap(m,t,target):
 keys={canon(m,u) for side in target[:2] for u in m.walk_subterms(side) if u[0]=='op'}
 return sum(canon(m,u) in keys for u in m.walk_subterms(t) if u[0]=='op')

def build_source_bridge_family(m,source,target,left_terms,endpoint_terms,limit=600):
 lhs,rhs,vars_=source;goal=target[1];raw={}
 # Right obligations are residual-derived: exact target side first, then frontier
 # endpoints carrying the most target structure.  Exact target is necessary for
 # a terminal proof, but no equality to it is supplied.
 rights=[goal]
 ranked=sorted(endpoint_terms,key=lambda t:(-target_overlap(m,t,target),abs(m.term_size(t)-m.term_size(goal)),m.term_size(t),m.render_term(t)))
 for t in ranked[:180]:
  if canon(m,t)!=canon(m,goal):rights.append(t)
 for a in left_terms[:120]:
  for b in rights:
   # Source orientation lhs=x, so force x to the left-component term and solve
   # the remaining variables by structural matching of the source rhs to b.
   mp={lhs[1]:a} if lhs[0]=='var' else {}
   if not match_bound(rhs,b,mp):continue
   full={v:mp.get(v,('var',v)) for v in vars_}
   il=m.substitute(lhs,full);ir=m.substitute(rhs,full)
   if il!=a or ir!=b:continue
   nodes=[m.EqualityNode(il,ir,'source instance',substitution=tuple((v,full[v]) for v in vars_),orientation=False,constructor='residual-component-cut-source-instance')]
   if not m.replay_dag(source,nodes,0,maximum_term_size=220,maximum_nodes=1000):continue
   key=(canon(m,il),canon(m,ir))
   if key in raw:continue
   exact=(canon(m,ir)==canon(m,goal))
   raw[key]={'schema':(il,ir,tuple(sorted(m.term_variables(il)|m.term_variables(ir)))),'proof':(nodes,0),'name':'cut_bridge','exact_target_side':exact,'left':m.render_term(il),'right':m.render_term(ir),'mapping':{v:m.render_term(full[v]) for v in vars_}}
   if len(raw)>=limit:break
  if len(raw)>=limit:break
 out=list(raw.values());out.sort(key=lambda x:(not x['exact_target_side'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return out

def main():
 m=load(SOLVER,'mg_cut');sym=load(SYM,'sym_cut');selfmod=load(SELF,'self_cut');op=load(OPC,'op_cut');op.selfmod=selfmod;missmod=load(MISS,'miss_cut');multimod=load(MULTI,'multi_cut');multimod.selfmod=selfmod
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfmod.proposals(m,source):
  pr=selfmod.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfmod.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128]
 _,_,base_terms=missmod.frontier(m,sym,source,target,base,10.0);missing=missmod.target_missing(m,target,base_terms)
 multi=multimod.synthesize(m,source,target,missing,limit=400);hits=[x for x in multi if x.get('hits',0)>0]
 for x in hits:x['name']='multisub'
 composed=op.build_gen2(m,source,target,hits,limit=500) if hits else []
 for x in composed:x['name']='multisub_g2'
 expanded=g1[:24]+g2[:56]+hits[:32]+composed[:128]
 s,found,_=missmod.frontier(m,sym,source,target,expanded,20.0)
 parent,term_by,find,comps=uf_components(m,s.nodes)
 kl=canon(m,target[0]);kr=canon(m,target[1]);left_present=kl in parent;right_present=kr in parent
 left_root=find(kl) if left_present else None;right_root=find(kr) if right_present else None
 same=bool(left_present and right_present and left_root==right_root)
 left_terms=sorted(comps.get(left_root,[]),key=lambda t:(m.term_size(t),m.render_term(t))) if left_root is not None else [target[0]]
 endpoints=list(term_by.values())
 bridges=build_source_bridge_family(m,source,target,left_terms,endpoints,limit=600) if not same else []
 A=missmod.run_arm(m,sym,source,target,expanded,35.0,'A_post_multisub')
 C=missmod.run_arm(m,sym,source,target,expanded+bridges[:128],55.0,'C_component_cut_bridge') if bridges else A
 Abl=missmod.run_arm(m,sym,source,target,expanded,55.0,'C_ablation') if bridges and C['closure'] else None
 out={'schema':'mathgraph.post-multisub-component-cut.v1','id':RID,
  'diagnostic':{'frontier_nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates,'target_lhs_endpoint_present':left_present,'target_rhs_endpoint_present':right_present,'target_sides_same_component':same,'left_component_size':len(comps.get(left_root,[])) if left_root is not None else 0,'right_component_size':len(comps.get(right_root,[])) if right_root is not None else 0},
  'counts':{'multisub_hits':len(hits),'multisub_composed':len(composed),'cut_bridge_verified':len(bridges),'cut_bridge_exact_target_side':sum(x['exact_target_side'] for x in bridges)},
  'arms':{'A':A,'C':C,'C_ablation':Abl},
  'top_bridges':[{k:x[k] for k in ('exact_target_side','left','right','mapping')} for x in bridges[:20]],
  'protocol':{'residual_cut_derived_from_expanded_frontier':True,'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity_supplied':True,'all_bridge_candidates_replay_to_source':True},
  'decision':('PASS' if bridges and C['closure'] and not A['closure'] and Abl and not Abl['closure'] else ('BRIDGE_NO_CLOSURE' if bridges else ('ALREADY_CONNECTED' if same else 'NO_BRIDGE')))}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
