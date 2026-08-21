#!/usr/bin/env python3
"""Residual-cut two-source-chain gate for evaluation_order5_0014.

Prior post-development tests established:
  * target lhs/rhs occupy distinct verified equality components;
  * no direct replay-verified source instance crosses the cut;
  * no congruence-completion pair exists;
  * ten broader direct source-instance proposal families do not close it.

This gate therefore negates the remaining "one source instance = one operator"
restriction.  It searches for a *new intermediate term M* such that two
independently replay-verified instances of the original source law establish

    A = M    and    M = B

with A in the target-lhs component and B in the target-rhs component.  When a
pair is found, the new operator family is the transitive composition of those
two source instances.  This is not a new trusted inference rule: source
instances + symmetry + transitivity are already trusted and the complete
composite proof is replay checked against the original source law.

No external proof trace or answer identity is used.  The residual contributes
only the component-cut constraint.
"""
import importlib.util, itertools, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
CC=ROOT/'experiments/mathgraph/run_residual_cut_congruence_completion_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-cut-two-source-chain-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t): return m.alpha_canonical_term(t,{})

def orient_item(m,item,want_left=None,want_right=None,tag='two-source-chain'):
 ns,root=item['proof']; ns=list(ns); n=ns[root]
 if (want_left is None or canon(m,n.lhs)==want_left) and (want_right is None or canon(m,n.rhs)==want_right): return ns,root
 if (want_left is None or canon(m,n.rhs)==want_left) and (want_right is None or canon(m,n.lhs)==want_right):
  ns.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(root,),constructor=tag));return ns,len(ns)-1
 return None

def compose(m,source,item1,item2,mid_key):
 a=orient_item(m,item1,want_right=mid_key)
 b=orient_item(m,item2,want_left=mid_key)
 if not a or not b:return None
 n1,r1=a;n2,r2=b
 off=len(n1)
 for n in n2:
  n1.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'two-source-chain',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 r2+=off
 L=n1[r1];R=n1[r2]
 if L.rhs!=R.lhs:return None
 n1.append(m.EqualityNode(L.lhs,R.rhs,'transitivity',parents=(r1,r2),constructor='residual-cut-two-source-chain'));root=len(n1)-1
 if not m.replay_dag(source,n1,root,maximum_term_size=160,maximum_nodes=64):return None
 schema=(n1[root].lhs,n1[root].rhs,tuple(sorted(m.term_variables(n1[root].lhs)|m.term_variables(n1[root].rhs))))
 return {'schema':schema,'proof':(n1,root),'name':'residual-cut-two-source-chain','activation':0.0}

def main():
 m=load(SOLVER,'mg_chain');sym=load(SYM,'sym_chain');selfm=load(SELF,'self_chain');op=load(OPC,'op_chain');r=load(REIFY,'reify_chain');cc=load(CC,'cc_chain');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=cc.build_state(m,sym,selfm,op,r,source,target)
 s,_,_=r.frontier(m,sym,source,target,state,20.0)
 uf,adj,terms=cc.graph(m,r,s.nodes)
 lk=canon(m,target[0]);rk=canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 lhs=[t for k,t in terms.items() if uf.find(k)==lr]
 rhs=[t for k,t in terms.items() if uf.find(k)==rr]
 lhs.sort(key=lambda t:(m.structural_distance(t,target[0]),m.term_size(t),m.render_term(t)))
 rhs.sort(key=lambda t:(m.structural_distance(t,target[1]),m.term_size(t),m.render_term(t)))
 # Residual-conditioned atoms: close terms from each component plus target subterms
 # and the small native source atoms.  No target equality itself is supplied.
 atoms=[];seen=set()
 for t in lhs[:12]+rhs[:12]:
  for u in m.walk_subterms(t):
   if m.term_size(u)<=18:
    k=canon(m,u)
    if k not in seen:seen.add(k);atoms.append(u)
 for side in target[:2]:
  for u in m.walk_subterms(side):
   if m.term_size(u)<=18:
    k=canon(m,u)
    if k not in seen:seen.add(k);atoms.append(u)
 for u in r.source_atoms(m,source):
  k=canon(m,u)
  if k not in seen:seen.add(k);atoms.append(u)
 atoms=sorted(atoms,key=lambda t:(m.term_size(t),m.render_term(t)))[:24]
 vars_=list(source[2])
 pool=[];keys=set();max_pool=12000
 for vals in itertools.product(atoms,repeat=len(vars_)):
  item=r.make_instance(m,source,target,dict(zip(vars_,vals)),'two-source-chain-atom-instance')
  if not item:continue
  a,b=item['schema'][:2];k=tuple(sorted((repr(canon(m,a)),repr(canon(m,b)))))
  if k in keys:continue
  keys.add(k);pool.append(item)
  if len(pool)>=max_pool:break
 lhs_keys={canon(m,t) for t in lhs};rhs_keys={canon(m,t) for t in rhs}
 # Index candidate edges by their non-component endpoint.  We want one edge
 # touching lhs component and one touching rhs component with the same middle.
 left_by_mid={}; right_by_mid={}
 for item in pool:
  a,b=item['schema'][:2];ka,kb=canon(m,a),canon(m,b)
  if ka in lhs_keys and kb not in lhs_keys:left_by_mid.setdefault(kb,[]).append(item)
  if kb in lhs_keys and ka not in lhs_keys:left_by_mid.setdefault(ka,[]).append(item)
  if ka in rhs_keys and kb not in rhs_keys:right_by_mid.setdefault(kb,[]).append(item)
  if kb in rhs_keys and ka not in rhs_keys:right_by_mid.setdefault(ka,[]).append(item)
 mids=sorted(set(left_by_mid)&set(right_by_mid),key=repr)
 composites=[];witnesses=[];seen_comp=set()
 for mid in mids:
  for a in left_by_mid[mid][:8]:
   for b in right_by_mid[mid][:8]:
    c=compose(m,source,a,b,mid)
    if not c:continue
    x,y=c['schema'][:2];ck=tuple(sorted((repr(canon(m,x)),repr(canon(m,y)))))
    if ck in seen_comp:continue
    seen_comp.add(ck);c['activation']=selfm.activation(m,c['schema'],target);composites.append(c)
    witnesses.append({'mid':m.render_term(a['schema'][0] if canon(m,a['schema'][0])==mid else a['schema'][1]),'lhs_edge':m.render_term(a['schema'][0])+' = '+m.render_term(a['schema'][1]),'rhs_edge':m.render_term(b['schema'][0])+' = '+m.render_term(b['schema'][1])})
    if len(composites)>=256:break
   if len(composites)>=256:break
  if len(composites)>=256:break
 composites.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 baseline=r.run_arm(m,sym,source,target,state,20.0,'baseline_post_development')
 intervention=r.run_arm(m,sym,source,target,state+composites[:96],30.0,'two_source_chain_intervention') if composites else {'closure':False,'installed':0,'error':'no_composites'}
 ablation=r.run_arm(m,sym,source,target,state,30.0,'two_source_chain_ablation') if intervention.get('closure') else None
 out={'schema':'mathgraph.residual-cut-two-source-chain.v1','id':RID,'protocol':{'post_development_cut_recomputed':True,'no_external_proof_trace':True,'no_answer_label':True,'new_family_is_two_replay_verified_source_instances_plus_transitivity':True},'component_state':{'lhs_size':len(lhs),'rhs_size':len(rhs),'already_joined':lr==rr,'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates},'atom_count':len(atoms),'source_instance_pool':len(pool),'shared_middle_terms':len(mids),'composite_candidates':len(composites),'witnesses':witnesses[:12],'baseline':baseline,'intervention':intervention,'ablation':ablation,'decision':'PASS' if intervention.get('closure') and not baseline.get('closure') and ablation and not ablation.get('closure') else ('CLOSURE_NO_CAUSAL_ABLATION' if intervention.get('closure') else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
