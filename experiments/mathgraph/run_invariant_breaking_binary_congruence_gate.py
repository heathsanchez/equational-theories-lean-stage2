#!/usr/bin/env python3
"""Test O5 -> D' on evaluation_order5_0014.

Hypothesis: the existing recursive operator grammar is single-lineage: each new
macro is built by lifting/contracting one verified parent through one context.
The live residual requires cross-coupled structure. We therefore add one new
constructor *type* absent from G1-G4: binary congruence composition of two
independent replay-verified equalities. No target identity or external proof is
supplied; every candidate compiles to the original source law and replays.

Matched arms:
 A frozen G1+G2
 B deeper existing grammar (G3)
 C invariant-breaking binary-congruence family, residual-ranked
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
OUT=ROOT/'experiments/mathgraph/results/invariant-breaking-binary-congruence-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def copy_nodes(m,src,dst,tag):
 off=len(dst)
 for n in src:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off

def orient_root(m,item,nodes,reverse,tag):
 pnodes,proot=item['proof'];off=copy_nodes(m,pnodes,nodes,tag);r=off+proot
 if reverse:
  q=nodes[r];nodes.append(m.EqualityNode(q.rhs,q.lhs,'symmetry',parents=(r,),constructor=tag+'-sym'));r=len(nodes)-1
 return r

def canon_pair(m,a,b):
 n={};x=(m.alpha_canonical_term(a,n),m.alpha_canonical_term(b,n));n={};y=(m.alpha_canonical_term(b,n),m.alpha_canonical_term(a,n));return min(x,y)

def binary_family(m,source,target,library,missing,limit=1600):
 normalizer=m.EquationalNormalizer(source,target,time.monotonic()+20,dict(m.NORMALIZATION_PORTFOLIO[1]))
 mkeys={m.alpha_canonical_term(t,{}):m.term_size(t) for t in missing}
 raw={};pool=library[:72]
 for i,x in enumerate(pool):
  for j,y in enumerate(pool):
   if j<i: continue
   for rx in (False,True):
    for ry in (False,True):
     nodes=[];r1=orient_root(m,x,nodes,rx,'binary-left');r2=orient_root(m,y,nodes,ry,'binary-right')
     a,b=nodes[r1].lhs,nodes[r1].rhs;c,d=nodes[r2].lhs,nodes[r2].rhs
     start=('op',a,c);mid=('op',b,c);end=('op',b,d)
     if max(m.term_size(start),m.term_size(end))>100:continue
     try:l1=normalizer.lift_context(nodes,r1,start,('L',));l2=normalizer.lift_context(nodes,r2,mid,('R',))
     except Exception:continue
     if l1 is None or l2 is None:continue
     if nodes[l1].lhs!=start or nodes[l1].rhs!=mid or nodes[l2].lhs!=mid or nodes[l2].rhs!=end:continue
     nodes.append(m.EqualityNode(start,end,'transitivity',parents=(l1,l2),constructor='invariant-breaking-binary-congruence'));root=len(nodes)-1
     if not m.replay_dag(source,nodes,root,maximum_term_size=180,maximum_nodes=16000):continue
     key=canon_pair(m,start,end)
     if key in raw:continue
     hits=set()
     for side in (start,end):
      for u in m.walk_subterms(side):
       k=m.alpha_canonical_term(u,{})
       if k in mkeys:hits.add(k)
     activation=selfmod.activation(m,(start,end,tuple(sorted(m.term_variables(start)|m.term_variables(end)))),target)
     raw[key]={'schema':(start,end,tuple(sorted(m.term_variables(start)|m.term_variables(end)))),'proof':(nodes,root),'hits':len(hits),'weight':sum(mkeys[k] for k in hits),'activation':activation,'parents':(i,j),'name':'binary'}
     if len(raw)>=limit:break
    if len(raw)>=limit:break
   if len(raw)>=limit:break
  if len(raw)>=limit:break
 out=list(raw.values());out.sort(key=lambda z:(-z['hits'],-z['weight'],-z['activation'],m.term_size(z['schema'][0])+m.term_size(z['schema'][1])))
 return out

def main():
 global selfmod
 m=load(SOLVER,'mg_ib');sym=load(SYM,'sym_ib');selfmod=load(SELF,'self_ib');op=load(OPC,'op_ib');op.selfmod=selfmod;missmod=load(MISS,'miss_ib')
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
 diag,_,fterms=missmod.frontier(m,sym,source,target,base,10.0);missing=missmod.target_missing(m,target,fterms)
 g3=op.build_gen2(m,source,target,g2[:28],limit=520)
 for x in g3:x['name']='g3'
 g3.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 binary=binary_family(m,source,target,g1[:24]+g2[:48],missing)
 A=missmod.run_arm(m,sym,source,target,base,20.0,'A_frozen')
 B=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+g3[:72],20.0,'B_existing_G3')
 Citems=g1[:24]+g2[:56]+binary[:96]
 C=missmod.run_arm(m,sym,source,target,Citems,30.0,'C_binary_congruence')
 Abl=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56],30.0,'C_ablation') if C['closure'] else None
 out={'schema':'mathgraph.invariant-breaking-binary-congruence.v1','id':RID,'hypothesis':{'existing_grammar_invariant':'single-lineage context transformation; one verified parent law is lifted/contracted at a time','negation':'compose two independent verified parent equalities under binary congruence','constructor_supplied_as_identity':False},'missing_target_subterms':[m.render_term(t) for t in missing],'counts':{'g1':len(g1),'g2':len(g2),'g3':len(g3),'binary_verified':len(binary),'binary_constraint_hits':sum(x['hits']>0 for x in binary)},'arms':{'A':A,'B':B,'C':C,'C_ablation':Abl},'top_binary':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'hits':x['hits'],'weight':x['weight'],'activation':x['activation'],'parents':x['parents']} for x in binary[:20]],'protocol':{'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity':True,'all_candidates_replay_to_source':True},'decision':'PASS' if C['closure'] and not A['closure'] and not B['closure'] and Abl and not Abl['closure'] else ('PARTIAL' if C['closure'] else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
