#!/usr/bin/env python3
"""Residual-derived invariant breaker for evaluation_order5_0014.

Hypothesis inferred from the G1-G4 constructor algebra:
  existing recursive operator closure is unary/contextual: each generated macro
  changes one proved branch inside a fixed context at a time.  The frozen
  residual requires a cross-coupled binary motif whose two children have
  independently structured variable supports.

Invariant-breaking primitive tested here:
  BINARY FUSION.  Given two replay-verified equalities a=a' and b=b', construct
      (a ◇ b) = (a' ◇ b')
  by two ordinary congruence lifts plus transitivity.  This is not an axiom and
  adds no trust: every fused macro replays to the original source equation.

The gate derives the desired child-support signatures from the missing target
subterms, ranks parent pairs by whether fusion can introduce those signatures,
then compares:
 A: frozen G1+G2
 B: matched number of ordinary recursively generated operators
 C: G1+G2 plus replay-verified residual-conditioned binary fusions
A positive requires C closure, A/B failure, replay, and C ablation failure.
"""
import importlib.util,json,sys,time,itertools
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
OUT=ROOT/'experiments/mathgraph/results/binary-fusion-invariant-breaker-gate.json'
RID='evaluation_order5_0014'

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def copy_nodes(m,src,dst,tag):
 off=len(dst)
 for n in src:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off

def append_proof(m,dst,proof):
 ns,r=proof;off=copy_nodes(m,ns,dst,'binary-fusion-installed');return off+r

def canon(m,t):return m.alpha_canonical_term(t,{})

def all_subterms(m,t):return list(m.walk_subterms(t))

def support(m,t):return tuple(sorted(m.term_variables(t)))

def structured_support_pairs(m,t):
 out=set()
 for u in all_subterms(m,t):
  if u[0]=='op':out.add((support(m,u[1]),support(m,u[2])))
 return out

def target_missing(m,target,frontier_terms):
 miss=[];seen=set()
 for side in target[:2]:
  for u in all_subterms(m,side):
   if u[0]!='op':continue
   k=canon(m,u)
   if k not in frontier_terms and k not in seen:seen.add(k);miss.append(u)
 return sorted(miss,key=lambda t:(-m.term_size(t),m.render_term(t)))

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

def orient_item(m,item,rev):
 ns,root=item['proof'];nodes=[];off=copy_nodes(m,ns,nodes,'binary-fusion-parent');r=off+root
 n=nodes[r]
 if rev:
  rr=len(nodes);nodes.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(r,),constructor='binary-fusion-parent-symmetry'));r=rr
 return nodes,r,nodes[r].lhs,nodes[r].rhs

def fuse(m,source,target,a,b,rev_a=False,rev_b=False,max_size=100):
 na,ra,al,ar=orient_item(m,a,rev_a);nb,rb,bl,br=orient_item(m,b,rev_b)
 nodes=list(na);off=len(nodes)
 # copy second proof and offset its root
 for n in nb:
  nodes.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'binary-fusion-parent-b',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 rb2=off+rb
 # Build op(al,bl)=op(ar,bl) by congruence in left child.
 left0=('op',al,bl);left1=('op',ar,bl);right1=('op',ar,br)
 if max(m.term_size(left0),m.term_size(left1),m.term_size(right1))>max_size:return None
 # Congruence nodes are represented as context lifts through one-step contexts.
 # Use EquationalNormalizer.lift_context so replay semantics are identical to production.
 norm=m.EquationalNormalizer(source,target,time.monotonic()+2,dict(m.NORMALIZATION_PORTFOLIO[1]))
 try:
  lroot=norm.lift_context(nodes,ra,left0,('L',))
  rroot=norm.lift_context(nodes,rb2,left1,('R',))
 except Exception:return None
 if lroot is None or rroot is None:return None
 if nodes[lroot].lhs!=left0 or nodes[lroot].rhs!=left1:return None
 if nodes[rroot].lhs!=left1 or nodes[rroot].rhs!=right1:return None
 root=len(nodes);nodes.append(m.EqualityNode(left0,right1,'transitivity',parents=(lroot,rroot),constructor='binary-fusion'))
 if not m.replay_dag(source,nodes,root,maximum_term_size=180,maximum_nodes=16000):return None
 schema=(left0,right1,tuple(sorted(m.term_variables(left0)|m.term_variables(right1))))
 return {'schema':schema,'proof':(nodes,root),'name':'binary_fusion','parents':(a.get('name'),b.get('name'))}

def build_fusions(m,source,target,library,desired_pairs,missing_keys,limit=520):
 raw={};scored=[]
 # Compact parent pool prioritizes short, target-active, structurally diverse operators.
 pool=sorted(library,key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))[:52]
 for i,a in enumerate(pool):
  for j,b in enumerate(pool):
   if len(scored)>=limit*3:break
   for ra,rb in ((False,False),(False,True),(True,False),(True,True)):
    x=fuse(m,source,target,a,b,ra,rb)
    if not x:continue
    lhs,rhs,_=x['schema'];key=min((canon(m,lhs),canon(m,rhs)),(canon(m,rhs),canon(m,lhs)))
    if key in raw:continue
    pairs=structured_support_pairs(m,lhs)|structured_support_pairs(m,rhs)
    pair_hits=len(pairs & desired_pairs)
    missing_hits=0
    for side in (lhs,rhs):
     for u in all_subterms(m,side):
      if canon(m,u) in missing_keys:missing_hits+=1
    x['pair_hits']=pair_hits;x['missing_hits']=missing_hits
    x['activation']=selfm.activation(m,x['schema'],target)
    raw[key]=x;scored.append(x)
   if len(scored)>=limit*3:break
  if len(scored)>=limit*3:break
 scored.sort(key=lambda x:(-x['missing_hits'],-x['pair_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return scored[:limit]

def run_arm(m,sym,source,target,items,seconds,tag):
 s,found,_=frontier(m,sym,source,target,items,seconds);ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=120,maximum_nodes=120000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 return {'closure':ok,'installed':len(items),'rules':len(s.rules),'overlaps':s.overlap_candidates,'nodes':len(s.nodes),'seconds':seconds,'certificate_bytes':cert,'proof_nodes':pn,'tag':tag}

def main():
 global selfm
 m=load(SOLVER,'mg_binary_fusion');sym=load(SYM,'sym_binary_fusion');selfm=load(SELF,'self_binary_fusion');op=load(OPC,'op_binary_fusion');op.selfmod=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
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
 diag,base_found,fterms=frontier(m,sym,source,target,base,10.0)
 missing=target_missing(m,target,fterms);missing_keys={canon(m,t) for t in missing}
 desired=set()
 for t in missing:desired|=structured_support_pairs(m,t)

 # Infer candidate invariant from observed language: target-required child-support pairs absent in every generated endpoint.
 observed=set()
 for x in g1+g2:
  observed|=structured_support_pairs(m,x['schema'][0]);observed|=structured_support_pairs(m,x['schema'][1])
 absent_pairs=desired-observed

 armA=run_arm(m,sym,source,target,base,20.0,'A_frozen_g1_g2')
 g3=op.build_gen2(m,source,target,g2[:28],limit=520)
 for x in g3:x['name']='g3_unconstrained'
 armB=run_arm(m,sym,source,target,g1[:24]+g2[:56]+g3[:72],20.0,'B_unconstrained_g3')

 fusions=build_fusions(m,source,target,g1+g2,absent_pairs or desired,missing_keys,520)
 positive=[x for x in fusions if x['missing_hits']>0 or x['pair_hits']>0]
 cnew=(positive if positive else fusions)[:72]
 armC=run_arm(m,sym,source,target,g1[:24]+g2[:56]+cnew,20.0,'C_binary_fusion')
 ablation=run_arm(m,sym,source,target,g1[:24]+g2[:56],20.0,'C_ablation') if armC['closure'] else None

 def show(xs,n=20):
  return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'missing_hits':x['missing_hits'],'pair_hits':x['pair_hits'],'activation':x['activation'],'parents':x['parents']} for x in xs[:n]]
 out={'schema':'mathgraph.binary-fusion-invariant-breaker.v1','id':RID,
  'source':m.render_term(source[0])+' = '+m.render_term(source[1]),'target':m.render_term(target[0])+' = '+m.render_term(target[1]),
  'protocol':{'no_external_proof_trace':True,'no_answer_label_in_generator':True,'all_fusions_replay_to_source':True,'matched_arm_seconds':20.0},
  'invariant_hypothesis':'current recursive grammar is unary/contextual and cannot synthesize target-required cross-branch child-support pairs unless already present in a parent endpoint',
  'frozen_frontier':{'nodes':len(diag.nodes),'rules':len(diag.rules),'overlaps':diag.overlap_candidates,'base_found':base_found is not None},
  'missing_target_subterms':[m.render_term(t) for t in missing],
  'desired_child_support_pairs':[[list(a),list(b)] for a,b in sorted(desired)],
  'observed_required_pairs':[[list(a),list(b)] for a,b in sorted(desired & observed)],
  'absent_required_pairs':[[list(a),list(b)] for a,b in sorted(absent_pairs)],
  'counts':{'g1':len(g1),'g2':len(g2),'g3':len(g3),'fusions':len(fusions),'positive_fusions':len(positive),'fusion_missing_hits':sum(x['missing_hits']>0 for x in fusions),'fusion_pair_hits':sum(x['pair_hits']>0 for x in fusions)},
  'arms':{'A':armA,'B':armB,'C':armC,'C_ablation':ablation},'top_fusions':show(fusions),
  'decision':('PASS' if armC['closure'] and not armA['closure'] and not armB['closure'] and ablation and not ablation['closure'] else 'PARTIAL' if armC['closure'] else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
