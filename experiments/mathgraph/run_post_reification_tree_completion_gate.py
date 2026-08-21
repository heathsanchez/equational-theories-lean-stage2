#!/usr/bin/env python3
"""Second developmental iteration: post-reification residual -> missing parent composition.

After missing-subterm reification, proper target motifs become reachable but the
original theorem remains open.  This gate recomputes the frontier AFTER that
verified language change and derives the next structural residual generically:
find missing target subterms whose immediate children are already reachable.
Those missing parents are promoted as first-class substitution atoms in fresh
instances of the ORIGINAL source law.

Matched arms:
 A: retained reification state.
 B: matched source instances built from reachable near-parent controls.
 C: source instances built from post-change fillable missing parents.
A positive requires C closure, A/B failure, replay, and C ablation failure.
"""
import importlib.util, json, sys
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
OUT=ROOT/'experiments/mathgraph/results/post-reification-tree-completion-gate.json'
RID='evaluation_order5_0014'

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def immediate_children(t):
 return (t[1],t[2]) if isinstance(t,tuple) and len(t)>=3 and t[0]=='op' else ()

def main():
 m=load(SOLVER,'mg_postreify');sym=load(SYM,'sym_postreify');selfm=load(SELF,'self_postreify');op=load(OPC,'op_postreify');r=load(REIFY,'reify_postreify')
 r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
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
 _,_,initial_terms=r.frontier(m,sym,source,target,base,10.0)
 initial_missing=r.target_missing(m,target,initial_terms);proper=r.proper_missing(m,target,initial_missing)
 c1=r.generate_instances(m,source,target,proper,'retained-missing-subterm-reification',520)
 initial_keys={r.canon(m,t) for t in initial_missing}
 for x in c1:x['missing_hits']=r.hit_count(m,x,initial_keys)
 c1.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 retained=g1[:24]+g2[:56]+c1[:72]
 post,_,post_terms=r.frontier(m,sym,source,target,retained,15.0)
 post_missing=r.target_missing(m,target,post_terms)
 post_keys=set(post_terms)
 fillable=[]
 for t in post_missing:
  ch=immediate_children(t)
  if ch and all(r.canon(m,u) in post_keys for u in ch):fillable.append(t)
 # Controls: reachable terms of comparable size whose own children are reachable.
 controls=[];seen=set();targets=fillable or post_missing
 vals=[t for t in post_terms.values() if isinstance(t,tuple) and t and t[0]=='op']
 vals.sort(key=lambda t:(min((m.structural_distance(t,q) for q in targets),default=999),abs(m.term_size(t)-(m.term_size(targets[0]) if targets else 1)),m.term_size(t),m.render_term(t)))
 for t in vals:
  k=r.canon(m,t)
  if k in seen or any(k==r.canon(m,q) for q in post_missing):continue
  seen.add(k);controls.append(t)
  if len(controls)>=max(1,len(fillable)):break
 cC=r.generate_instances(m,source,target,fillable,'post-reification-tree-completion',520)
 cB=r.generate_instances(m,source,target,controls,'post-reification-near-parent-control',520)
 pkeys={r.canon(m,t) for t in post_missing}
 for x in cC:x['missing_hits']=r.hit_count(m,x,pkeys)
 for x in cB:x['missing_hits']=r.hit_count(m,x,pkeys)
 cC.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 cB.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 n=min(72,len(cC),len(cB)) if cB else min(72,len(cC))
 armA=r.run_arm(m,sym,source,target,retained,25.0,'A_retained_reification')
 armB=r.run_arm(m,sym,source,target,g1[:20]+g2[:40]+c1[:48]+cB[:n],25.0,'B_near_parent_control') if n and cB else {'closure':False,'installed':0,'tag':'B_near_parent_control','error':'no_control_candidates'}
 armC=r.run_arm(m,sym,source,target,g1[:20]+g2[:40]+c1[:48]+cC[:n],25.0,'C_post_reification_tree_completion') if n else {'closure':False,'installed':0,'tag':'C_post_reification_tree_completion','error':'no_fillable_parent_candidates'}
 ablation=r.run_arm(m,sym,source,target,g1[:20]+g2[:40]+c1[:48],25.0,'C_ablation') if armC.get('closure') else None
 out={'schema':'mathgraph.post-reification-tree-completion.v1','id':RID,
  'source':m.render_term(source[0])+' = '+m.render_term(source[1]),'target':m.render_term(target[0])+' = '+m.render_term(target[1]),
  'protocol':{'post_change_residual_recomputed':True,'all_new_operators_are_direct_source_instances':True,'no_external_proof_trace':True,'no_answer_label':True,'matched_seconds':25.0},
  'initial_missing':[m.render_term(t) for t in initial_missing],
  'post_frontier':{'nodes':len(post.nodes),'rules':len(post.rules),'overlaps':post.overlap_candidates},
  'post_missing':[m.render_term(t) for t in post_missing],
  'fillable_missing_parents':[m.render_term(t) for t in fillable],
  'control_terms':[m.render_term(t) for t in controls],
  'counts':{'retained_reification_candidates':len(c1),'tree_completion_candidates':len(cC),'control_candidates':len(cB),'tree_completion_positive_missing':sum(x['missing_hits']>0 for x in cC),'control_positive_missing':sum(x['missing_hits']>0 for x in cB),'installed_new_per_arm':n},
  'arms':{'A':armA,'B':armB,'C':armC,'C_ablation':ablation}}
 out['decision']='PASS' if armC.get('closure') and not armA.get('closure') and not armB.get('closure') and ablation and not ablation.get('closure') else 'PARTIAL' if armC.get('closure') else 'NO_FILLABLE_PARENT' if not fillable else 'INVARIANT_BROKEN_NO_CLOSURE' if any(x.get('missing_hits',0)>0 for x in cC) else 'NO_CLOSURE'
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
