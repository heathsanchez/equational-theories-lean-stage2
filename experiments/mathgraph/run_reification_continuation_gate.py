#!/usr/bin/env python3
"""Test whether a residual-driven representation change enables the next operator family.

The preceding missing-subterm gate established a causal intermediate result on
`evaluation_order5_0014`: proper target subterm reification creates source-law
instances containing a motif absent from the frozen frontier, while a matched
near-miss control does not.  Direct installation still did not close the target.

This gate tests the developmental continuation predicted by that result:

    residual -> reify missing motif -> regenerate operators FROM the changed
    representation -> closure

Matched arms:
 A: frozen G1+G2.
 B: near-miss source instances, then one G2-style continuation generation from
    those control instances.
 C: missing-subterm source instances, then the identical continuation generator
    applied to those residual-conditioned instances.

All installed equalities must replay to the original source law.  A strict pass
requires C closure, A/B failure, and failure when C's continuation descendants
are ablated while retaining the reification seeds.
"""
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
OUT=ROOT/'experiments/mathgraph/results/reification-continuation-gate.json'
RID='evaluation_order5_0014'


def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def canon(m,t): return m.alpha_canonical_term(t,{})

def all_subterms(m,t): return list(m.walk_subterms(t))

def eqkey(m,a,b):
 names={};x=(m.alpha_canonical_term(a,names),m.alpha_canonical_term(b,names))
 names={};y=(m.alpha_canonical_term(b,names),m.alpha_canonical_term(a,names))
 return min(x,y)

def replay_ok(m,source,item):
 ns,r=item['proof']
 return bool(m.replay_dag(source,ns,r,maximum_term_size=180,maximum_nodes=50000))

def endpoint_hits(m,item,keys):
 hits=set()
 for side in item['schema'][:2]:
  for u in all_subterms(m,side):
   k=canon(m,u)
   if k in keys:hits.add(k)
 return len(hits)

def full_target_hits(m,item,target):
 keys={canon(m,target[0]),canon(m,target[1])}
 return endpoint_hits(m,item,keys)

def run_arm(m,reify,sym,source,target,items,seconds,tag):
 return reify.run_arm(m,sym,source,target,items,seconds,tag)

def dedup(m,items,limit):
 out=[];seen=set()
 for x in items:
  k=eqkey(m,x['schema'][0],x['schema'][1])
  if k in seen:continue
  seen.add(k);out.append(x)
  if len(out)>=limit:break
 return out

def main():
 m=load(SOLVER,'mg_reify_continue');sym=load(SYM,'sym_reify_continue');selfm=load(SELF,'self_reify_continue');op=load(OPC,'op_reify_continue');reify=load(REIFY,'reify_continue')
 op.selfmod=selfm;reify.selfm=selfm
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

 diag,_,fterms=reify.frontier(m,sym,source,target,base,10.0)
 missing=reify.target_missing(m,target,fterms);proper=reify.proper_missing(m,target,missing)
 mkeys={canon(m,t) for t in missing}
 vals=[t for t in fterms.values() if t[0]=='op' and canon(m,t) not in mkeys]
 vals.sort(key=lambda t:(min((m.structural_distance(t,q) for q in (proper or missing)),default=999),abs(m.term_size(t)-(m.term_size((proper or missing)[0]) if (proper or missing) else 1)),m.term_size(t),m.render_term(t)))
 near=[];seen=set()
 for t in vals:
  k=canon(m,t)
  if k in seen:continue
  seen.add(k);near.append(t)
  if len(near)>=max(1,len(proper)):break

 cseed=reify.generate_instances(m,source,target,proper,'missing-subterm-reification-seed',520)
 bseed=reify.generate_instances(m,source,target,near,'near-miss-reification-seed',520)
 for x in cseed:
  x['missing_hits']=endpoint_hits(m,x,mkeys);x['activation']=selfm.activation(m,x['schema'],target);x['name']='c_reify_seed'
 for x in bseed:
  x['missing_hits']=endpoint_hits(m,x,mkeys);x['activation']=selfm.activation(m,x['schema'],target);x['name']='b_reify_seed'
 cseed.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 bseed.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 nseed=min(72,len(cseed),len(bseed))
 cseed=cseed[:nseed];bseed=bseed[:nseed]

 # Crucial intervention: regenerate the SAME verified recursive constructor from
 # the changed seed basis instead of merely adding the reified terms to search.
 ccont=op.build_gen2(m,source,target,cseed,limit=520)
 bcont=op.build_gen2(m,source,target,bseed,limit=520)
 for xs,name in ((ccont,'c_reification_continuation'),(bcont,'b_control_continuation')):
  for x in xs:
   x['name']=name;x['activation']=selfm.activation(m,x['schema'],target);x['missing_hits']=endpoint_hits(m,x,mkeys);x['full_target_hits']=full_target_hits(m,x,target)
 # Require replay before an item is admissible.
 ccont=[x for x in ccont if replay_ok(m,source,x)]
 bcont=[x for x in bcont if replay_ok(m,source,x)]
 ccont.sort(key=lambda x:(-x['full_target_hits'],-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 bcont.sort(key=lambda x:(-x['full_target_hits'],-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 ncont=min(72,len(ccont),len(bcont)) if bcont else min(72,len(ccont))
 cnew=dedup(m,ccont,ncont);bnew=dedup(m,bcont,ncont)

 common=g1[:24]+g2[:56]
 armA=run_arm(m,reify,sym,source,target,base,20.0,'A_frozen_g1_g2')
 armB=run_arm(m,reify,sym,source,target,common+bseed+bnew,20.0,'B_near_miss_then_continuation') if bseed else {'closure':False,'tag':'B_near_miss_then_continuation','error':'no_control_seeds'}
 armC=run_arm(m,reify,sym,source,target,common+cseed+cnew,20.0,'C_missing_reification_then_continuation') if cseed else {'closure':False,'tag':'C_missing_reification_then_continuation','error':'no_reification_seeds'}
 ablation=run_arm(m,reify,sym,source,target,common+cseed,20.0,'C_continuation_ablation') if armC.get('closure') else None

 def show(xs,k=20):
  return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x.get('activation',0),'missing_hits':x.get('missing_hits',0),'full_target_hits':x.get('full_target_hits',0)} for x in xs[:k]]
 out={'schema':'mathgraph.reification-continuation.v1','id':RID,
  'source':m.render_term(source[0])+' = '+m.render_term(source[1]),'target':m.render_term(target[0])+' = '+m.render_term(target[1]),
  'hypothesis':'residual-driven reification is not itself the closing operator; it changes the seed representation so the existing verified constructor can generate a previously unavailable continuation family',
  'protocol':{'same_continuation_generator_B_C':True,'all_installed_equalities_replay_to_source':True,'no_external_proof_trace':True,'no_answer_label_in_generator':True,'matched_arm_seconds':20.0},
  'frozen_frontier':{'nodes':len(diag.nodes),'rules':len(diag.rules),'overlaps':diag.overlap_candidates},
  'missing_target_subterms':[m.render_term(t) for t in missing],'proper_missing_subterms':[m.render_term(t) for t in proper],'near_miss_control_terms':[m.render_term(t) for t in near],
  'counts':{'g1':len(g1),'g2':len(g2),'C_seeds':len(cseed),'B_seeds':len(bseed),'C_continuations':len(ccont),'B_continuations':len(bcont),'installed_continuations_per_arm':ncont,
            'C_continuations_with_missing':sum(x.get('missing_hits',0)>0 for x in ccont),'B_continuations_with_missing':sum(x.get('missing_hits',0)>0 for x in bcont),'C_continuations_with_full_target':sum(x.get('full_target_hits',0)>0 for x in ccont),'B_continuations_with_full_target':sum(x.get('full_target_hits',0)>0 for x in bcont)},
  'arms':{'A':armA,'B':armB,'C':armC,'C_continuation_ablation':ablation},'top_C_continuations':show(ccont),'top_B_continuations':show(bcont),
  'decision':('PASS' if armC.get('closure') and not armA.get('closure') and not armB.get('closure') and ablation and not ablation.get('closure') else 'PARTIAL_CLOSURE' if armC.get('closure') else 'REPRESENTATION_ENABLEMENT_NO_CLOSURE' if sum(x.get('missing_hits',0)>0 for x in ccont)>sum(x.get('missing_hits',0)>0 for x in bcont) else 'NO_ENABLEMENT')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
