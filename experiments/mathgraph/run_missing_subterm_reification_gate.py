#!/usr/bin/env python3
"""Residual -> missing structured subterm -> first-class substitution atom.

This gate tests the next invariant exposed by the binary-fusion negative.
The frozen G1/G2 language can contain useful target children deep inside proof
states while never promoting the absent *composite* target motif to a reusable
substitution atom.  We therefore derive proper missing target subterms from the
frozen frontier and permit those residual objects -- not a hand-written theorem
identity -- as substitution values in fresh instances of the ORIGINAL source law.

Matched arms:
 A: frozen G1+G2.
 B: same number of source instances built from closest already-reachable
    frontier terms (near-miss control).
 C: source instances built from the proper missing target subterm(s).
Every C operator is a one-step source instance and replays directly to the
original axiom.  A positive requires C closure, A/B failure, replay and ablation.
"""
import importlib.util, itertools, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
OUT=ROOT/'experiments/mathgraph/results/missing-subterm-reification-gate.json'
RID='evaluation_order5_0014'


def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def copy_nodes(m,src,dst,tag):
 off=len(dst)
 for n in src:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off

def append_proof(m,dst,proof):
 ns,r=proof;off=copy_nodes(m,ns,dst,'missing-subterm-reification-installed');return off+r

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

def target_missing(m,target,terms):
 miss=[];seen=set()
 for side in target[:2]:
  for u in all_subterms(m,side):
   if u[0]!='op':continue
   k=canon(m,u)
   if k not in terms and k not in seen:seen.add(k);miss.append(u)
 return sorted(miss,key=lambda t:(-m.term_size(t),m.render_term(t)))

def proper_missing(m,target,missing):
 sides={canon(m,target[0]),canon(m,target[1])}
 return [t for t in missing if canon(m,t) not in sides]

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
 fillers=source_atoms(m,source);raw={};out=[]
 vars_=source[2]
 for special in specials:
  for focus in vars_:
   others=[v for v in vars_ if v!=focus]
   for vals in itertools.product(fillers[:6],repeat=len(others)):
    mp={focus:special};mp.update(zip(others,vals))
    item=make_instance(m,source,target,mp,tag)
    if not item:continue
    k=eqkey(m,item['schema'][0],item['schema'][1])
    if k in raw:continue
    raw[k]=item;out.append(item)
    if len(out)>=limit:return out
 return out

def hit_count(m,item,missing_keys):
 hits=set()
 for side in item['schema'][:2]:
  for u in all_subterms(m,side):
   k=canon(m,u)
   if k in missing_keys:hits.add(k)
 return len(hits)

def run_arm(m,sym,source,target,items,seconds,tag):
 s,found,_=frontier(m,sym,source,target,items,seconds);ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=120,maximum_nodes=120000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 return {'closure':ok,'installed':len(items),'rules':len(s.rules),'overlaps':s.overlap_candidates,'nodes':len(s.nodes),'seconds':seconds,'certificate_bytes':cert,'proof_nodes':pn,'tag':tag}

def main():
 global selfm
 m=load(SOLVER,'mg_reify');sym=load(SYM,'sym_reify');selfm=load(SELF,'self_reify');op=load(OPC,'op_reify');op.selfmod=selfm
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
 diag,_,fterms=frontier(m,sym,source,target,base,10.0)
 missing=target_missing(m,target,fterms);proper=proper_missing(m,target,missing)
 # The control gets the closest already reachable structured terms of comparable size.
 vals=[t for t in fterms.values() if t[0]=='op' and canon(m,t) not in {canon(m,x) for x in missing}]
 vals.sort(key=lambda t:(min((m.structural_distance(t,q) for q in (proper or missing)),default=999),abs(m.term_size(t)-(m.term_size((proper or missing)[0]) if (proper or missing) else 1)),m.term_size(t),m.render_term(t)))
 near=[];seen=set()
 for t in vals:
  k=canon(m,t)
  if k in seen:continue
  seen.add(k);near.append(t)
  if len(near)>=max(1,len(proper)):break

 candsC=generate_instances(m,source,target,proper,'missing-subterm-reification',520)
 candsB=generate_instances(m,source,target,near,'near-miss-reification-control',520)
 mkeys={canon(m,t) for t in missing}
 for x in candsC:x['missing_hits']=hit_count(m,x,mkeys)
 for x in candsB:x['missing_hits']=hit_count(m,x,mkeys)
 candsC.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 candsB.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 n=min(72,len(candsC),len(candsB)) if candsB else min(72,len(candsC))
 armA=run_arm(m,sym,source,target,base,20.0,'A_frozen_g1_g2')
 armB=run_arm(m,sym,source,target,g1[:24]+g2[:56]+candsB[:n],20.0,'B_near_miss_reification') if n and candsB else {'closure':False,'installed':0,'tag':'B_near_miss_reification','error':'no_control_candidates'}
 armC=run_arm(m,sym,source,target,g1[:24]+g2[:56]+candsC[:n],20.0,'C_missing_subterm_reification') if n else {'closure':False,'installed':0,'tag':'C_missing_subterm_reification','error':'no_candidates'}
 ablation=run_arm(m,sym,source,target,g1[:24]+g2[:56],20.0,'C_ablation') if armC.get('closure') else None
 def show(xs,k=15):return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x['activation'],'missing_hits':x['missing_hits']} for x in xs[:k]]
 out={'schema':'mathgraph.missing-subterm-reification.v1','id':RID,
      'source':m.render_term(source[0])+' = '+m.render_term(source[1]),'target':m.render_term(target[0])+' = '+m.render_term(target[1]),
      'protocol':{'residual_derived_subterms_only':True,'no_external_proof_trace':True,'no_answer_label_in_generator':True,'proper_target_subterm_only':True,'all_new_operators_are_direct_source_instances':True,'matched_arm_seconds':20.0},
      'frozen_frontier':{'nodes':len(diag.nodes),'rules':len(diag.rules),'overlaps':diag.overlap_candidates},
      'missing_target_subterms':[m.render_term(t) for t in missing],'proper_missing_subterms':[m.render_term(t) for t in proper],'near_miss_control_terms':[m.render_term(t) for t in near],
      'counts':{'g1':len(g1),'g2':len(g2),'C_candidates':len(candsC),'B_candidates':len(candsB),'C_positive_missing':sum(x['missing_hits']>0 for x in candsC),'B_positive_missing':sum(x['missing_hits']>0 for x in candsB),'installed_new_per_arm':n},
      'arms':{'A':armA,'B':armB,'C':armC,'C_ablation':ablation},'top_C':show(candsC),'top_B':show(candsB),
      'decision':('PASS' if armC.get('closure') and not armA.get('closure') and not armB.get('closure') and ablation and not ablation.get('closure') else 'PARTIAL' if armC.get('closure') else 'INVARIANT_BROKEN_NO_CLOSURE' if any(x['missing_hits']>0 for x in candsC) else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
