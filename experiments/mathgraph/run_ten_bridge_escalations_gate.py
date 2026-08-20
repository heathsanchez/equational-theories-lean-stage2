#!/usr/bin/env python3
"""Ten post-development bridge escalations for evaluation_order5_0014.

All candidates are replay-verified instances of the original source law.  No
external proof trace, answer label, or new trusted inference rule is supplied.
The ten probes differ only in how substitutions are proposed from the verified
post-development residual/component state.
"""
import importlib.util, itertools, json, sys
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
OUT=ROOT/'experiments/mathgraph/results/ten-bridge-escalations-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t): return m.alpha_canonical_term(t,{})

def walk(m,t): return list(m.walk_subterms(t))

class UF:
 def __init__(self): self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a

def match(p,t,env):
 if p[0]=='var':
  v=p[1]
  if v in env:return env[v]==t
  env[v]=t;return True
 if p[0]!='op' or t[0]!='op':return False
 return match(p[1],t[1],env) and match(p[2],t[2],env)

def complete_env(source,env):
 return {v:env.get(v,('var',v)) for v in source[2]}

def make(m,r,source,target,env,tag):
 env=complete_env(source,env)
 item=r.make_instance(m,source,target,env,tag)
 return item

def uniq(m,items,limit=96):
 out=[];seen=set()
 for x in items:
  if not x: continue
  a,b=x['schema'][0],x['schema'][1]
  k=(canon(m,a),canon(m,b))
  if k in seen: continue
  seen.add(k);out.append(x)
  if len(out)>=limit: break
 return out

def target_distance(m,item,target):
 a,b=item['schema'][:2]
 return min(m.structural_distance(a,target[0])+m.structural_distance(b,target[1]),m.structural_distance(a,target[1])+m.structural_distance(b,target[0]))

def main():
 m=load(SOLVER,'mg10');sym=load(SYM,'sym10');selfm=load(SELF,'self10');op=load(OPC,'op10');r=load(REIFY,'reify10');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 # Rebuild the verified post-development state used by the prior component-cut gate.
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
 _,_,t0=r.frontier(m,sym,source,target,base,10.0);miss0=r.target_missing(m,target,t0);proper=r.proper_missing(m,target,miss0)
 c1=r.generate_instances(m,source,target,proper,'retained-reification',520);k0={canon(m,t) for t in miss0}
 for x in c1:x['missing_hits']=r.hit_count(m,x,k0)
 c1.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state1=g1[:24]+g2[:56]+c1[:72]
 _,_,t1=r.frontier(m,sym,source,target,state1,15.0);miss1=r.target_missing(m,target,t1);postkeys=set(t1)
 fill=[q for q in miss1 if q[0]=='op' and canon(m,q[1]) in postkeys and canon(m,q[2]) in postkeys]
 c2=r.generate_instances(m,source,target,fill,'retained-tree-completion',520);k1={canon(m,t) for t in miss1}
 for x in c2:x['missing_hits']=r.hit_count(m,x,k1)
 c2.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state=g1[:20]+g2[:40]+c1[:48]+c2[:72]
 s,_,_=r.frontier(m,sym,source,target,state,20.0)
 uf=UF();terms={}
 for n in s.nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk=canon(m,target[0]);rk=canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 lhs_terms=[t for k,t in terms.items() if uf.find(k)==lr]
 rhs_terms=[t for k,t in terms.items() if uf.find(k)==rr]
 all_terms=list(terms.values())
 # compact pools chosen by target structural proximity.
 lhs_terms.sort(key=lambda t:(m.structural_distance(t,target[0]),m.term_size(t)))
 rhs_terms.sort(key=lambda t:(m.structural_distance(t,target[1]),m.term_size(t)))
 all_terms.sort(key=lambda t:(min(m.structural_distance(t,target[0]),m.structural_distance(t,target[1])),m.term_size(t)))
 L=lhs_terms[:24];R=rhs_terms[:24];A=all_terms[:48]
 src_sub=[]
 for side in source[:2]: src_sub.extend([u for u in walk(m,side) if u[0]=='op'])
 tgt_sub=[]
 for side in target[:2]: tgt_sub.extend([u for u in walk(m,side) if u[0]=='op'])
 probes={}

 # 1/2: direct endpoint matching, both source orientations.
 for idx,pat in [(1,source[1]),(2,source[0])]:
  cand=[]
  for t in (R+L):
   env={}
   if match(pat,t,env): cand.append(make(m,r,source,target,env,f'p{idx}-direct-endpoint'))
  probes[idx]=uniq(m,cand)

 # 3: any nontrivial source subterm matched against endpoint-component terms.
 cand=[]
 for pat in src_sub:
  for t in L+R:
   env={}
   if match(pat,t,env): cand.append(make(m,r,source,target,env,'p3-subterm-unification'))
 probes[3]=uniq(m,cand)

 # 4: residual target-subterm reification into every source variable, component-conditioned.
 cand=[]
 atoms=tgt_sub[:12]
 for v in source[2]:
  for a in atoms:
   cand.append(make(m,r,source,target,{v:a},'p4-target-atom-reification'))
 probes[4]=uniq(m,cand)

 # 5: simultaneous two-variable substitution using opposite-component endpoint atoms.
 cand=[]
 vars_=list(source[2])
 for v1,v2 in itertools.permutations(vars_,2):
  for a in L[:8]:
   for b in R[:8]: cand.append(make(m,r,source,target,{v1:a,v2:b},'p5-cross-component-multisub'))
 probes[5]=uniq(m,cand)

 # 6: simultaneous substitutions using target immediate children / missing-parent atoms.
 cand=[]
 special=[]
 for q in tgt_sub:
  if q not in special:special.append(q)
 for vals in itertools.product(special[:8],repeat=min(2,len(vars_))):
  env={vars_[i]:vals[i] for i in range(min(2,len(vars_)))}
  cand.append(make(m,r,source,target,env,'p6-target-tree-multisub'))
 probes[6]=uniq(m,cand)

 # 7: endpoint-pair anti-unification surrogate: substitutions from common close subterms.
 cand=[]
 for a in L[:12]:
  sa=walk(m,a)
  for b in R[:12]:
   sb=walk(m,b)
   pair=sorted([(m.structural_distance(x,y),x,y) for x in sa for y in sb],key=lambda z:(z[0],m.term_size(z[1])+m.term_size(z[2])))[:2]
   if len(pair)>=2 and len(vars_)>=2:
    cand.append(make(m,r,source,target,{vars_[0]:pair[0][1],vars_[1]:pair[1][2]},'p7-endpoint-pair-synthesis'))
 probes[7]=uniq(m,cand)

 # 8: near-cut source instances: brute-force small substitutions, rank by target distance.
 cand=[]
 atoms=(L[:6]+R[:6]+tgt_sub[:6])
 for vals in itertools.product(atoms,repeat=min(2,len(vars_))):
  env={vars_[i]:vals[i] for i in range(min(2,len(vars_)))}
  cand.append(make(m,r,source,target,env,'p8-near-cut-enumeration'))
 cand=[x for x in cand if x];cand.sort(key=lambda x:target_distance(m,x,target));probes[8]=uniq(m,cand)

 # 9: context lift: wrap opposite-component atoms as binary contexts then substitute.
 cand=[]
 if len(vars_)>=2:
  for a in L[:8]:
   for b in R[:8]:
    for c in [('op',a,b),('op',b,a)]:
     cand.append(make(m,r,source,target,{vars_[0]:c,vars_[1]:a},'p9-context-lift'))
 probes[9]=uniq(m,cand)

 # 10: two-hop bridge seeds: first generate near-cut instances, then use their endpoints as substitution atoms.
 seeds=probes[8][:24]+probes[5][:24]
 cand=[]
 seed_atoms=[]
 for x in seeds: seed_atoms.extend(x['schema'][:2])
 for v in vars_:
  for a in seed_atoms[:48]: cand.append(make(m,r,source,target,{v:a},'p10-two-hop-seed'))
 probes[10]=uniq(m,cand)

 results=[]
 baseline=r.run_arm(m,sym,source,target,state,20.0,'baseline_post_development')
 for i in range(1,11):
  xs=probes[i]
  arm=r.run_arm(m,sym,source,target,state+xs[:72],25.0,f'probe_{i}') if xs else {'closure':False,'installed':0,'tag':f'probe_{i}','error':'no_candidates'}
  results.append({'probe':i,'candidates':len(xs),'closure':bool(arm.get('closure')),'nodes':arm.get('nodes'),'rules':arm.get('rules'),'overlaps':arm.get('overlaps'),'certificate_bytes':arm.get('certificate_bytes'),'proof_nodes':arm.get('proof_nodes')})
  if arm.get('closure'): break
 out={'schema':'mathgraph.ten-bridge-escalations.v1','id':RID,'protocol':{'no_external_proof_trace':True,'no_answer_label':True,'all_candidates_direct_replay_verified_source_instances':True,'post_development_residual_recomputed':True},'component_state':{'lhs_size':len(lhs_terms),'rhs_size':len(rhs_terms),'already_joined':lr==rr,'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates},'baseline':baseline,'results':results,'decision':'PASS' if any(x['closure'] for x in results) else 'NO_CLOSURE'}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__': main()
