#!/usr/bin/env python3
"""Residual -> necessary missing-subterm constraint -> operator-language induction.

For evaluation_order5_0014, construct a frozen replay-verified G1+G2 language,
run it to obtain the actual bounded symbolic proof frontier, and identify target
subterms absent from every generated endpoint. Any bounded proof that reaches
the target must contain a first inference that introduces each such absent
subterm, so "can introduce a currently missing target subterm" is a genuine
necessary structural property of some successful continuation in this bounded
regime.

Matched arms:
 A: frozen G1+G2.
 B: unconstrained recursive G3, activation-ranked.
 C: residual-conditioned recursive G3/G4, where parent choice and installation
    are ranked by verified ability to introduce missing target structure from
    the frozen frontier.
All macros compile to source instances/congruence/transitivity and replay.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
OUT=ROOT/'experiments/mathgraph/results/missing-subterm-constraint-induction-gate.json'
RID='evaluation_order5_0014'


def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def append_proof(m,dst,proof):
 nodes,root=proof;off=len(dst)
 for n in nodes:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'missing-subterm-installed',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off+root

def generation(m,op,source,target,parents,limit=520):
 out=op.build_gen2(m,source,target,parents,limit=limit)
 out.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return out

def all_subterms(m,t):
 return list(m.walk_subterms(t))

def canon(m,t):return m.alpha_canonical_term(t,{})

def frontier(m,sym,source,target,items,seconds=10.0):
 started=time.monotonic();Norm=sym.make_normalizer(m)
 cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=7000,overlap_candidates=6500,selected_rules=1000,replayed_rules=4000,maximum_term_size=100,maximum_proof_nodes=100000)
 s=Norm(source,target,started+seconds,cfg)
 for x in items:append_proof(m,s.nodes,x['proof'])
 found=s.solve()
 terms={}
 for n in s.nodes:
  for side in (n.lhs,n.rhs):
   terms[canon(m,side)]=side
   for u in all_subterms(m,side):terms.setdefault(canon(m,u),u)
 return s,found,terms

def target_missing(m,target,terms):
 # Ignore single variables; the useful constraints are structured target pieces.
 miss=[]
 for side in target[:2]:
  for u in all_subterms(m,side):
   if u[0]!='op':continue
   k=canon(m,u)
   if k not in terms and k not in {canon(m,x) for x in miss}:miss.append(u)
 return sorted(miss,key=lambda t:(-m.term_size(t),m.render_term(t)))

def paths(t,p=()):
 yield p,t
 if t[0]=='op':
  yield from paths(t[1],p+('L',));yield from paths(t[2],p+('R',))

def rewrite_once(m,term,schema,max_size=100):
 lhs,rhs,_=schema;out=[];seen=set()
 for a,b in ((lhs,rhs),(rhs,lhs)):
  for p,u in paths(term):
   mp={}
   if not m.match_term(a,u,mp):continue
   try:r=m.substitute(b,mp)
   except Exception:continue
   nt=m.replace_subterm(term,p,r)
   if nt==term or m.term_size(nt)>max_size:continue
   k=canon(m,nt)
   if k not in seen:seen.add(k);out.append(nt)
 return out

def contains_missing(m,t,missing_keys):
 hits=[]
 for u in all_subterms(m,t):
  k=canon(m,u)
  if k in missing_keys:hits.append(k)
 return set(hits)

def induction_score(m,item,frontier_terms,missing):
 mkeys={canon(m,t):m.term_size(t) for t in missing}
 if not mkeys:return (0,0,0)
 # Deterministic compact frontier sample: terms closest in size to target pieces,
 # plus short terms. This is only a proposer signal; all promoted macros replay.
 target_sizes=[m.term_size(t) for t in missing]
 vals=list(frontier_terms.values())
 vals.sort(key=lambda t:(min(abs(m.term_size(t)-s) for s in target_sizes),m.term_size(t),m.render_term(t)))
 vals=vals[:320]
 best=set();rewrites=0
 for t in vals:
  for nt in rewrite_once(m,t,item['schema'],100):
   rewrites+=1;best|=contains_missing(m,nt,mkeys)
   if len(best)==len(mkeys):break
  if len(best)==len(mkeys):break
 weighted=sum(mkeys[k] for k in best)
 return (len(best),weighted,rewrites)

def run_arm(m,sym,source,target,items,seconds,tag):
 s,found,_=frontier(m,sym,source,target,items,seconds)
 ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=100,maximum_nodes=100000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':seconds,'installed':len(items),'rules':len(s.rules),'overlaps':s.overlap_candidates,'nodes':len(s.nodes),'certificate_bytes':cert,'proof_nodes':pn,'tag':tag}

def main():
 m=load(SOLVER,'mg_missing_constraint');sym=load(SYM,'sym_missing_constraint');selfm=load(SELF,'self_missing_constraint');op=load(OPC,'op_missing_constraint');op.selfmod=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:
   sc=p['schema'];g1.append({'schema':sc,'proof':pr,'name':'g1','activation':selfm.activation(m,sc,target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=generation(m,op,source,target,g1,520)
 for x in g2:x['name']='g2'
 base=g1[:32]+g2[:128]
 diag,base_found,fterms=frontier(m,sym,source,target,base,10.0)
 missing=target_missing(m,target,fterms)

 armA=run_arm(m,sym,source,target,base,20.0,'A_frozen')
 g3b=generation(m,op,source,target,g2[:28],520)
 for x in g3b:x['name']='g3_unconstrained'
 bitems=g1[:24]+g2[:56]+g3b[:72]
 armB=run_arm(m,sym,source,target,bitems,20.0,'B_unconstrained')

 scored2=[]
 for x in g2:
  h,w,r=induction_score(m,x,fterms,missing);y=dict(x);y['missing_hits']=h;y['missing_weight']=w;y['probe_rewrites']=r;scored2.append(y)
 scored2.sort(key=lambda x:(-x['missing_hits'],-x['missing_weight'],-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 parents=scored2[:28]
 g3c=generation(m,op,source,target,parents,520)
 scored3=[]
 for x in g3c:
  h,w,r=induction_score(m,x,fterms,missing);y=dict(x);y['name']='g3_conditioned';y['missing_hits']=h;y['missing_weight']=w;y['probe_rewrites']=r;scored3.append(y)
 scored3.sort(key=lambda x:(-x['missing_hits'],-x['missing_weight'],-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g4c=generation(m,op,source,target,scored3[:24],520) if scored3 else []
 scored4=[]
 for x in g4c:
  h,w,r=induction_score(m,x,fterms,missing);y=dict(x);y['name']='g4_conditioned';y['missing_hits']=h;y['missing_weight']=w;y['probe_rewrites']=r;scored4.append(y)
 scored4.sort(key=lambda x:(-x['missing_hits'],-x['missing_weight'],-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 cnew=scored3[:48]+scored4[:48];citems=g1[:24]+g2[:56]+cnew[:72]
 armC=run_arm(m,sym,source,target,citems,20.0,'C_missing_subterm_conditioned')
 ablation=run_arm(m,sym,source,target,g1[:24]+g2[:56],20.0,'C_ablation') if armC['closure'] else None
 def sh(xs,n=15):
  return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'name':x.get('name'),'activation':x.get('activation',0),'missing_hits':x.get('missing_hits'),'missing_weight':x.get('missing_weight')} for x in xs[:n]]
 out={'schema':'mathgraph.missing-subterm-constraint-induction.v1','id':RID,
      'source':m.render_term(source[0])+' = '+m.render_term(source[1]),'target':m.render_term(target[0])+' = '+m.render_term(target[1]),
      'protocol':{'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity':True,'all_macros_replay_to_source':True,'matched_arm_seconds':20.0},
      'frozen_frontier':{'nodes':len(diag.nodes),'rules':len(diag.rules),'overlaps':diag.overlap_candidates,'subterms':len(fterms),'base_found':base_found is not None},
      'missing_target_subterms':[m.render_term(t) for t in missing],
      'counts':{'g1':len(g1),'g2':len(g2),'g3_unconstrained':len(g3b),'g3_conditioned':len(scored3),'g4_conditioned':len(scored4),'g2_positive_constraints':sum(x['missing_hits']>0 for x in scored2),'g3_positive_constraints':sum(x['missing_hits']>0 for x in scored3),'g4_positive_constraints':sum(x['missing_hits']>0 for x in scored4)},
      'arms':{'A':armA,'B':armB,'C':armC,'C_ablation':ablation},'top_g2':sh(scored2),'top_g3':sh(scored3),'top_g4':sh(scored4),
      'decision':('PASS' if armC['closure'] and not armA['closure'] and not armB['closure'] and ablation and not ablation['closure'] else 'PARTIAL' if armC['closure'] else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
