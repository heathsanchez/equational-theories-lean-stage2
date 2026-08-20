#!/usr/bin/env python3
"""Residual-derived escape from the one-variable self-embedding grammar.

The previous binary-congruence breaker still produced zero missing-structure hits.
This gate derives a sharper invariant from the existing G1-G4 constructor code:
source instances alter one variable per construction step, and self-embedding
replacements must contain that same variable.  The missing target composite can
instead be the image of a *source subterm* under a simultaneous substitution of
multiple variables.  We synthesize those substitutions by unifying source
subterm patterns with residual-missing target structures.

Every induced operator is literally a source-law instance and must replay.
No external proof trace or target-specific equality is supplied.
"""
import importlib.util,json,sys,time,itertools
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-unified-multisubstitution-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t):return m.alpha_canonical_term(t,{})

def source_patterns(m,source):
 out=[];seen=set()
 for side in source[:2]:
  for u in m.walk_subterms(side):
   if u[0]!='op':continue
   k=canon(m,u)
   if k not in seen:seen.add(k);out.append(u)
 return sorted(out,key=lambda t:(m.term_size(t),m.render_term(t)))

def synthesize(m,source,target,missing,limit=400):
 lhs,rhs,vars_=source;raw={};mkeys={canon(m,t):m.term_size(t) for t in missing}
 for pat in source_patterns(m,source):
  for goal in missing:
   mp={}
   if not m.match_term(pat,goal,mp):continue
   full={v:mp.get(v,('var',v)) for v in vars_}
   changed=[v for v in vars_ if full[v] != ('var',v)]
   if len(changed)<2:continue
   il=m.substitute(lhs,full);ir=m.substitute(rhs,full)
   if max(m.term_size(il),m.term_size(ir))>140:continue
   for rev,a,b in ((False,il,ir),(True,ir,il)):
    nodes=[m.EqualityNode(a,b,'source instance',substitution=tuple((v,full[v]) for v in vars_),orientation=rev,constructor='residual-unified-multisubstitution')]
    if not m.replay_dag(source,nodes,0,maximum_term_size=200,maximum_nodes=1000):continue
    key=(canon(m,a),canon(m,b))
    if key in raw:continue
    hits=set()
    for side in (a,b):
     for u in m.walk_subterms(side):
      k=canon(m,u)
      if k in mkeys:hits.add(k)
    activation=selfmod.activation(m,(a,b,tuple(sorted(m.term_variables(a)|m.term_variables(b)))),target)
    raw[key]={'schema':(a,b,tuple(sorted(m.term_variables(a)|m.term_variables(b)))),'proof':(nodes,0),'hits':len(hits),'weight':sum(mkeys[k] for k in hits),'activation':activation,'pattern':m.render_term(pat),'goal':m.render_term(goal),'changed':changed,'mapping':{v:m.render_term(full[v]) for v in changed},'name':'multisub'}
    if len(raw)>=limit:break
   if len(raw)>=limit:break
  if len(raw)>=limit:break
 out=list(raw.values());out.sort(key=lambda z:(-z['hits'],-z['weight'],-z['activation'],m.term_size(z['schema'][0])+m.term_size(z['schema'][1])))
 return out

def main():
 global selfmod
 m=load(SOLVER,'mg_ms');sym=load(SYM,'sym_ms');selfmod=load(SELF,'self_ms');op=load(OPC,'op_ms');op.selfmod=selfmod;missmod=load(MISS,'miss_ms')
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
 multi=synthesize(m,source,target,missing)
 A=missmod.run_arm(m,sym,source,target,base,20.0,'A_frozen')
 B=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+g3[:72],20.0,'B_existing_G3')
 C=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+multi[:96],30.0,'C_residual_multisub')
 Abl=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56],30.0,'C_ablation') if C['closure'] else None
 out={'schema':'mathgraph.residual-unified-multisubstitution.v1','id':RID,'derived_invariant':'existing operator constructor changes one source variable at a time via self-containing replacement; it does not synthesize simultaneous multi-variable source instances from a residual cut','escape_constructor':'unify a source subterm pattern with each residual-missing structure, then compile the induced simultaneous substitution as a replay-verified source instance','missing_target_subterms':[m.render_term(t) for t in missing],'counts':{'g1':len(g1),'g2':len(g2),'g3':len(g3),'multisub_verified':len(multi),'multisub_constraint_hits':sum(x['hits']>0 for x in multi)},'arms':{'A':A,'B':B,'C':C,'C_ablation':Abl},'top_multisub':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'hits':x['hits'],'weight':x['weight'],'activation':x['activation'],'pattern':x['pattern'],'goal':x['goal'],'changed':x['changed'],'mapping':x['mapping']} for x in multi[:20]],'protocol':{'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity':True,'all_candidates_are_replay_verified_source_instances':True},'decision':'PASS' if C['closure'] and not A['closure'] and not B['closure'] and Abl and not Abl['closure'] else ('PARTIAL' if C['closure'] else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
