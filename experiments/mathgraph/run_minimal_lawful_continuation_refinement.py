#!/usr/bin/env python3
"""Prospectively frozen minimal lawful continuation-space refinement for O5-0014.

Searches a finite lattice of replay-valid constructor families for the cheapest regime
that intersects the residual-derived first-introduction constraint K(rho), then
searches target-context attachments and tests closure/ablation.
"""
import importlib.util,itertools,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
JOIN=ROOT/'experiments/mathgraph/run_0014_semantic_join_endpoint_multisub_gate.py'
BRIDGE=ROOT/'experiments/mathgraph/run_0014_component_bridge_unification_gate.py'
ATT=ROOT/'experiments/mathgraph/run_residual_active_continuation_attachment_gate.py'
OUT=ROOT/'experiments/mathgraph/results/minimal-lawful-continuation-refinement.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t):return m.alpha_canonical_term(t,{})
def eqkey(m,a,b):return min((canon(m,a),canon(m,b)),(canon(m,b),canon(m,a)))
def tcost(m,it):return m.term_size(it['schema'][0])+m.term_size(it['schema'][1])

def replay_filter(m,source,items,limit=160):
 out=[];seen=set()
 for it in items:
  try:ok=m.replay_dag(source,it['proof'][0],it['proof'][1],maximum_term_size=240,maximum_nodes=60000)
  except Exception:ok=False
  if not ok:continue
  k=eqkey(m,*it['schema'][:2])
  if k in seen:continue
  seen.add(k);out.append(it)
  if len(out)>=limit:break
 return out

def contains_required(m,it,required_keys):
 for side in it['schema'][:2]:
  for u in m.walk_subterms(side):
   if canon(m,u) in required_keys:return True
 return False

def make_join_family(m,source,target,multi,jmod):
 eps=jmod.endpoint_vars(source)
 if not eps:return []
 ep=eps[0];out=[];seen=set()
 for it in multi:
  node=it['proof'][0][it['proof'][1]];mp=dict(node.substitution or ())
  if not mp or any(v not in mp for v in source[2]):continue
  for side in target[:2]:
   q=dict(mp);q[ep]=side;x=jmod.make(m,source,target,q,'minimal-J-endpoint-promotion')
   if not x:continue
   k=eqkey(m,*x['schema'][:2])
   if k in seen:continue
   seen.add(k);out.append(x)
 return out

def make_component_family(m,sym,source,target,multi,join_items,bridge,jmod,common):
 eps=jmod.endpoint_vars(source)
 if not eps:return []
 ep=eps[0]
 s=bridge.state(m,sym,source,target,common+join_items[:48],24)
 _,_,L,R,_,_=bridge.components(m,target,s.nodes)
 maps=[]
 for it in multi:
  mp=dict(it['proof'][0][it['proof'][1]].substitution or ())
  if mp and all(v in mp for v in source[2]):maps.append(mp)
 out=[];seen=set()
 for bmp in maps[:48]:
  for side_name,comp in (('L',L),('R',R)):
   for a in sorted(comp,key=lambda t:(m.term_size(t),m.render_term(t)))[:48]:
    mp=dict(bmp);mp[ep]=a;x=bridge.make(m,source,target,mp,'minimal-C-component-anchor')
    if not x:continue
    x['anchor_side']=side_name
    k=eqkey(m,*x['schema'][:2])
    if k in seen:continue
    seen.add(k);out.append(x)
    if len(out)>=160:return out
 return out

def regime_cost(m,names,items):
 return (len(names),len(items),sum(tcost(m,x) for x in items))

def main():
 global selfm
 m=load(SOLVER,'mg_minlaw');sym=load(SYM,'sym_minlaw');selfm=load(SELF,'self_minlaw');op=load(OPC,'op_minlaw');op.selfmod=selfm
 miss=load(MISS,'miss_minlaw');reify=load(REIFY,'reify_minlaw');reify.selfm=selfm
 ms=load(MS,'ms_minlaw');ms.selfmod=selfm;j=load(JOIN,'join_minlaw');j.selfm=selfm
 bridge=load(BRIDGE,'bridge_minlaw');bridge.selfm=selfm;att=load(ATT,'att_minlaw');att.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],tcost(m,x)));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),tcost(m,x)))
 base=g1[:32]+g2[:128];common=g1[:24]+g2[:56]
 _,_,fterms=miss.frontier(m,sym,source,target,base,10.0)
 missing=miss.target_missing(m,target,fterms);proper=reify.proper_missing(m,target,missing)
 required=proper or missing;required_keys={canon(m,t) for t in required}
 R=replay_filter(m,source,reify.generate_instances(m,source,target,required,'minimal-R-reification',520),160)
 M=replay_filter(m,source,ms.synthesize(m,source,target,missing),160)
 J=replay_filter(m,source,make_join_family(m,source,target,M,j),160)
 C=replay_filter(m,source,make_component_family(m,sym,source,target,M,J,bridge,j,common),160)
 fam={'R':R,'M':M,'J':J,'C':C}
 regimes=[]
 for k in range(1,5):
  for names in itertools.combinations(('R','M','J','C'),k):
   items=[];seen=set()
   for name in names:
    for x in fam[name]:
     q=eqkey(m,*x['schema'][:2])
     if q in seen:continue
     seen.add(q);items.append(x)
   hits=[x for x in items if contains_required(m,x,required_keys)]
   regimes.append({'names':names,'items':items,'hits':hits,'cost':regime_cost(m,names,items)})
 feasible=[r for r in regimes if r['hits']]
 feasible.sort(key=lambda r:r['cost'])
 chosen=feasible[0] if feasible else None
 A=j.run(m,sym,source,target,base,25,'A_frozen')
 if not chosen:
  out={'schema':'mathgraph.minimal-lawful-continuation-refinement.v1','id':RID,'required':[m.render_term(t) for t in required],'family_counts':{n:len(v) for n,v in fam.items()},'arms':{'A':A},'decision':'NO_LAWFUL_REFINEMENT'}
  OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True));return
 chosen_items=sorted(chosen['items'],key=lambda x:(0 if contains_required(m,x,required_keys) else 1,-x.get('activation',0),tcost(m,x)))[:96]
 C0=j.run(m,sym,source,target,common+chosen_items,32,'C_refined_no_attachment')
 attachments=att.attachments(m,source,target,chosen_items,limit=256)
 candidates=[]
 baseline_dist=C0.get('cross_distance')
 for idx,a in enumerate(attachments[:48]):
  arm=j.run(m,sym,source,target,common+chosen_items+[a],18,'D_attachment_probe')
  dist=arm.get('cross_distance')
  progress=bool(arm.get('closure')) or (baseline_dist is not None and dist is not None and dist<baseline_dist)
  candidates.append((0 if arm.get('closure') else 1,dist if dist is not None else 10**9,len(a.get('path',())),tcost(m,a),idx,a,arm,progress))
  if arm.get('closure'):break
 candidates.sort(key=lambda z:z[:5])
 improving=[z for z in candidates if z[-1]]
 selected=improving[0] if improving else None
 if selected:
  _,_,_,_,_,sel,D,_=selected
  Abl=j.run(m,sym,source,target,common+chosen_items,32,'D_attachment_ablation')
 else:
  sel=None;D={'closure':False,'tag':'D_attached','error':'no_improving_attachment'};Abl=None
 strong=bool(selected and D.get('closure') and not A.get('closure') and not C0.get('closure') and Abl and not Abl.get('closure'))
 if strong:decision='PASS_CLOSURE'
 elif selected:decision='MINIMAL_ATTACHMENT_PROGRESS'
 else:decision='MINIMAL_GRAMMAR_REFINEMENT_ONLY'
 out={
  'schema':'mathgraph.minimal-lawful-continuation-refinement.v1','id':RID,
  'rho':{'missing_required':[m.render_term(t) for t in required],'K':'at least one replay-valid installed candidate first-introduces a residual-required missing subterm'},
  'family_counts':{n:len(v) for n,v in fam.items()},
  'family_K_hits':{n:sum(contains_required(m,x,required_keys) for x in v) for n,v in fam.items()},
  'regimes_tested':len(regimes),'feasible_regimes':len(feasible),
  'minimum_regime':{'families':list(chosen['names']),'cost':chosen['cost'],'installed_for_closure':len(chosen_items),'K_hits':len(chosen['hits'])},
  'attachment_candidates':len(attachments),'attachment_probes':len(candidates),
  'selected_attachment':None if sel is None else {'lhs':m.render_term(sel['schema'][0]),'rhs':m.render_term(sel['schema'][1]),'path':list(sel.get('path',())),'activation':sel.get('activation'),'direct_target_contact':sel.get('direct_target_contact')},
  'arms':{'A_frozen':A,'C_refined':C0,'D_attached':D,'D_ablation':Abl},
  'protocol':{'precommitted_family_lattice':['R','M','J','C'],'lexicographic_minimality':True,'all_installed_equalities_replay_to_source':True,'no_external_proof_trace':True,'no_answer_label':True,'attachment_separate_from_constructor_refinement':True},
  'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
