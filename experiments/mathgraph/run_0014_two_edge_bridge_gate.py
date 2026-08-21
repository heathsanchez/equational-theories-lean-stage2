#!/usr/bin/env python3
"""O5-0014: after one-edge source bridging is exhausted, test minimal two-edge coordination.

Freeze the semantic-JOIN geometry and generate replay-valid source-law instances
anchored independently in the LHS and RHS live target components.  Search first for
an exact shared far endpoint (a two-edge bridge); otherwise rank L/R pairs by the
structural distance between their far endpoints.  Install only the best coordinated
pairs and ask whether this strictly contracts the frozen cross-component distance or
closes the theorem.  No new trusted proof rule is introduced.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py';MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
JOIN=ROOT/'experiments/mathgraph/run_0014_semantic_join_endpoint_multisub_gate.py';BR=ROOT/'experiments/mathgraph/run_0014_component_bridge_unification_gate.py'
OUT=ROOT/'experiments/mathgraph/results/0014-two-edge-bridge-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def canon(m,t):return m.alpha_canonical_term(t,{})
def main():
 m=load(SOLVER,'mg_2e');sym=load(SYM,'sym_2e');selfm=load(SELF,'self_2e');op=load(OPC,'op_2e');op.selfmod=selfm
 miss=load(MISS,'miss_2e');ms=load(MS,'ms_2e');ms.selfmod=selfm;j=load(JOIN,'join_2e');j.selfm=selfm;br=load(BR,'br_2e');br.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);ep=j.endpoint_vars(source)[0]
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128];_,_,fterms=miss.frontier(m,sym,source,target,base,10.0);missing=miss.target_missing(m,target,fterms);multi=ms.synthesize(m,source,target,missing)
 maps=[]
 for it in multi:
  mp=dict(it['proof'][0][it['proof'][1]].substitution or ())
  if mp and all(v in mp for v in source[2]):maps.append(mp)
 join=[];seen=set()
 for bmp in maps:
  for side in target[:2]:
   mp=dict(bmp);mp[ep]=side;x=br.make(m,source,target,mp,'frozen-semantic-join')
   if x:
    k=(canon(m,x['schema'][0]),canon(m,x['schema'][1]))
    if k not in seen:seen.add(k);join.append(x)
 join.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 common=g1[:24]+g2[:56];frozen=common+join[:64];s=br.state(m,sym,source,target,frozen,35);uf,terms,L,R,lr,rr=br.components(m,target,s.nodes)
 bare_left=source[0][0]=='var' and source[0][1]==ep
 def far(x): return x['schema'][1] if bare_left else x['schema'][0]
 def anchored(side,terms_side):
  out=[];seen=set()
  for bmp in maps:
   for a in sorted(terms_side,key=lambda t:(m.term_size(t),m.render_term(t)))[:100]:
    mp=dict(bmp);mp[ep]=a;x=br.make(m,source,target,mp,f'two-edge-{side}-anchor')
    if not x:continue
    k=(canon(m,x['schema'][0]),canon(m,x['schema'][1]))
    if k in seen:continue
    seen.add(k);x['anchor_side']=side;out.append(x)
  return out
 LC=anchored('L',L);RC=anchored('R',R)
 pairs=[];exact=[]
 for a in LC:
  fa=far(a);ka=canon(m,fa)
  for b in RC:
   fb=far(b);kb=canon(m,fb);d=m.structural_distance(fa,fb)
   rec={'L':a,'R':b,'distance':d}
   pairs.append(rec)
   if ka==kb: exact.append(rec)
 pairs.sort(key=lambda q:(q['distance'],-q['L']['activation']-q['R']['activation'],m.term_size(far(q['L']))+m.term_size(far(q['R']))))
 chosen=(exact if exact else pairs)[:48]
 # Install both direct source instances from each coordinated pair; the existing prover
 # performs any sound transitive/contextual composition using its normal replay path.
 items=[];seen=set()
 for q in chosen:
  for x in (q['L'],q['R']):
   k=(canon(m,x['schema'][0]),canon(m,x['schema'][1]))
   if k not in seen:seen.add(k);items.append(x)
 A=j.run(m,sym,source,target,frozen,35,'A_frozen_join_geometry')
 C=j.run(m,sym,source,target,frozen+items,50,'C_two_edge_coordinated') if items else {'closure':False,'tag':'C_two_edge_coordinated','error':'no_pairs'}
 frozen_d=A.get('cross_distance');best_pair=pairs[0]['distance'] if pairs else None
 out={'schema':'mathgraph.0014-two-edge-bridge.v1','id':RID,
      'frozen_residual':{'lhs_component':len(L),'rhs_component':len(R),'cross_distance':frozen_d},
      'counts':{'L_anchored':len(LC),'R_anchored':len(RC),'pairs':len(pairs),'exact_shared_midpoints':len(exact),'installed_pair_edges':len(items)},
      'pair_geometry':{'best_far_endpoint_distance':best_pair,'distance_lt_frozen':sum(q['distance']<(frozen_d or 999) for q in pairs)},
      'arms':{'A':A,'C':C},
      'best_pairs':[{'distance':q['distance'],'L_far':m.render_term(far(q['L'])),'R_far':m.render_term(far(q['R'])),'L_activation':q['L']['activation'],'R_activation':q['R']['activation']} for q in pairs[:20]],
      'protocol':{'one_edge_bridge_previously_exhausted':True,'semantic_join_state_frozen':True,'both_edges_direct_source_instances_replay_verified':True,'same_pairing_rule_for_all_candidates':True,'no_external_proof_trace':True,'no_answer_label':True},
      'decision':'PASS_CLOSURE' if C.get('closure') and not A.get('closure') else 'EXACT_TWO_EDGE_BRIDGE_NO_CLOSURE' if exact else 'TWO_EDGE_DISTANCE_REDUCED' if C.get('cross_distance') is not None and frozen_d is not None and C['cross_distance']<frozen_d else 'TWO_EDGE_GEOMETRIC_SIGNAL' if best_pair is not None and frozen_d is not None and best_pair<frozen_d else 'TWO_EDGE_RESIDUAL'}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
