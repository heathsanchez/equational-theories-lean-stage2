#!/usr/bin/env python3
"""Test whether the post-residual failure is target-recognition, not derivation.

A: ordinary TargetGroundedRefutation solve/replay.
C: after exactly the same search, inspect only already-derived schematic clauses;
   if one simultaneously matches both rigid target sides under one substitution,
   instantiate that existing proof, compile it, and replay from the original law.
No target identity, external proof body, or new inference rule is introduced.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/schematic-target-closure-gate.json'
RID='evaluation_order5_0014'
SECONDS=20.0

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def engine(m,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
 limits.update(seconds=SECONDS,maximum_term_size=80,maximum_replay_term_size=300,maximum_depth=14,maximum_rules=1600,maximum_rounds=160,new_clauses_per_round=512,maximum_clauses=18000,normalization_steps=384,maximum_proof_nodes=120000)
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,limits)

def replay(m,e,recipe):
 if recipe is None:return {'closure':False}
 try:
  r=e.inline_recipe(recipe)
  c=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+5.0,e.search.limits)
  nodes,root=c.compile(r)
  ok=(nodes[root].lhs==e.target[0] and nodes[root].rhs==e.target[1] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes']))
  return {'closure':bool(ok),'proof_nodes':len(nodes),'root_kind':nodes[root].kind if ok else None}
 except Exception as ex:return {'closure':False,'error':repr(ex)}

def schematic_cover(m,e):
 tl=e.encode_rigid(e.target[0]);tr=e.encode_rigid(e.target[1]);hits=[]
 for clause in sorted(e.search.clauses,key=e.search.target_score):
  for rev in (False,True):
   left=clause.rhs if rev else clause.lhs;right=clause.lhs if rev else clause.rhs;mp={}
   if not m.match_term(left,tl,mp):continue
   if not m.match_term(right,tr,mp):continue
   vars_=m.term_variables(left)|m.term_variables(right)
   if not vars_<=set(mp):continue
   proof=e.search.instantiate(clause,mp)
   if rev:proof=m.Recipe(proof.rhs,proof.lhs,'symmetry',(proof,))
   if (proof.lhs,proof.rhs)!=(tl,tr):continue
   hits.append((clause,rev,mp,proof))
 return hits

def main():
 m=load(SOLVER,'mg_schematic_gate')
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
 e=engine(m,row);started=time.monotonic();base=e.search.solve();elapsed=time.monotonic()-started
 A=replay(m,e,base)
 hits=schematic_cover(m,e);C=replay(m,e,hits[0][3]) if hits else {'closure':False,'error':'no_schematic_cover'}
 witness=None
 if hits:
  cl,rev,mp,_=hits[0]
  witness={'clause_lhs':m.render_term(e.decode_rigid(cl.lhs)) if hasattr(e,'decode_rigid') else repr(cl.lhs),'clause_rhs':m.render_term(e.decode_rigid(cl.rhs)) if hasattr(e,'decode_rigid') else repr(cl.rhs),'reverse':rev,'mapping':{str(k):repr(v) for k,v in mp.items()}}
 out={'schema':'mathgraph.schematic-target-closure.v1','id':RID,'seconds':SECONDS,'search_elapsed':elapsed,'clauses':len(e.search.clauses),'superpositions':getattr(e.search,'superpositions',None),'protocol':{'same_search_for_A_and_C':True,'C_uses_only_already_derived_clause':True,'single_substitution_must_match_both_target_sides':True,'final_replay_from_original_source_required':True,'no_external_proof_trace':True,'no_target_identity_added':True},'A':A,'schematic_cover_count':len(hits),'C':C,'witness':witness,'decision':'PASS' if C.get('closure') and not A.get('closure') else 'BASELINE_ALREADY_CLOSES' if A.get('closure') else 'SCHEMATIC_COVER_REPLAY_FAILED' if hits else 'NO_SCHEMATIC_TARGET_COVER'}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
