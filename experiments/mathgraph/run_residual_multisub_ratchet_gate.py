#!/usr/bin/env python3
"""Ratchet residual-derived multisubstitution through existing verified composition."""
import importlib.util,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'; MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-multisub-ratchet-gate.json'; RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def main():
 m=load(SOLVER,'mg_r');sym=load(SYM,'sym_r');selfm=load(SELF,'self_r');op=load(OPC,'op_r');op.selfmod=selfm;miss=load(MISS,'miss_r');ms=load(MS,'ms_r');ms.selfmod=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128]
 _,_,fterms=miss.frontier(m,sym,source,target,base,10.0);missing=miss.target_missing(m,target,fterms)
 multi=ms.synthesize(m,source,target,missing)
 # Ratchet: use only replay-verified residual-derived operators as parents for the existing generic composition constructor.
 ratchet=op.build_gen2(m,source,target,multi,limit=520)
 for x in ratchet:x['name']='multisub_ratchet'
 ratchet.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 A=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56],30.0,'A_ablation')
 B=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56]+multi[:96],30.0,'B_multisub')
 C=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56]+multi[:96]+ratchet[:160],45.0,'C_multisub_ratchet')
 out={'schema':'mathgraph.residual-multisub-ratchet.v1','id':RID,'counts':{'g1':len(g1),'g2':len(g2),'multisub_verified':len(multi),'ratchet_verified':len(ratchet)},'missing_target_subterms':[m.render_term(t) for t in missing],'arms':{'A':A,'B':B,'C':C},'protocol':{'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity':True,'all_multisub_candidates_replay_verified':True,'ratchet_uses_existing_verified_composition_constructor':True},'decision':'PASS' if C['closure'] and not A['closure'] and not B['closure'] else ('PARTIAL' if C['closure'] else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
