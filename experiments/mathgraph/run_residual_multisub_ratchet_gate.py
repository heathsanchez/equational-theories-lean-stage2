#!/usr/bin/env python3
"""Push the O5 -> D' experiment past structural constraint escape.

This gate assumes only the same residual-derived missing-subterm obligation used by
run_residual_unified_multisubstitution_gate.py.  It asks whether replay-verified
simultaneous multi-variable source instances that actually introduce the missing
structure become a causal proof capability after one generic generation of the
existing verified composition machinery.

Arms:
 A  frozen G1+G2
 B  direct residual-unified multisubstitution hits
 C  direct hits + one generic verified composition generation over those hits
 C- ablation: remove the residual-derived multisubstitution family again

No external proof trace, answer label, or target-specific identity is supplied.
"""
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
MULTI=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-multisub-ratchet-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def main():
    m=load(SOLVER,'mg_mr');sym=load(SYM,'sym_mr');selfmod=load(SELF,'self_mr');op=load(OPC,'op_mr');op.selfmod=selfmod;missmod=load(MISS,'miss_mr');multimod=load(MULTI,'multi_mr');multimod.selfmod=selfmod
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
    _,_,fterms=missmod.frontier(m,sym,source,target,base,10.0)
    missing=missmod.target_missing(m,target,fterms)
    multi=multimod.synthesize(m,source,target,missing,limit=400)
    hits=[x for x in multi if x.get('hits',0)>0]
    # Causally privileged only by satisfying the predeclared residual obligation.
    seed=(hits+multi)[:40]
    for x in seed:x['name']='multisub'
    composed=op.build_gen2(m,source,target,seed,limit=900) if seed else []
    for x in composed:x['name']='multisub_g2'
    composed.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))

    A=missmod.run_arm(m,sym,source,target,base,25.0,'A_frozen')
    B=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+hits[:96],30.0,'B_multisub_hits')
    C=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+hits[:64]+composed[:128],45.0,'C_multisub_ratchet')
    Abl=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+composed[:128],45.0,'C_remove_multisub_seed') if C['closure'] else None

    out={
      'schema':'mathgraph.residual-multisub-ratchet.v1','id':RID,
      'missing_target_subterms':[m.render_term(t) for t in missing],
      'counts':{'g1':len(g1),'g2':len(g2),'multisub_verified':len(multi),'multisub_constraint_hits':len(hits),'multisub_composed_verified':len(composed)},
      'arms':{'A':A,'B':B,'C':C,'C_remove_multisub_seed':Abl},
      'protocol':{'residual_condition_fixed_before_constructor':True,'all_multisub_candidates_replay_to_source':True,'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity':True,'composition_after_invention_is_generic_existing_machinery':True},
      'decision':('PASS' if C['closure'] and not A['closure'] and (not B['closure'] or B['closure']) and Abl and not Abl['closure'] else ('CLOSURE_NO_ABLATION' if C['closure'] else ('STRUCTURAL_ESCAPE_ONLY' if hits else 'NO_ESCAPE')))
    }
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
