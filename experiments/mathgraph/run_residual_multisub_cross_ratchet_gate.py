#!/usr/bin/env python3
"""Cross-capability ratchet after residual-derived multisubstitution.

Previous result: residual-unified multisubstitution produced 4 replay-verified
operators satisfying the predeclared missing-subterm obligation, but direct
installation plus one generation composed only over the new family did not close
`evaluation_order5_0014`.

This gate tests the developmentally natural next step: a newly invented
capability is added to, and generically composed with, the retained old capability
basis rather than evolved in isolation. No new trusted inference rule, target
identity, external proof trace, or answer label is introduced.
"""
import importlib.util, json, sys
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
MULTI=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-multisub-cross-ratchet-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def uniq(m,items,limit):
    seen=set();out=[]
    for x in items:
        a,b=x['schema'][:2]
        names={};k=(m.alpha_canonical_term(a,names),m.alpha_canonical_term(b,names))
        names={};kr=(m.alpha_canonical_term(b,names),m.alpha_canonical_term(a,names))
        key=min(k,kr)
        if key in seen:continue
        seen.add(key);out.append(x)
        if len(out)>=limit:break
    return out

def active_count(xs):return sum(int(x.get('activation',0)>0) for x in xs)

def main():
    m=load(SOLVER,'mg_cross');sym=load(SYM,'sym_cross');selfmod=load(SELF,'self_cross');op=load(OPC,'op_cross');op.selfmod=selfmod;missmod=load(MISS,'miss_cross');multimod=load(MULTI,'multi_cross');multimod.selfmod=selfmod
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
    for x in hits:x['name']='multisub'

    # Critical intervention: let the new residual-derived capability and retained
    # old capabilities inhabit the same generic composition generation.
    cross_seed=uniq(m,hits + g1[:8] + g2[:12],24)
    cross1=op.build_gen2(m,source,target,cross_seed,limit=1200) if cross_seed else []
    for x in cross1:x['name']='cross1'
    cross1.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))

    # One further generic generation, prioritizing operators that actually align
    # with target subterms but without adding any theorem-specific identity.
    cross1_active=[x for x in cross1 if x.get('activation',0)>0]
    cross2_seed=uniq(m,cross1_active + cross1[:12] + hits + g1[:4] + g2[:4],24)
    cross2=op.build_gen2(m,source,target,cross2_seed,limit=1200) if cross2_seed else []
    for x in cross2:x['name']='cross2'
    cross2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))

    A=missmod.run_arm(m,sym,source,target,base,25.0,'A_frozen')
    B=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+hits[:32],30.0,'B_multisub_direct')
    C=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+hits[:32]+cross1[:160],45.0,'C_cross1')
    D=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+hits[:32]+cross1[:96]+cross2[:160],60.0,'D_cross2')
    winner=next((z for z in (B,C,D) if z['closure']),None)
    Abl=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56],60.0,'ablation_remove_residual_family') if winner else None
    pass_gate=bool(winner and not A['closure'] and Abl and not Abl['closure'])
    out={
      'schema':'mathgraph.residual-multisub-cross-ratchet.v1','id':RID,
      'source':row['equation1'],'target':row['equation2'],
      'missing_target_subterms':[m.render_term(t) for t in missing],
      'counts':{'g1':len(g1),'g2':len(g2),'g1_active':active_count(g1),'g2_active':active_count(g2),'multisub_hits':len(hits),'cross1_verified':len(cross1),'cross1_active':active_count(cross1),'cross2_verified':len(cross2),'cross2_active':active_count(cross2)},
      'arms':{'A':A,'B':B,'C':C,'D':D,'ablation':Abl},
      'top_cross1':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x.get('activation',0),'parent':x.get('parent'),'variable':x.get('variable')} for x in cross1[:20]],
      'top_cross2':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x.get('activation',0),'parent':x.get('parent'),'variable':x.get('variable')} for x in cross2[:20]],
      'protocol':{'residual_constraint_predeclared':True,'new_family_replay_verified':True,'composition_is_existing_generic_machinery':True,'old_capability_retained':True,'no_external_proof_trace':True,'no_answer_label':True,'no_target_specific_identity':True},
      'decision':'PASS' if pass_gate else ('CLOSURE_NO_CAUSAL_ABLATION' if winner else ('TARGET_ALIGNMENT_GAIN' if active_count(cross1)+active_count(cross2)>0 else 'NO_ALIGNMENT_GAIN'))
    }
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
