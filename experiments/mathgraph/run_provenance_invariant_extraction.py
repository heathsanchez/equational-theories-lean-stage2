#!/usr/bin/env python3
"""Lifted Test 1b: provenance/dependency invariant extraction for order5_0014.

The term-pair feature miner found no exact separator.  This test lifts the
observable language one level: it reconstructs the post-development state,
adds the bounded contextual critical-pair family, freezes the resulting
component partition, and asks what kinds of *derivational mixing* the admitted
nodes actually realize.

In particular it measures whether any derived consequence has immediate or
transitive proof ancestry touching both target-side components before those
components are joined.  If the current grammar never mixes the two provenance
cones, while any first joining proof step must either mix them or introduce a
direct cross-cut primitive, that is a concrete higher-level K(rho) candidate.

This remains diagnostic.  Necessity is tested separately with a relaxed oracle.
"""
import importlib.util, json, sys, time
from collections import Counter, deque
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py'
OUT=ROOT/'experiments/mathgraph/results/provenance-invariant-extraction.json'
RID='evaluation_order5_0014'

def load(p,n):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def endpoint_mask(node, comps, lc, rc):
    mask=0
    for t in (node.lhs,node.rhs):
        c=comps.get(t)
        if c==lc: mask|=1
        if c==rc: mask|=2
    return mask

def ancestry_masks(nodes, comps, lc, rc):
    memo={}
    def rec(i):
        if i in memo:return memo[i]
        n=nodes[i];mask=endpoint_mask(n,comps,lc,rc)
        for p in n.parents:
            if 0<=p<i: mask|=rec(p)
        memo[i]=mask;return mask
    for i in range(len(nodes)):rec(i)
    return memo

def main():
    m=load(SOLVER,'mg_pinv');sym=load(SYM,'sym_pinv');selfm=load(SELF,'self_pinv');op=load(OPC,'op_pinv');r=load(REIFY,'reify_pinv');cp=load(CP,'cp_pinv')
    r.selfm=selfm;op.selfmod=selfm
    row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);tl,tr=target[:2]
    state=cp.build_state(m,sym,selfm,op,r,source,target)
    deadline=time.monotonic()+70.0
    limits={'max_term_size':120,'max_pool_terms':110,'max_core_terms':18,'max_source_attempts':180000,'max_source_edges':4500,'max_derivation_nodes':45000,'max_graph_edges':28000,'max_congruence_rounds':1}
    s=m.ContextualSearch(source,target,deadline,limits)
    roots=[]
    for item in state:
        q=cp.copy_proof_into(m,s,item['proof'],'post-development-installed')
        if q is not None:roots.append(q)
    pool=s.make_pool();s.instantiate_sources(pool)
    source_nodes=[i for i,n in enumerate(s.nodes) if n.kind in ('source instance','source reentry')]
    # Freeze the pre-overlap cut for selection, then add the same generic critical-pair family.
    pre=s.components();lc0,rc0=pre.get(tl),pre.get(tr)
    outer=list(dict.fromkeys(roots+source_nodes))[:4500];inner=list(dict.fromkeys(source_nodes+roots))[:4500]
    cand=s.collect_overlap_candidates(outer,inner,4,12000)
    for c in cand[:6000]:
        if time.monotonic()>=deadline:break
        s.apply_overlap(c,1)
    comps=s.components();lc,rc=comps.get(tl),comps.get(tr)
    am=ancestry_masks(s.nodes,comps,lc,rc)
    immediate_mixed=0;ancestry_mixed=0;direct_cross=0
    mixed_examples=[];constructor_mix=Counter();kind_counts=Counter();parent_arity=Counter()
    for i,n in enumerate(s.nodes):
        kind=n.constructor or n.kind;kind_counts[kind]+=1;parent_arity[len(n.parents)]+=1
        em=endpoint_mask(n,comps,lc,rc)
        if em==3: direct_cross+=1
        pm=0
        for p in n.parents:
            if 0<=p<i: pm|=endpoint_mask(s.nodes[p],comps,lc,rc)
        if pm==3:
            immediate_mixed+=1;constructor_mix[kind]+=1
            if len(mixed_examples)<8:mixed_examples.append({'node':i,'kind':kind,'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),'parents':list(n.parents)})
        if am[i]==3: ancestry_mixed+=1
    # A stronger local statistic: two-parent nodes whose two parents separately touch opposite cones.
    opposite_parent_pairs=0
    opposite_examples=[]
    for i,n in enumerate(s.nodes):
        if len(n.parents)<2:continue
        masks=[endpoint_mask(s.nodes[p],comps,lc,rc) if 0<=p<i else 0 for p in n.parents]
        ok=any((a&1 and b&2) or (a&2 and b&1) for j,a in enumerate(masks) for b in masks[j+1:])
        if ok:
            opposite_parent_pairs+=1
            if len(opposite_examples)<8:opposite_examples.append({'node':i,'kind':n.constructor or n.kind,'parent_masks':masks,'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs)})
    candidates=[]
    if lc!=rc and direct_cross==0:
        candidates.append({'name':'no_direct_cross_cut_edge','observed':True,'required_break':'successful closure must introduce a first cross-cut edge'})
    if lc!=rc and immediate_mixed==0:
        candidates.append({'name':'no_immediate_two_cone_provenance_mix','observed':True,'required_break':'successful nonprimitive bridge must combine parents carrying opposite target-component provenance'})
    if lc!=rc and opposite_parent_pairs==0:
        candidates.append({'name':'no_two_parent_opposite_component_mix','observed':True,'required_break':'permit a constructor whose verified parents separately touch the lhs and rhs residual components'})
    out={'schema':'mathgraph.provenance-invariant-extraction.v1','id':RID,
      'protocol':{'post_development_state':True,'includes_contextual_critical_pairs':True,'target_used_only_to_name_residual_components':True,'diagnostic_not_necessity_proof':True,'no_external_proof_trace':True,'no_answer_label_for_operator_generation':True},
      'pre_overlap_components':{'lhs':lc0,'rhs':rc0,'joined':lc0==rc0},
      'final_components':{'lhs':lc,'rhs':rc,'joined':lc==rc},
      'nodes':len(s.nodes),'graph_edges':s.graph_edges,'overlap_candidates':len(cand),'overlaps_added':s.overlaps_added,
      'direct_cross_edges':direct_cross,'immediate_mixed_provenance_nodes':immediate_mixed,'transitive_mixed_ancestry_nodes':ancestry_mixed,'two_parent_opposite_component_nodes':opposite_parent_pairs,
      'constructor_counts':dict(kind_counts),'mixed_constructor_counts':dict(constructor_mix),'parent_arity_counts':{str(k):v for k,v in parent_arity.items()},
      'mixed_examples':mixed_examples,'opposite_parent_examples':opposite_examples,'candidate_K':candidates,
      'decision':'PROVENANCE_K_CANDIDATE_FOUND' if candidates else 'NO_SIMPLE_PROVENANCE_INVARIANT'}
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
