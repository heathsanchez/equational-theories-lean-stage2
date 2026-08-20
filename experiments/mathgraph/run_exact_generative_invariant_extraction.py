#!/usr/bin/env python3
"""Fast Test 1: exact simple invariant extraction for evaluation_order5_0014.

This is a diagnostic, not a proof of necessity.  It reconstructs the current
post-development operator state, adds the previously tested contextual
critical-pair family, then mines *simple structural predicates* that hold for
every observed admitted equality edge but fail on the still-unreachable target
edge.  Such predicates are candidate K(rho) constraints for the next oracle
necessity test.

No answer label is used to generate operators.  The target is used only after
construction, as the held-out residual transition against which invariants are
checked.
"""
import importlib.util, json, sys, time
from collections import Counter
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py'
OUT=ROOT/'experiments/mathgraph/results/exact-generative-invariant-extraction.json'
RID='evaluation_order5_0014'

def load(p,n):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def depth(t):
    return 0 if t[0]=='var' else 1+max(depth(t[1]),depth(t[2]))

def mult(t,c=None):
    c=Counter() if c is None else c
    if t[0]=='var': c[t[1]]+=1
    else: mult(t[1],c);mult(t[2],c)
    return c

def proper_subterms(m,t):
    xs=list(m.walk_subterms(t));return set(xs[1:])

def child_support(t):
    if t[0]!='op': return (frozenset(),frozenset())
    return (frozenset(mult(t[1])),frozenset(mult(t[2])))

def features(m,a,b):
    va,vb=set(mult(a)),set(mult(b));ca,cb=mult(a),mult(b);vs=va|vb
    sa,sb=m.term_size(a),m.term_size(b);da,db=depth(a),depth(b)
    pa,pb=proper_subterms(m,a),proper_subterms(m,b)
    ach=child_support(a);bch=child_support(b)
    cross=sum(bool(x & y) for x in ach for y in bch)
    return {
      'support_symdiff':len(va^vb),
      'common_vars':len(va&vb),
      'size_delta_abs':abs(sa-sb),
      'depth_delta_abs':abs(da-db),
      'mult_l1':sum(abs(ca[v]-cb[v]) for v in vs),
      'max_mult_delta':max([abs(ca[v]-cb[v]) for v in vs] or [0]),
      'shared_proper_subterms':len(pa&pb),
      'child_support_crossings':cross,
      'same_support':va==vb,
      'lhs_support_subset_rhs':va<=vb,
      'rhs_support_subset_lhs':vb<=va,
      'has_common_variable':bool(va&vb),
      'same_root_kind':a[0]==b[0],
      'same_size_parity':(sa%2)==(sb%2),
      'same_depth_parity':(da%2)==(db%2),
      'one_endpoint_subterm_of_other':m.is_subterm(a,b) or m.is_subterm(b,a),
    }

def main():
    m=load(SOLVER,'mg_inv');sym=load(SYM,'sym_inv');selfm=load(SELF,'self_inv');op=load(OPC,'op_inv');r=load(REIFY,'reify_inv');cp=load(CP,'cp_inv')
    r.selfm=selfm;op.selfmod=selfm
    row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
    state=cp.build_state(m,sym,selfm,op,r,source,target)
    deadline=time.monotonic()+55.0
    limits={'max_term_size':120,'max_pool_terms':100,'max_core_terms':16,'max_source_attempts':140000,'max_source_edges':3500,'max_derivation_nodes':35000,'max_graph_edges':22000,'max_congruence_rounds':1}
    s=m.ContextualSearch(source,target,deadline,limits)
    roots=[]
    for item in state:
        root=cp.copy_proof_into(m,s,item['proof'],'post-development-installed')
        if root is not None: roots.append(root)
    pool=s.make_pool();s.instantiate_sources(pool)
    source_nodes=[i for i,n in enumerate(s.nodes) if n.kind in ('source instance','source reentry')]
    outer=list(dict.fromkeys(roots+source_nodes))[:3500];inner=list(dict.fromkeys(source_nodes+roots))[:3500]
    candidates=s.collect_overlap_candidates(outer,inner,4,9000)
    for c in candidates[:4500]:
        if time.monotonic()>=deadline: break
        s.apply_overlap(c,1)
    # Mine only semantic graph edges (support nodes excluded) and deduplicate unordered pairs.
    pairs=[];seen=set();kind_counts=Counter()
    for n in s.nodes:
        key=tuple(sorted((m.render_term(n.lhs),m.render_term(n.rhs))))
        if key in seen: continue
        seen.add(key);pairs.append((n.lhs,n.rhs));kind_counts[n.constructor or n.kind]+=1
    rows=[features(m,a,b) for a,b in pairs]
    tf=features(m,target[0],target[1])
    invariants=[]
    if rows:
        keys=list(rows[0])
        for k in keys:
            vals=[x[k] for x in rows]
            if isinstance(vals[0],bool):
                if all(v==vals[0] for v in vals) and tf[k]!=vals[0]:
                    invariants.append({'feature':k,'form':'constant','observed':vals[0],'target':tf[k],'coverage':len(vals)})
            else:
                lo,hi=min(vals),max(vals);tv=tf[k]
                if tv<lo or tv>hi:
                    invariants.append({'feature':k,'form':'closed_interval','observed_min':lo,'observed_max':hi,'target':tv,'margin':(lo-tv if tv<lo else tv-hi),'coverage':len(vals)})
                # Also mine one-sided laws when the extremum is informative.
                if all(v>=lo for v in vals) and tv<lo:
                    invariants.append({'feature':k,'form':'lower_bound','bound':lo,'target':tv,'margin':lo-tv,'coverage':len(vals)})
                if all(v<=hi for v in vals) and tv>hi:
                    invariants.append({'feature':k,'form':'upper_bound','bound':hi,'target':tv,'margin':tv-hi,'coverage':len(vals)})
    invariants.sort(key=lambda z:(-z.get('margin',1),z['feature'],z['form']))
    out={'schema':'mathgraph.exact-generative-invariant-extraction.v1','id':RID,
      'protocol':{'target_hidden_during_operator_generation':True,'target_used_only_for_posthoc_invariant_violation':True,'diagnostic_not_necessity_proof':True,'includes_post_development_state':True,'includes_contextual_critical_pair_family':True},
      'observed_unique_equalities':len(pairs),'nodes':len(s.nodes),'overlap_candidates':s.overlap_candidates,'overlaps_added':s.overlaps_added,'constructor_counts':dict(kind_counts),
      'target_features':tf,'candidate_invariants':invariants[:40],
      'decision':'CANDIDATE_K_FOUND' if invariants else 'NO_SIMPLE_EXACT_INVARIANT'}
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
