#!/usr/bin/env python3
"""Search the real residual's *effect version space* without prescribing a constructor topology.

The effect specification is frozen in
REAL_RESIDUAL_EFFECT_VERSION_SPACE_FREEZE_20260821.json before this file.

K_effect requires only that a derived equality:
  1. replay under the original source law,
  2. contain a proper target subterm absent from the frozen pre-intervention frontier,
  3. have at least one endpoint already belonging to a pre-intervention lhs/rhs target component.

No cross-cone, congruence, site-count, distance, or named topology is required.
The intervention merely seeds the existing generic proof-combinator closure with
residual-reified direct source instances, then asks whether *any* derived edge
lands in the frozen effect version space.

Matched arms:
 A frozen generic closure
 B near-miss reification control
 C residual-derived reification

A positive scientific result is not required to close the theorem immediately:
C can first demonstrate that the previously empty effect version space becomes
nonempty.  Closure, ablation, and transfer remain stronger downstream gates.
"""
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py'
ACC=ROOT/'experiments/mathgraph/run_anchored_cut_contraction_gate.py'
FREEZE=ROOT/'experiments/mathgraph/REAL_RESIDUAL_EFFECT_VERSION_SPACE_FREEZE_20260821.json'
OUT=ROOT/'experiments/mathgraph/results/real-residual-effect-version-space-gate.json'
RID='evaluation_order5_0014'
FREEZE_COMMIT='c5a15f63a29eebb17b3f2b52658fbae9bc5336fb'


def load(path,name):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m


def canon(m,t): return m.alpha_canonical_term(t,{})


def all_terms(m,s):
    out={}
    for n in s.nodes:
        for side in (n.lhs,n.rhs):
            out.setdefault(canon(m,side),side)
            for u in m.walk_subterms(side): out.setdefault(canon(m,u),u)
    return out


def component_term_sets(m,s,target):
    comps=s.components(); tl,tr=target[:2]; lc,rc=comps.get(tl),comps.get(tr)
    left=set(); right=set()
    for n in s.nodes:
        for t in (n.lhs,n.rhs):
            c=comps.get(t)
            if c==lc:left.add(t)
            if c==rc:right.add(t)
    return comps,lc,rc,left,right


def nearest_reachable_controls(m,preterms,proper,limit):
    missing_keys={canon(m,t) for t in proper}
    vals=[t for t in preterms.values() if t[0]=='op' and canon(m,t) not in missing_keys]
    vals.sort(key=lambda t:(
        min((m.structural_distance(t,q) for q in proper),default=999),
        abs(m.term_size(t)-(m.term_size(proper[0]) if proper else 1)),
        m.term_size(t),m.render_term(t)))
    out=[];seen=set()
    for t in vals:
        k=canon(m,t)
        if k in seen:continue
        seen.add(k);out.append(t)
        if len(out)>=limit:break
    return out


def seed_items(m,reify,source,target,specials,tag,n=72):
    xs=reify.generate_instances(m,source,target,specials,tag,520)
    mkeys={canon(m,t) for t in specials}
    for x in xs:
        x['special_hits']=reify.hit_count(m,x,mkeys)
    xs.sort(key=lambda x:(-x['special_hits'],-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
    return xs[:min(n,len(xs))],len(xs)


def propagate(s,edge_limit=12000):
    pool=s.make_pool();s.instantiate_sources(pool)
    outer=list(range(max(0,len(s.nodes)-min(len(s.nodes),6500)),len(s.nodes)))
    cs=s.collect_overlap_candidates(outer,outer,5,18000)
    for q in cs[:edge_limit]:
        if time.monotonic()>=s.deadline:break
        s.apply_overlap(q,1)


def contains_required(m,t,proper_keys):
    return any(canon(m,u) in proper_keys for u in m.walk_subterms(t))


def scan_effects(m,source,s,start_idx,pre_left,pre_right,proper_keys,max_replay=64):
    raw=[]
    for i,n in enumerate(s.nodes[start_idx:],start=start_idx):
        attached=(n.lhs in pre_left or n.rhs in pre_left or n.lhs in pre_right or n.rhs in pre_right)
        if not attached:continue
        introduced=contains_required(m,n.lhs,proper_keys) or contains_required(m,n.rhs,proper_keys)
        if not introduced:continue
        raw.append((i,n))
    verified=[]
    for i,n in raw[:max_replay]:
        ok=bool(m.replay_dag(source,s.nodes,i,maximum_term_size=220,maximum_nodes=120000))
        if ok:
            verified.append({
                'node':i,'kind':n.kind,'constructor':n.constructor,
                'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),
                'attached_left':n.lhs in pre_left or n.rhs in pre_left,
                'attached_right':n.lhs in pre_right or n.rhs in pre_right,
                'required_in_lhs':contains_required(m,n.lhs,proper_keys),
                'required_in_rhs':contains_required(m,n.rhs,proper_keys),
            })
    return raw,verified


def run_arm(m,sym,selfm,op,reify,cp,acc,source,target,specials,mode,secs=38):
    state,s,roots=acc.make_search(m,sym,selfm,op,reify,cp,source,target,secs)
    preterms=all_terms(m,s)
    missing=reify.target_missing(m,target,preterms);proper=reify.proper_missing(m,target,missing)
    comps,lc,rc,pre_left,pre_right=component_term_sets(m,s,target)
    pre_nodes=len(s.nodes)
    selected=[];total_candidates=0
    if mode!='base':
        selected,total_candidates=seed_items(m,reify,source,target,specials,('effect-version-residual' if mode=='residual' else 'effect-version-control'))
        for x in selected:acc.install(m,s,x,'effect-version-space-seed')
    install_end=len(s.nodes)
    propagate(s)
    proper_keys={canon(m,t) for t in proper}
    raw,verified=scan_effects(m,source,s,pre_nodes,pre_left,pre_right,proper_keys)
    fin=s.components();closed=fin.get(target[0])==fin.get(target[1])
    return {
        'closure':closed,'pre_nodes':pre_nodes,'nodes':len(s.nodes),'graph_edges':s.graph_edges,
        'seed_candidates_total':total_candidates,'seeds_installed':len(selected),
        'seed_install_nodes_added':install_end-pre_nodes,
        'raw_effect_version_members':len(raw),'replay_verified_effect_members':len(verified),
        'effect_examples':verified[:12],
        'proper_missing':[m.render_term(t) for t in proper],
        'lhs_component_endpoint_count':len(pre_left),'rhs_component_endpoint_count':len(pre_right),
    }


def main():
    freeze=json.loads(FREEZE.read_text())
    m=load(SOLVER,'mg_ev');sym=load(SYM,'sym_ev');selfm=load(SELF,'self_ev');op=load(OPC,'op_ev');reify=load(REIFY,'reify_ev');cp=load(CP,'cp_ev');acc=load(ACC,'acc_ev')
    reify.selfm=selfm;op.selfmod=selfm
    row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])

    # Freeze the residual objects from a fresh pre-intervention state, then build matched seeds.
    _,s0,_=acc.make_search(m,sym,selfm,op,reify,cp,source,target,24)
    preterms=all_terms(m,s0);missing=reify.target_missing(m,target,preterms);proper=reify.proper_missing(m,target,missing)
    near=nearest_reachable_controls(m,preterms,proper,max(1,len(proper)))

    A=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,[], 'base')
    B=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,near,'control')
    C=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,proper,'residual')
    ab=None
    if C['closure'] or C['replay_verified_effect_members']>0:
        ab=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,[],'base')

    if C['closure'] and not A['closure'] and not B['closure'] and ab and not ab['closure']:
        decision='EFFECT_VERSION_CLOSES_WITH_ABLATION'
    elif C['replay_verified_effect_members']>0 and A['replay_verified_effect_members']==0 and B['replay_verified_effect_members']==0:
        decision='EFFECT_VERSION_SPACE_OPENED_BY_RESIDUAL_REIFICATION'
    elif C['replay_verified_effect_members']>0:
        decision='EFFECT_VERSION_SPACE_NONEMPTY_NOT_SPECIFIC'
    else:
        decision='EFFECT_VERSION_SPACE_EMPTY_UNDER_GENERIC_COMBINATOR_CLOSURE'

    out={
        'schema':'mathgraph.real-residual-effect-version-space.v1','id':RID,
        'freeze_commit':FREEZE_COMMIT,'freeze':freeze,
        'protocol':{
            'effect_spec_frozen_before_search_implementation':True,
            'no_named_constructor_topology_required':True,
            'no_external_proof_trace':True,
            'target_used_only_to_define_residual_objects_and_final_closure':True,
            'all_counted_effect_members_replay_to_source':True,
            'matched_near_miss_control':True,
        },
        'frozen_missing_target_subterms':[m.render_term(t) for t in missing],
        'frozen_proper_missing_subterms':[m.render_term(t) for t in proper],
        'near_miss_controls':[m.render_term(t) for t in near],
        'arms':{'A_frozen':A,'B_near_miss_control':B,'C_residual_effect_search':C,'C_ablation':ab},
        'decision':decision,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
