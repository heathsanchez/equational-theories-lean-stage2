#!/usr/bin/env python3
"""Mechanism-neutral cut-effect version-space search for evaluation_order5_0014.

The surviving residual is component disconnection, not target-structure absence.
K_cut_effect was frozen in REAL_RESIDUAL_CUT_EFFECT_FREEZE_20260821.json
before this implementation.

A candidate counts only by its verified *effect* on the frozen component quotient:
  - replay-valid under the original source law;
  - its equality endpoints lie in distinct frozen components (an unseen endpoint is
    treated as a fresh singleton component);
  - at least one endpoint touches the frozen lhs-target or rhs-target component.

K does not prescribe a constructor topology.  The proposal search deliberately
uses a mixed bounded program family of source-law instances whose substitution
atoms are drawn from frozen components.  Controls use same-component atoms;
the residual arm permits atoms from different frozen components.  After seeding,
the ordinary generic overlap/source-instantiation machinery is allowed to run.
"""
import importlib.util, itertools, json, sys, time
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
FREEZE=ROOT/'experiments/mathgraph/REAL_RESIDUAL_CUT_EFFECT_FREEZE_20260821.json'
OUT=ROOT/'experiments/mathgraph/results/real-residual-cut-effect-gate.json'
RID='evaluation_order5_0014'
FREEZE_COMMIT='aabf080d33de1cdbb5853bd8173f806e10a2b153'


def load(path,name):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m


def canon(m,t): return m.alpha_canonical_term(t,{})

def keyterm(m,t): return (m.term_size(t),m.render_term(t))


def component_inventory(m,s,target,per_component=16):
    comps=s.components(); tl,tr=target[:2]; lc,rc=comps.get(tl),comps.get(tr)
    by={}
    for n in s.nodes:
        for t in (n.lhs,n.rhs):
            c=comps.get(t)
            if c is not None: by.setdefault(c,{})[canon(m,t)]=t
    short={c:sorted(v.values(),key=keyterm)[:per_component] for c,v in by.items()}
    return comps,lc,rc,short


def source_instance(m,source,mapping,tag,max_size=180):
    lhs=m.substitute(source[0],mapping); rhs=m.substitute(source[1],mapping)
    if max(m.term_size(lhs),m.term_size(rhs))>max_size:return None
    node=m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,mapping[v]) for v in source[2]),orientation=False,constructor=tag)
    if not m.replay_dag(source,[node],0,maximum_term_size=max_size+20,maximum_nodes=8):return None
    return {'schema':(lhs,rhs,tuple(sorted(m.term_variables(lhs)|m.term_variables(rhs)))),'proof':([node],0),'name':tag}


def proposal_instances(m,source,short,lc,rc,mode,limit=160):
    vars_=list(source[2]); comps=[c for c,ts in short.items() if ts]
    fillers=[]
    for c in comps:
        fillers.extend(short[c][:3])
    fillers=sorted({canon(m,t):t for t in fillers}.values(),key=keyterm)[:8]
    out=[];seen=set()
    # Mixed search over two focused variables where possible.  The residual arm
    # allows different frozen components; the control requires the same one.
    focus_pairs=list(itertools.combinations(vars_,2)) or [(vars_[0],vars_[0])]
    comp_pairs=[]
    for c1 in comps:
        for c2 in comps:
            if mode=='cross' and c1==c2:continue
            if mode=='same' and c1!=c2:continue
            # Keep target-relevant proposals first without requiring a direct L-R bridge.
            score=0 if c1 in (lc,rc) or c2 in (lc,rc) else 1
            comp_pairs.append((score,c1,c2))
    comp_pairs.sort(key=lambda x:(x[0],str(x[1]),str(x[2])))
    for _,c1,c2 in comp_pairs:
        for v1,v2 in focus_pairs:
            for a in short[c1][:6]:
                for b in short[c2][:6]:
                    base={v1:a,v2:b}
                    rest=[v for v in vars_ if v not in base]
                    for fill in itertools.product(fillers[:4],repeat=len(rest)):
                        mp=dict(base);mp.update(zip(rest,fill))
                        item=source_instance(m,source,mp,'cut-effect-'+mode)
                        if not item:continue
                        names={}; k=(m.alpha_canonical_term(item['schema'][0],names),m.alpha_canonical_term(item['schema'][1],names))
                        rk=(k[1],k[0]); kk=min(k,rk)
                        if kk in seen:continue
                        seen.add(kk);out.append(item)
                        if len(out)>=limit:return out
    return out


def propagate(s,edge_limit=10000):
    # Give the installed candidates the same generic continuation machinery.
    s.deadline=time.monotonic()+28.0
    pool=s.make_pool();s.instantiate_sources(pool)
    outer=list(range(max(0,len(s.nodes)-min(len(s.nodes),7000)),len(s.nodes)))
    cs=s.collect_overlap_candidates(outer,outer,5,20000)
    for q in cs[:edge_limit]:
        if time.monotonic()>=s.deadline:break
        s.apply_overlap(q,1)


def frozen_label(m,comps,t):
    c=comps.get(t)
    return ('old',c) if c is not None else ('new',canon(m,t))


def cut_effect(n,m,comps,lc,rc):
    a=frozen_label(m,comps,n.lhs); b=frozen_label(m,comps,n.rhs)
    if a==b:return False
    ta=a==('old',lc) or b==('old',lc)
    tr=a==('old',rc) or b==('old',rc)
    return ta or tr


def scan(m,source,s,start,comps,lc,rc,max_replay=96):
    raw=[]
    for i,n in enumerate(s.nodes[start:],start=start):
        if cut_effect(n,m,comps,lc,rc):raw.append((i,n))
    verified=[]
    for i,n in raw[:max_replay]:
        if m.replay_dag(source,s.nodes,i,maximum_term_size=240,maximum_nodes=140000):
            a=frozen_label(m,comps,n.lhs);b=frozen_label(m,comps,n.rhs)
            verified.append({'node':i,'kind':n.kind,'constructor':n.constructor,'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),'lhs_label':repr(a),'rhs_label':repr(b),'touches_lhs_component':a==('old',lc) or b==('old',lc),'touches_rhs_component':a==('old',rc) or b==('old',rc),'direct_target_component_bridge':{a,b}=={('old',lc),('old',rc)}})
    return raw,verified


def run_arm(m,sym,selfm,op,reify,cp,acc,source,target,mode):
    # Reconstruct the same frozen state deterministically for each arm.
    _,s,_=acc.make_search(m,sym,selfm,op,reify,cp,source,target,36)
    comps,lc,rc,short=component_inventory(m,s,target)
    start=len(s.nodes)
    candidates=[]
    if mode in ('same','cross'):
        candidates=proposal_instances(m,source,short,lc,rc,mode,160)
        for x in candidates[:96]:acc.install(m,s,x,'cut-effect-seed-'+mode)
    installed_end=len(s.nodes)
    propagate(s)
    raw,verified=scan(m,source,s,start,comps,lc,rc)
    fin=s.components();closed=fin.get(target[0])==fin.get(target[1])
    return {'closure':closed,'pre_nodes':start,'nodes':len(s.nodes),'graph_edges':s.graph_edges,'proposal_candidates':len(candidates),'proposals_installed':min(96,len(candidates)),'seed_nodes_added':installed_end-start,'frozen_component_count':len(short),'lhs_component_atoms':len(short.get(lc,[])),'rhs_component_atoms':len(short.get(rc,[])),'raw_cut_effect_members':len(raw),'replay_verified_cut_effect_members':len(verified),'direct_target_component_bridges':sum(x['direct_target_component_bridge'] for x in verified),'effect_examples':verified[:12]}


def main():
    freeze=json.loads(FREEZE.read_text())
    m=load(SOLVER,'mg_cutv');sym=load(SYM,'sym_cutv');selfm=load(SELF,'self_cutv');op=load(OPC,'op_cutv');reify=load(REIFY,'reify_cutv');cp=load(CP,'cp_cutv');acc=load(ACC,'acc_cutv')
    reify.selfm=selfm;op.selfmod=selfm
    row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
    A=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,'base')
    B=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,'same')
    C=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,'cross')
    ab=None
    if C['closure'] or (C['replay_verified_cut_effect_members']>A['replay_verified_cut_effect_members'] and C['replay_verified_cut_effect_members']>B['replay_verified_cut_effect_members']):
        ab=run_arm(m,sym,selfm,op,reify,cp,acc,source,target,'base')
    if C['closure'] and not A['closure'] and not B['closure'] and ab and not ab['closure']:
        decision='CUT_EFFECT_CLOSES_WITH_ABLATION'
    elif C['replay_verified_cut_effect_members']>0 and A['replay_verified_cut_effect_members']==0 and B['replay_verified_cut_effect_members']==0:
        decision='CUT_EFFECT_VERSION_SPACE_OPENED_BY_CROSS_COMPONENT_PROPOSALS'
    elif C['replay_verified_cut_effect_members']>max(A['replay_verified_cut_effect_members'],B['replay_verified_cut_effect_members']):
        decision='CUT_EFFECT_ENRICHED_BY_CROSS_COMPONENT_PROPOSALS'
    elif max(A['replay_verified_cut_effect_members'],B['replay_verified_cut_effect_members'],C['replay_verified_cut_effect_members'])>0:
        decision='CUT_EFFECT_ALREADY_IN_GENERIC_OR_CONTROL_CLOSURE'
    else:
        decision='CUT_EFFECT_VERSION_SPACE_EMPTY_UNDER_TESTED_CONSTRUCTOR_PROGRAMS'
    out={'schema':'mathgraph.real-residual-cut-effect.v1','id':RID,'freeze_commit':FREEZE_COMMIT,'freeze':freeze,'protocol':{'cut_effect_frozen_before_implementation':True,'K_is_effect_not_constructor_shape':True,'no_external_proof_trace':True,'all_counted_members_replay_to_source':True,'same_component_matched_control':True,'target_used_only_for_frozen_component_labels_and_final_closure':True},'arms':{'A_frozen_generic':A,'B_same_component_control':B,'C_cross_component_program_search':C,'C_ablation':ab},'decision':decision}
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
