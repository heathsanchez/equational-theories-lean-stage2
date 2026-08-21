#!/usr/bin/env python3
"""Residual-derived normal_0040 distance-2 exact-context site-lift gate.

The effect predicate and constructor-family hypothesis were frozen before this
implementation in NORMAL0040_DISTANCE2_SITE_LIFT_FREEZE_20260821.json.

The prior gate showed that 72 replay-valid *direct source instances* touching
the unique post-contractor distance-2 shell cannot realize a 2->1 contraction.
This gate changes the constructor family without changing the trust base:
replay-valid equalities already present in the frontier are reused as local
transformations and lifted through exact contexts of the two shell terms.

Matched arms:
 A retained 3->2 capability only
 B replay-valid shell context lifts whose prospective cut distance stays 2
 C replay-valid shell context lifts whose prospective cut distance is <2
If C contracts, rerun A as ablation while retaining the prior 3->2 capability.
"""
import importlib.util, json, sys
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
D2=ROOT/'experiments/mathgraph/run_normal0040_distance2_to1_gate.py'
FREEZE=ROOT/'experiments/mathgraph/NORMAL0040_DISTANCE2_SITE_LIFT_FREEZE_20260821.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-distance2-site-lift-gate.json'
RID='evaluation_normal_0040'
FREEZE_COMMIT='505f8887c18b8b6d6c26cc9326b07f3548f17891'


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod);return mod


def canon(m,t): return m.alpha_canonical_term(t,{})


def walk_paths(t,path=()):
    out=[(path,t)]
    if t[0]=='op':
        out.extend(walk_paths(t[1],path+('L',)))
        out.extend(walk_paths(t[2],path+('R',)))
    return out


def mismatch_paths(a,b,path=()):
    if a==b:return []
    if a[0]=='op' and b[0]=='op':
        return mismatch_paths(a[1],b[1],path+('L',))+mismatch_paths(a[2],b[2],path+('R',))
    return [{'path':path,'left':a,'right':b}]


def proof_item(acc,m,s,idx):
    return acc.proof_item_from_root(m,s,idx,'distance2-frontier-proof')


def collect_local_equalities(m,acc,s,anchors,max_items=180):
    subs=set()
    for A in anchors:
        for _,u in walk_paths(A):subs.add(canon(m,u))
    picked=[]
    # Prefer compact existing replay-valid transformations that can match an exact
    # shell subterm in either orientation. Nodes are topological, so prefixes replay.
    for i,n in enumerate(s.nodes):
        if canon(m,n.lhs) not in subs and canon(m,n.rhs) not in subs:continue
        if m.term_size(n.lhs)+m.term_size(n.rhs)>90:continue
        try:item=proof_item(acc,m,s,i)
        except Exception:continue
        ns,root=item['proof']
        if not m.replay_dag(s.source,ns,root,maximum_term_size=240,maximum_nodes=70000):continue
        picked.append(item)
        if len(picked)>=max_items:break
    return picked


def derive_lifts(m,acc,source,target,s,L,R,LS,RS,d0):
    anchors=[('L',A) for A in LS]+[('R',A) for A in RS]
    items=collect_local_equalities(m,acc,s,[A for _,A in anchors])
    seen=set();out=[]
    for side,A in anchors:
        for item in items:
            for rev in (False,True):
                try:x=acc.derive(m,source,target,item,A,rev,max_size=180)
                except Exception:x=None
                if not x:continue
                a,b=x['schema'][:2]
                k=tuple(sorted((repr(canon(m,a)),repr(canon(m,b)))))
                if k in seen:continue
                seen.add(k)
                if not m.replay_dag(source,x['proof'][0],x['proof'][1],maximum_term_size=240,maximum_nodes=80000):continue
                # A is one endpoint by construction. Evaluate the other endpoint
                # directly against the opposite *frozen* component.
                other=b if a==A else a if b==A else None
                if other is None:continue
                opp=R if side=='L' else L
                hd=min((m.structural_distance(other,z) for z in opp),default=d0)
                out.append((hd,m.term_size(a)+m.term_size(b),side,x))
    out.sort(key=lambda q:(q[0],q[1]))
    return out,len(items)


def install_measure(m,sym,selfm,op,reify,cp,acc,d2,source,target,mode,n=16):
    s,prior=d2.make_post_contractor(m,sym,selfm,op,reify,cp,acc,source,target,40)
    if prior is None:return {'error':'prior_contractor_not_reconstructed'}
    comps,lc,rc,L,R=d2.comp_terms(s,target)
    d0,pair=d2.cross_distance(m,L,R)
    LS,RS=d2.shell(m,L,R,d0)
    lifts,item_count=derive_lifts(m,acc,source,target,s,L,R,LS,RS,d0)
    pos=[q for q in lifts if q[0]<d0];neg=[q for q in lifts if q[0]>=d0]
    chosen=[]
    if mode=='contract':chosen=pos[:n]
    elif mode=='control':chosen=sorted(neg,key=lambda q:(q[1],q[0]))[:min(n,max(1,len(pos)))]
    for _,_,_,x in chosen:acc.install(m,s,x,'normal0040-distance2-site-lift-installed')
    comps1,lc1,rc1,L1,R1=d2.comp_terms(s,target);d1,pair1=d2.cross_distance(m,L1,R1)
    closed=(lc1==rc1)
    verified=False;cert_bytes=None
    if closed:
        for i,node in enumerate(s.nodes):
            if {node.lhs,node.rhs}=={target[0],target[1]} and m.replay_dag(source,s.nodes,i,maximum_term_size=260,maximum_nodes=140000):
                verified=True
                try:cert,_=m.make_dag_certificate(target,s.nodes,i);cert_bytes=len(cert.encode())
                except Exception:pass
                break
    def ex(q):
        hd,sz,side,x=q
        return {'hypothetical_distance':hd,'side':side,'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'size':sz}
    return {
        'distance_before':d0,'distance_after':d1,'shell_left':[m.render_term(x) for x in LS],
        'shell_right':[m.render_term(x) for x in RS],
        'shell_pair':None if pair is None else [m.render_term(pair[0]),m.render_term(pair[1])],
        'shell_mismatches':[] if pair is None else [
            {'path':''.join(z['path']) or 'ROOT','left':m.render_term(z['left']),'right':m.render_term(z['right'])}
            for z in mismatch_paths(pair[0],pair[1])],
        'frontier_local_equalities':item_count,'lift_candidates':len(lifts),'strict_contractors':len(pos),
        'noncontracting_lifts':len(neg),'installed':len(chosen),'selected':[ex(q) for q in chosen[:12]],
        'top_contractors':[ex(q) for q in pos[:12]],'closure_component_joined':closed,
        'verified_target_replay':verified,'certificate_bytes':cert_bytes,
        'lhs_component_before':len(L),'rhs_component_before':len(R),'lhs_component_after':len(L1),'rhs_component_after':len(R1)
    }


def main():
    freeze=json.loads(FREEZE.read_text())
    m=load(SOLVER,'mg_n40sl');sym=load(SYM,'sym_n40sl');selfm=load(SELF,'self_n40sl');op=load(OPC,'op_n40sl');reify=load(REIFY,'reify_n40sl');cp=load(CP,'cp_n40sl');acc=load(ACC,'acc_n40sl');d2=load(D2,'d2_n40sl')
    reify.selfm=selfm;op.selfmod=selfm
    row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if x['id']==RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
    A=install_measure(m,sym,selfm,op,reify,cp,acc,d2,source,target,'base')
    B=install_measure(m,sym,selfm,op,reify,cp,acc,d2,source,target,'control')
    C=install_measure(m,sym,selfm,op,reify,cp,acc,d2,source,target,'contract')
    ab=None
    if C.get('distance_after',999)<C.get('distance_before',999):
        ab=install_measure(m,sym,selfm,op,reify,cp,acc,d2,source,target,'base')
    if A.get('distance_before')!=2:decision='PRECONDITION_NOT_REPRODUCED'
    elif C.get('verified_target_replay') and not B.get('verified_target_replay') and ab and not ab.get('verified_target_replay'):
        decision='PASS_SITE_LIFT_CLOSURE_WITH_ABLATION'
    elif C.get('distance_after')==1 and B.get('distance_after')==2 and ab and ab.get('distance_after')==2:
        decision='PASS_SITE_LIFT_2_TO1_WITH_ABLATION'
    elif C.get('distance_after')==0 and C.get('closure_component_joined'):
        decision='PASS_SITE_LIFT_2_TO0_COMPONENT_CLOSURE'
    elif C.get('strict_contractors',0)>0:
        decision='SITE_LIFT_CONTRACTORS_FOUND_NO_UNIQUE_EFFECT'
    else:
        decision='NO_2_TO1_CONTRACTOR_IN_EXACT_CONTEXT_LIFT_FAMILY'
    out={'schema':'mathgraph.normal0040.distance2-site-lift.v1','id':RID,'freeze_commit':FREEZE_COMMIT,'freeze':freeze,
         'protocol':{'freeze_precedes_implementation':True,'prior_3to2_retained_all_arms':True,'no_external_proof_trace':True,'all_lifts_replay_to_source':True,'matched_noncontracting_control':True,'target_only_defines_components_and_final_closure':True},
         'arms':{'A_post_3to2_frozen':A,'B_noncontracting_site_lifts':B,'C_contracting_site_lifts':C,'C_ablation':ab},'decision':decision}
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
