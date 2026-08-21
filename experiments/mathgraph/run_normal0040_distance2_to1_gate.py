#!/usr/bin/env python3
"""Prospectively frozen normal_0040 2->1 residual contraction gate.

The effect predicate was frozen in NORMAL0040_DISTANCE2_TO1_FREEZE_20260821.json
before this implementation.  It does not prescribe a constructor topology.

Protocol:
  1. Rebuild the post-development normal_0040 state.
  2. Reinstall the previously discovered replay-valid 3->2 contractor.
  3. Freeze the resulting distance-2 shell.
  4. Enumerate replay-valid direct source-law instances using shell terms as
     substitution atoms.
  5. Classify candidates prospectively by their counterfactual effect on the
     frozen component distance.
  6. Compare matched non-contracting controls with strict 2->1/0 contractors.
  7. If contraction occurs, ablate the new operators while retaining the prior
     3->2 contractor.

No external proof trace or answer label is used.  The target is used only to
identify the two residual components and final closure.
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
FREEZE=ROOT/'experiments/mathgraph/NORMAL0040_DISTANCE2_TO1_FREEZE_20260821.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-distance2-to1-gate.json'
RID='evaluation_normal_0040'
FREEZE_COMMIT='6f8af0a812eaf0a6467b0728ff849d010d987a5c'
KNOWN_CONTRACTOR='x = ((((x ◇ y) ◇ x) ◇ x) ◇ y)'


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod);return mod


def canon(m,t): return m.alpha_canonical_term(t,{})


def comp_terms(s,target):
    comps=s.components();tl,tr=target[:2];lc,rc=comps.get(tl),comps.get(tr)
    L=set();R=set()
    for n in s.nodes:
        for t in (n.lhs,n.rhs):
            c=comps.get(t)
            if c==lc:L.add(t)
            if c==rc:R.add(t)
    return comps,lc,rc,L,R


def cross_distance(m,L,R):
    if not L or not R:return 10**9,None
    best=10**9;pair=None
    for a in L:
        for b in R:
            d=m.structural_distance(a,b)
            if d<best:
                best=d;pair=(a,b)
                if best==0:return best,pair
    return best,pair


def shell(m,L,R,d):
    LS=[];RS=[]
    for a in L:
        if min((m.structural_distance(a,b) for b in R),default=999)==d:LS.append(a)
    for b in R:
        if min((m.structural_distance(a,b) for a in L),default=999)==d:RS.append(b)
    LS.sort(key=lambda t:(m.term_size(t),m.render_term(t)))
    RS.sort(key=lambda t:(m.term_size(t),m.render_term(t)))
    return LS,RS


def direct_identity_item(m,source,target):
    want=m.parse_equation(KNOWN_CONTRACTOR)
    # First try identity substitution; this is the previously observed source-law instance.
    mp={v:('var',v) for v in source[2]}
    lhs=m.substitute(source[0],mp);rhs=m.substitute(source[1],mp)
    pairs=[(lhs,rhs),(rhs,lhs)]
    for a,b in pairs:
        if (a,b)==want[:2] or (b,a)==want[:2]:
            node=m.EqualityNode(a,b,'source instance',substitution=tuple((v,mp[v]) for v in source[2]),orientation=False,constructor='normal0040-prior-3to2-contractor')
            if m.replay_dag(source,[node],0,maximum_term_size=220,maximum_nodes=8):
                return {'schema':(a,b,tuple(sorted(m.term_variables(a)|m.term_variables(b)))),'proof':([node],0),'name':'prior_3to2'}
    return None


def find_prior_contractor(m,reify,source,target,s,limit=12000):
    item=direct_identity_item(m,source,target)
    if item:return item
    # Fallback: search direct source instances built from short component terms.
    _,_,_,L,R=comp_terms(s,target)
    vals=sorted(L|R,key=lambda t:(m.term_size(t),m.render_term(t)))[:24]
    xs=reify.generate_instances(m,source,target,vals,'normal0040-prior-contractor-search',limit)
    want=m.parse_equation(KNOWN_CONTRACTOR)
    wk={canon(m,want[0]),canon(m,want[1])}
    for x in xs:
        if {canon(m,x['schema'][0]),canon(m,x['schema'][1])}==wk:
            return x
    return None


def make_post_contractor(m,sym,selfm,op,reify,cp,acc,source,target,secs=32):
    _,s,_=acc.make_search(m,sym,selfm,op,reify,cp,source,target,secs)
    prior=find_prior_contractor(m,reify,source,target,s)
    if prior is None:return s,None
    acc.install(m,s,prior,'normal0040-prior-3to2-installed')
    return s,prior


def hypothetical_distance(m,item,L,R,LS,RS,current):
    a,b=item['schema'][:2]
    shellL=set(LS);shellR=set(RS)
    effects=[]
    if a in shellL or b in shellL:
        new=b if a in L else a if b in L else None
        if new is not None:
            effects.append(min((m.structural_distance(new,r) for r in R),default=current))
    if a in shellR or b in shellR:
        new=b if a in R else a if b in R else None
        if new is not None:
            effects.append(min((m.structural_distance(l,new) for l in L),default=current))
    if not effects:return None
    return min([current]+effects)


def candidates(m,reify,source,target,L,R,LS,RS,current):
    specials=(LS+RS)[:32]
    xs=reify.generate_instances(m,source,target,specials,'normal0040-distance2-frontier',12000)
    seen=set();out=[]
    for x in xs:
        a,b=x['schema'][:2]
        k=tuple(sorted((repr(canon(m,a)),repr(canon(m,b)))))
        if k in seen:continue
        seen.add(k)
        if not m.replay_dag(source,x['proof'][0],x['proof'][1],maximum_term_size=220,maximum_nodes=50000):continue
        hd=hypothetical_distance(m,x,L,R,LS,RS,current)
        if hd is None:continue
        out.append((hd,m.term_size(a)+m.term_size(b),x))
    out.sort(key=lambda q:(q[0],q[1]))
    return out


def install_and_measure(m,sym,selfm,op,reify,cp,acc,source,target,mode,n=24):
    s,prior=make_post_contractor(m,sym,selfm,op,reify,cp,acc,source,target,38)
    if prior is None:return {'error':'prior_contractor_not_reconstructed','closure':False}
    comps,lc,rc,L,R=comp_terms(s,target);d0,pair=cross_distance(m,L,R);LS,RS=shell(m,L,R,d0)
    cs=candidates(m,reify,source,target,L,R,LS,RS,d0)
    pos=[q for q in cs if q[0]<d0];neg=[q for q in cs if q[0]>=d0]
    chosen=[]
    if mode=='contract': chosen=pos[:n]
    elif mode=='control': chosen=sorted(neg,key=lambda q:(q[1],q[0]))[:min(n,len(pos) if pos else n)]
    for _,_,x in chosen:acc.install(m,s,x,'normal0040-distance2-step-installed')
    comps1,lc1,rc1,L1,R1=comp_terms(s,target);d1,pair1=cross_distance(m,L1,R1)
    closed=(lc1==rc1)
    verified_closure=False;cert_bytes=None
    if closed:
        # Graph connectivity is necessary; final proof acceptance still requires a replay-valid target root.
        for i,nod in enumerate(s.nodes):
            if {nod.lhs,nod.rhs}=={target[0],target[1]} and m.replay_dag(source,s.nodes,i,maximum_term_size=240,maximum_nodes=120000):
                verified_closure=True
                try: cert,_=m.make_dag_certificate(target,s.nodes,i);cert_bytes=len(cert.encode())
                except Exception: pass
                break
    def ex(q):
        hd,sz,x=q;return {'hypothetical_distance':hd,'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'size':sz}
    return {
        'closure_component_joined':closed,'verified_target_replay':verified_closure,'certificate_bytes':cert_bytes,
        'distance_before':d0,'distance_after':d1,'lhs_component_before':len(L),'rhs_component_before':len(R),
        'lhs_component_after':len(L1),'rhs_component_after':len(R1),'distance2_left_shell':len(LS),'distance2_right_shell':len(RS),
        'candidate_count':len(cs),'strict_contractors':len(pos),'noncontracting_candidates':len(neg),'installed':len(chosen),
        'selected':[ex(q) for q in chosen[:12]],'top_contractors':[ex(q) for q in pos[:12]],
        'prior_contractor':{'lhs':m.render_term(prior['schema'][0]),'rhs':m.render_term(prior['schema'][1])}
    }


def main():
    freeze=json.loads(FREEZE.read_text())
    m=load(SOLVER,'mg_n40d');sym=load(SYM,'sym_n40d');selfm=load(SELF,'self_n40d');op=load(OPC,'op_n40d');reify=load(REIFY,'reify_n40d');cp=load(CP,'cp_n40d');acc=load(ACC,'acc_n40d')
    reify.selfm=selfm;op.selfmod=selfm
    row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if x['id']==RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
    A=install_and_measure(m,sym,selfm,op,reify,cp,acc,source,target,'base')
    B=install_and_measure(m,sym,selfm,op,reify,cp,acc,source,target,'control')
    C=install_and_measure(m,sym,selfm,op,reify,cp,acc,source,target,'contract')
    ab=None
    if C.get('distance_after',999)<C.get('distance_before',999):
        ab=install_and_measure(m,sym,selfm,op,reify,cp,acc,source,target,'base')
    pre_ok=(A.get('distance_before')==2 and A.get('distance_after')==2)
    if not pre_ok: decision='PRECONDITION_NOT_REPRODUCED'
    elif C.get('verified_target_replay') and not B.get('verified_target_replay') and ab and not ab.get('verified_target_replay'):
        decision='PASS_CLOSURE_WITH_ABLATION'
    elif C.get('distance_after',999)==0 and C.get('closure_component_joined'):
        decision='PASS_DISTANCE_2_TO_0_COMPONENT_CLOSURE'
    elif C.get('distance_after',999)==1 and B.get('distance_after')==2 and ab and ab.get('distance_after')==2:
        decision='PASS_DISTANCE_2_TO_1_WITH_ABLATION'
    elif C.get('strict_contractors',0)>0:
        decision='CONTRACTORS_FOUND_BUT_NO_UNIQUE_2_TO1_EFFECT'
    else:
        decision='NO_DISTANCE_2_TO1_CONTRACTOR_IN_ENUMERATED_SOURCE_INSTANCE_FAMILY'
    out={'schema':'mathgraph.normal0040.distance2-to1.v1','id':RID,'freeze_commit':FREEZE_COMMIT,'freeze':freeze,
         'protocol':{'freeze_precedes_implementation':True,'no_external_proof_trace':True,'target_only_defines_components_and_final_closure':True,'all_candidates_replay_to_source':True,'matched_noncontracting_control':True,'prior_3to2_capability_retained_in_all_arms':True},
         'arms':{'A_post_3to2_frozen':A,'B_noncontracting_control':B,'C_distance_contractor':C,'C_ablation':ab},'decision':decision}
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
