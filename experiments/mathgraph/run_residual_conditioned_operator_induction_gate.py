#!/usr/bin/env python3
"""Decisive residual-conditioned operator-family induction gate.

Frozen target: evaluation_order5_0014, chosen because prior supplied-language
(genome/schema/self-embedding/operator-closure) gates all leave it unresolved.

Protocol:
  A. Build the currently verified operator language G1+G2 from source only.
  B. Compute a bounded rewrite cut around the target under that frozen language.
     This is the residual-derived constraint K(rho): any one-edge bridge between
     the two bounded reachability regions must cross this cut.
  C. Compare matched-budget arms:
       A0 frozen G1+G2 only;
       B  unconstrained G3 recursive operator closure, ranked by old target
          activation heuristic;
       C  residual-conditioned G3/G4 recursive closure, where parents and
          installations are selected by bridge pressure against K(rho).
  D. Every invented macro is compiled to the original source proof primitives
     and replay-verified before installation. No Vampire proof body, answer
     label, target-specific identity, or new trusted inference rule is used.

A positive is only a replay-valid closure; a result file records the cut,
operator generations, matched arms, and certificate size.
"""
import importlib.util, json, sys, time
from collections import deque
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-conditioned-operator-induction-gate.json'
RID='evaluation_order5_0014'


def load(path,name):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m


def paths(term,path=()):
    yield path,term
    if term[0]=='op':
        yield from paths(term[1],path+('L',))
        yield from paths(term[2],path+('R',))


def rewrite_once(m,term,schema,max_size=90):
    out=[];seen=set();lhs,rhs,_=schema
    for a,b in ((lhs,rhs),(rhs,lhs)):
        for p,t in paths(term):
            mp={}
            if not m.match_term(a,t,mp):continue
            try:r=m.substitute(b,mp)
            except Exception:continue
            nt=m.replace_subterm(term,p,r)
            if nt==term or m.term_size(nt)>max_size:continue
            k=m.alpha_canonical_term(nt,{})
            if k not in seen:seen.add(k);out.append(nt)
    return out


def bounded_reach(m,start,schemas,depth=2,cap=1400,max_size=90):
    canon=lambda t:m.alpha_canonical_term(t,{})
    seen={canon(start):start};q=deque([(start,0)])
    while q and len(seen)<cap:
        t,d=q.popleft()
        if d>=depth:continue
        for s in schemas:
            for nt in rewrite_once(m,t,s,max_size=max_size):
                k=canon(nt)
                if k in seen:continue
                seen[k]=nt;q.append((nt,d+1))
                if len(seen)>=cap:break
            if len(seen)>=cap:break
    return seen


def term_distance(a,b):
    if a==b:return 0
    if a[0]!=b[0]:return 1
    if a[0]=='var':return 1
    return term_distance(a[1],b[1])+term_distance(a[2],b[2])


def bridge_score(m,item,left,right):
    """Pressure toward crossing the frozen residual cut.

    Exact bridge gets a very large score. Otherwise score the best reduction in
    tree distance between a rewrite from one region and the opposite region.
    This uses only the bounded residual regions, not any external proof trace.
    """
    s=item['schema'];rvals=list(right.values());lvals=list(left.values())
    rc=set(right);lc=set(left);best=0
    L=lvals[:220];R=rvals[:220]
    def nearest(t,vals):
        if not vals:return 10**9
        return min(term_distance(t,v) for v in vals)
    for src,opp,oppkeys in ((L,R,rc),(R,L,lc)):
        for t in src:
            base=nearest(t,opp)
            for nt in rewrite_once(m,t,s,max_size=90):
                k=m.alpha_canonical_term(nt,{})
                if k in oppkeys:return 1000000,True
                imp=base-nearest(nt,opp)
                if imp>best:best=imp
    return best*100 + int(item.get('activation',0)),False


def append_proof(m,dst,proof):
    nodes,root=proof;off=len(dst)
    for n in nodes:
        dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'residual-conditioned-installed',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
    return off+root


def run_arm(m,sym,source,target,items,seconds=20.0,tag='arm'):
    started=time.monotonic();Norm=sym.make_normalizer(m)
    cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=6500,overlap_candidates=6000,selected_rules=900,replayed_rules=3500,maximum_term_size=100,maximum_proof_nodes=90000)
    search=Norm(source,target,started+seconds,cfg)
    roots=[append_proof(m,search.nodes,x['proof']) for x in items]
    found=search.solve();ok=False;cert=None;pn=None
    if found:
        nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=100,maximum_nodes=90000))
        if ok:
            code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
    return {'closure':ok,'seconds':round(time.monotonic()-started,6),'installed':len(roots),'rules':len(search.rules),'overlaps':search.overlap_candidates,'left_steps':search.left_steps,'right_steps':search.right_steps,'certificate_bytes':cert,'proof_nodes':pn,'tag':tag}


def generation(m,opmod,source,target,parents,limit=420):
    out=opmod.build_gen2(m,source,target,parents,limit=limit)
    out.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
    return out


def show_eq(m,e):
    return m.render_term(e[0])+' = '+m.render_term(e[1])


def main():
    global selfmod
    m=load(SOLVER,'mg_residual_induction');sym=load(SYM,'sym_residual_induction');selfmod=load(SELF,'self_residual_induction');op=load(OPC,'op_residual_induction')
    op.selfmod=selfmod
    rows={r['id']:dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID}
    row=rows[RID];source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])

    g1=[]
    for p in selfmod.proposals(m,source):
        pr=selfmod.compile_proposal(m,source,target,p)
        if pr:
            s=p['schema'];g1.append({'schema':s,'proof':pr,'name':'g1','activation':selfmod.activation(m,s,target),'meta':p})
    g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
    g2=generation(m,op,source,target,g1,limit=420)
    for x in g2:x['name']='g2'

    frozen=(g1[:32]+g2[:96])
    schemas=[x['schema'] for x in frozen]
    left=bounded_reach(m,target[0],schemas,depth=2,cap=1400,max_size=90)
    right=bounded_reach(m,target[1],schemas,depth=2,cap=1400,max_size=90)
    intersection=set(left).intersection(right)
    cut={'left_states':len(left),'right_states':len(right),'intersection':len(intersection),'depth':2,'cap':1400,'frozen_operators':len(frozen)}

    arm_a=run_arm(m,sym,source,target,frozen,20.0,'A_frozen_g1_g2')

    bparents=g2[:24]
    g3b=generation(m,op,source,target,bparents,limit=420)
    for x in g3b:x['name']='g3_unconstrained'
    bins=(g1[:24]+g2[:48]+g3b[:64])
    arm_b=run_arm(m,sym,source,target,bins,20.0,'B_unconstrained_g3')

    scored=[]
    for x in g2:
        sc,ex=bridge_score(m,x,left,right);x=dict(x);x['bridge_score']=sc;x['exact_bridge']=ex;scored.append(x)
    scored.sort(key=lambda x:(-x['bridge_score'],-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
    cparents=scored[:24]
    g3c=generation(m,op,source,target,cparents,limit=420)
    g3sc=[]
    for x in g3c:
        sc,ex=bridge_score(m,x,left,right);x=dict(x);x['name']='g3_conditioned';x['bridge_score']=sc;x['exact_bridge']=ex;g3sc.append(x)
    g3sc.sort(key=lambda x:(-x['bridge_score'],-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))

    g4c=[]
    if g3sc:
        g4c=generation(m,op,source,target,g3sc[:20],limit=420)
        tmp=[]
        for x in g4c:
            sc,ex=bridge_score(m,x,left,right);x=dict(x);x['name']='g4_conditioned';x['bridge_score']=sc;x['exact_bridge']=ex;tmp.append(x)
        g4c=sorted(tmp,key=lambda x:(-x['bridge_score'],-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))

    c_new=(g3sc[:44]+g4c[:44])
    nnew=min(64,len(c_new));cins=g1[:24]+g2[:48]+c_new[:nnew]
    arm_c=run_arm(m,sym,source,target,cins,20.0,'C_residual_conditioned_g3_g4')
    ablation=run_arm(m,sym,source,target,g1[:24]+g2[:48],20.0,'C_ablation_remove_induced') if arm_c['closure'] else None

    def show(xs,n=12):
        return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x.get('activation',0),'bridge_score':x.get('bridge_score'),'exact_bridge':x.get('exact_bridge',False),'name':x.get('name')} for x in xs[:n]]
    out={
      'schema':'mathgraph.residual-conditioned-operator-induction.v1',
      'id':RID,
      'protocol':{'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity':True,'all_macros_replay_to_source':True,'matched_arm_seconds':20.0},
      'source':show_eq(m,source),'target':show_eq(m,target),
      'cut':cut,
      'counts':{'g1':len(g1),'g2':len(g2),'g3_unconstrained':len(g3b),'g3_conditioned':len(g3sc),'g4_conditioned':len(g4c),'g2_exact_bridges':sum(x.get('exact_bridge',False) for x in scored),'g3_exact_bridges':sum(x.get('exact_bridge',False) for x in g3sc),'g4_exact_bridges':sum(x.get('exact_bridge',False) for x in g4c)},
      'arms':{'A':arm_a,'B':arm_b,'C':arm_c,'C_ablation':ablation},
      'top_conditioned_g2':show(scored),'top_conditioned_g3':show(g3sc),'top_conditioned_g4':show(g4c),
      'decision':('PASS' if arm_c['closure'] and not arm_a['closure'] and (not arm_b['closure']) and ablation and not ablation['closure'] else 'PARTIAL' if arm_c['closure'] else 'NO_CLOSURE')
    }
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
