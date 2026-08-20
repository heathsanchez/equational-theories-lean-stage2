#!/usr/bin/env python3
"""Residual -> constructor experiment for evaluation_order5_0014.

Previous gates established that the bounded frontier lacks two target subterms,
and that G1-G4 plus 1,600 raw two-parent binary-congruence macros produce zero
instances of either missing structure.  This gate tests the next inferred
invariant: existing macro composition combines *uninstantiated* derived laws;
it does not jointly solve substitutions that align two independent parent laws
with the two children demanded by a residual term.

New constructor type: residual-unified binary congruence.
  1. take a missing residual term M = op(L,R),
  2. independently match a verified parent-law side against L and another
     verified parent-law side against R,
  3. instantiate the two replay proofs under those substitutions,
  4. combine the instantiated equalities by ordinary congruence/transitivity,
  5. replay the whole DAG to the original source law.

No external proof trace, answer label, target-specific identity, or trusted rule
is added.  The residual supplies only the structurally absent term; the
constructor is generic joint matching + congruence.
"""
import importlib.util, json, sys, time
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
BIN=ROOT/'experiments/mathgraph/run_invariant_breaking_binary_congruence_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-unified-congruence-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def psubst(m,t,mp):
    if t[0]=='var': return mp.get(t[1],t)
    return ('op',psubst(m,t[1],mp),psubst(m,t[2],mp))

def transformed_proof(m,item,mp,tag):
    src,root=item['proof']; out=[]
    for n in src:
        ctx=n.context
        if ctx is not None:
            side,sib=ctx; ctx=(side,psubst(m,sib,mp))
        cr=n.context_record
        if cr is not None:
            rt,path,orig,repl,res=cr
            cr=(psubst(m,rt,mp),path,psubst(m,orig,mp),psubst(m,repl,mp),psubst(m,res,mp))
        ov=n.overlap_record
        if ov is not None:
            oi,ii,os,iside,path,ot,bef,aft,chg,other,score=ov
            ov=(oi,ii,os,iside,path,psubst(m,ot,mp),psubst(m,bef,mp),psubst(m,aft,mp),psubst(m,chg,mp),psubst(m,other,mp),score)
        origins=tuple((v,psubst(m,t,mp),pids) for v,t,pids in n.term_origins)
        out.append(m.EqualityNode(
            psubst(m,n.lhs,mp),psubst(m,n.rhs,mp),n.kind,parents=n.parents,
            substitution=tuple((v,psubst(m,t,mp)) for v,t in n.substitution),
            context=ctx,orientation=n.orientation,generation=n.generation,
            term_origins=origins,constructor=n.constructor or tag,
            derivation_depth=n.derivation_depth,context_record=cr,overlap_record=ov))
    return out,root

def complete_matches(m,item,desired,fill_terms,max_fill=12):
    ans=[]; lhs,rhs,_=item['schema']
    for sideidx,pat in enumerate((lhs,rhs)):
        sub={}
        if not m.match_term(pat,desired,sub): continue
        vars_=sorted(m.term_variables(lhs)|m.term_variables(rhs))
        miss=[v for v in vars_ if v not in sub]
        if len(miss)>2: continue
        fills=fill_terms[:max_fill]
        for vals in product(fills,repeat=len(miss)):
            mp=dict(sub); mp.update(zip(miss,vals)); ans.append((sideidx,mp))
            if len(ans)>=40:return ans
    return ans

def orient_to_desired(m,item,desired,sideidx,mp,tag):
    nodes,root=transformed_proof(m,item,mp,tag)
    if not m.replay_dag(source_global,nodes,root,maximum_term_size=220,maximum_nodes=24000): return None
    q=nodes[root]
    if sideidx==0:
        if q.lhs!=desired:return None
        return nodes,root,q.rhs
    if q.rhs!=desired:return None
    nodes.append(m.EqualityNode(q.rhs,q.lhs,'symmetry',parents=(root,),constructor=tag+'-sym'))
    return nodes,len(nodes)-1,q.lhs

def append_nodes(m,dst,src):
    off=len(dst)
    for n in src:
        dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=tuple((v,t,tuple(off+p for p in pids)) for v,t,pids in n.term_origins),constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=(None if n.overlap_record is None else (off+n.overlap_record[0],off+n.overlap_record[1],*n.overlap_record[2:]))))
    return off

def canon_pair(m,a,b):
    n={};x=(m.alpha_canonical_term(a,n),m.alpha_canonical_term(b,n));n={};y=(m.alpha_canonical_term(b,n),m.alpha_canonical_term(a,n));return min(x,y)

def residual_unified_family(m,target,library,missing,limit=1200):
    raw={}; fill=[]
    for t in list(missing)+list(target[:2]):
        for u in m.walk_subterms(t):
            if u not in fill:fill.append(u)
    fill.sort(key=lambda t:(m.term_size(t),m.render_term(t)))
    for residual in sorted(missing,key=lambda t:(-m.term_size(t),m.render_term(t))):
        if residual[0]!='op':continue
        L,R=residual[1],residual[2]
        left=[];right=[]
        for i,item in enumerate(library):
            for side,mp in complete_matches(m,item,L,fill):
                q=orient_to_desired(m,item,L,side,mp,'residual-left')
                if q:left.append((i,q,mp))
                if len(left)>=80:break
            if len(left)>=80:break
        for j,item in enumerate(library):
            for side,mp in complete_matches(m,item,R,fill):
                q=orient_to_desired(m,item,R,side,mp,'residual-right')
                if q:right.append((j,q,mp))
                if len(right)>=80:break
            if len(right)>=80:break
        for i,(li,(ln,lr,lother),lmp) in enumerate(left):
            for rj,(ri,(rn,rr,rother),rmp) in enumerate(right):
                nodes=[]; lo=append_nodes(m,nodes,ln); ro=append_nodes(m,nodes,rn)
                lr2=lo+lr; rr2=ro+rr
                start=('op',L,R); mid=('op',lother,R); end=('op',lother,rother)
                nodes.append(m.EqualityNode(start,mid,'congruence on left child',parents=(lr2,),context=('left',R),constructor='residual-unified-congruence')); a=len(nodes)-1
                nodes.append(m.EqualityNode(mid,end,'congruence on right child',parents=(rr2,),context=('right',lother),constructor='residual-unified-congruence')); b=len(nodes)-1
                nodes.append(m.EqualityNode(start,end,'transitivity',parents=(a,b),constructor='residual-unified-congruence')); root=len(nodes)-1
                if max(m.term_size(start),m.term_size(end))>180:continue
                if not m.replay_dag(source_global,nodes,root,maximum_term_size=220,maximum_nodes=30000):continue
                key=canon_pair(m,start,end)
                if key in raw:continue
                activation=selfmod.activation(m,(start,end,tuple(sorted(m.term_variables(start)|m.term_variables(end)))),target)
                raw[key]={'schema':(start,end,tuple(sorted(m.term_variables(start)|m.term_variables(end)))),'proof':(nodes,root),'name':'residual-unified','residual':m.render_term(residual),'parents':(li,ri),'activation':activation,'size':m.term_size(end)}
                if len(raw)>=limit:break
            if len(raw)>=limit:break
        if len(raw)>=limit:break
    out=list(raw.values());out.sort(key=lambda z:(-z['activation'],z['size'],z['residual']))
    return out

def main():
    global selfmod,source_global
    m=load(SOLVER,'mg_ru');sym=load(SYM,'sym_ru');selfmod=load(SELF,'self_ru');op=load(OPC,'op_ru');op.selfmod=selfmod;missmod=load(MISS,'miss_ru');binmod=load(BIN,'bin_ru');binmod.selfmod=selfmod
    row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);source_global=source
    g1=[]
    for p in selfmod.proposals(m,source):
        pr=selfmod.compile_proposal(m,source,target,p)
        if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfmod.activation(m,p['schema'],target)})
    g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
    g2=op.build_gen2(m,source,target,g1,limit=520)
    for x in g2:x['name']='g2'
    g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
    base=g1[:32]+g2[:128]
    diag,_,fterms=missmod.frontier(m,sym,source,target,base,10.0);missing=missmod.target_missing(m,target,fterms)
    binary=binmod.binary_family(m,source,target,g1[:24]+g2[:48],missing,limit=1200)
    ru=residual_unified_family(m,target,g1[:23]+g2[:120],missing,limit=1200)
    A=missmod.run_arm(m,sym,source,target,base,20.0,'A_frozen')
    B=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+binary[:96],30.0,'B_raw_binary')
    C=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56]+ru[:96],30.0,'C_residual_unified')
    Abl=missmod.run_arm(m,sym,source,target,g1[:24]+g2[:56],30.0,'C_ablation') if C['closure'] else None
    out={'schema':'mathgraph.residual-unified-congruence.v1','id':RID,'source':row['equation1'],'target':row['equation2'],'inferred_invariant':'existing derived-operator composition does not jointly instantiate independent verified laws to the child obligations of an absent residual term','constructor':'independent residual-side matching + proof substitution + binary congruence','missing_target_subterms':[m.render_term(t) for t in missing],'counts':{'g1':len(g1),'g2':len(g2),'raw_binary_verified':len(binary),'raw_binary_hits':sum(any(m.is_subterm(t,x['schema'][0]) or m.is_subterm(t,x['schema'][1]) for t in missing) for x in binary),'residual_unified_verified':len(ru),'residual_unified_hits':sum(any(m.is_subterm(t,x['schema'][0]) or m.is_subterm(t,x['schema'][1]) for t in missing) for x in ru)},'arms':{'A':A,'B':B,'C':C,'C_ablation':Abl},'top_residual_unified':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'residual':x['residual'],'parents':x['parents'],'activation':x['activation'],'size':x['size']} for x in ru[:20]],'protocol':{'no_external_proof_trace':True,'no_answer_label_in_generator':True,'no_target_specific_identity':True,'all_candidates_replay_to_source':True,'residual_used_only_as_structural_obligation':True},'decision':'PASS' if C['closure'] and not A['closure'] and not B['closure'] and Abl and not Abl['closure'] else ('PARTIAL_CONSTRAINT_ESCAPE' if ru else 'NO_CONSTRUCTOR')}
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
