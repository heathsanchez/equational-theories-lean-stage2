#!/usr/bin/env python3
import importlib.util, json, sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'experiments/mathgraph/run_obstruction_vector_q0_composition.py'

def load(p,n):
    s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def closure(rel, objs):
    R={(x,x) for x in objs}|set(rel)
    changed=True
    while changed:
        changed=False
        add={(a,d) for (a,b) in R for (c,d) in R if b==c and (a,d) not in R}
        if add:R|=add;changed=True
    return R

def quotient_preorder(objs, rel, q):
    Q=sorted(set(q[x] for x in objs), key=str)
    QR=closure({(q[a],q[b]) for (a,b) in rel},Q)
    return Q,QR

def monotone(objs, rel, q, target_rel):
    return all((q[a],q[b]) in target_rel for (a,b) in rel)

def nat_exists_poset(objs, F, G, target_rel):
    # CompleteCover_coh for thin target category: eta_x exists iff F(x)<=G(x) for every x.
    bad=[x for x in objs if (F[x],G[x]) not in target_rel]
    return len(bad)==0,bad

def main():
    ov=load(BASE,'l2_ov');m=ov.load(ov.SOLVER,'l2_m');sym=ov.load(ov.SYM,'l2_sym');selfm=ov.load(ov.SELF,'l2_self');op=ov.load(ov.OPC,'l2_op');op.selfmod=selfm
    miss=ov.load(ov.MISS,'l2_miss');reify=ov.load(ov.REIFY,'l2_reify');reify.selfm=selfm;ms=ov.load(ov.MS,'l2_ms');ms.selfmod=selfm
    j=ov.load(ov.JOIN,'l2_j');j.selfm=selfm;bridge=ov.load(ov.BRIDGE,'l2_bridge');bridge.selfm=selfm;att=ov.load(ov.ATT,'l2_att');att.selfm=selfm
    row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==ov.RID)
    source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
    *_,S2items=ov.build_atomic(m,sym,source,target,selfm,op,miss,reify,ms,j,bridge,att)
    s2,_=ov.state(m,sym,source,target,S2items,28)
    N=min(160,len(s2.nodes));objs=list(range(N))
    edges=set()
    for i,n in enumerate(s2.nodes[:N]):
        for p in n.parents:
            if 0<=p<N: edges.add((p,i))
    rel=closure(edges,objs)
    # Transforming quotient 1: identify nodes with the same proof-rule kind.
    q1={i:str(s2.nodes[i].kind) for i in objs}
    Q1,R1=quotient_preorder(objs,rel,q1)
    # Transforming quotient 2: coarsen kinds by deterministic two-way partition.
    def coarse(k): return ('K0' if sum(ord(c) for c in str(k))%2==0 else 'K1')
    q2={k:coarse(k) for k in Q1}
    Q2,R2=quotient_preorder(Q1,R1,q2)
    direct={i:coarse(q1[i]) for i in objs}
    stepwise={i:q2[q1[i]] for i in objs}
    f1=monotone(objs,rel,q1,R1);f2=monotone(Q1,R1,q2,R2);fd=monotone(objs,rel,direct,R2)
    strict_equal=all(direct[i]==stepwise[i] for i in objs)
    comp_ok,bad=nat_exists_poset(objs,stepwise,direct,R2)
    rev_ok,rbad=nat_exists_poset(objs,direct,stepwise,R2)
    out={
      'schema':'mathgraph.l2-real-bounded-category.v1','id':ov.RID,
      'boundary':{'proof_nodes_prefix':N,'source_morphisms_reachability_pairs':len(rel),'q1_objects':len(Q1),'q2_objects':len(Q2),'thin_target':True},
      'transport':{'F_delta1_functorial':f1,'F_delta2_functorial':f2,'F_composite_direct_functorial':fd},
      'compositor':{'stepwise_equals_direct_on_objects':strict_equal,'forward_natural_transformation_exists':comp_ok,'reverse_natural_transformation_exists':rev_ok,'bad_components_forward':bad[:20],'bad_components_reverse':rbad[:20]},
      'CompleteCover_coh':{'method':'thin-poset pointwise exhaustive over every bounded source object','covered_objects':N,'complete':True},
      'classification':('STRICT_COMPOSITOR_ON_BOUNDED_REAL_DAG_SLICE' if f1 and f2 and fd and strict_equal else 'L2_OBLIGATION_FAILURE_IN_BOUND'),
      'protocol':{'real_S2_proof_dag':True,'transformations_are_synthetic_quotients_over_real_data':True,'bounded_only':True,'no_global_L2_claim':True}
    }
    p=ROOT/'experiments/mathgraph/results/l2-real-bounded-category.json';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
