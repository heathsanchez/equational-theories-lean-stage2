import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_3366_attr', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

MAX_TERM_SIZE=180
MAX_NODES=50000
FRONTIER_CAP=16
BASIS_CAP=6
ROUNDS=8


def main():
    eqs=h.load_equations(); m=h.load_solver()
    source=m.parse_equation(eqs[3366]); target=m.parse_equation(eqs[41]); tl,tr=target[:2]
    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))

    limits={'max_term_size':MAX_TERM_SIZE,'max_pool_terms':80,'max_core_terms':18,'max_source_attempts':120000,'max_source_edges':4000,'max_derivation_nodes':6000,'max_graph_edges':5000,'max_congruence_rounds':0}
    seed=m.EqualitySearch(source,target,time.monotonic()+12.0,limits)
    pool=seed.make_pool(); seed.initial_pool=tuple(pool); seed.instantiate_sources(pool)
    raw=[n for n in seed.nodes if n.kind in ('source instance','source reentry')]
    cands=[]; seen=set()
    for n in raw:
        k=(n.lhs,n.rhs,tuple(n.substitution),bool(getattr(n,'orientation',False)))
        if k not in seen: seen.add(k); cands.append(n)

    nodes=[]; depth=[]; best={}
    def add(n,d):
        if len(nodes)>=MAX_NODES:return None
        k=(n.lhs,n.rhs); old=best.get(k)
        if old is not None and depth[old]<=d:return old
        nodes.append(n);depth.append(d);i=len(nodes)-1;best[k]=i;return i
    def M(a,b):return ('op',a,b)
    def R(t):return add(m.EqualityNode(t,t,'reflexivity',constructor='round8-attribution'),0)
    def S(i,d):
        p=nodes[i];return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='round8-attribution'),d)
    def T(i,j,d):
        a,b=nodes[i],nodes[j]
        if a.rhs!=b.lhs:return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='round8-attribution'),d)
    def C(i,j,d):
        a,b=nodes[i],nodes[j]; lhs=M(a.lhs,b.lhs);rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE:return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='round8-attribution'),d)
        if i1 is None:return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='round8-attribution'),d)
        return None if i2 is None else T(i1,i2,d)

    source_cache={}
    def src(n,rev=False):
        k=(n.lhs,n.rhs,tuple(n.substitution),bool(getattr(n,'orientation',False)),rev)
        if k in source_cache:return source_cache[k]
        i=add(m.EqualityNode(n.lhs,n.rhs,'source instance',substitution=n.substitution,orientation=getattr(n,'orientation',False),constructor='round8-attribution'),0)
        if i is not None and rev:i=S(i,0)
        source_cache[k]=i;return i

    visible=set(target_terms)
    for n in cands:
        for t in tuple(m.walk_subterms(n.lhs))+tuple(m.walk_subterms(n.rhs)):
            if m.term_size(t)<=9:visible.add(t)
    reflex={t:R(t) for t in sorted(visible,key=lambda q:(m.term_size(q),m.render_term(q)))}
    compact=[i for t,i in sorted(reflex.items(),key=lambda kv:(m.term_size(kv[0]),m.render_term(kv[0]))) if m.term_size(t)<=9]

    def scorecand(n,front):
        vals=[]
        for lhs,rhs,rev in ((n.lhs,n.rhs,False),(n.rhs,n.lhs,True)):
            exact=context=0
            for i in front[:FRONTIER_CAP]:
                f=nodes[i]; exact+=int(f.rhs==lhs)+int(rhs==f.lhs)
                ft=set(m.walk_subterms(f.lhs))|set(m.walk_subterms(f.rhs));context+=int(lhs in ft)+int(rhs in ft)
            exposure=int(lhs in target_terms)+int(rhs in target_terms)
            overlap=sum(t in target_terms for t in m.walk_subterms(lhs))+sum(t in target_terms for t in m.walk_subterms(rhs))
            dist=min(m.structural_distance(lhs,tl)+m.structural_distance(rhs,tr),m.structural_distance(lhs,tr)+m.structural_distance(rhs,tl))
            vals.append(((-exact,-context,-exposure,-overlap,dist,m.term_size(lhs)+m.term_size(rhs),m.render_term(lhs),m.render_term(rhs),rev),rev))
        return min(vals)[0]
    def basis(front):
        ranked=sorted(cands,key=lambda n:scorecand(n,front))[:BASIS_CAP];out=[]
        for n in ranked:
            for rev in (False,True):
                i=src(n,rev)
                if i is not None:out.append(i)
        return list(dict.fromkeys(out))
    def fscore(i):
        n=nodes[i]; exact=int(n.lhs in (tl,tr))+int(n.rhs in (tl,tr)); overlap=sum(t in target_terms for t in m.walk_subterms(n.lhs))+sum(t in target_terms for t in m.walk_subterms(n.rhs));dist=min(m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr),m.structural_distance(n.lhs,tr)+m.structural_distance(n.rhs,tl));return(-exact,-overlap,dist,depth[i],m.term_size(n.lhs)+m.term_size(n.rhs),i)

    b=basis([]);front=[]
    for i in b:
        for j in compact[:40]:
            for k in (C(i,j,1),C(j,i,1)):
                if k is not None and depth[k]==1:front.append(k)
    front=list(dict.fromkeys(front))
    for r in range(2,ROUNDS+1):
        active=sorted(set(front),key=fscore)[:FRONTIER_CAP];b=basis(active);new=[]
        for i in active:
            for j in b:
                for k in (T(i,j,r),T(j,i,r)):
                    if k is not None and depth[k]==r:new.append(k)
        seeds=list(dict.fromkeys(new))+active
        for i in seeds[:FRONTIER_CAP]:
            for j in compact[:24]:
                for k in (C(i,j,r),C(j,i,r)):
                    if k is not None and depth[k]==r:new.append(k)
        for i in list(dict.fromkeys(new))[:FRONTIER_CAP]:
            k=S(i,r)
            if k is not None and depth[k]==r:new.append(k)
        unique=list(dict.fromkeys(new))[:FRONTIER_CAP];bylhs={};byrhs={}
        for j in list(best.values()):bylhs.setdefault(nodes[j].lhs,[]).append(j);byrhs.setdefault(nodes[j].rhs,[]).append(j)
        for i in unique:
            for j in bylhs.get(nodes[i].rhs,())[:8]:
                k=T(i,j,r)
                if k is not None and depth[k]==r:new.append(k)
            for j in byrhs.get(nodes[i].lhs,())[:8]:
                k=T(j,i,r)
                if k is not None and depth[k]==r:new.append(k)
        front=list(dict.fromkeys(new))

    active=sorted(set(front),key=fscore)[:FRONTIER_CAP]
    allids=list(dict.fromkeys(list(best.values())))
    attribution={}

    # 1-step exact transitivity against any generated/source/reflexive state.
    hit=None
    for i in active:
        for j in allids:
            a,b=nodes[i],nodes[j]
            if a.rhs==b.lhs and a.lhs==tl and b.rhs==tr:hit=(i,j)
            if b.rhs==a.lhs and b.lhs==tl and a.rhs==tr:hit=(j,i)
            if hit:break
        if hit:break
    attribution['transitivity']={'reachable':hit is not None,'witness':hit}

    # 1-step binary congruence: target must be op; find equalities matching both child changes.
    ch=None
    if tl[0]=='op' and tr[0]=='op':
        l1,l2=tl[1],tl[2];r1,r2=tr[1],tr[2]
        left=[i for i in allids if nodes[i].lhs==l1 and nodes[i].rhs==r1]
        right=[i for i in allids if nodes[i].lhs==l2 and nodes[i].rhs==r2]
        if left and right:ch=(left[0],right[0])
    attribution['binary_congruence']={'reachable':ch is not None,'witness':ch}

    # Source re-entry: any source candidate orientation exactly bridges an active endpoint to target.
    rh=None
    for i in active:
        f=nodes[i]
        for n in cands:
            for lhs,rhs,rev in ((n.lhs,n.rhs,False),(n.rhs,n.lhs,True)):
                if f.lhs==tl and f.rhs==lhs and rhs==tr:rh=(i,m.render_term(lhs),m.render_term(rhs),rev)
                if lhs==tl and rhs==f.lhs and f.rhs==tr:rh=('pre',i,m.render_term(lhs),m.render_term(rhs),rev)
                if rh:break
            if rh:break
        if rh:break
    attribution['source_reentry']={'reachable':rh is not None,'witness':rh}

    # Contextual/unification interface diagnostic: does some active endpoint match a target subterm or source side pattern at all?
    ctx=[]
    for i in active:
        n=nodes[i]
        for side_name,t in (('lhs',n.lhs),('rhs',n.rhs)):
            for target_side,tt in (('target_lhs',tl),('target_rhs',tr)):
                for sub in m.walk_subterms(tt):
                    subst={}
                    if m.match_term(t,sub,subst) or m.match_term(sub,t,{}):
                        ctx.append((i,side_name,target_side,m.render_term(sub)));break
                if ctx and ctx[-1][0]==i:break
    attribution['contextual_interface']={'present':bool(ctx),'examples':ctx[:10]}

    out={'schema':'mathgraph.3366-round8-interface-attribution.v1','edge':'3366->41','teacher_information_used':False,'frontier_cap':FRONTIER_CAP,'rounds':ROUNDS,'nodes':len(nodes),'active_round8':len(active),'target_found':(tl,tr) in best,'attribution':attribution}
    p=Path('experiments/mathgraph/results/3366-round8-interface-attribution.json');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__':main()
