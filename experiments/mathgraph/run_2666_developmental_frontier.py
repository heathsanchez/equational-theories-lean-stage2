import importlib.util,json,sys
from pathlib import Path

HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_frontier',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)

MAX_TERM_SIZE=180
MAX_NODES=50000
MAX_DEPTH=12
FRONTIER_CAP=600


def main():
    eqs=h.load_equations(); m=h.load_solver()
    source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860]); tl,tr=target[:2]
    nodes=[]; best={}; depth=[]
    def add(node,d):
        if len(nodes)>=MAX_NODES: return None
        k=(node.lhs,node.rhs); old=best.get(k)
        if old is not None and depth[old]<=d: return old
        nodes.append(node); depth.append(d); i=len(nodes)-1; best[k]=i; return i
    V=lambda s:('var',s); M=lambda a,b:('op',a,b)
    def H(args):
        sl,sr,vs=source; mp=dict(zip(vs,args))
        return add(m.EqualityNode(m.substitute(sl,mp),m.substitute(sr,mp),'source instance',substitution=tuple((v,mp[v]) for v in vs),constructor='developmental-frontier'),0)
    def R(t): return add(m.EqualityNode(t,t,'reflexivity',constructor='developmental-frontier'),0)
    def S(i,d):
        p=nodes[i]; return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='developmental-frontier'),d)
    def T(i,j,d):
        a,b=nodes[i],nodes[j]
        if a.rhs!=b.lhs: return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='developmental-frontier'),d)
    def C(i,j,d):
        a,b=nodes[i],nodes[j]; lhs=M(a.lhs,b.lhs); rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='developmental-frontier'),d)
        if i1 is None:return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='developmental-frontier'),d)
        if i2 is None:return None
        return T(i1,i2,d)

    x,y,z=V('x'),V('y'),V('z'); v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
    teacher_args=[(v3,v0,v0),(v2,z,z),(v1,z,z),(M(v3,v3),z,z),(M(v6,v6),v0,v0),(x,v0,y)]
    atoms=[H(a) for a in teacher_args]
    visible=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    for i in atoms: visible|=set(m.walk_subterms(nodes[i].lhs)); visible|=set(m.walk_subterms(nodes[i].rhs))
    refs=[R(t) for t in sorted(visible,key=lambda q:(m.term_size(q),m.render_term(q)))]
    basis=[i for i in atoms+refs if i is not None]

    h7=atoms[1]
    c_h7_h7_expected=(M(nodes[h7].lhs,nodes[h7].lhs),M(nodes[h7].rhs,nodes[h7].rhs))
    first_id=C(h7,h7,1)
    if first_id is None: raise RuntimeError('failed to build first congruence')
    first=nodes[first_id]
    rz=next(i for i in refs if nodes[i].lhs==z)
    desired=(M(first.lhs,z),M(first.rhs,z))

    # Remove the explicitly-created first congruence from being a teacher injection only in spirit:
    # it is exactly the generic depth-1 transition already demonstrated by the prior run. Seed the
    # frontier with all depth-1 generic compositions instead, then require the desired depth-2 result
    # to arise from frontier reactivation.
    seed_before=len(nodes)
    frontier=set()
    for i in basis:
        q=S(i,1)
        if q is not None and q>=seed_before: frontier.add(q)
    for i in basis:
        for j in basis:
            q=C(i,j,1)
            if q is not None and q>=seed_before: frontier.add(q)
    # Exact transitivity among basis too.
    for i in basis:
        for j in basis:
            q=T(i,j,1)
            if q is not None and q>=seed_before: frontier.add(q)

    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    def score(i):
        n=nodes[i]
        direct=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr)
        rev=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        touch=(0 if n.lhs in target_terms else 1)+(0 if n.rhs in target_terms else 1)
        return (min(direct,rev),touch,m.term_size(n.lhs)+m.term_size(n.rhs),i)

    rounds=[]; found=best.get((tl,tr)); reached_desired=(desired in best)
    for d in range(2,MAX_DEPTH+1):
        if found is not None: break
        active=sorted(frontier,key=score)[:FRONTIER_CAP]
        before=len(nodes); new=set()
        # Developmental rule: every newly derived compact state is privileged for one step and
        # composed with the frozen basis and with the other active frontier states.
        partners=basis+active[:120]
        for i in active:
            for q in (S(i,d),):
                if q is not None and q>=before:new.add(q)
            for j in partners:
                for q in (C(i,j,d),C(j,i,d),T(i,j,d),T(j,i,d)):
                    if q is not None and q>=before:new.add(q)
                if len(nodes)>=MAX_NODES: break
            if len(nodes)>=MAX_NODES: break
        frontier=new
        found=best.get((tl,tr)); reached_desired=(desired in best)
        rounds.append({'depth':d,'active':len(active),'new_frontier':len(frontier),'nodes':len(nodes),'reached_first_missing':reached_desired,'found_target':found is not None})
        print(json.dumps(rounds[-1],sort_keys=True),flush=True)
        if len(nodes)>=MAX_NODES or not frontier: break

    out={'schema':'mathgraph.2666-developmental-frontier.v1','source_atoms':6,'source_instantiation_disabled':True,
         'frontier_cap':FRONTIER_CAP,'node_count':len(nodes),'rounds':rounds,'reached_first_missing':reached_desired,
         'first_missing_name':'C(C(h7,h7),R(z))','found':found is not None,'replayed':False}
    if found is not None:
        try: out['replayed']=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as e: out['replay_error']=type(e).__name__+': '+str(e)
        out['proof']=h.proof_summary(nodes,found)
    p=Path('experiments/mathgraph/results/2666-developmental-frontier.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__': main()
