import importlib.util
import json
import sys
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_sixatom', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

MAX_NODES = 120000
MAX_TERM_SIZE = 180
ROUNDS = 10
BEAM = 900
C_BEAM = 220


def main():
    eqs = h.load_equations(); m = h.load_solver()
    source = m.parse_equation(eqs[2666]); target = m.parse_equation(eqs[2860])
    tl, tr = target[:2]
    nodes = []
    best = {}
    depths = []

    def add(node, depth):
        if len(nodes) >= MAX_NODES:
            return None
        key = (node.lhs, node.rhs)
        old = best.get(key)
        if old is not None and depths[old] <= depth:
            return old
        nodes.append(node); depths.append(depth); idx = len(nodes)-1; best[key] = idx
        return idx

    def V(name): return ('var', name)
    def M(a,b): return ('op', a,b)

    def H(args):
        sl,sr,vs = source; mp = dict(zip(vs,args))
        return add(m.EqualityNode(m.substitute(sl,mp),m.substitute(sr,mp),'source instance',
                                  substitution=tuple((v,mp[v]) for v in vs),constructor='six-atom-program-search'),0)
    def R(t):
        return add(m.EqualityNode(t,t,'reflexivity',constructor='six-atom-program-search'),0)
    def S(i,depth):
        p=nodes[i]
        return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='six-atom-program-search'),depth)
    def T(i,j,depth):
        a,b=nodes[i],nodes[j]
        if a.rhs != b.lhs: return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='six-atom-program-search'),depth)
    def C(i,j,depth):
        a,b=nodes[i],nodes[j]
        lhs=M(a.lhs,b.lhs); rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='six-atom-program-search'),depth)
        if i1 is None: return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='six-atom-program-search'),depth)
        if i2 is None: return None
        return T(i1,i2,depth)

    x,y,z=V('x'),V('y'),V('z')
    v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
    teacher_args=[(v3,v0,v0),(v2,z,z),(v1,z,z),(M(v3,v3),z,z),(M(v6,v6),v0,v0),(x,v0,y)]
    atom_ids=[H(a) for a in teacher_args]

    # Reflexivity is logical infrastructure, not new source knowledge. Seed it only on
    # terms already visible in the six atoms or target.
    visible=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    for i in atom_ids:
        visible.update(m.walk_subterms(nodes[i].lhs)); visible.update(m.walk_subterms(nodes[i].rhs))
    for t in sorted(visible,key=lambda q:(m.term_size(q),m.render_term(q))): R(t)

    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    def score(i):
        n=nodes[i]
        direct=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr)
        rev=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        hit=(0 if n.lhs in target_terms else 1)+(0 if n.rhs in target_terms else 1)
        return (0 if (n.lhs,n.rhs)==(tl,tr) else 1,min(direct,rev),hit,depths[i],m.term_size(n.lhs)+m.term_size(n.rhs),i)

    found=best.get((tl,tr)); rounds=[]
    for r in range(1,ROUNDS+1):
        if found is not None: break
        current=list(best.values())
        ranked=sorted(current,key=score)[:BEAM]
        # Symmetry and exact-chain transitivity preserve program structure.
        for i in ranked: S(i,r)
        ranked=sorted(list(best.values()),key=score)[:BEAM]
        by_lhs={}; by_rhs={}
        for i in ranked:
            by_lhs.setdefault(nodes[i].lhs,[]).append(i); by_rhs.setdefault(nodes[i].rhs,[]).append(i)
        for mid,lefts in list(by_rhs.items()):
            rights=by_lhs.get(mid,())
            for i in lefts[:20]:
                for j in rights[:20]: T(i,j,r)
        # Keep all six atoms permanently eligible for congruence; mix them with the
        # best currently derived programs. This avoids losing the source basis to beam ranking.
        ranked=sorted(list(best.values()),key=score)
        cset=[]; seen=set()
        for i in atom_ids + ranked[:C_BEAM]:
            if i not in seen: seen.add(i); cset.append(i)
        for i in cset:
            for j in cset:
                C(i,j,r)
                if len(nodes)>=MAX_NODES: break
            if len(nodes)>=MAX_NODES: break
        found=best.get((tl,tr))
        rounds.append({'round':r,'nodes':len(nodes),'unique_equalities':len(best),
                       'best_score':score(sorted(best.values(),key=score)[0]),'found':found is not None})
        print(json.dumps(rounds[-1],sort_keys=True),flush=True)
        if len(nodes)>=MAX_NODES: break

    out={'schema':'mathgraph.2666-six-atom-program-search.v1','source_atoms':6,
         'source_instantiation_disabled':True,'node_count':len(nodes),'unique_equalities':len(best),
         'rounds':rounds,'found':found is not None,'replayed':False}
    if found is not None:
        try: out['replayed']=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as e: out['replay_error']=type(e).__name__+': '+str(e)
        out['proof']=h.proof_summary(nodes,found)
    p=Path('experiments/mathgraph/results/2666-six-atom-program-search.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__': main()
