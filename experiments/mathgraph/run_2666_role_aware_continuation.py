import importlib.util
import json
import sys
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_roleaware', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

MAX_NODES = 50000
MAX_TERM_SIZE = 180
FRONTIER_CAP = 400
ROUNDS = 8


def main():
    eqs = h.load_equations(); m = h.load_solver()
    source = m.parse_equation(eqs[2666]); target = m.parse_equation(eqs[2860])
    tl, tr = target[:2]
    nodes = []; depth = []; best = {}

    def add(node, d):
        if len(nodes) >= MAX_NODES:
            return None
        key = (node.lhs, node.rhs)
        old = best.get(key)
        if old is not None and depth[old] <= d:
            return old
        nodes.append(node); depth.append(d); idx = len(nodes)-1; best[key] = idx
        return idx

    def V(name): return ('var', name)
    def M(a,b): return ('op', a,b)
    def H(args):
        sl,sr,vs = source; mp=dict(zip(vs,args))
        return add(m.EqualityNode(m.substitute(sl,mp),m.substitute(sr,mp),'source instance',
                                  substitution=tuple((v,mp[v]) for v in vs),constructor='role-aware'),0)
    def R(t): return add(m.EqualityNode(t,t,'reflexivity',constructor='role-aware'),0)
    def S(i,d):
        p=nodes[i]; return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='role-aware'),d)
    def T(i,j,d):
        a,b=nodes[i],nodes[j]
        if a.rhs != b.lhs: return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='role-aware'),d)
    def C(i,j,d):
        a,b=nodes[i],nodes[j]
        lhs=M(a.lhs,b.lhs); rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='role-aware'),d)
        if i1 is None: return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='role-aware'),d)
        if i2 is None: return None
        return T(i1,i2,d)

    x,y,z=V('x'),V('y'),V('z')
    v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
    teacher_args=[(v3,v0,v0),(v2,z,z),(v1,z,z),(M(v3,v3),z,z),(M(v6,v6),v0,v0),(x,v0,y)]
    atom_ids=[H(a) for a in teacher_args]

    visible=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    for i in atom_ids:
        visible.update(m.walk_subterms(nodes[i].lhs)); visible.update(m.walk_subterms(nodes[i].rhs))
    reflexive_ids={t:R(t) for t in sorted(visible,key=lambda q:(m.term_size(q),m.render_term(q)))}

    # Exact first teacher milestone only for measurement, never injected into search.
    h7 = atom_ids[1]
    first_level = C(h7,h7,1)
    first_missing_lhs = M(nodes[first_level].lhs, z)
    first_missing_rhs = M(nodes[first_level].rhs, z)
    first_missing_key = (first_missing_lhs, first_missing_rhs)

    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    def score(i):
        n=nodes[i]
        direct=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr)
        rev=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        return (min(direct,rev), depth[i], m.term_size(n.lhs)+m.term_size(n.rhs), i)

    # Developmental state is typed by the operation it is ready for next.
    # A congruence-derived equality is preferentially paired with reflexivities on
    # compact terms visible in either endpoint before any global composition.
    frontier=[first_level]
    rounds=[]; found=best.get((tl,tr))
    for r in range(2,ROUNDS+1):
        if found is not None: break
        new=[]
        active=sorted(set(frontier), key=score)[:FRONTIER_CAP]
        compact_reflexives=[rid for t,rid in sorted(reflexive_ids.items(), key=lambda kv:(m.term_size(kv[0]),m.render_term(kv[0]))) if m.term_size(t)<=9]

        # Role-aware continuation 1: derived equality as left congruence operand,
        # reflexivity as context-preserving right operand.
        for i in active:
            for j in compact_reflexives:
                k=C(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
                if len(nodes)>=MAX_NODES: break
            if len(nodes)>=MAX_NODES: break

        # Role-aware continuation 2: symmetric context position.
        if len(nodes)<MAX_NODES:
            for j in compact_reflexives:
                for i in active:
                    k=C(j,i,r)
                    if k is not None and depth[k]==r: new.append(k)
                    if len(nodes)>=MAX_NODES: break
                if len(nodes)>=MAX_NODES: break

        # Then only exact-chain transitivity/symmetry involving the new frontier.
        if len(nodes)<MAX_NODES:
            for i in list(dict.fromkeys(new))[:FRONTIER_CAP]:
                s=S(i,r)
                if s is not None and depth[s]==r: new.append(s)
            pool=list(best.values())
            by_lhs={}; by_rhs={}
            for j in pool:
                by_lhs.setdefault(nodes[j].lhs,[]).append(j); by_rhs.setdefault(nodes[j].rhs,[]).append(j)
            for i in list(dict.fromkeys(new))[:FRONTIER_CAP]:
                for j in by_lhs.get(nodes[i].rhs,())[:20]:
                    k=T(i,j,r)
                    if k is not None and depth[k]==r: new.append(k)
                for j in by_rhs.get(nodes[i].lhs,())[:20]:
                    k=T(j,i,r)
                    if k is not None and depth[k]==r: new.append(k)
                if len(nodes)>=MAX_NODES: break

        frontier=list(dict.fromkeys(new))
        found=best.get((tl,tr))
        rec={'round':r,'nodes':len(nodes),'frontier':len(frontier),
             'reached_first_missing':first_missing_key in best,'found_target':found is not None}
        rounds.append(rec); print(json.dumps(rec,sort_keys=True),flush=True)
        if first_missing_key in best and r==2:
            # Continue; the whole point is to see whether the same role-aware policy chains onward.
            pass
        if not frontier or len(nodes)>=MAX_NODES: break

    out={'schema':'mathgraph.2666-role-aware-continuation.v1','source_atoms':6,
         'source_instantiation_disabled':True,'node_count':len(nodes),'rounds':rounds,
         'reached_first_missing':first_missing_key in best,'found':found is not None,'replayed':False}
    if found is not None:
        try: out['replayed']=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as e: out['replay_error']=type(e).__name__+': '+str(e)
        out['proof']=h.proof_summary(nodes,found)
    p=Path('experiments/mathgraph/results/2666-role-aware-continuation.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__': main()
