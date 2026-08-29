import importlib.util
import json
import sys
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_rolecoverage', HELPER)
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
    nodes=[]; depth=[]; best={}

    def add(node,d):
        if len(nodes)>=MAX_NODES: return None
        key=(node.lhs,node.rhs); old=best.get(key)
        if old is not None and depth[old] <= d: return old
        nodes.append(node); depth.append(d); idx=len(nodes)-1; best[key]=idx; return idx
    def V(name): return ('var',name)
    def M(a,b): return ('op',a,b)
    def H(args):
        sl,sr,vs=source; mp=dict(zip(vs,args))
        return add(m.EqualityNode(m.substitute(sl,mp),m.substitute(sr,mp),'source instance',
                                  substitution=tuple((v,mp[v]) for v in vs),constructor='role-aware-coverage'),0)
    def R(t): return add(m.EqualityNode(t,t,'reflexivity',constructor='role-aware-coverage'),0)
    def S(i,d):
        p=nodes[i]; return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='role-aware-coverage'),d)
    def T(i,j,d):
        a,b=nodes[i],nodes[j]
        if a.rhs != b.lhs: return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='role-aware-coverage'),d)
    def C(i,j,d):
        a,b=nodes[i],nodes[j]
        lhs=M(a.lhs,b.lhs); rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='role-aware-coverage'),d)
        if i1 is None: return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='role-aware-coverage'),d)
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

    # Build the verified teacher route in a separate measurement-only DAG. None of these nodes
    # are injected into the search below; only their endpoint equality keys are compared.
    tn=[]
    def ta(node): tn.append(node); return len(tn)-1
    def tH(args):
        sl,sr,vs=source; mp=dict(zip(vs,args))
        return ta(m.EqualityNode(m.substitute(sl,mp),m.substitute(sr,mp),'teacher source'))
    def tR(t): return ta(m.EqualityNode(t,t,'teacher reflexivity'))
    def tS(i):
        p=tn[i]; return ta(m.EqualityNode(p.rhs,p.lhs,'teacher symmetry',parents=(i,)))
    def tT(i,j):
        a,b=tn[i],tn[j]; assert a.rhs==b.lhs
        return ta(m.EqualityNode(a.lhs,b.rhs,'teacher transitivity',parents=(i,j)))
    def tC(i,j):
        a,b=tn[i],tn[j]
        i1=ta(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'teacher congruence-left',parents=(i,)))
        i2=ta(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'teacher congruence-right',parents=(j,)))
        return tT(i1,i2)

    th4=tH((v3,v0,v0)); th5=tR(v0); th7=tH((v2,z,z))
    q0=tC(th7,th7)
    q1=tC(q0,tR(z))
    p1=tT(tH((v1,z,z)),q1)
    p2=tT(p1,tS(tH((M(v3,v3),z,z))))
    q2=tC(th4,th4)
    p3=tT(p2,q2)
    p4=tC(p3,th5)
    p5=tT(p4,tS(tH((M(v6,v6),v0,v0))))
    p6=tC(p5,th5)
    p7=tT(tH((x,v0,y)),p6)
    root=tT(p7,tS(th4))
    milestones=[('C(h7,h7)',q0),('C(C(h7,h7),R(z))',q1),('p1',p1),('p2',p2),
                ('C(h4,h4)',q2),('p3',p3),('p4',p4),('p5',p5),('p6',p6),('p7',p7),('root',root)]
    teacher_keys=[(name,(tn[i].lhs,tn[i].rhs)) for name,i in milestones]

    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    def score(i):
        n=nodes[i]
        direct=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr)
        rev=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        return (min(direct,rev),depth[i],m.term_size(n.lhs)+m.term_size(n.rhs),i)
    def coverage(round_no):
        rows=[{'name':name,'present':key in best} for name,key in teacher_keys]
        first_missing=next((row['name'] for row in rows if not row['present']),None)
        return {'round':round_no,'nodes':len(nodes),'present':sum(r['present'] for r in rows),
                'total':len(rows),'first_missing':first_missing,'rows':rows}

    # Same successful role-aware policy as v1. Seed only its generic first-level congruence.
    first_level=C(atom_ids[1],atom_ids[1],1)
    frontier=[first_level]
    snapshots=[coverage(1)]
    found=best.get((tl,tr))
    for r in range(2,ROUNDS+1):
        if found is not None: break
        new=[]; active=sorted(set(frontier),key=score)[:FRONTIER_CAP]
        compact_reflexives=[rid for t,rid in sorted(reflexive_ids.items(),key=lambda kv:(m.term_size(kv[0]),m.render_term(kv[0]))) if m.term_size(t)<=9]
        for i in active:
            for j in compact_reflexives:
                k=C(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
                if len(nodes)>=MAX_NODES: break
            if len(nodes)>=MAX_NODES: break
        if len(nodes)<MAX_NODES:
            for j in compact_reflexives:
                for i in active:
                    k=C(j,i,r)
                    if k is not None and depth[k]==r: new.append(k)
                    if len(nodes)>=MAX_NODES: break
                if len(nodes)>=MAX_NODES: break
        if len(nodes)<MAX_NODES:
            for i in list(dict.fromkeys(new))[:FRONTIER_CAP]:
                s=S(i,r)
                if s is not None and depth[s]==r: new.append(s)
            pool=list(best.values()); by_lhs={}; by_rhs={}
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
        frontier=list(dict.fromkeys(new)); found=best.get((tl,tr))
        snap=coverage(r); snap['frontier']=len(frontier); snap['found_target']=found is not None
        snapshots.append(snap)
        print(json.dumps({k:v for k,v in snap.items() if k!='rows'},sort_keys=True),flush=True)
        if not frontier or len(nodes)>=MAX_NODES: break

    final=snapshots[-1]
    out={'schema':'mathgraph.2666-role-aware-intermediate-coverage.v1','source_atoms':6,
         'source_instantiation_disabled':True,'node_count':len(nodes),'found':found is not None,
         'teacher_intermediates_present':final['present'],'teacher_intermediates_total':final['total'],
         'first_missing':final['first_missing'],'snapshots':snapshots,'replayed':False}
    if found is not None:
        try: out['replayed']=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as e: out['replay_error']=type(e).__name__+': '+str(e)
    p=Path('experiments/mathgraph/results/2666-role-aware-intermediate-coverage.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps({'found':out['found'],'replayed':out['replayed'],'nodes':out['node_count'],
          'present':out['teacher_intermediates_present'],'total':out['teacher_intermediates_total'],
          'first_missing':out['first_missing']},sort_keys=True),flush=True)

if __name__=='__main__': main()
