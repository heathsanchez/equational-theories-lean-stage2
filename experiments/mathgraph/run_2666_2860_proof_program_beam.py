import importlib.util
import json
import sys
from pathlib import Path
from itertools import product

HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_progbeam',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)

MAX_NODES=80000
BEAM=180
C_BEAM=70
TERM_BEAM=24
ROUNDS=8
MAX_TERM_SIZE=45


def main():
    eqs=h.load_equations(); m=h.load_solver()
    source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860])
    nodes=[]; best={}; candidates=[]; term_origins={}

    def add(node,depth,tag):
        if len(nodes)>=MAX_NODES: return None
        key=(node.lhs,node.rhs)
        old=best.get(key)
        if old is not None and old[0]<=depth: return old[1]
        nodes.append(node); i=len(nodes)-1; best[key]=(depth,i); candidates.append((depth,i,tag))
        for t in m.walk_subterms(node.lhs): term_origins.setdefault(t,set()).add(i)
        for t in m.walk_subterms(node.rhs): term_origins.setdefault(t,set()).add(i)
        return i

    def H(args,depth,tag):
        sl,sr,vs=source; mp=dict(zip(vs,args)); lhs=m.substitute(sl,mp); rhs=m.substitute(sr,mp)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        return add(m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,mp[v]) for v in vs),constructor='proof-program-beam'),depth,tag)

    def R(t,depth):
        return add(m.EqualityNode(t,t,'reflexivity',constructor='proof-program-beam'),depth,'R')

    def S(i,depth):
        p=nodes[i]; return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='proof-program-beam'),depth,'S')

    def T(i,j,depth):
        a,b=nodes[i],nodes[j]
        if a.rhs!=b.lhs: return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='proof-program-beam'),depth,'T')

    def C(i,j,depth):
        a,b=nodes[i],nodes[j]
        lhs=('op',a.lhs,b.lhs); rhs=('op',a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        n1=m.EqualityNode(('op',a.lhs,b.lhs),('op',a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='proof-program-beam')
        i1=add(n1,depth,'C-left')
        if i1 is None:return None
        n2=m.EqualityNode(('op',a.rhs,b.lhs),('op',a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='proof-program-beam')
        i2=add(n2,depth,'C-right')
        if i2 is None:return None
        return T(i1,i2,depth)

    tl,tr=target[:2]
    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))

    def score(i):
        n=nodes[i]
        direct=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr)
        sym=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        hit=(0 if n.lhs in target_terms else 1)+(0 if n.rhs in target_terms else 1)
        return (0 if (n.lhs,n.rhs)==(tl,tr) else 1,min(direct,sym),hit,m.term_size(n.lhs)+m.term_size(n.rhs),i)

    # Initial term vocabulary is target-centric; this includes v0..v3 from the known
    # route but does not include teacher-only composites such as v3◇v3 or v6◇v6.
    terms=set(target_terms)
    for v in target[2]: terms.add(('var',v))
    term_list=sorted(terms,key=lambda t:(m.term_size(t),m.render_term(t)))
    for t in term_list: R(t,0)

    # Target-side matching seeds source instances without using the teacher proof.
    sv=source[2]
    seed_fill=term_list[:14]
    for pattern in source[:2]:
        for concrete in term_list:
            partial={}
            if not m.match_term(pattern,concrete,partial): continue
            missing=[v for v in sv if v not in partial]
            for fill in product(seed_fill,repeat=len(missing)):
                mp=dict(partial); mp.update(zip(missing,fill)); H(tuple(mp[v] for v in sv),0,'H-seed')
                if len(nodes)>=12000: break
            if len(nodes)>=12000: break
        if len(nodes)>=12000: break

    found=None; rounds=[]
    for r in range(1,ROUNDS+1):
        ranked=sorted({i for _,i,_ in candidates},key=score)[:BEAM]
        for i in list(ranked): S(i,r)
        # Exact composition first.
        by_lhs={}; by_rhs={}
        for i in ranked:
            by_lhs.setdefault(nodes[i].lhs,[]).append(i); by_rhs.setdefault(nodes[i].rhs,[]).append(i)
        for mid,lefts in by_rhs.items():
            for i in lefts[:12]:
                for j in by_lhs.get(mid,[])[:12]: T(i,j,r)
        # Binary congruence only among the best compact proof programs.
        cranked=sorted(ranked,key=score)[:C_BEAM]
        for i in cranked:
            for j in cranked: C(i,j,r)
            if len(nodes)>=MAX_NODES: break
        # Successful programs create the next argument vocabulary. Reinstantiate source
        # from the best program-local terms rather than saturating every equality edge.
        ranked2=sorted({i for _,i,_ in candidates},key=score)[:BEAM]
        dynamic=[]
        seen=set()
        for i in ranked2:
            for side in (nodes[i].lhs,nodes[i].rhs):
                for t in m.walk_subterms(side):
                    if t not in seen and m.term_size(t)<=25:
                        seen.add(t); dynamic.append(t)
        dynamic=sorted(dynamic,key=lambda t:(min(m.structural_distance(t,tl),m.structural_distance(t,tr)),m.term_size(t),m.render_term(t)))[:TERM_BEAM]
        for pattern in source[:2]:
            for concrete in dynamic:
                partial={}
                if not m.match_term(pattern,concrete,partial): continue
                missing=[v for v in sv if v not in partial]
                for fill in product(dynamic[:12],repeat=len(missing)):
                    mp=dict(partial); mp.update(zip(missing,fill)); H(tuple(mp[v] for v in sv),r,'H-reentry')
                    if len(nodes)>=MAX_NODES: break
                if len(nodes)>=MAX_NODES: break
            if len(nodes)>=MAX_NODES: break
        root_entry=best.get((tl,tr))
        rounds.append({'round':r,'nodes':len(nodes),'candidate_equalities':len(best),'dynamic_terms':len(dynamic),'best_score':score(sorted({i for _,i,_ in candidates},key=score)[0])})
        print(json.dumps(rounds[-1],sort_keys=True),flush=True)
        if root_entry is not None:
            found=root_entry[1]; break
        if len(nodes)>=MAX_NODES: break

    result={'schema':'mathgraph.2666-2860-proof-program-beam.v1','found':found is not None,'node_count':len(nodes),'unique_equalities':len(best),'rounds':rounds}
    if found is not None:
        try: replay=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as e: replay=False; result['replay_error']=type(e).__name__+': '+str(e)
        result['replayed']=replay
        result['proof']=h.proof_summary(nodes,found)
    else: result['replayed']=False
    p=Path('experiments/mathgraph/results/2666-2860-proof-program-beam.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps(result,sort_keys=True),flush=True)

if __name__=='__main__': main()
