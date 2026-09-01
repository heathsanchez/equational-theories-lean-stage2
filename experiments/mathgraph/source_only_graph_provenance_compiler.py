#!/usr/bin/env python3
import argparse, importlib.util, json, time
from collections import deque


def load(path):
    spec = importlib.util.spec_from_file_location('mgsolver', path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', required=True)
    ap.add_argument('--row', required=True)
    ap.add_argument('--certificate-out')
    a = ap.parse_args()
    m = load(a.solver)
    row = json.load(open(a.row))
    source = m.parse_equation(row['equation1'])
    neutral = m.parse_equation('x = x')
    target = m.parse_equation('x = x * x')
    base = dict(m.COMPACT_SUPERPOSITION_PROBE)
    base.update({'maximum_term_size':75,'maximum_replay_term_size':512,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})

    def setup(goal, sec):
        lim = dict(base); lim['seconds'] = sec
        e = m.TargetGroundedRefutation(source, goal, time.monotonic() + sec, lim)
        return e, e.search

    def canon(lhs, rhs):
        names = {}
        def f(t):
            if t[0] == 'var':
                if t[1] not in names:
                    names[t[1]] = chr(ord('x') + len(names))
                return ('var', names[t[1]])
            return ('op', f(t[1]), f(t[2]))
        return f(lhs), f(rhs), tuple(dict.fromkeys(names.values())), dict(names)

    def skey(s, q):
        return (m.term_size(q.lhs)+m.term_size(q.rhs), str(s.alpha_signature(q.lhs,q.rhs)), m.render_term(q.lhs), m.render_term(q.rhs))

    def subst_var(t, var, repl):
        if t[0] == 'var':
            return repl if t[1] == var else t
        return ('op', subst_var(t[1],var,repl), subst_var(t[2],var,repl))

    def tkey(t):
        return (m.term_size(t), m.render_term(t))

    # Target-blind three-generation source development, matching the positive graph probe.
    t0 = time.monotonic(); e,s = setup(neutral,20.0); pre=[]
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append(c); proposed += 1
                    if proposed >= 512: stop=True; break
        props.sort(key=lambda q:skey(s,q)); added=0
        for q in props:
            if s.add_clause(q): s.superpositions += 1; added += 1
            if added >= 64: break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    # Preserve the actual replayable DAG for every projected unary interface.
    seen=set(); spectrum={}; census=replayed=projected=0; rules=s.rules(); s.deadline=time.monotonic()+12.0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=176: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census += 1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=512,maximum_nodes=70000): continue
                replayed += 1
                raw=canon(c.lhs,c.rhs)
                pe,ps=setup(raw,2.0); pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=512,maximum_nodes=70000): continue
                projected += 1
                ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                if act[2] != ('x',): continue
                epvars=sorted(m.term_variables(ep[0])|m.term_variables(ep[1]))
                if len(epvars)!=1: continue
                k=(m.render_term(act[0]),m.render_term(act[1]))
                rec={'lhs_t':act[0],'rhs_t':act[1],'lhs':k[0],'rhs':k[1],
                     'proof_nodes':len(pn),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs),
                     'pn':pn,'pr':pr,'proof_var':epvars[0]}
                prev=spectrum.get(k)
                if prev is None or rec['proof_nodes'] < prev['proof_nodes']: spectrum[k]=rec
            if s.expired() or census>=176: break
        if s.expired() or census>=176: break

    ordered=sorted(spectrum.values(), key=lambda r:(m.term_size(r['lhs_t'])+m.term_size(r['rhs_t']),r['proof_nodes'],r['lhs'],r['rhs']))[:32]
    x=('var','x'); xx=('op',x,x)
    universe={x,xx}
    for r in ordered:
        def addsubs(t):
            universe.add(t)
            if t[0]=='op': addsubs(t[1]); addsubs(t[2])
        addsubs(r['lhs_t']); addsubs(r['rhs_t'])
    simple=sorted(universe,key=tkey)[:24]
    for u in simple:
        for v in simple:
            z=('op',u,v)
            if m.term_size(z)<=15: universe.add(z)
    universe=set(sorted(universe,key=tkey)[:256])

    # Global proof DAG and explicit equality graph. Every graph edge carries a replayable root.
    nodes=[]; adj={t:[] for t in universe}; parent={t:t for t in universe}; rank={t:0 for t in universe}
    proof_cache={}

    def ensure(t):
        if t not in parent:
            parent[t]=t; rank[t]=0; adj[t]=[]; universe.add(t)
        if t[0]=='op': ensure(t[1]); ensure(t[2])

    def find(t):
        p=parent[t]
        if p!=t: parent[t]=find(p)
        return parent[t]

    def union(a,b):
        ra,rb=find(a),find(b)
        if ra==rb: return False
        if rank[ra]<rank[rb]: ra,rb=rb,ra
        parent[rb]=ra
        if rank[ra]==rank[rb]: rank[ra]+=1
        return True

    def add_edge(a,b,root,why):
        ensure(a); ensure(b)
        adj[a].append((b,root,False,why)); adj[b].append((a,root,True,why))
        union(a,b)

    def clone_instantiated(rec, T):
        src=rec['pn']; root=rec['pr']; var=rec['proof_var']
        needed=set()
        def visit(i):
            if i in needed: return
            for p in src[i].parents: visit(p)
            needed.add(i)
        visit(root)
        idmap={}
        def mt(t): return subst_var(t,var,T)
        for old in sorted(needed):
            n=src[old]
            parents_new=tuple(idmap[p] for p in n.parents)
            substitution=tuple((v,mt(t)) for v,t in n.substitution)
            context=None if n.context is None else (n.context[0],mt(n.context[1]))
            term_origins=tuple((v,mt(t),tuple(idmap[p] for p in ps if p in idmap)) for v,t,ps in n.term_origins)
            context_record=None
            if n.context_record is not None:
                rt,path,orig,repl,res=n.context_record
                context_record=(mt(rt),path,mt(orig),mt(repl),mt(res))
            overlap_record=None
            if n.overlap_record is not None:
                q=list(n.overlap_record)
                q[0]=idmap[q[0]]; q[1]=idmap[q[1]]
                for j in range(5,10): q[j]=mt(q[j])
                overlap_record=tuple(q)
            nn=m.EqualityNode(mt(n.lhs),mt(n.rhs),n.kind,parents=parents_new,substitution=substitution,
                              context=context,orientation=n.orientation,generation=n.generation,
                              term_origins=term_origins,constructor=n.constructor,
                              derivation_depth=n.derivation_depth,context_record=context_record,
                              overlap_record=overlap_record)
            idmap[old]=len(nodes); nodes.append(nn)
        rr=idmap[root]
        if not m.replay_dag(source,nodes,rr,maximum_term_size=512,maximum_nodes=70000):
            raise RuntimeError('instantiated law DAG failed replay')
        return rr

    def refl(t):
        k=('refl',t)
        if k in proof_cache: return proof_cache[k]
        i=len(nodes); nodes.append(m.EqualityNode(t,t,'reflexivity')); proof_cache[k]=i; return i

    def sym(i):
        n=nodes[i]; k=('sym',i)
        if k in proof_cache: return proof_cache[k]
        j=len(nodes); nodes.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(i,))); proof_cache[k]=j; return j

    def trans(i,j):
        a,b=nodes[i],nodes[j]
        if a.rhs!=b.lhs: raise RuntimeError('bad transitivity join')
        k=('trans',i,j)
        if k in proof_cache: return proof_cache[k]
        z=len(nodes); nodes.append(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j))); proof_cache[k]=z; return z

    def between(a,b):
        if a==b: return refl(a)
        k=('between',a,b)
        if k in proof_cache: return proof_cache[k]
        q=deque([a]); prev={a:None}; pe={}
        while q:
            u=q.popleft()
            if u==b: break
            for v,root,rev,why in adj.get(u,()):
                if v not in prev:
                    prev[v]=u; pe[v]=(root,rev); q.append(v)
        if b not in prev: return None
        edges=[]; cur=b
        while prev[cur] is not None:
            root,rev=pe[cur]; edges.append(sym(root) if rev else root); cur=prev[cur]
        edges.reverse(); root=edges[0]
        for e2 in edges[1:]: root=trans(root,e2)
        proof_cache[k]=root
        return root

    instantiated=0
    bases=sorted(list(universe),key=tkey)[:96]
    for idx,r in enumerate(ordered):
        for T in bases:
            l=subst_var(r['lhs_t'],'x',T); rr=subst_var(r['rhs_t'],'x',T)
            if max(m.term_size(l),m.term_size(rr))>31: continue
            ensure(l); ensure(rr)
            proot=clone_instantiated(r,T)
            if (nodes[proot].lhs,nodes[proot].rhs)!=(l,rr):
                # Projection can reverse the canonical orientation; normalize explicitly.
                if (nodes[proot].lhs,nodes[proot].rhs)==(rr,l): proot=sym(proot)
                else: raise RuntimeError('instantiated endpoint mismatch')
            add_edge(l,rr,proot,{'kind':'law_subst','law':idx,'subst':m.render_term(T)})
            instantiated += 1

    congruence_edges=0
    for _round in range(6):
        changed=False; ops=[t for t in list(universe) if t[0]=='op']; buckets={}
        for t in ops:
            sig=(find(t[1]),find(t[2]))
            if sig not in buckets:
                buckets[sig]=t; continue
            u=buckets[sig]
            if find(t)==find(u): continue
            pl=between(t[1],u[1]); pr=between(t[2],u[2])
            if pl is None or pr is None: raise RuntimeError('missing child proof')
            # t=(tl,tr) -> (ul,tr) -> u=(ul,ur)
            nl=nodes[pl]
            lroot=len(nodes); nodes.append(m.EqualityNode(('op',nl.lhs,t[2]),('op',nl.rhs,t[2]),'congruence on left child',parents=(pl,),context=('left',t[2])))
            nr=nodes[pr]
            rroot=len(nodes); nodes.append(m.EqualityNode(('op',u[1],nr.lhs),('op',u[1],nr.rhs),'congruence on right child',parents=(pr,),context=('right',u[1])))
            if nodes[lroot].rhs != nodes[rroot].lhs:
                raise RuntimeError('congruence bridge mismatch')
            root=trans(lroot,rroot)
            if (nodes[root].lhs,nodes[root].rhs)!=(t,u): raise RuntimeError('congruence endpoint mismatch')
            add_edge(t,u,root,{'kind':'congruence'})
            congruence_edges += 1; changed=True
        if not changed: break

    connected=find(x)==find(xx)
    root=between(x,xx) if connected else None
    replay=bool(root is not None and m.replay_dag(source,nodes,root,maximum_term_size=512,maximum_nodes=70000))
    cert=None; cert_nodes=None
    if replay:
        cert,cert_nodes=m.make_dag_certificate(target,nodes,root)
        if a.certificate_out: open(a.certificate_out,'w').write(cert)

    result={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,
            'replayed':replayed,'projected':projected,'interfaces':len(spectrum),'selected':len(ordered),
            'graph_nodes':len(universe),'instantiated_edges':instantiated,'congruence_edges':congruence_edges,
            'target_revealed_after_closure':True,'connected_idempotence':connected,'compiled_replay':replay,
            'compiled_dag_nodes':len(nodes),'certificate_nodes':cert_nodes,'certificate_bytes':None if cert is None else len(cert.encode())}
    print('SOURCE_ONLY_GRAPH_PROVENANCE_COMPILER '+json.dumps(result,sort_keys=True),flush=True)
    if not replay: raise SystemExit(2)

if __name__=='__main__': main()
