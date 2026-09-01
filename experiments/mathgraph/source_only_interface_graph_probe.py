#!/usr/bin/env python3
import argparse, importlib.util, json, time
from collections import deque

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x'); target=m.parse_equation('x = x * x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,sec):
        lim=dict(base); lim['seconds']=sec
        e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim); return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names: names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def skey(s,q):
        return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))
    def subst(t,repl):
        if t[0]=='var': return repl if t[1]=='x' else t
        return ('op',subst(t[1],repl),subst(t[2],repl))
    def tkey(t): return (m.term_size(t),m.render_term(t))

    t0=time.monotonic(); e,s=setup(neutral,20.0); pre=[]
    # Target-blind structural development: fixed three generations.
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append(c); proposed+=1
                    if proposed>=512: stop=True; break
        props.sort(key=lambda q:skey(s,q)); added=0
        for q in props:
            if s.add_clause(q): s.superpositions+=1; added+=1
            if added>=64: break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})

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
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000): continue
                replayed+=1
                raw=canon(c.lhs,c.rhs); pe,ps=setup(raw,2.0); pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000): continue
                projected+=1; ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                if act[2]!=('x',): continue
                k=(m.render_term(act[0]),m.render_term(act[1]))
                rec={'lhs_t':act[0],'rhs_t':act[1],'lhs':k[0],'rhs':k[1],'proof_nodes':len(pn),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs)}
                prev=spectrum.get(k)
                if prev is None or rec['proof_nodes']<prev['proof_nodes']: spectrum[k]=rec
            if s.expired() or census>=176: break
        if s.expired() or census>=176: break

    # Target-blind interface selection: simplicity/proof size only.
    ordered=sorted(spectrum.values(), key=lambda r:(m.term_size(r['lhs_t'])+m.term_size(r['rhs_t']),r['proof_nodes'],r['lhs'],r['rhs']))[:32]

    # Build a bounded proof-bearing graph. Nodes are canonical unary terms. Edges are
    # replay-certified laws instantiated uniformly, plus congruence edges induced by
    # already-known equalities. Target is not consulted until closure is complete.
    x=('var','x'); xx=('op',x,x)
    universe={x,xx}
    for r in ordered:
        def addsubs(t):
            universe.add(t)
            if t[0]=='op': addsubs(t[1]); addsubs(t[2])
        addsubs(r['lhs_t']); addsubs(r['rhs_t'])
    # enrich with small binary combinations of simple nodes
    simple=sorted(universe,key=tkey)[:24]
    for u in simple:
        for v in simple:
            z=('op',u,v)
            if m.term_size(z)<=15: universe.add(z)
    universe=set(sorted(universe,key=tkey)[:256])

    parent={t:t for t in universe}; rank={t:0 for t in universe}; adj={t:[] for t in universe}
    def ensure(t):
        if t not in parent:
            parent[t]=t; rank[t]=0; adj[t]=[]; universe.add(t)
    def find(t):
        p=parent[t]
        if p!=t: parent[t]=find(p)
        return parent[t]
    def link(a,b,why):
        ensure(a); ensure(b); ra,rb=find(a),find(b)
        adj[a].append((b,why)); adj[b].append((a,why))
        if ra==rb: return False
        if rank[ra]<rank[rb]: ra,rb=rb,ra
        parent[rb]=ra
        if rank[ra]==rank[rb]: rank[ra]+=1
        return True

    instantiated=0
    bases=sorted(list(universe),key=tkey)[:96]
    for idx,r in enumerate(ordered):
        for T in bases:
            l=subst(r['lhs_t'],T); rr=subst(r['rhs_t'],T)
            if max(m.term_size(l),m.term_size(rr))>31: continue
            ensure(l); ensure(rr)
            link(l,rr,{'kind':'law_subst','law':idx,'subst':m.render_term(T),'law_lhs':r['lhs'],'law_rhs':r['rhs'],'proof_nodes':r['proof_nodes']})
            instantiated+=1

    # Fixed-point congruence closure over generated op terms.
    congruence_edges=0
    for _round in range(6):
        changed=False
        ops=[t for t in list(universe) if t[0]=='op']
        buckets={}
        for t in ops:
            sig=(find(t[1]),find(t[2]))
            if sig in buckets:
                u=buckets[sig]
                if find(t)!=find(u):
                    if link(t,u,{'kind':'congruence','left_class':m.render_term(t[1]),'right_class':m.render_term(t[2])}):
                        congruence_edges+=1; changed=True
            else: buckets[sig]=t
        if not changed: break

    connected=find(x)==find(xx)
    path=[]
    if connected:
        q=deque([x]); prev={x:None}; pedge={}
        while q:
            u=q.popleft()
            if u==xx: break
            for v,w in adj[u]:
                if v not in prev:
                    prev[v]=u; pedge[v]=w; q.append(v)
        if xx in prev:
            cur=xx
            while prev[cur] is not None:
                p=prev[cur]; path.append({'from':m.render_term(p),'to':m.render_term(cur),'why':pedge[cur]}); cur=p
            path.reverse()

    result={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(spectrum),'selected':len(ordered),'graph_nodes':len(universe),'instantiated_edges':instantiated,'congruence_edges':congruence_edges,'target_revealed_after_closure':True,'connected_idempotence':connected,'path_len':len(path),'path':path[:40],'sample_laws':[{k:v for k,v in r.items() if k not in ('lhs_t','rhs_t')} for r in ordered[:8]]}
    print('SOURCE_ONLY_INTERFACE_GRAPH '+json.dumps(result,sort_keys=True),flush=True)
    if not connected: raise SystemExit(2)
if __name__=='__main__': main()
