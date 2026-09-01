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
    def skey(s,q): return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))
    def subst_x(t,repl):
        if t[0]=='var': return repl if t[1]=='x' else t
        return ('op',subst_x(t[1],repl),subst_x(t[2],repl))
    def tkey(t): return (m.term_size(t),m.render_term(t))

    t0=time.monotonic(); e,s=setup(neutral,20.0); pre=[]
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
                rec={'lhs_t':act[0],'rhs_t':act[1],'lhs':k[0],'rhs':k[1],'proof_nodes':len(pn),'nodes':pn,'root':pr}
                prev=spectrum.get(k)
                if prev is None or rec['proof_nodes']<prev['proof_nodes']: spectrum[k]=rec
            if s.expired() or census>=176: break
        if s.expired() or census>=176: break

    ordered=sorted(spectrum.values(),key=lambda r:(m.term_size(r['lhs_t'])+m.term_size(r['rhs_t']),r['proof_nodes'],r['lhs'],r['rhs']))[:32]
    x=('var','x'); xx=('op',x,x); universe={x,xx}
    def addsubs(t):
        universe.add(t)
        if t[0]=='op': addsubs(t[1]); addsubs(t[2])
    for r in ordered: addsubs(r['lhs_t']); addsubs(r['rhs_t'])
    simple=sorted(universe,key=tkey)[:24]
    for u in simple:
        for v in simple:
            z=('op',u,v)
            if m.term_size(z)<=15: universe.add(z)
    universe=set(sorted(universe,key=tkey)[:256])

    parent={t:t for t in universe}; rank={t:0 for t in universe}; adj={t:[] for t in universe}; edge_seq=0
    def ensure(t):
        if t not in parent: parent[t]=t; rank[t]=0; adj[t]=[]; universe.add(t)
        if t[0]=='op': ensure(t[1]); ensure(t[2])
    def find(t):
        p=parent[t]
        if p!=t: parent[t]=find(p)
        return parent[t]
    def link(a,b,why):
        nonlocal edge_seq
        ensure(a); ensure(b); ra,rb=find(a),find(b); edge_seq+=1; rec={'seq':edge_seq,'a':a,'b':b,'why':why}
        adj[a].append((b,rec)); adj[b].append((a,rec))
        if ra==rb: return False
        if rank[ra]<rank[rb]: ra,rb=rb,ra
        parent[rb]=ra
        if rank[ra]==rank[rb]: rank[ra]+=1
        return True

    bases=sorted(list(universe),key=tkey)[:96]; instantiated=0
    for idx,r in enumerate(ordered):
        for T in bases:
            l=subst_x(r['lhs_t'],T); rr=subst_x(r['rhs_t'],T)
            if max(m.term_size(l),m.term_size(rr))>31: continue
            link(l,rr,{'kind':'law_subst','law':idx,'subst_t':T}); instantiated+=1

    congruence_edges=0
    for _round in range(6):
        changed=False; ops=[t for t in list(universe) if t[0]=='op']; buckets={}
        for t in ops:
            sig=(find(t[1]),find(t[2]))
            if sig in buckets:
                u=buckets[sig]
                if find(t)!=find(u):
                    why={'kind':'congruence','a_left':t[1],'a_right':t[2],'b_left':u[1],'b_right':u[2]}
                    if link(t,u,why): congruence_edges+=1; changed=True
            else: buckets[sig]=t
        if not changed: break

    def bfs(a0,b0,before):
        if a0==b0: return []
        q=deque([a0]); prev={a0:None}; pedge={}
        while q:
            u=q.popleft()
            for v,er in adj.get(u,()):
                if er['seq']>=before or v in prev: continue
                prev[v]=u; pedge[v]=er
                if v==b0:
                    out=[]; cur=v
                    while prev[cur] is not None:
                        p=prev[cur]; out.append((p,cur,pedge[cur])); cur=p
                    out.reverse(); return out
                q.append(v)
        return None

    proof=[]; memo={}; compiling=set()
    def clone_term(t,T): return subst_x(t,T)
    def clone_record(obj,T,idmap=None):
        if isinstance(obj,tuple):
            if len(obj)>=1 and obj[0] in ('var','op'):
                try: return clone_term(obj,T)
                except Exception: pass
            return tuple(clone_record(z,T,idmap) for z in obj)
        if isinstance(obj,list): return [clone_record(z,T,idmap) for z in obj]
        return obj
    def clone_law(idx,T):
        key=('law',idx,T)
        if key in memo: return memo[key]
        r=ordered[idx]; nodes=r['nodes']; root=r['root']; needed=set()
        def visit(i):
            if i in needed:return
            for p in nodes[i].parents: visit(p)
            needed.add(i)
        visit(root); idmap={}
        for old in sorted(needed):
            n=nodes[old]; parents=tuple(idmap[p] for p in n.parents)
            sub=tuple((v,clone_term(t,T)) for v,t in n.substitution)
            context=None if n.context is None else (n.context[0],clone_term(n.context[1],T))
            origins=tuple((v,clone_term(t,T),tuple(idmap[p] for p in ps)) for v,t,ps in n.term_origins)
            cr=None if n.context_record is None else tuple(clone_record(z,T,idmap) for z in n.context_record)
            orc=None
            if n.overlap_record is not None:
                z=list(n.overlap_record)
                z[0]=idmap[z[0]]; z[1]=idmap[z[1]]
                for j in (5,6,7,8,9): z[j]=clone_term(z[j],T)
                orc=tuple(z)
            nn=m.EqualityNode(clone_term(n.lhs,T),clone_term(n.rhs,T),n.kind,parents=parents,substitution=sub,context=context,orientation=n.orientation,generation=n.generation,term_origins=origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=cr,overlap_record=orc)
            idmap[old]=len(proof); proof.append(nn)
        memo[key]=idmap[root]; return memo[key]
    def sym(pid):
        n=proof[pid]; proof.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(pid,))); return len(proof)-1
    def trans(p,q):
        a1=proof[p]; b1=proof[q]
        if a1.rhs!=b1.lhs: raise RuntimeError('bad transitivity')
        proof.append(m.EqualityNode(a1.lhs,b1.rhs,'transitivity',parents=(p,q))); return len(proof)-1
    def refl(t):
        proof.append(m.EqualityNode(t,t,'reflexivity')); return len(proof)-1
    def orient(pid,a0,b0):
        n=proof[pid]
        if (n.lhs,n.rhs)==(a0,b0): return pid
        if (n.lhs,n.rhs)==(b0,a0): return sym(pid)
        raise RuntimeError('edge endpoint mismatch')
    def compile_pair(a0,b0,before):
        key=('pair',a0,b0,before)
        if key in memo:return memo[key]
        if a0==b0: memo[key]=refl(a0); return memo[key]
        path=bfs(a0,b0,before)
        if path is None: raise RuntimeError('missing earlier child path')
        cur=None
        for u,v,er in path:
            pid=orient(compile_edge(er),u,v)
            cur=pid if cur is None else trans(cur,pid)
        memo[key]=cur; return cur
    def compile_edge(er):
        key=('edge',er['seq'])
        if key in memo:return memo[key]
        if key in compiling: raise RuntimeError('recursive edge')
        compiling.add(key); w=er['why']
        if w['kind']=='law_subst': pid=clone_law(w['law'],w['subst_t'])
        else:
            al,ar,bl,br=w['a_left'],w['a_right'],w['b_left'],w['b_right']
            pl=compile_pair(al,bl,er['seq']); pr=compile_pair(ar,br,er['seq'])
            if al==bl: left=refl(('op',al,ar))
            else:
                proof.append(m.EqualityNode(('op',al,ar),('op',bl,ar),'congruence on left child',parents=(pl,),context=('left',ar))); left=len(proof)-1
            if ar==br: right=refl(('op',bl,ar))
            else:
                proof.append(m.EqualityNode(('op',bl,ar),('op',bl,br),'congruence on right child',parents=(pr,),context=('right',bl))); right=len(proof)-1
            pid=right if al==bl else left if ar==br else trans(left,right)
        pid=orient(pid,er['a'],er['b']); memo[key]=pid; compiling.remove(key); return pid

    connected=find(x)==find(xx); root=None; compiled_path_len=0
    if connected:
        path=bfs(x,xx,10**18); compiled_path_len=len(path)
        cur=None
        for u,v,er in path:
            pid=orient(compile_edge(er),u,v); cur=pid if cur is None else trans(cur,pid)
        root=cur
    replay=bool(root is not None and m.replay_dag(source,proof,root,maximum_term_size=320,maximum_nodes=70000))
    certificate=None
    if replay:
        certificate=m.make_dag_certificate(target,proof,root)
    result={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(spectrum),'selected':len(ordered),'graph_nodes':len(universe),'instantiated_edges':instantiated,'congruence_edges':congruence_edges,'connected_idempotence':connected,'compiled_path_len':compiled_path_len,'compiled_nodes':len(proof),'replay':replay,'certificate_bytes':len(certificate.encode()) if certificate else None,'target_revealed_after_closure':True}
    print('SOURCE_ONLY_GRAPH_PATH_COMPILER '+json.dumps(result,sort_keys=True),flush=True)
    if certificate: print('CERTIFICATE_BEGIN\n'+certificate+'\nCERTIFICATE_END',flush=True)
    if not replay: raise SystemExit(2)

if __name__=='__main__': main()
