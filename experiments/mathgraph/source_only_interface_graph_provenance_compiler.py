#!/usr/bin/env python3
import argparse, importlib.util, json, time
from collections import deque


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x'); target=m.parse_equation('x = x * x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':400,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':90000})
    def setup(goal,sec):
        lim=dict(base); lim['seconds']=sec; e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim); return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names: names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def subst_x(t,repl):
        if t[0]=='var': return repl if t[1]=='x' else t
        return ('op',subst_x(t[1],repl),subst_x(t[2],repl))
    def subst_named(t,name,repl):
        if t[0]=='var': return repl if t[1]==name else t
        return ('op',subst_named(t[1],name,repl),subst_named(t[2],name,repl))
    def skey(s,q): return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))
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
                if not m.replay_dag(source,ns,r,maximum_term_size=400,maximum_nodes=90000): continue
                replayed+=1
                raw=canon(c.lhs,c.rhs); pe,ps=setup(raw,2.0); pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=400,maximum_nodes=90000): continue
                projected+=1; ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                if act[2]!=('x',): continue
                epvars=sorted(m.term_variables(ep[0])|m.term_variables(ep[1]))
                if len(epvars)!=1: continue
                k=(m.render_term(act[0]),m.render_term(act[1]))
                rec={'lhs_t':act[0],'rhs_t':act[1],'lhs':k[0],'rhs':k[1],'proof_nodes':len(pn),'nodes':pn,'root':pr,'dag_var':epvars[0]}
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

    dag=[]
    def append_node(node): dag.append(node); return len(dag)-1
    def orient(root,lhs,rhs):
        n=dag[root]
        if (n.lhs,n.rhs)==(lhs,rhs): return root
        if (n.lhs,n.rhs)==(rhs,lhs): return append_node(m.EqualityNode(lhs,rhs,'symmetry',parents=(root,),constructor='interface-graph'))
        raise RuntimeError('proof endpoint mismatch')
    def clone_law(rec,T):
        local=[]; remap={}; exposed=rec['dag_var']
        def st(t): return subst_named(t,exposed,T)
        def add_local(nn): local.append(nn); return len(local)-1
        for old_id,n in enumerate(rec['nodes']):
            parents=tuple(remap[p] for p in n.parents)
            lhs=st(n.lhs); rhs=st(n.rhs); kind=n.kind
            if kind in ('source instance','source reentry'):
                sub=tuple((v,st(val)) for v,val in n.substitution)
                term_origins=tuple((v,st(term),tuple(remap[p] for p in pids)) for v,term,pids in n.term_origins)
                nn=m.EqualityNode(lhs,rhs,kind,parents=parents,substitution=sub,orientation=n.orientation,generation=n.generation,term_origins=term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth)
            elif kind=='symmetry': nn=m.EqualityNode(lhs,rhs,'symmetry',parents=parents,constructor=n.constructor,derivation_depth=n.derivation_depth)
            elif kind=='transitivity':
                overlap=None
                if n.overlap_record is not None:
                    vals=list(n.overlap_record); vals[0]=remap[vals[0]]; vals[1]=remap[vals[1]]
                    for j in (5,6,7,8,9): vals[j]=st(vals[j])
                    overlap=tuple(vals)
                nn=m.EqualityNode(lhs,rhs,'transitivity',parents=parents,constructor=n.constructor,derivation_depth=n.derivation_depth,overlap_record=overlap)
            elif kind in ('congruence on left child','congruence on right child'):
                side,sib=n.context
                cr=None
                if n.context_record is not None:
                    root_term,path,original,replacement,result=n.context_record
                    cr=(st(root_term),path,st(original),st(replacement),st(result))
                nn=m.EqualityNode(lhs,rhs,kind,parents=parents,context=(side,st(sib)),constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=cr)
            elif kind=='reflexivity': nn=m.EqualityNode(lhs,rhs,'reflexivity',constructor=n.constructor,derivation_depth=n.derivation_depth)
            else: raise RuntimeError('unsupported node kind '+kind)
            remap[old_id]=add_local(nn)
        local_root=remap[rec['root']]
        if not m.replay_dag(source,local,local_root,maximum_term_size=400,maximum_nodes=90000):
            bad=None
            for i,n in enumerate(local):
                if not m.replay_dag(source,local[:i+1],i,maximum_term_size=400,maximum_nodes=90000):
                    bad={'index':i,'kind':n.kind,'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),'parents':list(n.parents),'substitution':[(v,m.render_term(t)) for v,t in n.substitution]}; break
            print('PROVENANCE_CLONE_FAILURE '+json.dumps({'law_lhs':rec['lhs'],'law_rhs':rec['rhs'],'dag_var':exposed,'T':m.render_term(T),'bad':bad},sort_keys=True),flush=True)
            raise RuntimeError('cloned law local replay failed')
        offset=len(dag); local_to_global={}
        for i,n in enumerate(local):
            parents=tuple(offset+p for p in n.parents)
            term_origins=tuple((v,term,tuple(offset+p for p in pids)) for v,term,pids in n.term_origins)
            overlap=None
            if n.overlap_record is not None:
                vals=list(n.overlap_record); vals[0]+=offset; vals[1]+=offset; overlap=tuple(vals)
            nn=m.EqualityNode(n.lhs,n.rhs,n.kind,parents=parents,substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=overlap)
            local_to_global[i]=append_node(nn)
        root=local_to_global[local_root]
        want=(subst_x(rec['lhs_t'],T),subst_x(rec['rhs_t'],T))
        return orient(root,want[0],want[1])

    parent={t:t for t in universe}; rank={t:0 for t in universe}; adj={t:[] for t in universe}
    def ensure(t):
        if t not in parent: parent[t]=t; rank[t]=0; adj[t]=[]; universe.add(t)
        if t[0]=='op': ensure(t[1]); ensure(t[2])
    def find(t):
        if parent[t]!=t: parent[t]=find(parent[t])
        return parent[t]
    def link(a,b,root):
        ensure(a); ensure(b); root=orient(root,a,b); adj[a].append((b,root)); adj[b].append((a,root)); ra,rb=find(a),find(b)
        if ra==rb: return False
        if rank[ra]<rank[rb]: ra,rb=rb,ra
        parent[rb]=ra
        if rank[ra]==rank[rb]: rank[ra]+=1
        return True
    def path_proof(a,b):
        ensure(a); ensure(b)
        if a==b: return append_node(m.EqualityNode(a,a,'reflexivity',constructor='interface-graph'))
        q=deque([a]); prev={a:None}; edge={}
        while q:
            u=q.popleft()
            if u==b: break
            for v,r in adj[u]:
                if v not in prev: prev[v]=u; edge[v]=r; q.append(v)
        if b not in prev: return None
        chain=[]; cur=b
        while prev[cur] is not None:
            p=prev[cur]; chain.append((p,cur,edge[cur])); cur=p
        chain.reverse(); root=None
        for p,v,r in chain:
            r=orient(r,p,v)
            if root is None: root=r
            else:
                left=dag[root]; right=dag[r]
                root=append_node(m.EqualityNode(left.lhs,right.rhs,'transitivity',parents=(root,r),constructor='interface-graph'))
        return root

    instantiated=0; bases=sorted(list(universe),key=tkey)[:96]
    for rec in ordered:
        for T in bases:
            l=subst_x(rec['lhs_t'],T); r=subst_x(rec['rhs_t'],T)
            if max(m.term_size(l),m.term_size(r))>31: continue
            root=clone_law(rec,T); link(l,r,root); instantiated+=1

    congruence_edges=0
    for _ in range(6):
        changed=False; ops=[t for t in list(universe) if t[0]=='op']; buckets={}
        for t in ops:
            sig=(find(t[1]),find(t[2]))
            if sig not in buckets: buckets[sig]=t; continue
            u=buckets[sig]
            if find(t)==find(u): continue
            pl=path_proof(t[1],u[1]); pr=path_proof(t[2],u[2])
            if pl is None or pr is None: continue
            l1=append_node(m.EqualityNode(t,('op',u[1],t[2]),'congruence on left child',parents=(pl,),context=('left',t[2]),constructor='interface-graph'))
            r1=append_node(m.EqualityNode(('op',u[1],t[2]),u,'congruence on right child',parents=(pr,),context=('right',u[1]),constructor='interface-graph'))
            root=append_node(m.EqualityNode(t,u,'transitivity',parents=(l1,r1),constructor='interface-graph'))
            if not m.replay_dag(source,dag,root,maximum_term_size=400,maximum_nodes=200000): raise RuntimeError('congruence replay failed')
            if link(t,u,root): congruence_edges+=1; changed=True
        if not changed: break

    root=path_proof(x,xx); replay=root is not None and m.replay_dag(source,dag,root,maximum_term_size=400,maximum_nodes=200000)
    certificate_bytes=None; certificate_lines=None
    if replay:
        code,_=m.make_dag_certificate(target,dag,root); certificate_bytes=len(code.encode()); certificate_lines=len(code.splitlines())
    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(spectrum),'selected':len(ordered),'graph_nodes':len(universe),'instantiated_edges':instantiated,'congruence_edges':congruence_edges,'connected_idempotence':root is not None,'direct_provenance_replay':replay,'dag_nodes':len(dag),'certificate_bytes':certificate_bytes,'certificate_lines':certificate_lines,'target_revealed_after_closure':True}
    print('SOURCE_ONLY_INTERFACE_GRAPH_PROVENANCE '+json.dumps(out,sort_keys=True),flush=True)
    if not replay: raise SystemExit(2)

if __name__=='__main__': main()
