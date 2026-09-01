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
    ap.add_argument('--certificate', default='/tmp/interface_idempotence.lean')
    a = ap.parse_args()
    m = load(a.solver)
    row = json.load(open(a.row))
    source = m.parse_equation(row['equation1'])
    neutral = m.parse_equation('x = x')
    target = m.parse_equation('x = x * x')
    base = dict(m.COMPACT_SUPERPOSITION_PROBE)
    base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})

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
        return f(lhs), f(rhs), tuple(dict.fromkeys(names.values()))

    def skey(s, q):
        return (m.term_size(q.lhs)+m.term_size(q.rhs), str(s.alpha_signature(q.lhs,q.rhs)), m.render_term(q.lhs), m.render_term(q.rhs))

    def subst(t, repl):
        if t[0] == 'var': return repl if t[1] == 'x' else t
        return ('op', subst(t[1], repl), subst(t[2], repl))

    def tkey(t): return (m.term_size(t), m.render_term(t))

    t0 = time.monotonic()
    e, s = setup(neutral, 20.0)
    pre = []
    for gen in range(1, 4):
        rules = s.rules(); snap = list(rules); props = []; proposed = 0; stop = False
        for oi, o in enumerate(snap):
            if stop: break
            for ii, i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs, maximum_depth=12, include_root=True):
                    c = s.critical_pair(o, i, oi, ii, path)
                    if c is None: continue
                    c = s.interreduce(c, rules); props.append(c); proposed += 1
                    if proposed >= 512: stop = True; break
        props.sort(key=lambda q: skey(s, q)); added = 0
        for q in props:
            if s.add_clause(q): s.superpositions += 1; added += 1
            if added >= 64: break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    seen = set(); spectrum = {}; census = replayed = projected = 0
    rules = s.rules(); s.deadline = time.monotonic() + 12.0
    for oi, o in enumerate(rules):
        for ii, i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs, maximum_depth=12, include_root=True):
                if s.expired() or census >= 176: break
                c = s.critical_pair(o, i, oi, ii, path)
                if c is None: continue
                c = s.interreduce(c, rules)
                names = m.term_variables(c.lhs) | m.term_variables(c.rhs)
                if c.lhs == c.rhs or any(v.startswith('@') for v in names): continue
                key = (s.alpha_signature(c.lhs,c.rhs), c.lhs, c.rhs)
                if key in seen: continue
                seen.add(key); census += 1
                ns, r = s.compile(c)
                if not m.replay_dag(source, ns, r, maximum_term_size=320, maximum_nodes=70000): continue
                replayed += 1
                raw = canon(c.lhs, c.rhs)
                pe, ps = setup(raw, 2.0)
                pn, pr = ps.compile(c)
                if not m.replay_dag(source, pn, pr, maximum_term_size=320, maximum_nodes=70000): continue
                projected += 1
                ep = (pn[pr].lhs, pn[pr].rhs); act = canon(ep[0], ep[1])
                if act[2] != ('x',): continue
                k = (m.render_term(act[0]), m.render_term(act[1]))
                rec = {'lhs_t':act[0], 'rhs_t':act[1], 'lhs':k[0], 'rhs':k[1], 'proof_nodes':len(pn), 'raw_lhs':m.render_term(c.lhs), 'raw_rhs':m.render_term(c.rhs), 'dag':pn, 'root':pr}
                prev = spectrum.get(k)
                if prev is None or rec['proof_nodes'] < prev['proof_nodes']: spectrum[k] = rec
            if s.expired() or census >= 176: break
        if s.expired() or census >= 176: break

    ordered = sorted(spectrum.values(), key=lambda r:(m.term_size(r['lhs_t'])+m.term_size(r['rhs_t']),r['proof_nodes'],r['lhs'],r['rhs']))[:32]
    x = ('var','x'); xx = ('op',x,x)
    universe = {x,xx}
    def addsubs(t):
        universe.add(t)
        if t[0]=='op': addsubs(t[1]); addsubs(t[2])
    for r in ordered:
        addsubs(r['lhs_t']); addsubs(r['rhs_t'])
    simple = sorted(universe,key=tkey)[:24]
    for u in simple:
        for v in simple:
            z=('op',u,v)
            if m.term_size(z)<=15: universe.add(z)
    universe=set(sorted(universe,key=tkey)[:256])

    parent={t:t for t in universe}; rank={t:0 for t in universe}; adj={t:[] for t in universe}
    def ensure(t):
        if t not in parent:
            parent[t]=t; rank[t]=0; adj[t]=[]; universe.add(t)
        if t[0]=='op': ensure(t[1]); ensure(t[2])
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
            link(l,rr,{'kind':'law_subst','law':idx,'subst_t':T,'proof_nodes':r['proof_nodes']})
            instantiated += 1

    congruence_edges=0
    for _round in range(6):
        changed=False; ops=[t for t in list(universe) if t[0]=='op']; buckets={}
        for t in ops:
            sig=(find(t[1]),find(t[2]))
            if sig in buckets:
                u=buckets[sig]
                if find(t)!=find(u):
                    if link(t,u,{'kind':'congruence'}): congruence_edges += 1; changed=True
            else: buckets[sig]=t
        if not changed: break

    if find(x) != find(xx):
        print('SOURCE_ONLY_INTERFACE_GRAPH_COMPILE '+json.dumps({'id':row['id'],'connected':False,'elapsed':round(time.monotonic()-t0,4)},sort_keys=True),flush=True)
        raise SystemExit(2)

    def bfs(a0,b0):
        q=deque([a0]); prev={a0:None}; pedge={}
        while q:
            u=q.popleft()
            if u==b0: break
            for v,w in adj.get(u,()):
                if v not in prev:
                    prev[v]=u; pedge[v]=w; q.append(v)
        if b0 not in prev: return None
        out=[]; cur=b0
        while prev[cur] is not None:
            p=prev[cur]; out.append((p,cur,pedge[cur])); cur=p
        out.reverse(); return out

    out=[]
    def tr_term(t,T):
        if t[0]=='var': return T
        return ('op',tr_term(t[1],T),tr_term(t[2],T))

    def clone_dag(nodes, root, T):
        off=len(out)
        for n in nodes:
            parents=tuple(off+p for p in n.parents)
            substitution=tuple((v,tr_term(val,T)) for v,val in n.substitution)
            context=None if n.context is None else (n.context[0],tr_term(n.context[1],T))
            term_origins=tuple((v,tr_term(term,T),tuple(off+p for p in ids)) for v,term,ids in n.term_origins)
            context_record=None
            if n.context_record is not None:
                rt,path,orig,repl,res=n.context_record
                context_record=(tr_term(rt,T),path,tr_term(orig,T),tr_term(repl,T),tr_term(res,T))
            overlap_record=None
            if n.overlap_record is not None:
                z=list(n.overlap_record)
                z[0]=off+z[0]; z[1]=off+z[1]
                for j in range(5,10): z[j]=tr_term(z[j],T)
                overlap_record=tuple(z)
            out.append(m.EqualityNode(tr_term(n.lhs,T),tr_term(n.rhs,T),n.kind,parents=parents,substitution=substitution,context=context,orientation=n.orientation,generation=n.generation,term_origins=term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=context_record,overlap_record=overlap_record))
        return off+root

    proving=set(); cache={}
    def orient(root,a0,b0):
        n=out[root]
        if (n.lhs,n.rhs)==(a0,b0): return root
        if (n.lhs,n.rhs)==(b0,a0):
            out.append(m.EqualityNode(a0,b0,'symmetry',parents=(root,)))
            return len(out)-1
        raise RuntimeError('compiled edge endpoint mismatch')

    def trans(roots):
        if not roots: return None
        root=roots[0]
        for r in roots[1:]:
            l=out[root]; rr=out[r]
            if l.rhs!=rr.lhs: raise RuntimeError('transitivity mismatch')
            out.append(m.EqualityNode(l.lhs,rr.rhs,'transitivity',parents=(root,r)))
            root=len(out)-1
        return root

    def prove_edge(a0,b0,why,depth):
        if why['kind']=='law_subst':
            rec=ordered[why['law']]
            return orient(clone_dag(rec['dag'],rec['root'],why['subst_t']),a0,b0)
        if why['kind']=='congruence':
            if a0[0]!='op' or b0[0]!='op': raise RuntimeError('bad congruence edge')
            roots=[]
            if a0[1]!=b0[1]:
                p=prove_pair(a0[1],b0[1],depth+1)
                out.append(m.EqualityNode(('op',a0[1],a0[2]),('op',b0[1],a0[2]),'congruence on left child',parents=(p,),context=('left',a0[2])))
                roots.append(len(out)-1)
            mid=('op',b0[1],a0[2])
            if a0[2]!=b0[2]:
                p=prove_pair(a0[2],b0[2],depth+1)
                out.append(m.EqualityNode(mid,('op',b0[1],b0[2]),'congruence on right child',parents=(p,),context=('right',b0[1])))
                roots.append(len(out)-1)
            if not roots:
                out.append(m.EqualityNode(a0,b0,'reflexivity')); return len(out)-1
            return trans(roots)
        raise RuntimeError('unknown edge kind')

    def prove_pair(a0,b0,depth=0):
        if a0==b0:
            out.append(m.EqualityNode(a0,b0,'reflexivity')); return len(out)-1
        key=(a0,b0)
        if key in cache: return cache[key]
        if depth>20 or key in proving: raise RuntimeError('recursive proof cycle')
        proving.add(key)
        path=bfs(a0,b0)
        if path is None: raise RuntimeError('missing graph path')
        roots=[]
        for u,v,w in path:
            roots.append(prove_edge(u,v,w,depth))
        root=trans(roots)
        proving.remove(key); cache[key]=root
        return root

    graph_path=bfs(x,xx)
    root=prove_pair(x,xx)
    replay=m.replay_dag(source,out,root,maximum_term_size=500,maximum_nodes=100000)
    cert=''; cert_nodes=0
    if replay:
        cert,cert_nodes=m.make_dag_certificate(target,out,root)
        open(a.certificate,'w').write(cert)
    result={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(spectrum),'selected':len(ordered),'graph_nodes':len(universe),'instantiated_edges':instantiated,'congruence_edges':congruence_edges,'graph_path_len':len(graph_path or []),'compiled_nodes':len(out),'root':root,'internal_replay':replay,'certificate_nodes':cert_nodes,'certificate_path':a.certificate}
    print('SOURCE_ONLY_INTERFACE_GRAPH_COMPILE '+json.dumps(result,sort_keys=True),flush=True)
    if not replay: raise SystemExit(3)

if __name__=='__main__': main()
