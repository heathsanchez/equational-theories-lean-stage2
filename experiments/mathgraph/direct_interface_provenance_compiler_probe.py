#!/usr/bin/env python3
import argparse, importlib.util, json, time


def load(path):
    spec = importlib.util.spec_from_file_location('mgsolver', path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x'); target=m.parse_equation('x = x * x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
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
    def skey(s,q): return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))
    def tkey(t): return (m.term_size(t),m.render_term(t))

    t0=time.monotonic(); _,s=setup(neutral,20.0); pre=[]
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
                raw=canon(c.lhs,c.rhs); _,ps=setup(raw,2.0); pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000): continue
                projected+=1; ep=pn[pr]; act=canon(ep.lhs,ep.rhs)
                if act[2]!=('x',): continue
                # The projection compile is already alpha-normalized to the one-variable interface.
                k=(m.render_term(act[0]),m.render_term(act[1]))
                rec={'lhs_t':act[0],'rhs_t':act[1],'lhs':k[0],'rhs':k[1],'proof_nodes':len(pn),'nodes':pn,'root':pr}
                prev=spectrum.get(k)
                if prev is None or rec['proof_nodes']<prev['proof_nodes']: spectrum[k]=rec
            if s.expired() or census>=176: break
        if s.expired() or census>=176: break

    ordered=sorted(spectrum.values(),key=lambda r:(m.term_size(r['lhs_t'])+m.term_size(r['rhs_t']),r['proof_nodes'],r['lhs'],r['rhs']))[:32]
    # Direct proof graph: import each replay-certified interface DAG unchanged; only its root becomes an equality edge.
    limits={'max_term_size':63,'max_derivation_nodes':20000,'max_graph_edges':12000,'max_congruence_rounds':0}
    g=m.EqualitySearch(source,target,time.monotonic()+20.0,limits)
    imported=[]
    for idx,r in enumerate(ordered):
        local_to_global={}
        ok=True
        for j,node in enumerate(r['nodes']):
            parents=tuple(local_to_global[p] for p in node.parents)
            clone=m.EqualityNode(node.lhs,node.rhs,node.kind,parents=parents,substitution=node.substitution,context=node.context,orientation=node.orientation,generation=node.generation,term_origins=node.term_origins,constructor=node.constructor,derivation_depth=node.derivation_depth,context_record=node.context_record,overlap_record=node.overlap_record)
            gid=g.add_node(clone,graph_edge=(j==r['root']))
            if gid is None:
                if j==r['root']: ok=False; break
                raise RuntimeError('unexpected internal DAG insertion failure')
            local_to_global[j]=gid
        if ok: imported.append((idx,local_to_global[r['root']]))

    root=g.shortest_path()
    direct_before=root is not None
    # Generic congruence compiler. It lifts every certified graph edge through bounded left/right contexts,
    # preserving the parent proof explicitly; shortest_path then emits symmetry/transitivity nodes.
    all_terms=set()
    for rec in ordered:
        for side in (rec['lhs_t'],rec['rhs_t']):
            all_terms.update(m.walk_subterms(side))
    x=('var','x'); xx=('op',x,x); all_terms.update((x,xx))
    siblings=sorted(all_terms,key=tkey)[:40]
    congruence_edges=0
    first=0
    for rnd in range(1,7):
        snapshot=len(g.nodes); edge_ids=[]
        for nid in range(first,snapshot):
            n=g.nodes[nid]
            if (n.lhs,n.rhs) not in g.edge_keys and (n.rhs,n.lhs) not in g.edge_keys: continue
            edge_ids.append(nid)
        for nid in edge_ids:
            n=g.nodes[nid]
            for sib in siblings:
                ll=('op',n.lhs,sib); lr=('op',n.rhs,sib)
                if max(m.term_size(ll),m.term_size(lr))<=63:
                    q=m.EqualityNode(ll,lr,'congruence on left child',parents=(nid,),context=('left',sib),constructor='direct-interface-provenance')
                    if g.add_node(q,graph_edge=True) is not None: congruence_edges+=1
                rl=('op',sib,n.lhs); rr=('op',sib,n.rhs)
                if max(m.term_size(rl),m.term_size(rr))<=63:
                    q=m.EqualityNode(rl,rr,'congruence on right child',parents=(nid,),context=('right',sib),constructor='direct-interface-provenance')
                    if g.add_node(q,graph_edge=True) is not None: congruence_edges+=1
        root=g.shortest_path()
        if root is not None: break
        first=snapshot

    replay=False; proof_nodes=None; certificate_bytes=None
    if root is not None:
        replay=m.replay_dag(source,g.nodes,root,maximum_term_size=320,maximum_nodes=70000)
        proof_nodes=len(g.nodes)
        if replay:
            code,_=m.make_dag_certificate(target,g.nodes,root); certificate_bytes=len(code.encode())
    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(spectrum),'selected':len(ordered),'imported_roots':len(imported),'direct_before_congruence':direct_before,'congruence_edges':congruence_edges,'found':root is not None,'replay':replay,'proof_nodes':proof_nodes,'certificate_bytes':certificate_bytes,'target_revealed_after_interface_discovery':True}
    print('DIRECT_INTERFACE_PROVENANCE_COMPILER '+json.dumps(out,sort_keys=True),flush=True)
    if not replay: raise SystemExit(2)

if __name__=='__main__': main()
