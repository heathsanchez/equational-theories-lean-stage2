#!/usr/bin/env python3
"""Reconstruct quotient-discovered one-variable interfaces and compose them.

Unlike interface_chain_idempotence_probe.py, this does not ask ordinary target-grounded
search to rediscover L2/L3. It rebuilds the bounded quotient world, enumerates replay-certified
novel classes, compiles their proof-bearing recipes through the observable interface, and
selects the two already-observed one-variable interfaces only for this causal diagnostic:
  L2: x = x*(x*x)
  L3: x = x*(x*(x*x))
Then it composes their exact source-derived certificates into idempotence and retests 0036.
"""
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    args=ap.parse_args(); m=load(args.solver); row=json.load(open(args.row))
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':80,'maximum_replay_term_size':340,'maximum_depth':14,'maximum_rules':1024,'maximum_rounds':160,'new_clauses_per_round':96,'maximum_clauses':18000,'normalization_steps':320,'maximum_proof_nodes':90000})
    def setup(goal,seconds):
        lim=dict(base); lim['seconds']=seconds
        e=m.TargetGroundedRefutation(source,goal,time.monotonic()+seconds,lim); return e,e.search
    def canon(q):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(q.lhs),f(q.rhs),tuple(dict.fromkeys(names.values()))
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))

    e,s=setup(target,32.0)
    for _ in range(4):
        rules=s.rules(); snap=list(rules); props=[]
        for oi,o in enumerate(snap):
            for ii,i in enumerate(snap):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=14,include_root=True):
                    if s.expired(): break
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append((s.target_score(c),c))
                    if len(props)>=192:
                        props.sort(key=lambda x:x[0]); added=0
                        for _,q in props:
                            if s.add_clause(q): s.superpositions+=1; added+=1
                            if added>=96: break
                        props=[]; rules=s.rules()
                if s.expired(): break
            if s.expired(): break
        if props and not s.expired():
            props.sort(key=lambda x:x[0]); added=0
            for _,q in props:
                if s.add_clause(q): s.superpositions+=1; added+=1
                if added>=96: break
        if s.expired(): break

    objects=sorted(s.clauses,key=s.target_score)[:256]; probes=objects[:48]
    def alpha(q): return str(s.alpha_signature(q.lhs,q.rhs))
    def future(q):
        out=set()
        for pi,p in enumerate(probes):
            for first,second in ((q,p),(p,q)):
                for fr in (False,True):
                    aa=orient(first,fr)
                    for sr in (False,True):
                        bb=orient(second,sr)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=7,include_root=True):
                            c=s.critical_pair(aa,bb,0,pi,path)
                            if c is not None: out.add(alpha(c))
        return frozenset(out)
    old={future(q) for q in objects}

    x=('var','x'); xx=('op',x,x); xxx=('op',x,xx); xxxx=('op',x,xxx)
    wants={(x,xxx):'L2',(x,xxxx):'L3',(xxx,x):'L2',(xxxx,x):'L3'}
    found={}; census=0; replayed=0
    s.deadline=time.monotonic()+55.0; rules=s.rules(); seen=set()
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=14,include_root=True):
                if s.expired() or len(found)==2: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules)
                names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=340,maximum_nodes=90000): continue
                replayed+=1
                fs=future(c)
                if fs in old: continue
                cl,cr,cvars=canon(c)
                if cvars!=('x',): continue
                tag=wants.get((cl,cr))
                if tag is None or tag in found: continue
                # Normalize the proof-bearing recipe to x = ... orientation.
                q=c
                if (cl,cr) in ((xxx,x),(xxxx,x)):
                    q=m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
                found[tag]=(q,{'future_size':len(fs),'proof_nodes':len(ns),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs)})
            if s.expired() or len(found)==2: break
        if s.expired() or len(found)==2: break

    report={'id':row['id'],'census':census,'replayed':replayed,'found_interfaces':{k:v[1] for k,v in found.items()},'idempotence':{'constructed':False,'replay':False},'target':{'found':False,'replay':False}}
    if len(found)<2:
        print('QUOTIENT_CHAIN '+json.dumps(report,sort_keys=True),flush=True); return

    l2=found['L2'][0]; l3=found['L3'][0]
    # Canonicalize actual endpoints through alpha-renaming by compiling against canonical goals.
    def project(q,text):
        goal=m.parse_equation(text); pe,ps=setup(goal,6.0); nodes,root=ps.compile(q)
        ok=m.replay_dag(source,nodes,root,maximum_term_size=340,maximum_nodes=90000)
        if not ok: return None,{'replay':False}
        pq=m.Recipe(nodes[root].lhs,nodes[root].rhs,'replay_projection',(q,))
        if (pq.lhs,pq.rhs)==(goal[1],goal[0]): pq=m.Recipe(pq.rhs,pq.lhs,'symmetry',(pq,))
        return (q if (q.lhs,q.rhs)==goal[:2] else pq),{'replay':True,'proof_nodes':len(nodes),'endpoint':m.render_term(nodes[root].lhs)+' = '+m.render_term(nodes[root].rhs)}
    l2p,r2=project(l2,'x = x * (x * x)'); l3p,r3=project(l3,'x = x * (x * (x * x))')
    report['L2_projection']=r2; report['L3_projection']=r3
    if l2p is None or l3p is None:
        print('QUOTIENT_CHAIN '+json.dumps(report,sort_keys=True),flush=True); return

    # Use proof constructors directly on the canonical equations. The compiler/replayer decides validity.
    l2sym=m.Recipe(xxx,x,'symmetry',(l2p,))
    lifted=m.Recipe(xxxx,xx,'congruence',(l2sym,),('right',x))
    idem=m.Recipe(x,xx,'transitivity',(l3p,lifted))
    ie,isearch=setup(m.parse_equation('x = x * x'),6.0); nodes,root=isearch.compile(idem)
    idem_ok=m.replay_dag(source,nodes,root,maximum_term_size=340,maximum_nodes=90000)
    report['idempotence']={'constructed':True,'replay':bool(idem_ok),'proof_nodes':len(nodes),'lhs':m.render_term(idem.lhs),'rhs':m.render_term(idem.rhs)}
    if not idem_ok:
        print('QUOTIENT_CHAIN '+json.dumps(report,sort_keys=True),flush=True); return

    te,ts=setup(target,300.0); added=0
    for q in (l2p,l3p,idem):
        if ts.add_clause(q): added+=1
    tf=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
    tr={'found':tf is not None,'replay':False,'added':added,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
    if tf is not None:
        ti=te.inline_recipe(tf)
        if (ti.lhs,ti.rhs)==(target[1],target[0]): ti=m.Recipe(ti.rhs,ti.lhs,'symmetry',(ti,))
        if (ti.lhs,ti.rhs)==target[:2]:
            ns,r=ts.compile(ti); tr['replay']=m.replay_dag(source,ns,r,maximum_term_size=340,maximum_nodes=90000); tr['proof_nodes']=len(ns)
    report['target']=tr
    print('QUOTIENT_CHAIN '+json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__': main()
