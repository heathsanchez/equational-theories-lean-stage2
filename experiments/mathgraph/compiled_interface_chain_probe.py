#!/usr/bin/env python3
"""Recover quotient candidates by their compiled observable interfaces, then compose operationally.

Diagnostic for fresh order5_normal_0036. Rebuilds the same bounded quotient world, replay-checks
novel candidates from the original source, compiles each candidate through its own raw interface,
and classifies by the *actual compiled interface*. If the previously observed one-variable L2/L3
interfaces are recovered, seed a fresh idempotence search with their proof-bearing raw recipes,
replay the result from the original source, then retest the original target.
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
    def canon_pair(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        cl,cr=f(lhs),f(rhs); return cl,cr,tuple(dict.fromkeys(names.values()))
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))

    e,s=setup(target,30.0)
    for _ in range(3):
        rules=s.rules(); snap=list(rules); props=[]
        for oi,o in enumerate(snap):
            for ii,i in enumerate(snap):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired(): break
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append((s.target_score(c),c))
                    if len(props)>=128:
                        props.sort(key=lambda x:x[0]); added=0
                        for _,q in props:
                            if s.add_clause(q): s.superpositions+=1; added+=1
                            if added>=64: break
                        props=[]; rules=s.rules()
                if s.expired(): break
            if s.expired(): break
        if props and not s.expired():
            props.sort(key=lambda x:x[0]); added=0
            for _,q in props:
                if s.add_clause(q): s.superpositions+=1; added+=1
                if added>=64: break
        if s.expired(): break

    objects=sorted(s.clauses,key=s.target_score)[:224]; probes=objects[:40]
    def alpha(q): return str(s.alpha_signature(q.lhs,q.rhs))
    def future(q):
        out=set()
        for pi,p in enumerate(probes):
            for first,second in ((q,p),(p,q)):
                for fr in (False,True):
                    aa=orient(first,fr)
                    for sr in (False,True):
                        bb=orient(second,sr)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True):
                            c=s.critical_pair(aa,bb,0,pi,path)
                            if c is not None: out.add(alpha(c))
        return frozenset(out)
    old={future(q) for q in objects}

    x=('var','x'); xx=('op',x,x); xxx=('op',x,xx); xxxx=('op',x,xxx)
    want={(x,xxx):'L2',(xxx,x):'L2',(x,xxxx):'L3',(xxxx,x):'L3'}
    found={}; census=0; replayed=0; projected=0
    s.deadline=time.monotonic()+50.0; rules=s.rules(); seen=set()
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or len(found)==2: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=340,maximum_nodes=90000): continue
                replayed+=1
                fs=future(c)
                if fs in old: continue
                raw_iface=canon_pair(c.lhs,c.rhs)
                pe,ps=setup(raw_iface,5.0)
                pnodes,proot=ps.compile(c)
                if not m.replay_dag(source,pnodes,proot,maximum_term_size=340,maximum_nodes=90000): continue
                projected+=1
                endpoint=(pnodes[proot].lhs,pnodes[proot].rhs)
                actual=canon_pair(endpoint[0],endpoint[1])
                if actual[2] != ('x',): continue
                tag=want.get((actual[0],actual[1]))
                if tag is None or tag in found: continue
                found[tag]=(c,{'future_size':len(fs),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs),'compiled_lhs':m.render_term(endpoint[0]),'compiled_rhs':m.render_term(endpoint[1]),'proof_nodes':len(pnodes)})
            if s.expired() or len(found)==2: break
        if s.expired() or len(found)==2: break

    report={'id':row['id'],'census':census,'replayed':replayed,'projected':projected,'found_interfaces':{k:v[1] for k,v in found.items()},'idempotence':{'found':False,'replay':False},'target':{'found':False,'replay':False}}
    if len(found)<2:
        print('COMPILED_INTERFACE_CHAIN '+json.dumps(report,sort_keys=True),flush=True); return

    ig=m.parse_equation('x = x * x'); ie,isearch=setup(ig,120.0)
    added=0
    for tag in ('L2','L3'):
        if isearch.add_clause(found[tag][0]): added+=1
    iq=isearch.collapse_proof() or isearch.target_proof(isearch.rules()) or isearch.solve()
    ir={'found':iq is not None,'replay':False,'added':added,'rounds':isearch.rounds,'superpositions':isearch.superpositions,'clauses':len(isearch.clauses)}
    idem=None
    if iq is not None:
        q=ie.inline_recipe(iq)
        if (q.lhs,q.rhs)==(ig[1],ig[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==ig[:2]:
            nn,rr=isearch.compile(q); ok=m.replay_dag(source,nn,rr,maximum_term_size=340,maximum_nodes=90000)
            ir['replay']=ok; ir['proof_nodes']=len(nn)
            if ok: idem=q
    report['idempotence']=ir
    if idem is None:
        print('COMPILED_INTERFACE_CHAIN '+json.dumps(report,sort_keys=True),flush=True); return

    te,ts=setup(target,240.0); added=0
    for q in (found['L2'][0],found['L3'][0],idem):
        if ts.add_clause(q): added+=1
    tq=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
    tr={'found':tq is not None,'replay':False,'added':added,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
    if tq is not None:
        q=te.inline_recipe(tq)
        if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==target[:2]:
            nn,rr=ts.compile(q); tr['replay']=m.replay_dag(source,nn,rr,maximum_term_size=340,maximum_nodes=90000); tr['proof_nodes']=len(nn)
    report['target']=tr
    print('COMPILED_INTERFACE_CHAIN '+json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__': main()
