#!/usr/bin/env python3
"""Promote the first replay-certified compiled idempotence interface and retest fresh 0036.

Rebuilds the same bounded quotient world used by the successful compiled-interface spectrum,
selects the first novel consequence whose compiled observable interface is x = x*x, verifies
that consequence against the original source, then promotes only that proof-bearing consequence
into a fresh target search. No benchmark-specific bridge lemma is supplied.
"""
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    args=ap.parse_args(); m=load(args.solver); row=json.load(open(args.row))
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':80,'maximum_replay_term_size':360,'maximum_depth':14,'maximum_rules':1024,'maximum_rounds':180,'new_clauses_per_round':96,'maximum_clauses':20000,'normalization_steps':360,'maximum_proof_nodes':100000})
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
    x=('var','x'); xx=('op',x,x); desired={(x,xx),(xx,x)}
    chosen=None; info=None; census=0; replayed=0; projected=0
    s.deadline=time.monotonic()+55.0; rules=s.rules(); seen=set()
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or chosen is not None: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=360,maximum_nodes=100000): continue
                replayed+=1
                fs=future(c)
                if fs in old: continue
                raw_iface=canon_pair(c.lhs,c.rhs)
                pe,ps=setup(raw_iface,5.0); pnodes,proot=ps.compile(c)
                if not m.replay_dag(source,pnodes,proot,maximum_term_size=360,maximum_nodes=100000): continue
                projected+=1
                endpoint=(pnodes[proot].lhs,pnodes[proot].rhs); actual=canon_pair(*endpoint)
                if actual[2]==('x',) and (actual[0],actual[1]) in desired:
                    chosen=c; info={'future_size':len(fs),'proof_nodes':len(pnodes),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs),'compiled_lhs':m.render_term(endpoint[0]),'compiled_rhs':m.render_term(endpoint[1])}; break
            if s.expired() or chosen is not None: break
        if s.expired() or chosen is not None: break

    report={'id':row['id'],'census':census,'replayed':replayed,'projected':projected,'idempotence':info,'target':{'found':False,'replay':False}}
    if chosen is None:
        print('IDEMPOTENCE_PROMOTION '+json.dumps(report,sort_keys=True),flush=True); return

    te,ts=setup(target,300.0); added=ts.add_clause(chosen)
    tq=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
    tr={'found':tq is not None,'replay':False,'added':bool(added),'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
    if tq is not None:
        q=te.inline_recipe(tq)
        if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==target[:2]:
            nn,rr=ts.compile(q); tr['replay']=m.replay_dag(source,nn,rr,maximum_term_size=360,maximum_nodes=100000); tr['proof_nodes']=len(nn); tr['proof_cost']=q.cost
    report['target']=tr
    print('IDEMPOTENCE_PROMOTION '+json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__': main()
