#!/usr/bin/env python3
"""Promote the strongest replay-certified reducer that creates a new bounded future class.

Diagnostic only.  The selector is problem-blind: derive a bounded source world, discover
strict dependency reducers, quotient them by one-step continuation signatures against a
fixed pre-repair probe basis, and promote one representative for each continuation class
absent from the base quotient.  Then restart target-directed proof search from those laws.
"""
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    ap.add_argument('--world-seconds',type=float,default=24.0); ap.add_argument('--discover-seconds',type=float,default=12.0)
    ap.add_argument('--warm-seconds',type=float,default=120.0); ap.add_argument('--probes',type=int,default=32); ap.add_argument('--objects',type=int,default=192)
    a=ap.parse_args(); m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])

    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
    def setup(seconds):
        limits=dict(base); limits['seconds']=seconds
        e=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits); s=e.search
        return e,s

    # Pre-repair world, matching the quotient diagnostic.
    eng,s=setup(a.world_seconds); enumerated=0
    for _ in range(3):
        rules=s.rules(); snap=list(rules); props=[]
        for oi,o in enumerate(snap):
            for ii,i in enumerate(snap):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired(): break
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append((s.target_score(c),c)); enumerated+=1
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

    objects=sorted(s.clauses,key=s.target_score)[:a.objects]; probes=objects[:a.probes]
    def profile(q):
        lv=m.term_variables(q.lhs); rv=m.term_variables(q.rhs)
        for vside,other in ((q.lhs,q.rhs),(q.rhs,q.lhs)):
            if vside[0]=='var':
                d=vside[1]; ov=m.term_variables(other)
                if d not in ov: return (0,0,len(ov))
                return (1,len(ov-{d}),len(ov))
        if lv<rv:return (2,len(rv-lv),len(rv))
        if rv<lv:return (2,len(lv-rv),len(lv))
        return (3,len(lv|rv),len(lv|rv))
    source_profile=profile(m.Recipe(source[0],source[1],'reflexivity'))
    def good(q):
        return q.lhs!=q.rhs and m.render_term(q.lhs)!=m.render_term(q.rhs) and not any(x.startswith('@') for x in m.term_variables(q.lhs)|m.term_variables(q.rhs))
    def replay(q):
        ns,r=s.compile(q); return m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000)
    def alpha(q): return str(s.alpha_signature(q.lhs,q.rhs))
    def orient(q,rev): return q if not rev else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
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

    # Freeze pre-repair quotient before the independent reducer census.
    base_sigs={future(q) for q in objects}
    s.deadline=time.monotonic()+a.discover_seconds
    rules=s.rules(); seen=set(); reducers=[]; tested=0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired(): break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); tested+=1
                if not good(c) or not profile(c)<source_profile: continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key)
                if replay(c): reducers.append(c)
            if s.expired(): break
        if s.expired(): break
    reducers.sort(key=lambda q:(profile(q),m.term_size(q.lhs)+m.term_size(q.rhs),q.cost,m.render_term(q.lhs),m.render_term(q.rhs)))

    new=[]; new_sigs={}
    # Classify strongest candidates first; retain one representative per genuinely new future.
    for q in reducers[:96]:
        sig=future(q)
        if sig in base_sigs or sig in new_sigs: continue
        new_sigs[sig]=q; new.append(q)
        if len(new)>=8: break

    warm_eng,warm=setup(a.warm_seconds); added=0
    for q in new:
        if warm.add_clause(q): added+=1
    found=warm.collapse_proof()
    if found is None: found=warm.target_proof(warm.rules())
    if found is None: found=warm.solve()
    replay_ok=False; proof_nodes=0; exact=False
    if found is not None:
        inline=warm_eng.inline_recipe(found)
        exact=(inline.lhs,inline.rhs)==target[:2] or (inline.lhs,inline.rhs)==(target[1],target[0])
        ns,r=warm.compile(found); proof_nodes=len(ns); replay_ok=m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000)
    rec={'id':row['id'],'world_clauses':len(s.clauses),'world_enumerated':enumerated,'base_classes':len(base_sigs),'reducer_tested':tested,'replayable_reducers':len(reducers),'new_classes':len(new),'promoted_added':added,'promoted':[{'profile':list(profile(q)),'lhs':m.render_term(q.lhs),'rhs':m.render_term(q.rhs),'size':m.term_size(q.lhs)+m.term_size(q.rhs),'future_size':len(future(q))} for q in new], 'warm_found':found is not None,'warm_exact':exact,'warm_replay':replay_ok,'proof_nodes':proof_nodes,'warm_clauses':len(warm.clauses),'warm_rounds':warm.rounds,'warm_superpositions':warm.superpositions}
    print('QUOTIENT_CLASS_PROMOTION '+json.dumps(rec,sort_keys=True),flush=True)

if __name__=='__main__': main()
