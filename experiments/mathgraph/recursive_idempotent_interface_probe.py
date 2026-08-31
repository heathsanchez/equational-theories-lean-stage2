#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver', path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    a=ap.parse_args(); m=load(a.solver); row=json.load(open(a.row))
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,seconds=600.0):
        lim=dict(base); lim['seconds']=seconds
        e=m.TargetGroundedRefutation(source,goal,time.monotonic()+seconds,lim); return e,e.search
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names: names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def grow(s, rounds=3, proposal_budget=512, add_budget=64):
        trace=[]
        for _ in range(rounds):
            rules=s.rules(); snap=list(rules); props=[]; proposed=0
            for oi,o in enumerate(snap):
                if proposed>=proposal_budget: break
                for ii,i in enumerate(snap):
                    if proposed>=proposal_budget: break
                    for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                        c=s.critical_pair(o,i,oi,ii,path)
                        if c is None: continue
                        c=s.interreduce(c,rules); props.append((s.target_score(c),c)); proposed+=1
                        if proposed>=proposal_budget: break
            props.sort(key=lambda x:x[0]); added=0
            for _,q in props:
                if s.add_clause(q): s.superpositions+=1; added+=1
                if added>=add_budget: break
            trace.append({'proposed':proposed,'added':added,'clauses':len(s.clauses)})
        return trace
    def spectrum(s, candidate_budget=256):
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
        old={future(q) for q in objects}; seen=set(); rows=[]; chosen=None; census=replayed=projected=0
        rules=s.rules(); stop=False
        for oi,o in enumerate(rules):
            if stop: break
            for ii,i in enumerate(rules):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                    if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                    key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                    if key in seen: continue
                    seen.add(key); census+=1
                    ns,r=s.compile(c)
                    if m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000):
                        replayed+=1; fs=future(c)
                        if fs not in old:
                            raw=canon(c.lhs,c.rhs); pe,ps=setup(raw,60.0); pn,pr=ps.compile(c)
                            if m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000):
                                projected+=1; ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                                rec={'lhs':m.render_term(act[0]),'rhs':m.render_term(act[1]),'vars':list(act[2]),'future_size':len(fs),'proof_nodes':len(pn),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs),'recipe':c}
                                rows.append(rec)
                    if census>=candidate_budget: stop=True; break
        rows.sort(key=lambda z:(len(z['vars']), m.term_size(m.parse_equation(z['lhs']+' = '+z['rhs'])[0])+m.term_size(m.parse_equation(z['lhs']+' = '+z['rhs'])[1]), -z['future_size'], z['lhs'], z['rhs']))
        return {'census':census,'replayed':replayed,'projected':projected,'rows':rows}

    e0,s0=setup(target); pre0=grow(s0)
    sp0=spectrum(s0)
    x=('var','x'); xx=('op',x,x); idem=None
    for rec in sp0['rows']:
        lhs,rhs,_=canon(m.parse_equation(rec['lhs']+' = '+rec['rhs'])[0],m.parse_equation(rec['lhs']+' = '+rec['rhs'])[1])
        if (lhs,rhs)==(x,xx) or (lhs,rhs)==(xx,x): idem=rec; break
    result={'id':row['id'],'generation0':{'pre_trace':pre0,'census':sp0['census'],'replayed':sp0['replayed'],'projected':sp0['projected'],'idempotence':None if idem is None else {k:v for k,v in idem.items() if k!='recipe'}}}
    if idem is None:
        print('RECURSIVE_IDEMPOTENT_INTERFACE '+json.dumps(result,sort_keys=True),flush=True); return

    e1,s1=setup(target); added=s1.add_clause(idem['recipe']); pre1=grow(s1)
    sp1=spectrum(s1)
    # Report the simplest interfaces that are new relative to generation 0.
    sig0={(r['lhs'],r['rhs'],tuple(r['vars'])) for r in sp0['rows']}
    new=[]
    for r in sp1['rows']:
        sig=(r['lhs'],r['rhs'],tuple(r['vars']))
        if sig in sig0: continue
        new.append({k:v for k,v in r.items() if k!='recipe'})
        if len(new)>=20: break
    # Also detect simple binary projections without using them to steer the search.
    projections=[]
    for r in sp1['rows']:
        if len(r['vars'])==2 and r['lhs'] in ('x','y'):
            projections.append({k:v for k,v in r.items() if k!='recipe'})
            if len(projections)>=20: break
    tq=s1.collapse_proof() or s1.target_proof(s1.rules()) or s1.solve(); tr={'found':tq is not None,'replay':False}
    if tq is not None:
        q=e1.inline_recipe(tq)
        if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==target[:2]:
            nn,rr=s1.compile(q); tr={'found':True,'replay':m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000),'proof_nodes':len(nn)}
    result['generation1']={'idempotence_added':bool(added),'pre_trace':pre1,'census':sp1['census'],'replayed':sp1['replayed'],'projected':sp1['projected'],'new_interfaces':new,'binary_projections':projections,'target':tr}
    print('RECURSIVE_IDEMPOTENT_INTERFACE '+json.dumps(result,sort_keys=True),flush=True)
if __name__=='__main__': main()
