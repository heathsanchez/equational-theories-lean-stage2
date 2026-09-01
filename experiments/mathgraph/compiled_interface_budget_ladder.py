#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def run(m,row,seconds,rounds,objects_n,probes_n,census_cap):
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,sec):
        lim=dict(base); lim['seconds']=sec
        e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim); return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    t0=time.monotonic(); e,s=setup(target,seconds)
    for _ in range(rounds):
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
    objects=sorted(s.clauses,key=s.target_score)[:objects_n]; probes=objects[:probes_n]
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
    old={future(q) for q in objects}; seen=set(); census=replayed=projected=0
    # Keep the same mechanism, but use the remaining calibrated wall budget and early-stop on the positive control.
    s.deadline=time.monotonic()+seconds; rules=s.rules()
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=census_cap: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000): continue
                replayed+=1; fs=future(c)
                if fs in old: continue
                raw=canon(c.lhs,c.rhs); pe,ps=setup(raw,2.0); pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000): continue
                projected+=1; ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                if act[2]!=('x',): continue
                lhs=m.render_term(act[0]); rhs=m.render_term(act[1])
                if lhs=='x' and rhs=='(x ◇ x)':
                    return {'recovered':True,'elapsed':round(time.monotonic()-t0,4),'seconds':seconds,'rounds':rounds,'objects':objects_n,'probes':probes_n,'census_cap':census_cap,'census':census,'replayed':replayed,'projected':projected,'proof_nodes':len(pn),'future_size':len(fs)}
            if s.expired() or census>=census_cap: break
        if s.expired() or census>=census_cap: break
    return {'recovered':False,'elapsed':round(time.monotonic()-t0,4),'seconds':seconds,'rounds':rounds,'objects':objects_n,'probes':probes_n,'census_cap':census_cap,'census':census,'replayed':replayed,'projected':projected}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row))
    ladder=[
      (8,1,48,8,48),
      (12,1,64,12,64),
      (18,2,96,16,96),
      (25,2,128,24,128),
      (35,3,160,32,176),
      (50,3,224,40,227),
    ]
    out=[]
    for cfg in ladder:
        rec=run(m,row,*cfg); out.append(rec); print('COMPILED_INTERFACE_BUDGET_STEP '+json.dumps(rec,sort_keys=True),flush=True)
        if rec['recovered']:
            print('COMPILED_INTERFACE_BUDGET '+json.dumps({'recovered':True,'winner':rec,'steps':out},sort_keys=True),flush=True); return
    print('COMPILED_INTERFACE_BUDGET '+json.dumps({'recovered':False,'steps':out},sort_keys=True),flush=True); raise SystemExit(2)
if __name__=='__main__': main()
