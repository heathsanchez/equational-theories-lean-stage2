#!/usr/bin/env python3
"""Calibrate a genuinely target-blind source-interface discovery microkernel.

Search uses only the source equation.  Candidate ordering is intrinsic
(term size / variable count / alpha signature), never the real target or row id.
The known 0036 idempotence is inspected only after generation as a positive
control; it is not supplied to the search.
"""
import argparse, importlib.util, json, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'

def load():
    sp=importlib.util.spec_from_file_location('mg',SOLVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m

def canon(m,lhs,rhs):
    names={}
    def f(t):
        if t[0]=='var':
            if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
            return ('var',names[t[1]])
        return ('op',f(t[1]),f(t[2]))
    a,b=f(lhs),f(rhs)
    vs=tuple(dict.fromkeys(names.values()))
    return a,b,vs

def keyterm(m,t): return (m.term_size(t),len(m.term_variables(t)),m.render_term(t))
def qkey(m,s,q):
    a,b,vs=canon(m,q.lhs,q.rhs)
    return (m.term_size(a)+m.term_size(b),len(vs),max(m.term_size(a),m.term_size(b)),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(a),m.render_term(b))

def run(m,source,seconds,rounds,add_per_round,census_limit):
    # Synthetic reflexive goal exists only to instantiate the engine; no target
    # score or target term participates in candidate ordering below.
    x=('var','x'); dummy=(x,x,('x',))
    lim=dict(m.COMPACT_SUPERPOSITION_PROBE)
    lim.update({'seconds':seconds,'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    e=m.TargetGroundedRefutation(source,dummy,time.monotonic()+seconds,lim);s=e.search
    trace=[]
    for r in range(rounds):
        rules=s.rules(); snap=list(rules); seen=set(); props=[]
        for oi,o in enumerate(snap):
            for ii,i in enumerate(snap):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired():break
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules)
                    if c.lhs==c.rhs:continue
                    sig=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                    if sig in seen:continue
                    seen.add(sig);props.append(c)
                if s.expired():break
            if s.expired():break
        props.sort(key=lambda q:qkey(m,s,q));added=0
        for q in props:
            if s.add_clause(q):s.superpositions+=1;added+=1
            if added>=add_per_round:break
        trace.append({'round':r+1,'proposed':len(props),'added':added,'clauses':len(s.clauses)})
        if s.expired():break
    rules=s.rules(); seen=set(); interfaces={}; census=replayed=0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=census_limit:break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules)
                names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names):continue
                sig=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if sig in seen:continue
                seen.add(sig);census+=1
                ns,root=s.compile(c)
                if not m.replay_dag(source,ns,root,maximum_term_size=320,maximum_nodes=70000):continue
                replayed+=1
                ep=ns[root];a,b,vs=canon(m,ep.lhs,ep.rhs)
                if len(vs)>2:continue
                k=(m.render_term(a),m.render_term(b))
                rec={'lhs':k[0],'rhs':k[1],'variables':len(vs),'proof_nodes':len(ns),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs)}
                old=interfaces.get(k)
                if old is None or rec['proof_nodes']<old['proof_nodes']:interfaces[k]=rec
            if s.expired() or census>=census_limit:break
        if s.expired() or census>=census_limit:break
    vals=sorted(interfaces.values(),key=lambda z:(z['variables'],m.term_size(m.parse_equation(z['lhs']+' = '+z['rhs'])[0])+m.term_size(m.parse_equation(z['lhs']+' = '+z['rhs'])[1]),z['proof_nodes'],z['lhs'],z['rhs']))
    idem=next((z for z in vals if {z['lhs'],z['rhs']}=={'x','(x ◇ x)'}),None)
    return {'seconds':seconds,'trace':trace,'census':census,'replayed':replayed,'interfaces':len(vals),'idempotence':idem,'sample':vals[:20]}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('corpus',type=Path);a=ap.parse_args();m=load()
    rows=[json.loads(x) for x in a.corpus.read_text().splitlines() if x.strip()]
    row=next(r for r in rows if r['id']=='order5_normal_0036');source=m.parse_equation(row['equation1'])
    ladder=[(1.0,2,32,256),(3.0,3,64,512),(8.0,3,96,1024),(20.0,4,128,2048)]
    steps=[]
    for spec in ladder:
        t=time.monotonic();rec=run(m,source,*spec);rec['elapsed']=round(time.monotonic()-t,3);steps.append(rec)
        print('SOURCE_INTERFACE_CALIBRATION_STEP '+json.dumps(rec,sort_keys=True),flush=True)
        if rec['idempotence'] is not None:
            print('SOURCE_INTERFACE_CALIBRATION '+json.dumps({'recovered':True,'winning':rec,'steps':len(steps)},sort_keys=True),flush=True);return
    print('SOURCE_INTERFACE_CALIBRATION '+json.dumps({'recovered':False,'steps':steps},sort_keys=True),flush=True)
    raise SystemExit(2)
if __name__=='__main__':main()
