#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'
RID='evaluation_normal_0040'

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m

def row_for(path):
    with open(path) as f:
        for line in f:
            r=json.loads(line)
            if r.get('id')==RID: return r
    raise RuntimeError('0040 not found')

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--seconds',type=float,default=180.0); a=ap.parse_args()
    m=load(SOLVER,'mg_hybrid'); row=row_for(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':100000,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits); s=engine.search
    def expand_term(t):
        if t[0]=='var' and t[1] in engine.reverse_constants: return expand_term(engine.reverse_constants[t[1]])
        if t[0]=='op': return ('op',expand_term(t[1]),expand_term(t[2]))
        return t
    def expand_recipe(r,cache=None):
        cache={} if cache is None else cache
        if id(r) in cache: return cache[id(r)]
        ps=tuple(expand_recipe(p,cache) for p in r.parents); data=r.data
        if r.kind=='source':
            sub,rev=data; data=(tuple((k,expand_term(v)) for k,v in sub),rev)
        elif r.kind=='instantiate': data=tuple((k,expand_term(v)) for k,v in data)
        elif r.kind=='congruence': data=(data[0],expand_term(data[1]))
        q=m.Recipe(expand_term(r.lhs),expand_term(r.rhs),r.kind,ps,data); cache[id(r)]=q; return q
    orig=s.critical_pair
    def cp(o,i,oi,ii,path): return orig(expand_recipe(o),expand_recipe(i),oi,ii,path)
    s.critical_pair=cp
    def variants(c):
        o=s.orient(c)
        if o is not None: return [o]
        z=[]
        if c.lhs[0]!='var': z.append(c)
        if c.rhs[0]!='var': z.append(m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
        return z
    def rkey(r): return (s.alpha_signature(r.lhs,r.rhs),r.lhs,r.rhs)
    start=time.monotonic(); phase=max(20.0,min(60.0,a.seconds/3))
    # Phase A: streaming frontier batches, preserving all retained clauses.
    s.deadline=min(engine.deadline,start+phase)
    batch=128
    rounds=0; enumA=0
    while not s.expired() and rounds<3:
        rules=s.rules(); props=[]; complete=True
        for oi,o in enumerate(rules):
            for ii,i in enumerate(rules):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired(): complete=False; break
                    p=s.critical_pair(o,i,oi,ii,path)
                    if p is None: continue
                    p=s.interreduce(p,rules); props.append((s.target_score(p),p)); enumA+=1
                    if len(props)>=batch:
                        props.sort(key=lambda x:x[0]); added=0
                        for _,q in props:
                            if s.add_clause(q): s.superpositions+=1; added+=1
                            if added>=64: break
                        props=[]; rules=s.rules()
                if not complete: break
            if not complete: break
        if props:
            props.sort(key=lambda x:x[0]); added=0
            for _,q in props:
                if s.add_clause(q): s.superpositions+=1; added+=1
                if added>=64: break
        rounds+=1
        if not complete: break
    frontier_count=len(s.clauses)
    # Phase B: reset deadline and run incremental given-clause from the shared pool.
    s.deadline=engine.deadline
    pending=[]; queued=set(); processed=set(); active=[]
    def enqueue(r):
        k=rkey(r)
        if k in queued or k in processed: return
        queued.add(k); pending.append(r)
    for r in s.rules(): enqueue(r)
    given_steps=0; enumB=0; recipe=s.target_proof(s.rules())
    while recipe is None and pending and not s.expired():
        pending.sort(key=s.target_score); g=pending.pop(0); k=rkey(g); queued.discard(k)
        if k in processed: continue
        processed.add(k); given_steps+=1
        rules=s.rules(); props=[]
        for partner in active:
            for o,i in ((g,partner),(partner,g)):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired(): break
                    p=s.critical_pair(o,i,given_steps,given_steps+1,path)
                    if p is None: continue
                    p=s.interreduce(p,rules); props.append((s.target_score(p),p)); enumB+=1
                if s.expired(): break
            if s.expired(): break
        if not s.expired():
            for path in m.nonvariable_positions(g.lhs,maximum_depth=12,include_root=True):
                p=s.critical_pair(g,g,given_steps,given_steps+1,path)
                if p is not None: props.append((s.target_score(p),s.interreduce(p,rules))); enumB+=1
        props.sort(key=lambda x:x[0]); added=0
        for _,p in props:
            before=len(s.clauses)
            if s.add_clause(p):
                s.superpositions+=1; added+=1
                for c in s.clauses[before:]:
                    for r in variants(c): enqueue(r)
                if added>=64: break
        active.append(g); recipe=s.target_proof(s.rules())
    out={'id':RID,'found_recipe':bool(recipe),'frontier_clauses':frontier_count,'final_clauses':len(s.clauses),'frontier_rounds':rounds,'given_steps':given_steps,'enumerated_frontier':enumA,'enumerated_given':enumB,'seconds':time.monotonic()-start,'target_hit':False,'replay':False,'proof_nodes':None}
    if recipe:
        rr=engine.inline_recipe(recipe)
        if (rr.lhs,rr.rhs)==(target[1],target[0]): rr=m.Recipe(rr.rhs,rr.lhs,'symmetry',(rr,))
        nodes,root=s.compile(rr); out['target_hit']=(nodes[root].lhs,nodes[root].rhs)==target[:2]; out['replay']=bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000)); out['proof_nodes']=len(nodes)
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('HYBRID_POOL_CLOSURE',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
