#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'; RID='evaluation_normal_0040'
HELPER_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--frontier-seconds',type=float,default=120); ap.add_argument('--given-seconds',type=float,default=10); a=ap.parse_args()
    m=load(SOLVER,'mg_cross_portfolio'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg_cross_helper'); row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        defs={}; wanted={}
        for block in h.fof_blocks(proof):
            q=h.parse_fof(block)
            if not q: continue
            fid,kind,formula,_=q
            try: eq=h.formula_equality(formula)
            except Exception: eq=None
            if eq is None: continue
            x,y=eq
            if kind=='definition':
                if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
                elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
            elif fid in {'f217','f258','f259'}:
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        wsig={k:alpha_sig(rigid,*v) for k,v in wanted.items()}
        base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        def setup(seconds):
            lim=dict(base); lim['seconds']=seconds
            eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,lim); s=eng.search; orig=s.critical_pair
            def expand_term(t):
                if t[0]=='var' and t[1] in eng.reverse_constants: return expand_term(eng.reverse_constants[t[1]])
                if t[0]=='op': return ('op',expand_term(t[1]),expand_term(t[2]))
                return t
            def expand_recipe(r,cache=None):
                cache={} if cache is None else cache
                if id(r) in cache:return cache[id(r)]
                ps=tuple(expand_recipe(p,cache) for p in r.parents); data=r.data
                if r.kind=='source':
                    sub,rev=data; data=(tuple((k,expand_term(v)) for k,v in sub),rev)
                elif r.kind=='instantiate': data=tuple((k,expand_term(v)) for k,v in data)
                elif r.kind=='congruence': data=(data[0],expand_term(data[1]))
                q=m.Recipe(expand_term(r.lhs),expand_term(r.rhs),r.kind,ps,data); cache[id(r)]=q; return q
            s.critical_pair=lambda o,i,oi,ii,path: orig(expand_recipe(o),expand_recipe(i),oi,ii,path)
            def inline_pair(r): return (h.inline_engine_names(r.lhs,eng.reverse_constants),h.inline_engine_names(r.rhs,eng.reverse_constants))
            def match(r,fid): return alpha_sig(rigid,*inline_pair(r))==wsig[fid]
            return eng,s,orig,expand_recipe,match
        # Independent frontier search, stop as soon as f217 is retained.
        ef,sf,origf,expf,matchf=setup(a.frontier_seconds); f217=None; enumf=0; rounds=0; batch=128
        for ri in range(128):
            rounds=ri+1; rules=sf.rules(); snap=rules; props=[]; stop=False
            for oi,o in enumerate(snap):
                for ii,i in enumerate(snap):
                    for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                        if sf.expired(): stop=True; break
                        p=sf.critical_pair(o,i,oi,ii,path)
                        if p is None: continue
                        p=sf.interreduce(p,rules); props.append((sf.target_score(p),p)); enumf+=1
                        if len(props)>=batch:
                            props.sort(key=lambda x:x[0]); added=0
                            for _,q in props:
                                before=len(sf.clauses)
                                if sf.add_clause(q):
                                    sf.superpositions+=1; added+=1
                                    for c in sf.clauses[before:]:
                                        if matchf(c,'f217') and f217 is None:f217=c
                                    if f217 is not None or added>=64:break
                            props=[]; rules=sf.rules()
                            if f217 is not None: stop=True; break
                    if stop:break
                if stop:break
            if f217 is not None or sf.expired():break
        # Independent given-clause search, stop as soon as f258 is retained.
        eg,sg,origg,expg,matchg=setup(a.given_seconds)
        def variants(s,c):
            o=s.orient(c)
            if o is not None:return [o]
            z=[]
            if c.lhs[0]!='var':z.append(c)
            if c.rhs[0]!='var':z.append(m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
            return z
        def rkey(s,r):return (s.alpha_signature(r.lhs,r.rhs),r.lhs,r.rhs)
        pending=[]; queued=set(); processed=set(); active=[]
        def enqueue(r):
            k=rkey(sg,r)
            if k in queued or k in processed:return
            queued.add(k); pending.append(r)
        for r in sg.rules():enqueue(r)
        f258=None; givens=0; enumg=0
        while pending and not sg.expired() and f258 is None:
            pending.sort(key=sg.target_score); g=pending.pop(0); k=rkey(sg,g); queued.discard(k)
            if k in processed:continue
            processed.add(k); givens+=1; rules=sg.rules(); props=[]
            pairings=[]
            for p in active:
                pairings.append((g,p)); pairings.append((p,g))
            pairings.append((g,g))
            for oi,(o,i) in enumerate(pairings):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if sg.expired():break
                    q=sg.critical_pair(o,i,oi,oi+1,path)
                    if q is None:continue
                    q=sg.interreduce(q,rules); props.append((sg.target_score(q),q)); enumg+=1
                if sg.expired():break
            props.sort(key=lambda x:x[0]); added=0
            for _,q in props:
                before=len(sg.clauses)
                if sg.add_clause(q):
                    sg.superpositions+=1; added+=1
                    for c in sg.clauses[before:]:
                        if matchg(c,'f258') and f258 is None:f258=c
                        for r in variants(sg,c):enqueue(r)
                    if f258 is not None or added>=64:break
            active.append(g)
        # Cross-portfolio bridge: no Vampire IDs used in search, only to label the diagnostic target.
        def orient(c,rev):return c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        bridge=None; details=[]
        if f217 is not None and f258 is not None:
            # Parents are source-grounded recipes from identical source/target engines; expand with frontier naming.
            for A,B,label in ((f258,f217,'258x217'),(f217,f258,'217x258')):
                A=expf(A); B=expf(B)
                for ar in (False,True):
                    aa=orient(A,ar)
                    for br in (False,True):
                        bb=orient(B,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                            q=origf(aa,bb,0,1,path)
                            if q is None or not matchf(q,'f259'):continue
                            nodes,root=sf.compile(ef.inline_recipe(q)); ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000))
                            details.append({'order':label,'left_rev':ar,'right_rev':br,'path':list(path),'replay':ok,'nodes':len(nodes)})
                            if ok:bridge=q;break
                        if bridge:break
                    if bridge:break
                if bridge:break
        out={'id':RID,'frontier_f217':f217 is not None,'frontier_rounds':rounds,'frontier_enumerated':enumf,'frontier_clauses':len(sf.clauses),'given_f258':f258 is not None,'given_steps':givens,'given_enumerated':enumg,'given_clauses':len(sg.clauses),'cross_f259':bridge is not None,'cross_details':details}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('CROSS_PORTFOLIO_BRIDGE',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__':main()
