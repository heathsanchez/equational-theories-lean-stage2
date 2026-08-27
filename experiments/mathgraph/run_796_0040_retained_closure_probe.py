#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'; RID='evaluation_normal_0040'
HELPER_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
IDS=('f95','f123','f126','f130','f148','f150','f196','f217','f229','f231','f244','f258','f259','f278')

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--seconds',type=float,default=120); ap.add_argument('--closure-seconds',type=float,default=60); ap.add_argument('--batch',type=int,default=128); a=ap.parse_args()
    m=load(SOLVER,'mg_closure_probe'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg_closure_helper'); row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
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
            elif fid in IDS:
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        wanted_sig={fid:alpha_sig(rigid,*eq) for fid,eq in wanted.items()}; reverse={sig:fid for fid,sig in wanted_sig.items()}
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits); search=engine.search; original_cp=search.critical_pair
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
        def cp(outer,inner,oi,ii,path): return original_cp(expand_recipe(outer),expand_recipe(inner),oi,ii,path)
        search.critical_pair=cp
        def flush(props):
            if not props: return 0
            props.sort(key=lambda x:x[0]); added=0
            for _,p in props:
                if search.add_clause(p):
                    search.superpositions+=1; added+=1
                    if added>=limits['new_clauses_per_round']: break
            return added
        def solve_stream():
            for ri in range(limits['maximum_rounds']):
                search.rounds=ri+1; rules=search.rules(); goal=search.target_proof(rules)
                if goal is not None:return goal
                snap=rules; props=[]; added=0
                for oi,o in enumerate(snap):
                    for ii,i in enumerate(snap):
                        for path in m.nonvariable_positions(o.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                            if search.expired(): flush(props); return search.target_proof(search.rules())
                            p=search.critical_pair(o,i,oi,ii,path)
                            if p is None: continue
                            p=search.interreduce(p,rules); props.append((search.target_score(p),p))
                            if len(props)>=a.batch:
                                added+=flush(props); props=[]
                                g=search.target_proof(search.rules())
                                if g is not None:return g
                added+=flush(props)
                if not added: break
            return search.target_proof(search.rules())
        solve_stream()
        def inline_sig(r):
            try:return alpha_sig(rigid,h.inline_engine_names(r.lhs,engine.reverse_constants),h.inline_engine_names(r.rhs,engine.reverse_constants))
            except Exception:return None
        retained={fid:[] for fid in IDS}
        for idx,c in enumerate(search.clauses):
            fid=reverse.get(inline_sig(c))
            if fid: retained[fid].append(idx)
        before={fid:len(v) for fid,v in retained.items()}; reached={fid:[] for fid in IDS}; closure_deadline=time.monotonic()+a.closure_seconds; rules=search.rules(); tested=0
        for oi,o in enumerate(rules):
            if time.monotonic()>=closure_deadline: break
            for ii,i in enumerate(rules):
                if time.monotonic()>=closure_deadline: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                    if time.monotonic()>=closure_deadline: break
                    p=search.critical_pair(o,i,oi,ii,path); tested+=1
                    if p is None: continue
                    p=search.interreduce(p,rules); fid=reverse.get(inline_sig(p))
                    if fid and len(reached[fid])<5: reached[fid].append({'outer':oi,'inner':ii,'path':list(path),'score':search.target_score(p)})
        out={'id':RID,'search_seconds':a.seconds,'closure_seconds':a.closure_seconds,'clauses':len(search.clauses),'rounds':search.rounds,'retained_before':before,'closure_tested':tested,'one_step_reached':reached,'closure_timed_out':time.monotonic()>=closure_deadline}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('RETAINED_CLOSURE_PROBE',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__': main()
