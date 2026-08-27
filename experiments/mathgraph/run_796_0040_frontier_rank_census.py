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
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--seconds',type=float,default=120); ap.add_argument('--batch',type=int,default=128); a=ap.parse_args()
    m=load(SOLVER,'mg_rank_census'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg_rank_helper')
        row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
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
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits); search=engine.search
        original_cp=search.critical_pair; expansion_calls=0; expansion_changed=0; flushes=0; enumerated=0; completed_rounds=0
        stats={fid:{'generated':0,'batches':0,'best_rank':None,'worst_rank':None,'retained':0,'first_round':None,'scores':[]} for fid in IDS}
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
        def cp(outer,inner,oi,ii,path):
            nonlocal expansion_calls, expansion_changed
            expansion_calls+=1; eo=expand_recipe(outer); ei=expand_recipe(inner)
            if (eo.lhs,eo.rhs,ei.lhs,ei.rhs)!=(outer.lhs,outer.rhs,inner.lhs,inner.rhs): expansion_changed+=1
            return original_cp(eo,ei,oi,ii,path)
        search.critical_pair=cp
        def fid_of(r):
            try:
                p=(h.inline_engine_names(r.lhs,engine.reverse_constants),h.inline_engine_names(r.rhs,engine.reverse_constants))
                return reverse.get(alpha_sig(rigid,*p))
            except Exception: return None
        current_round=[0]
        def flush(proposals):
            nonlocal flushes
            if not proposals: return 0
            flushes+=1; proposals.sort(key=lambda x:x[0])
            seen=set()
            for rank,(score,p) in enumerate(proposals,1):
                fid=fid_of(p)
                if fid:
                    s=stats[fid]; s['generated']+=1; s['scores'].append(score); s['best_rank']=rank if s['best_rank'] is None else min(s['best_rank'],rank); s['worst_rank']=rank if s['worst_rank'] is None else max(s['worst_rank'],rank)
                    if fid not in seen: s['batches']+=1; seen.add(fid)
                    if s['first_round'] is None: s['first_round']=current_round[0]
            added=0
            for rank,(score,p) in enumerate(proposals,1):
                if search.add_clause(p):
                    search.superpositions+=1; added+=1
                    fid=fid_of(search.clauses[-1])
                    if fid: stats[fid]['retained']+=1
                    if added>=limits['new_clauses_per_round']: break
            return added
        def solve():
            nonlocal enumerated, completed_rounds
            for ri in range(limits['maximum_rounds']):
                current_round[0]=ri+1; search.rounds=ri+1; rules=search.rules(); goal=search.target_proof(rules)
                if goal is not None: return goal
                snapshot=rules; proposals=[]; round_added=0; expired=False
                for oi,outer in enumerate(snapshot):
                    for ii,inner in enumerate(snapshot):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                            if search.expired(): expired=True; break
                            p=search.critical_pair(outer,inner,oi,ii,path)
                            if p is None: continue
                            p=search.interreduce(p,rules); proposals.append((search.target_score(p),p)); enumerated+=1
                            if len(proposals)>=a.batch:
                                round_added+=flush(proposals); proposals=[]
                                goal=search.target_proof(search.rules())
                                if goal is not None: return goal
                        if expired: break
                    if expired: break
                round_added+=flush(proposals)
                if expired: return search.target_proof(search.rules())
                completed_rounds+=1
                goal=search.target_proof(search.rules())
                if goal is not None: return goal
                if not round_added or len(search.clauses)>=limits['maximum_clauses']: break
            return search.target_proof(search.rules())
        start=time.monotonic(); recipe=solve(); elapsed=time.monotonic()-start
        for s in stats.values():
            if s['scores']:
                s['best_score']=min(s['scores']); s['worst_score']=max(s['scores'])
            else: s['best_score']=None; s['worst_score']=None
            del s['scores']
        out={'id':RID,'found_recipe':bool(recipe),'seconds':elapsed,'batch':a.batch,'rounds':search.rounds,'completed_rounds':completed_rounds,'clauses':len(search.clauses),'generated':search.generated,'superpositions':search.superpositions,'reductions':search.reductions,'enumerated':enumerated,'flushes':flushes,'expansion_calls':expansion_calls,'expansion_changed':expansion_changed,'corridor':stats}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('FRONTIER_RANK_CENSUS',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__': main()
