#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'
HELPER_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'
IDS=('f95','f123','f126','f130','f148','f150','f196','f217','f229','f231','f244','f258','f259','f278')

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--seconds',type=float,default=120.0); a=ap.parse_args()
    m=load(SOLVER,'mg0040census'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg0040censushelper'); row=h.load_row(a.input)
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
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
        wanted_sig={fid:alpha_sig(rigid,*eq) for fid,eq in wanted.items()}
        reverse={sig:fid for fid,sig in wanted_sig.items()}
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits)
        search=engine.search
        events={fid:{'raw_cp':0,'post_interreduce':0,'add_attempt':0,'retained':0,'first_round':None} for fid in IDS}
        current_round=[0]
        def inline_pair(r): return (h.inline_engine_names(r.lhs,engine.reverse_constants),h.inline_engine_names(r.rhs,engine.reverse_constants))
        def hit(r,stage):
            try: sig=alpha_sig(rigid,*inline_pair(r))
            except Exception: return
            fid=reverse.get(sig)
            if fid:
                events[fid][stage]+=1
                if events[fid]['first_round'] is None: events[fid]['first_round']=current_round[0]
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
        original_cp=search.critical_pair; original_inter=search.interreduce; original_add=search.add_clause
        def cp(outer,inner,oi,ii,path):
            q=original_cp(expand_recipe(outer),expand_recipe(inner),oi,ii,path)
            if q is not None: hit(q,'raw_cp')
            return q
        def inter(q,rules):
            out=original_inter(q,rules); hit(out,'post_interreduce'); return out
        def add(q):
            hit(q,'add_attempt'); before=len(search.clauses); ok=original_add(q)
            if ok and len(search.clauses)>before: hit(search.clauses[-1],'retained')
            return ok
        search.critical_pair=cp; search.interreduce=inter; search.add_clause=add
        # Re-adding the already-created initial clauses through instrumentation is unnecessary.
        # Infer round numbers from calls to rules(): solve calls rules once at each round head.
        original_rules=search.rules
        def rules():
            current_round[0]+=1
            return original_rules()
        search.rules=rules
        start=time.monotonic(); recipe=search.solve(); elapsed=time.monotonic()-start
        retained=[]
        for fid,sig in wanted_sig.items():
            count=sum(1 for c in search.clauses if alpha_sig(rigid,*inline_pair(c))==sig)
            if count: retained.append(fid); events[fid]['retained']=max(events[fid]['retained'],count)
        out={'id':RID,'found_recipe':bool(recipe),'seconds':elapsed,'rounds':search.rounds,'clauses':len(search.clauses),'generated':search.generated,'superpositions':search.superpositions,'reductions':search.reductions,'events':events,'retained_corridor':retained,'first_missing_stage':None}
        for fid in IDS:
            e=events[fid]
            if e['raw_cp']==0: out['first_missing_stage']={'fid':fid,'stage':'generation'}; break
            if e['post_interreduce']==0: out['first_missing_stage']={'fid':fid,'stage':'interreduce'}; break
            if e['retained']==0: out['first_missing_stage']={'fid':fid,'stage':'retention'}; break
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
        print('SEARCH_CORRIDOR_CENSUS',json.dumps(out,sort_keys=True),flush=True)
    finally:
        hp.unlink(missing_ok=True)
if __name__=='__main__': main()
