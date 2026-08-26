#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
EXCLUDE='evaluation_normal_0040'

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def load_row_any(rid,normal_input,hard_input,h):
    errs=[]
    for label,path in (('normal',normal_input),('hard',hard_input)):
        try:
            return h.load_row(path,rid),label
        except RuntimeError as exc:
            errs.append(f'{label}:{exc}')
    raise RuntimeError(f'row missing in both inputs for {rid}: {errs}')

def run_one(rid,normal_input,hard_input,m,h):
    row,dataset=load_row_any(rid,normal_input,hard_input,h)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':45.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    warm_deadline=time.monotonic()+6.0; warm_lim=dict(lim); warm_lim['seconds']=6.0
    e=m.TargetGroundedRefutation(source,target,warm_deadline,warm_lim); warm=e.solve(); r=m.RigidSuperpositionModule()
    out={'id':rid,'dataset':dataset,'warm_found':bool(warm),'oracle_free':True,'policy':'fair-pair-coverage-before-expansion','frozen_from_0040':True}
    if warm:
        nodes,root=warm; out.update(found=True,phase='warm',proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000))); return out
    deadline=time.monotonic()+45.0; e.deadline=deadline
    if hasattr(e.search,'deadline'): e.search.deadline=deadline
    if hasattr(e.search,'seconds'): e.search.seconds=45.0
    target_terms=[]
    for side in target[:2]: target_terms.extend(m.walk_subterms(side))
    def inline(t): return h.inline_engine_names(t,e.reverse_constants)
    def score(c):
        x,y=inline(c.lhs),inline(c.rhs); d=min([m.structural_distance(x,t) for t in target_terms]+[m.structural_distance(y,t) for t in target_terms])
        return (d,max(m.term_size(x),m.term_size(y)),m.term_size(x)+m.term_size(y),m.render_term(x),m.render_term(y))
    def orientations(c): return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
    def cps(a0,b0,cap=1):
        made=[]
        for aa in orientations(a0):
            for bb in orientations(b0):
                for outer,inner in ((aa,bb),(bb,aa)):
                    for path in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
                        p=e.search.critical_pair(outer,inner,0,1,path)
                        if p is not None: made.append(p)
                        if len(made)>=cap: return made
        return made
    retained=list(e.search.clauses); out['initial_clauses']=len(retained)
    candidates=[]
    for c in list(retained):
        if time.monotonic()>=deadline: break
        candidates.extend(cps(c,c,cap=12))
    candidates=sorted(candidates,key=score)[:256]; frontier=[]
    for p in candidates:
        if e.search.add_clause(p): frontier.append(p); retained.append(p)
    out['bootstrap']={'selected':len(candidates),'added':len(frontier)}; out['round_stats']=[]
    for rnd in range(1,9):
        if time.monotonic()>=deadline or not frontier: break
        fs=sorted(frontier,key=score)[:96]; bank=sorted(retained,key=score)[:320]; raw=[]; pair_attempts=0; fair_complete=True
        for f in fs:
            for b in bank:
                if time.monotonic()>=deadline: fair_complete=False; break
                raw.extend(cps(f,b,cap=1)); pair_attempts+=1
            if not fair_complete: break
        expansion_attempts=0
        if fair_complete:
            for f in fs:
                for b in bank:
                    if time.monotonic()>=deadline or len(raw)>=12000: break
                    more=cps(f,b,cap=4)
                    if len(more)>1: raw.extend(more[1:])
                    expansion_attempts+=1
                if time.monotonic()>=deadline or len(raw)>=12000: break
        ranked=sorted(raw,key=score)[:1024]; new=[]
        for p in ranked:
            if e.search.add_clause(p): new.append(p); retained.append(p)
        out['round_stats'].append({'round':rnd,'frontier_in':len(frontier),'bank':len(bank),'fair_complete':fair_complete,'pair_attempts':pair_attempts,'expansion_attempts':expansion_attempts,'raw':len(raw),'selected':len(ranked),'added':len(new),'clauses':len(e.search.clauses)})
        frontier=new
    finish_deadline=time.monotonic()+10.0; e.deadline=finish_deadline
    if hasattr(e.search,'deadline'): e.search.deadline=finish_deadline
    if hasattr(e.search,'seconds'): e.search.seconds=10.0
    found=e.solve()
    if found:
        nodes,root=found; out.update(found=True,phase='finish',proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)))
    else: out.update(found=False,phase='finish',replay_ok=False)
    return out

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--normal-input',required=True); ap.add_argument('--hard-input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load(SOLVER,'mg_six_transfer'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_six_transfer')
    trace=json.load(urllib.request.urlopen(TRACE_URL)); ids=[x['id'] for x in trace['rows'] if x['id']!=EXCLUDE]
    rows=[]
    for rid in ids:
        res=run_one(rid,a.normal_input,a.hard_input,m,h); rows.append(res); print('SIX_TRUE_FAIR_PAIR_CASE',json.dumps(res,sort_keys=True),flush=True)
    out={'policy':'fair-pair-coverage-before-expansion','frozen_from_0040':True,'excluded_calibration_case':EXCLUDE,'attempted':len(rows),'solved':sum(bool(x.get('found')) for x in rows),'intervention_solved':sum(bool(x.get('found')) and x.get('phase')=='finish' for x in rows),'warm_solved':sum(bool(x.get('found')) and x.get('phase')=='warm' for x in rows),'replay_ok':sum(bool(x.get('replay_ok')) for x in rows),'rows':rows}
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('SIX_TRUE_FAIR_PAIR_TRANSFER',json.dumps({k:out[k] for k in ('attempted','solved','intervention_solved','warm_solved','replay_ok')},sort_keys=True),flush=True)
if __name__=='__main__': main()
