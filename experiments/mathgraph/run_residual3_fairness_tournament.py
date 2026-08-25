#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
RESIDUAL_IDS={'hard1_0067','hard2_0107','hard3_0208'}
SCHEDULES=(('target_only',None),('target7_age1',7),('target3_age1',3),('target1_age1',1))

# Reuse the already validated Vampire parser / canonicalizer.
sys.path.insert(0,str(Path(__file__).resolve().parent))
import run_residual3_fullpath_lifecycle as fp


def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796fair',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m


def all_rows():
    rows=[]
    for split in ('hard1','hard2','hard3'):
        for line in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line); rows.append(r)
    return rows


def oriented_variants(m,c):
    if c.lhs==c.rhs: return (c,)
    return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))


def trace_schedule(m,source,target,wanted,ratio,seconds):
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits); search=eng.search
    passive=list(search.clauses); active=[]; age={id(c):i for i,c in enumerate(passive)}; next_age=len(passive); given=0
    selected_keys=set(); age_picks=0; target_picks=0
    while passive and given<1024 and not search.expired():
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        use_age=(ratio is not None and given>0 and (given % (ratio+1)==ratio))
        if use_age:
            idx=min(range(len(passive)),key=lambda i:age.get(id(passive[i]),10**18)); age_picks+=1
        else:
            idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18))); target_picks+=1
        selected=passive.pop(idx); selected_keys.add(fp.clause_key(selected))
        selected=search.interreduce(selected,rules); active.append(selected); given+=1
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        proposals=[]
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(oriented_variants(m,bo)):
                    for iside,inner in enumerate(oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is None: continue
                            qr=search.interreduce(q,rules); proposals.append((search.target_score(qr),qr))
        proposals.sort(key=lambda x:x[0])
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q):
                passive.append(q); age[id(q)]=next_age; next_age+=1
        new=[]; seen=set()
        for c in passive:
            if search.expired(): break
            c=search.interreduce(c,rules)
            names={}; a=(m.alpha_canonical_term(c.lhs,names),m.alpha_canonical_term(c.rhs,names)); names={}; b=(m.alpha_canonical_term(c.rhs,names),m.alpha_canonical_term(c.lhs,names)); kk=min(a,b)
            if kk in seen: continue
            seen.add(kk); new.append(c)
        passive=new
    covered=sum(1 for k in wanted if k in selected_keys)
    return {'covered':covered,'total':len(wanted),'coverage':covered/len(wanted) if wanted else 0.0,'given':given,'age_picks':age_picks,'target_picks':target_picks}


def vampire_for_row(m,r):
    try:
        source,target,path=fp.vampire_path(m,r)
    except Exception:
        return None
    return source,target,path


def main():
    td,m=load_solver(); rows=all_rows(); byid={r['id']:r for r in rows}; out={'residuals':[],'protected':[],'summary':{}}
    try:
        # Full residual tournament.
        for rid in sorted(RESIDUAL_IDS):
            r=byid[rid]; got=vampire_for_row(m,r)
            if got is None: continue
            source,target,path=got; wanted={x['key'] for x in path}
            sched={}
            for name,ratio in SCHEDULES:
                sched[name]=trace_schedule(m,source,target,wanted,ratio,20.0)
            rec={'id':rid,'vampire_derived':len(wanted),'schedules':sched}; out['residuals'].append(rec)
            print('FAIRNESS_RESIDUAL',json.dumps(rec,sort_keys=True),flush=True)

        # Regression guard: find up to 9 additional TRUE hard cases whose Vampire path
        # baseline is already completely selected in a short run; then test fairness.
        candidates=[r for r in rows if r.get('answer') is True and r['id'] not in RESIDUAL_IDS]
        protected=[]
        for r in candidates:
            if len(protected)>=9: break
            got=vampire_for_row(m,r)
            if got is None: continue
            source,target,path=got; wanted={x['key'] for x in path}
            if not wanted or len(wanted)>20: continue
            base=trace_schedule(m,source,target,wanted,None,4.0)
            if base['covered']!=base['total']: continue
            sched={'target_only':base}
            for name,ratio in SCHEDULES[1:]:
                sched[name]=trace_schedule(m,source,target,wanted,ratio,4.0)
            rec={'id':r['id'],'vampire_derived':len(wanted),'schedules':sched}; protected.append(rec); out['protected'].append(rec)
            print('FAIRNESS_PROTECTED',json.dumps(rec,sort_keys=True),flush=True)

        summary={}
        for name,_ in SCHEDULES:
            residual_cov=sum(x['schedules'][name]['covered'] for x in out['residuals'])
            residual_total=sum(x['schedules'][name]['total'] for x in out['residuals'])
            regressions=sum(1 for x in protected if x['schedules'][name]['covered']<x['schedules']['target_only']['covered'])
            protected_delta=sum(x['schedules'][name]['covered']-x['schedules']['target_only']['covered'] for x in protected)
            summary[name]={'residual_covered':residual_cov,'residual_total':residual_total,'protected_cases':len(protected),'protected_regressions':regressions,'protected_delta_selected':protected_delta}
        out['summary']=summary
        print('FAIRNESS_SUMMARY',json.dumps(summary,sort_keys=True),flush=True)
    finally:
        td.cleanup()
    p=ROOT/'experiments/mathgraph/results/residual3-fairness-tournament.json'; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
