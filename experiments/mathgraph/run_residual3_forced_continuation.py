#!/usr/bin/env python3
import importlib.util, json, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
FP=ROOT/'experiments/mathgraph/run_residual3_fullpath_lifecycle.py'
spec=importlib.util.spec_from_file_location('fullpath',FP)
F=importlib.util.module_from_spec(spec); spec.loader.exec_module(F)


def trace_all(m,source,target,wanted,seconds=20.0,force_key=None):
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits); search=eng.search
    passive=list(search.clauses); active=[]; age={id(c):i for i,c in enumerate(passive)}; next_age=len(passive); given=0; forced=False
    hits={k:{'raw':False,'post_interreduce':False,'best_rank':None,'topk':False,'add_clause':False,'passive':False,'selected':False,'first_seen_given':None,'selected_given':None} for k in wanted}
    while passive and given<1024 and not search.expired():
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        idx=None
        if force_key is not None and not forced:
            for i,c in enumerate(passive):
                if F.clause_key(c)==force_key:
                    idx=i; forced=True; break
        if idx is None:
            idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        selected=passive.pop(idx); sk=F.clause_key(selected)
        if sk in hits:
            hits[sk]['selected']=True
            if hits[sk]['selected_given'] is None: hits[sk]['selected_given']=given
        selected=search.interreduce(selected,rules); active.append(selected); given+=1
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        proposals=[]
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(F.oriented_variants(m,bo)):
                    for iside,inner in enumerate(F.oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is None: continue
                            k0=F.clause_key(q)
                            if k0 in hits:
                                hits[k0]['raw']=True
                                if hits[k0]['first_seen_given'] is None: hits[k0]['first_seen_given']=given
                            qr=search.interreduce(q,rules); k1=F.clause_key(qr)
                            if k1 in hits: hits[k1]['post_interreduce']=True
                            proposals.append((search.target_score(qr),qr))
        proposals.sort(key=lambda x:x[0])
        rankmap={}
        for i,(_,q) in enumerate(proposals):
            k=F.clause_key(q)
            if k in hits and k not in rankmap: rankmap[k]=i
        for k,mr in rankmap.items():
            h=hits[k]; h['best_rank']=mr if h['best_rank'] is None else min(h['best_rank'],mr)
            if mr<search.limits['new_clauses_per_round']: h['topk']=True
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            k=F.clause_key(q); ok=search.add_clause(q)
            if ok:
                if k in hits: hits[k]['add_clause']=True
                passive.append(q); age[id(q)]=next_age; next_age+=1
        pkeys={F.clause_key(c) for c in passive}
        for k in hits:
            if k in pkeys: hits[k]['passive']=True
        new=[]; seen=set()
        for c in passive:
            if search.expired(): break
            c=search.interreduce(c,rules)
            names={}; a=(m.alpha_canonical_term(c.lhs,names),m.alpha_canonical_term(c.rhs,names)); names={}; b=(m.alpha_canonical_term(c.rhs,names),m.alpha_canonical_term(c.lhs,names)); kk=min(a,b)
            if kk in seen: continue
            seen.add(kk); new.append(c)
        passive=new
    return hits,given,forced


def status(h): return F.status(h)


def main():
    td,m=F.load_solver(); rows=[]
    try:
        for r in F.rows():
            source,target,path=F.vampire_path(m,r); wanted={x['key'] for x in path}
            base,g0,_=trace_all(m,source,target,wanted)
            first=None
            for x in path:
                if status(base[x['key']])!='selected': first=x; break
            force_key=first['key'] if first is not None and status(base[first['key']])=='passive-unselected' else None
            alt,g1,forced=trace_all(m,source,target,wanted,force_key=force_key)
            bsel=sum(status(base[x['key']])=='selected' for x in path)
            asel=sum(status(alt[x['key']])=='selected' for x in path)
            rec={'id':r['id'],'vampire_derived':len(path),'baseline_selected':bsel,'forced_selected':asel,'delta_selected':asel-bsel,'force_applied':forced,'first_unavailable_index':None if first is None else first['index'],'first_unavailable_status':None if first is None else status(base[first['key']]),'baseline_given':g0,'forced_given':g1}
            print('FORCED_CONTINUATION',json.dumps(rec,sort_keys=True),flush=True); rows.append(rec)
    finally: td.cleanup()
    p=ROOT/'experiments/mathgraph/results/residual3-forced-continuation.json'; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps({'rows':rows},indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
