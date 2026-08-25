#!/usr/bin/env python3
from __future__ import annotations
import json, time
from pathlib import Path
import run_residual3_fairness_proof_sweep as base

OUT=Path(__file__).parent/'results/continuation-priority-window.json'
WINDOWS=(0,2,4,8)
RATIO=7
RESIDUAL=base.RESIDUAL_IDS
PROTECTED=base.PROTECTED_IDS

def ckey(m,c):
    names={}; a=(m.alpha_canonical_term(c.lhs,names),m.alpha_canonical_term(c.rhs,names))
    names={}; b=(m.alpha_canonical_term(c.rhs,names),m.alpha_canonical_term(c.lhs,names))
    return min(a,b)

def search_with_window(m,search,window,maximum_given=1024):
    passive=list(search.clauses); active=[]
    age={ckey(m,c):i for i,c in enumerate(passive)}; next_age=len(passive)
    continuation=set(); remaining=0
    given=age_picks=target_picks=continuation_picks=proposals_total=accepted_total=0
    while passive and given<maximum_given and not search.expired():
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        goal=search.target_proof(rules)
        if goal is not None:
            return goal,locals_stats()

        # Priority order: bounded descendant continuation > sparse age fairness > target score.
        cand=[i for i,c in enumerate(passive) if remaining>0 and ckey(m,c) in continuation]
        use_age=(given>0 and given%(RATIO+1)==RATIO)
        if cand:
            idx=min(cand,key=lambda i:(search.target_score(passive[i]),age.get(ckey(m,passive[i]),10**18)))
            continuation_picks+=1; remaining-=1
        elif use_age:
            idx=min(range(len(passive)),key=lambda i:age.get(ckey(m,passive[i]),10**18)); age_picks+=1
        else:
            idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(ckey(m,passive[i]),10**18))); target_picks+=1
        selected=passive.pop(idx); selected=search.interreduce(selected,rules); active.append(selected); given+=1
        selected_was_age=use_age and not cand

        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        goal=search.target_proof(rules)
        if goal is not None: return goal,locals_stats()

        proposals=[]
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(base.oriented_variants(m,bo)):
                    for iside,inner in enumerate(base.oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is None: continue
                            qr=search.interreduce(q,rules); proposals.append((search.target_score(qr),qr))
        proposals_total+=len(proposals); proposals.sort(key=lambda x:x[0])
        descendants=set()
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q):
                passive.append(q); k=ckey(m,q); age[k]=next_age; next_age+=1; accepted_total+=1; descendants.add(k)
        if selected_was_age and window>0:
            continuation=descendants; remaining=window

        new=[]; seen=set(); surviving_cont=set()
        for c in passive:
            if search.expired(): break
            c=search.interreduce(c,rules); k=ckey(m,c)
            if k in seen: continue
            seen.add(k); new.append(c)
            if k in continuation: surviving_cont.add(k)
        passive=new; continuation=surviving_cont
    rules=[]
    for c in active:
        q=search.orient(c)
        if q is not None: rules.append(q)
    return search.target_proof(rules),locals_stats()

    
def locals_stats():
        pass

def one(m,r,window,seconds):
    source=m.parse_equation(r['equation1']); target=m.parse_equation(r['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    started=time.monotonic(); eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
    # local stats helper is bound here to avoid any oracle dependence
    def run():
        passive=list(eng.search.clauses); active=[]
        age={ckey(m,c):i for i,c in enumerate(passive)}; next_age=len(passive)
        continuation=set(); remaining=0
        given=age_picks=target_picks=continuation_picks=proposals_total=accepted_total=0
        def stats(): return {'given':given,'age_picks':age_picks,'target_picks':target_picks,'continuation_picks':continuation_picks,'proposals':proposals_total,'accepted':accepted_total}
        while passive and given<1024 and not eng.search.expired():
            rules=[q for c in active if (q:=eng.search.orient(c)) is not None]
            goal=eng.search.target_proof(rules)
            if goal is not None: return goal,stats()
            cand=[i for i,c in enumerate(passive) if remaining>0 and ckey(m,c) in continuation]
            use_age=(given>0 and given%(RATIO+1)==RATIO)
            if cand:
                idx=min(cand,key=lambda i:(eng.search.target_score(passive[i]),age.get(ckey(m,passive[i]),10**18))); continuation_picks+=1; remaining-=1
            elif use_age:
                idx=min(range(len(passive)),key=lambda i:age.get(ckey(m,passive[i]),10**18)); age_picks+=1
            else:
                idx=min(range(len(passive)),key=lambda i:(eng.search.target_score(passive[i]),age.get(ckey(m,passive[i]),10**18))); target_picks+=1
            selected=eng.search.interreduce(passive.pop(idx),rules); active.append(selected); given+=1
            selected_was_age=use_age and not cand
            rules=[q for c in active if (q:=eng.search.orient(c)) is not None]
            goal=eng.search.target_proof(rules)
            if goal is not None: return goal,stats()
            proposals=[]
            for oi,other in enumerate(active):
                for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                    for oside,outer in enumerate(base.oriented_variants(m,bo)):
                        for iside,inner in enumerate(base.oriented_variants(m,bi)):
                            for path in m.nonvariable_positions(outer.lhs,maximum_depth=eng.search.limits['maximum_depth'],include_root=True):
                                if eng.search.expired(): break
                                q=eng.search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                                if q is None: continue
                                qr=eng.search.interreduce(q,rules); proposals.append((eng.search.target_score(qr),qr))
            proposals_total+=len(proposals); proposals.sort(key=lambda x:x[0]); descendants=set()
            for _,q in proposals[:eng.search.limits['new_clauses_per_round']]:
                if eng.search.add_clause(q):
                    passive.append(q); k=ckey(m,q); age[k]=next_age; next_age+=1; accepted_total+=1; descendants.add(k)
            if selected_was_age and window>0: continuation=descendants; remaining=window
            new=[]; seen=set(); surviving=set()
            for c in passive:
                if eng.search.expired(): break
                c=eng.search.interreduce(c,rules); k=ckey(m,c)
                if k in seen: continue
                seen.add(k); new.append(c)
                if k in continuation: surviving.add(k)
            passive=new; continuation=surviving
        rules=[q for c in active if (q:=eng.search.orient(c)) is not None]
        return eng.search.target_proof(rules),stats()
    recipe,stats=run(); found=recipe is not None
    inline_ok=compile_ok=replay_ok=False; nodes_n=None; err=None
    if found:
        try:
            rr=eng.inline_recipe(recipe); inline_ok=rr is not None
            if rr is not None:
                compiler=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+4.0,eng.search.limits); compiled=compiler.compile(rr)
                if compiled is not None:
                    nodes,root=compiled; nodes_n=len(nodes); compile_ok=True; replay_ok=bool(m.replay_dag(source,nodes,root))
        except Exception as e: err=type(e).__name__+': '+str(e)
    return {'window':window,'ratio':RATIO,'recipe_found':found,'inline_ok':inline_ok,'compile_ok':compile_ok,'replay_ok':replay_ok,'proof_nodes':nodes_n,'seconds':round(time.monotonic()-started,4),'error':err,**stats}

def main():
    td,m=base.load_solver(); byid=base.rows(); out={'ratio':RATIO,'windows':WINDOWS,'residuals':[],'protected':[]}
    try:
        for rid in RESIDUAL:
            rec={'id':rid,'runs':{}}
            for w in WINDOWS: rec['runs'][str(w)]=one(m,byid[rid],w,20.0)
            out['residuals'].append(rec); print('CONTINUATION_RESIDUAL',json.dumps(rec,sort_keys=True),flush=True)
        for rid in PROTECTED:
            rec={'id':rid,'runs':{}}
            for w in WINDOWS: rec['runs'][str(w)]=one(m,byid[rid],w,4.0)
            out['protected'].append(rec); print('CONTINUATION_PROTECTED',json.dumps(rec,sort_keys=True),flush=True)
        summary={}
        for w in WINDOWS:
            k=str(w); summary[k]={'residual_replay':sum(int(x['runs'][k]['replay_ok']) for x in out['residuals']),'residual_recipe':sum(int(x['runs'][k]['recipe_found']) for x in out['residuals']),'protected_replay':sum(int(x['runs'][k]['replay_ok']) for x in out['protected']),'protected_recipe':sum(int(x['runs'][k]['recipe_found']) for x in out['protected'])}
        out['summary']=summary; print('CONTINUATION_SUMMARY',json.dumps(summary,sort_keys=True),flush=True)
    finally: td.cleanup()
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
