#!/usr/bin/env python3
from __future__ import annotations
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions' / 'mathgraph' / 'solver.py'
spec = importlib.util.spec_from_file_location('mg796exact', SOLVER)
m = importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)

def load_row(path: Path):
    for i,line in enumerate(path.read_text().splitlines()):
        if not line.strip(): continue
        r=json.loads(line); rid=r.get('id') or f'evaluation_normal_{i:04d}'
        if rid=='evaluation_normal_0040': return r
    raise RuntimeError('0040 not found')

def fields(r):
    a=r.get('equation1') or r.get('equation_1') or r.get('source') or r.get('hypothesis')
    b=r.get('equation2') or r.get('equation_2') or r.get('target') or r.get('conclusion')
    return a,b

def exact_recipe(search, maximum_given=512, focus_per_age=4):
    passive=list(search.clauses); active=[]; age={id(c):i for i,c in enumerate(passive)}; next_age=len(passive); given=0
    snapshots=[]
    while passive and given < maximum_given and not search.expired():
        rules=[r for c in active if (r:=search.orient(c)) is not None]
        goal=search.target_proof(rules)
        if goal is not None: return goal,snapshots
        if given % (focus_per_age+1) == focus_per_age:
            index=min(range(len(passive)), key=lambda i: age.get(id(passive[i]),10**18))
            pick='age'
        else:
            index=min(range(len(passive)), key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
            pick='focus'
        selected=passive.pop(index)
        reduced=search.interreduce(selected,rules)
        if reduced.lhs != selected.lhs or reduced.rhs != selected.rhs:
            search.add_clause(reduced); selected=reduced
        active.append(selected); given += 1
        rules=[r for c in active if (r:=search.orient(c)) is not None]
        goal=search.target_proof(rules)
        if goal is not None: return goal,snapshots
        proposals=[]
        for other_index,other in enumerate(active):
            for outer,inner,oi,ii in ((selected,other,given,other_index),(other,selected,other_index,given)):
                for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                    if search.expired(): break
                    q=search.critical_pair(outer,inner,oi,ii,path)
                    if q is None: continue
                    q=search.interreduce(q,rules)
                    proposals.append((search.target_score(q),q))
        proposals.sort(key=lambda x:x[0])
        added=0
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q):
                search.superpositions += 1; passive.append(q); age[id(q)]=next_age; next_age += 1; added += 1
        new_passive=[]; seen=set(); changed=0
        for clause in passive:
            if search.expired(): break
            reduced=search.interreduce(clause,rules)
            if reduced.lhs != clause.lhs or reduced.rhs != clause.rhs:
                changed += 1
                if search.add_clause(reduced): age[id(reduced)]=age.get(id(clause),next_age); next_age += 1
                clause=reduced
            names={}; a=(m.alpha_canonical_term(clause.lhs,names),m.alpha_canonical_term(clause.rhs,names))
            names={}; b=(m.alpha_canonical_term(clause.rhs,names),m.alpha_canonical_term(clause.lhs,names)); k=min(a,b)
            if k in seen: continue
            seen.add(k); new_passive.append(clause)
        passive=new_passive
        if given<=10 or given%25==0:
            snap={'given':given,'pick':pick,'active':len(active),'passive':len(passive),'proposals':len(proposals),'added':added,'passive_changed':changed,'superpositions':search.superpositions}
            snapshots.append(snap); print('EXACT0040_STEP',json.dumps(snap,sort_keys=True),flush=True)
    rules=[r for c in active if (r:=search.orient(c)) is not None]
    return search.target_proof(rules),snapshots

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--normal',required=True); ap.add_argument('--seconds',type=float,default=30); ap.add_argument('--output',required=True); a=ap.parse_args()
    row=load_row(Path(a.normal)); e1,e2=fields(row); source=m.parse_equation(e1); target=m.parse_equation(e2)
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits)
    recipe,snaps=exact_recipe(eng.search)
    out={'id':'evaluation_normal_0040','recipe_found':recipe is not None,'snapshots':snaps,'clauses':len(eng.search.clauses),'superpositions':eng.search.superpositions}
    if recipe is not None:
        try:
            rr=eng.inline_recipe(recipe); comp=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+5,eng.search.limits); nodes,root=comp.compile(rr)
            out['compiled']=True; out['root_matches']=(nodes[root].lhs,nodes[root].rhs)==target[:2]; out['replayed']=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)); out['proof_nodes']=len(nodes)
        except Exception as exc:
            out['compile_error']=type(exc).__name__+': '+str(exc)
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('EXACT0040_SUMMARY',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
