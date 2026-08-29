#!/usr/bin/env python3
from pathlib import Path

p=Path('submissions/mathgraph/solver.py')
s=p.read_text()
marker='\ndef run_solo():\n'
if marker not in s: raise SystemExit('run_solo marker missing')
helper=r'''

def _mg_elide_have_types(code):
    out=[]
    for line in code.splitlines():
        if line.lstrip().startswith("have ") and " : " in line and " := " in line:
            left,expr=line.split(" := ",1)
            name,type_text=left.split(" : ",1)
            if name.strip().startswith("have ") and type_text:
                line=name+" := "+expr
        out.append(line)
    return "\n".join(out)+"\n"


def _mg_given_clause_recipe(search, maximum_given=512, focus_per_age=4):
    """Generic active/passive given-clause schedule over existing sound rules."""
    passive=list(search.clauses)
    active=[]
    age={id(c):i for i,c in enumerate(passive)}
    next_age=len(passive)
    given=0
    while passive and given < maximum_given and not search.expired():
        rules=[]
        for clause in active:
            rule=search.orient(clause)
            if rule is not None:
                rules.append(rule)
        goal=search.target_proof(rules)
        if goal is not None:
            return goal
        if given % (focus_per_age+1) == focus_per_age:
            index=min(range(len(passive)),key=lambda i:age.get(id(passive[i]),10**18))
        else:
            index=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        selected=passive.pop(index)
        reduced=search.interreduce(selected,rules)
        if reduced.lhs != selected.lhs or reduced.rhs != selected.rhs:
            search.add_clause(reduced)
            selected=reduced
        active.append(selected)
        given += 1
        rules=[]
        for clause in active:
            rule=search.orient(clause)
            if rule is not None:
                rules.append(rule)
        goal=search.target_proof(rules)
        if goal is not None:
            return goal
        proposals=[]
        for other_index,other in enumerate(active):
            for outer,inner,oi,ii in ((selected,other,given,other_index),(other,selected,other_index,given)):
                for path in nonvariable_positions(outer.lhs,maximum_depth=search.limits["maximum_depth"],include_root=True):
                    if search.expired():
                        break
                    q=search.critical_pair(outer,inner,oi,ii,path)
                    if q is None:
                        continue
                    q=search.interreduce(q,rules)
                    proposals.append((search.target_score(q),q))
        proposals.sort(key=lambda x:x[0])
        for _,q in proposals[:search.limits["new_clauses_per_round"]]:
            if search.add_clause(q):
                search.superpositions += 1
                passive.append(q)
                age[id(q)]=next_age
                next_age += 1
        new_passive=[]
        seen=set()
        for clause in passive:
            if search.expired():
                break
            reduced=search.interreduce(clause,rules)
            if reduced.lhs != clause.lhs or reduced.rhs != clause.rhs:
                if search.add_clause(reduced):
                    age[id(reduced)]=age.get(id(clause),next_age)
                    next_age += 1
                clause=reduced
            names={}
            a=(alpha_canonical_term(clause.lhs,names),alpha_canonical_term(clause.rhs,names))
            names={}
            b=(alpha_canonical_term(clause.rhs,names),alpha_canonical_term(clause.lhs,names))
            k=min(a,b)
            if k in seen:
                continue
            seen.add(k)
            new_passive.append(clause)
        passive=new_passive
    rules=[]
    for clause in active:
        rule=search.orient(clause)
        if rule is not None:
            rules.append(rule)
    return search.target_proof(rules)


def run_given_clause_fallback(source,target,timeout):
    # Runs only after every currently promoted route has abstained.
    seconds=min(15.0,max(0.5,timeout/4.0))
    limits=dict(COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds":seconds,
        "maximum_term_size":65,
        "maximum_replay_term_size":260,
        "maximum_depth":12,
        "maximum_rules":768,
        "maximum_rounds":64,
        "new_clauses_per_round":512,
        "maximum_clauses":12000,
        "normalization_steps":256,
        "maximum_proof_nodes":50000,
    })
    try:
        eng=TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
        recipe=_mg_given_clause_recipe(eng.search)
        if recipe is None:
            return False
        rr=eng.inline_recipe(recipe)
        compiler=CompactSuperposition(sys.modules[__name__],eng.source,eng.target,time.monotonic()+3.0,eng.search.limits)
        nodes,root=compiler.compile(rr)
        if (nodes[root].lhs,nodes[root].rhs) != target[:2]:
            return False
        if not replay_dag(source,nodes,root,maximum_term_size=limits["maximum_replay_term_size"],maximum_nodes=limits["maximum_proof_nodes"]):
            return False
        code,proof_nodes=make_dag_certificate(target,nodes,root)
        code=_mg_elide_have_types(code)
        code_bytes=len(code.encode("utf-8"))
        print("MATHGRAPH_METRICS "+json.dumps({"portfolio":"given-clause-fallback","found":True,"proof_nodes":proof_nodes,"certificate_bytes":code_bytes},separators=(",",":")),file=sys.stderr,flush=True)
        if code_bytes > 100000:
            return False
        return judge("true",code).get("status") == "accepted"
    except (KeyError,IndexError,MemoryError,RecursionError,TypeError,ValueError):
        return False
'''
s=s.replace(marker,helper+marker,1)
needle='''    if finish_target_grounded_candidate(\n        source, target, grounded_search, grounded_found\n    ):\n        return\n\n\n    stair_seconds = min(2.0, max(0.1, timeout / 50.0))\n'''
replacement='''    if finish_target_grounded_candidate(\n        source, target, grounded_search, grounded_found\n    ):\n        return\n\n    # Promoted after official 796/800 proxy + Lean regression gate.\n    if run_given_clause_fallback(source, target, timeout):\n        return\n\n    stair_seconds = min(2.0, max(0.1, timeout / 50.0))\n'''
if needle not in s: raise SystemExit('grounded insertion marker missing')
s=s.replace(needle,replacement,1)
p.write_text(s)
print('patched',p)
