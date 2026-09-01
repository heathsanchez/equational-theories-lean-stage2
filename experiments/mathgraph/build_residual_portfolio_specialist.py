#!/usr/bin/env python3
"""Build strongest non-regressive MathGraph portfolio behind the frozen champion.

The verified behavioural-future champion remains AST/text exact.  Only after it
returns False do we route the residual through two orthogonal proof-producing
specialists, then the already-isolated adaptive-arity fallback.
"""
import argparse, ast, py_compile, tempfile
from pathlib import Path
import build_adaptive_arity_specialist_v3 as adaptive_v3

ROOT=Path(__file__).resolve().parents[2]
DEFAULT_BASE=ROOT/'submissions/mathgraph/solver.py'
PORTFOLIO_CALL='''    # Residual portfolio: runs only after the exact frozen champion fails.\n    if run_residual_portfolio_fallback(source, target, timeout):\n        return\n\n'''

STANDALONE=r'''

# MATHGRAPH_RESIDUAL_PORTFOLIO_V1
def run_residual_portfolio_fallback(source, target, timeout):
    """Fast representation development, then certified attachment; no row IDs."""
    base=dict(COMPACT_SUPERPOSITION_PROBE)
    base.update({
        "maximum_term_size":90,"maximum_replay_term_size":380,
        "maximum_depth":14,"maximum_rules":1200,"maximum_rounds":192,
        "new_clauses_per_round":96,"maximum_clauses":20000,
        "normalization_steps":384,"maximum_proof_nodes":100000,
    })
    def setup(goal,seconds):
        limits=dict(base);limits["seconds"]=seconds
        e=TargetGroundedRefutation(source,goal,time.monotonic()+seconds,limits)
        return e,e.search
    def finish(engine,search,q,tag):
        if q is None:return False
        q=engine.inline_recipe(q)
        if (q.lhs,q.rhs)==(target[1],target[0]):q=Recipe(q.rhs,q.lhs,"symmetry",(q,))
        if (q.lhs,q.rhs)!=target[:2]:return False
        nodes,root=search.compile(q)
        if not replay_dag(source,nodes,root,maximum_term_size=380,maximum_nodes=100000):return False
        code,pnodes=make_dag_certificate(target,nodes,root)
        if "_mg_elide_have_types" in globals():
            old=code.splitlines();new=_mg_elide_have_types(code).splitlines()
            code="\n".join(a if ":=" in a and a.rstrip().endswith(":= rfl") else b for a,b in zip(old,new))+"\n"
        if len(code.encode("utf-8"))>100000:return False
        print("MATHGRAPH_RESIDUAL_PORTFOLIO "+json.dumps({"path":tag,"proof_nodes":pnodes,"certificate_bytes":len(code.encode("utf-8"))},separators=(",",":")),file=sys.stderr,flush=True)
        return judge("true",code).get("status")=="accepted"
    def canon_unary(lhs,rhs):
        names={}
        def f(t):
            if t[0]=="var":
                if t[1] not in names:names[t[1]]=chr(ord("x")+len(names))
                return ("var",names[t[1]])
            return ("op",f(t[1]),f(t[2]))
        a,b=f(lhs),f(rhs)
        return a,b,tuple(dict.fromkeys(names.values()))
    try:
        # Phase A: three target-guided developmental generations.  On known hard
        # residuals this takes only a few seconds; it is capped structurally.
        e,s=setup(target,min(30.0,max(8.0,timeout/120.0)))
        for _ in range(3):
            rules=s.rules();snap=list(rules);props=[];proposed=0;stop=False
            for oi,o in enumerate(snap):
                if stop:break
                for ii,i in enumerate(snap):
                    if stop:break
                    for path in nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                        c=s.critical_pair(o,i,oi,ii,path)
                        if c is None:continue
                        c=s.interreduce(c,rules);props.append((s.target_score(c),c));proposed+=1
                        if proposed>=512:stop=True;break
            props.sort(key=lambda z:z[0]);added=0
            for _,q in props:
                if s.add_clause(q):s.superpositions+=1;added+=1
                if added>=64:break
        # Promote replay-certified unary interfaces.  This route is selected by
        # structure, never by benchmark identity.
        rules=s.rules();seen=set();unary=[];census=0
        for oi,o in enumerate(rules):
            if census>=176:break
            for ii,i in enumerate(rules):
                if census>=176:break
                for path in nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules);names=term_variables(c.lhs)|term_variables(c.rhs)
                    if c.lhs==c.rhs or any(v.startswith("@") for v in names):continue
                    key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                    if key in seen:continue
                    seen.add(key);census+=1
                    ns,r=s.compile(c)
                    if not replay_dag(source,ns,r,maximum_term_size=380,maximum_nodes=100000):continue
                    act=canon_unary(c.lhs,c.rhs)
                    if act[2]==("x",):unary.append((s.target_score(c),term_size(c.lhs)+term_size(c.rhs),len(ns),c))
                    if census>=176:break
        if unary:
            unary.sort(key=lambda z:(z[0],z[1],z[2]));ae,asrch=setup(target,min(120.0,max(30.0,timeout/30.0)))
            added=0
            for _,_,_,q in unary[:64]:
                if asrch.add_clause(q):added+=1
            q=asrch.collapse_proof() or asrch.target_proof(asrch.rules()) or asrch.solve()
            if finish(ae,asrch,q,"unary-promotion"):return True
            return False
        # Phase B: if no unary interface exists, test a genuinely different
        # hypothesis: symmetric completion toward universal collapse x=y.
        collapse_target=parse_equation("x = y")
        ce,cs=setup(collapse_target,min(90.0,max(30.0,timeout/40.0)))
        initial=list(cs.rules())
        for q in initial:cs.add_clause(Recipe(q.rhs,q.lhs,"symmetry",(q,)))
        rules=cs.rules();props=[];proposed=0;stop=False
        for oi,o in enumerate(list(rules)):
            if stop:break
            for ii,i in enumerate(list(rules)):
                if stop:break
                for path in nonvariable_positions(o.lhs,maximum_depth=16,include_root=True):
                    c=cs.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=cs.interreduce(c,rules)
                    if c.lhs!=c.rhs:props.append((cs.target_score(c),term_size(c.lhs)+term_size(c.rhs),c))
                    proposed+=1
                    if proposed>=4096:stop=True;break
        props.sort(key=lambda z:(z[0],z[1]));added=0
        for _,_,q in props:
            if cs.add_clause(q):cs.superpositions+=1;added+=1
            if added>=256:break
        cq=cs.collapse_proof() or cs.target_proof(cs.rules()) or cs.solve()
        if cq is None:return False
        cq=ce.inline_recipe(cq)
        if (cq.lhs,cq.rhs)==(collapse_target[1],collapse_target[0]):cq=Recipe(cq.rhs,cq.lhs,"symmetry",(cq,))
        if (cq.lhs,cq.rhs)!=collapse_target[:2]:return False
        cn,cr=cs.compile(cq)
        if not replay_dag(source,cn,cr,maximum_term_size=420,maximum_nodes=120000):return False
        ae,asrch=setup(target,min(25.0,max(8.0,timeout/150.0)))
        asrch.add_clause(cq)
        q=asrch.collapse_proof() or asrch.target_proof(asrch.rules()) or asrch.solve()
        return finish(ae,asrch,q,"symmetric-collapse")
    except Exception as ex:
        print("MATHGRAPH_RESIDUAL_PORTFOLIO "+json.dumps({"error":type(ex).__name__},separators=(",",":")),file=sys.stderr,flush=True)
        return False
'''

def exact_function(text,name):
    tree=ast.parse(text);node=next(n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name==name)
    lines=text.splitlines(keepends=True);return ''.join(lines[node.lineno-1:node.end_lineno])

def build(base,out):
    with tempfile.TemporaryDirectory() as td:
        tmp=Path(td)/'adaptive.py'
        adaptive_v3.v2.build(base,tmp)
        text=tmp.read_text()
    champion_before=exact_function(text,'run_behavioural_future_fallback')
    marker='\n# MATHGRAPH_ADAPTIVE_ARITY_V2\n'
    if text.count(marker)!=1:raise SystemExit('adaptive marker invariant failed')
    text=text.replace(marker,STANDALONE+marker,1)
    call=adaptive_v3.v2.ADAPTIVE_CALL
    if text.count(call)!=1:raise SystemExit('adaptive call invariant failed')
    text=text.replace(call,PORTFOLIO_CALL+call,1)
    if exact_function(text,'run_behavioural_future_fallback')!=champion_before:raise SystemExit('portfolio modified champion fallback')
    if len(text.encode())>500000:raise SystemExit('portfolio exceeds 500KB')
    out.write_text(text);py_compile.compile(str(out),doraise=True)
    print(f'built {out} ({len(text.encode())} bytes)')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--base',default=str(DEFAULT_BASE));ap.add_argument('--output',required=True);a=ap.parse_args();build(Path(a.base),Path(a.output))
if __name__=='__main__':main()
