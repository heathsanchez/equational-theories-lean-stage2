#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load_mod(path,name):
    spec=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(spec); sys.modules[name]=m; spec.loader.exec_module(m); return m

def alpha_sig(rigid,a,b):
    names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names); return min((x,y),(y,x))

def covers(rigid,sa,sb,ta,tb):
    for x,y in ((sa,sb),(sb,sa)):
        subst={}
        if rigid.match_term(x,ta,subst) and rigid.match_term(y,tb,subst): return True
    return False

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load_mod(SOLVER,'mg_postseed_solver')
    h=load_mod(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'mg_postseed_helpers')
    row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); engine.solve(); rigid=m.RigidSuperpositionModule()
    trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
    wanted=h.extract_wanted(proof,target[2],m,('f81','f95'))
    f81,f95=wanted['f81'],wanted['f95']
    cover=None
    for c in engine.search.clauses:
        x=h.inline_engine_names(c.lhs,engine.reverse_constants); y=h.inline_engine_names(c.rhs,engine.reverse_constants)
        for rev,(u,v) in enumerate(((x,y),(y,x))):
            subst={}
            if rigid.match_term(u,f81[0],subst) and rigid.match_term(v,f81[1],subst): cover=(c,subst,bool(rev)); break
        if cover: break
    seed=None
    if cover:
        c,subst,rev=cover; base=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,)); mat=engine.search.instantiate(base,subst); goal=alpha_sig(rigid,*f95)
        for path in rigid.nonvariable_positions(mat.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
            p=engine.search.critical_pair(mat,mat,0,0,path)
            if p is None: continue
            x=h.inline_engine_names(p.lhs,engine.reverse_constants); y=h.inline_engine_names(p.rhs,engine.reverse_constants)
            if alpha_sig(rigid,x,y)==goal: seed=p; engine.search.add_clause(seed); break
    student=[(h.inline_engine_names(c.lhs,engine.reverse_constants),h.inline_engine_names(c.rhs,engine.reverse_constants)) for c in engine.search.clauses]
    defs={}; audited=[]; after_f95=False; first=None
    for block in h.fof_blocks(proof):
        q=h.parse_fof(block)
        if not q: continue
        fid,kind,formula,tail=q
        try: eq=h.formula_equality(formula)
        except Exception: eq=None
        if eq is None: continue
        x,y=eq
        if kind=='definition':
            if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
            elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
            continue
        if fid=='f95': after_f95=True; continue
        if not after_f95: continue
        mi=re.search(r'inference\(([^,\]]+)',','.join(tail)); inf=mi.group(1) if mi else ''
        if inf not in ('superposition','forward_demodulation'): continue
        a1=h.map_rigids(h.inline_defs(x,defs),target[2]); b1=h.map_rigids(h.inline_defs(y,defs),target[2])
        exact=any(alpha_sig(rigid,a1,b1)==alpha_sig(rigid,sa,sb) for sa,sb in student)
        present=exact or any(covers(rigid,sa,sb,a1,b1) for sa,sb in student)
        rec={'id':fid,'inference':inf,'present':present,'exact':exact,'lhs':m.render_term(a1),'rhs':m.render_term(b1)}; audited.append(rec)
        if first is None and not present: first=rec
    out={'id':RID,'seed_generated':seed is not None,'clauses_after_seed':len(engine.search.clauses),'audited_after_f95':len(audited),'present_after_f95':sum(x['present'] for x in audited),'first_missing_after_f95':first,'first_steps':audited[:8]}
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_POSTSEED_DIVERGENCE',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
