#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
HELPER=ROOT/'experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(spec); sys.modules[name]=m; spec.loader.exec_module(m); return m

def alpha_sig(rigid,a,b):
    names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names)
    return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load(SOLVER,'mg_0040_alpha_solver'); h=load(HELPER,'mg_0040_alpha_helper')
    row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); baseline=engine.solve(); rigid=m.RigidSuperpositionModule()
    trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
    defs={}; wanted={}
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
        if fid in ('f81','f95'):
            wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
    f81,f95=wanted['f81'],wanted['f95']
    cover=None; cover_map=None; cover_rev=False
    for c in engine.search.clauses:
        x=h.inline_engine_names(c.lhs,engine.reverse_constants); y=h.inline_engine_names(c.rhs,engine.reverse_constants)
        for rev,(u,v) in enumerate(((x,y),(y,x))):
            subst={}
            if rigid.match_term(u,f81[0],subst) and rigid.match_term(v,f81[1],subst):
                cover=(c,x,y); cover_map=subst; cover_rev=bool(rev); break
        if cover: break
    out={'id':RID,'baseline_found':bool(baseline),'cover_found':bool(cover),'materialized_matches_f81':False,'alpha_self_overlap_matches_f95':False,'replay_ok':False,'proposal_count':0,'proposals':[]}
    if cover:
        c,x,y=cover; mx=rigid.substitute(x,cover_map); my=rigid.substitute(y,cover_map)
        if cover_rev: mx,my=my,mx
        out['materialized_matches_f81']=(mx,my)==f81
        base=c if not cover_rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        mat=engine.search.instantiate(base,cover_map)
        for path in rigid.nonvariable_positions(mat.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
            p=engine.search.critical_pair(mat,mat,0,0,path)
            if p is None: continue
            ix=h.inline_engine_names(p.lhs,engine.reverse_constants); iy=h.inline_engine_names(p.rhs,engine.reverse_constants)
            same=alpha_sig(rigid,ix,iy)==alpha_sig(rigid,f95[0],f95[1])
            rec={'path':list(path),'lhs':m.render_term(ix),'rhs':m.render_term(iy),'alpha_match_f95':same}
            out['proposals'].append(rec)
            if same:
                out['alpha_self_overlap_matches_f95']=True
                try:
                    nodes,root=m.recipe_to_dag(p)
                    out['replay_ok']=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000))
                except Exception as e:
                    out['replay_error']=type(e).__name__+': '+str(e)
        out['proposal_count']=len(out['proposals'])
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('NORMAL0040_ALPHA_SELF_OVERLAP',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
