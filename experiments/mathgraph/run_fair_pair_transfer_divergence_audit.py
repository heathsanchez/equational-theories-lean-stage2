#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
CASES=('evaluation_normal_0036','evaluation_hard_0196')

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def run_case(rid,input_path,proof,m,h):
    row=h.load_row(input_path,rid); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':45.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    warm_deadline=time.monotonic()+6.0; warm_lim=dict(lim); warm_lim['seconds']=6.0
    e=m.TargetGroundedRefutation(source,target,warm_deadline,warm_lim); warm=e.solve(); r=m.RigidSuperpositionModule()
    if warm: return {'id':rid,'warm_found':True}
    deadline=time.monotonic()+45.0; e.deadline=deadline
    if hasattr(e.search,'deadline'): e.search.deadline=deadline
    if hasattr(e.search,'seconds'): e.search.seconds=45.0

    ids=[]
    for block in h.fof_blocks(proof):
        q=h.parse_fof(block)
        if not q: continue
        fid,kind,formula,rest=q
        if kind!='plain' or not fid.startswith('f'): continue
        blob=' '.join(rest)
        # Derived equality clauses only: exclude CNF/source plumbing, definitions, and conjecture transforms.
        if 'inference(' not in blob: continue
        if any(tag in blob for tag in ('cnf_transformation','definition_folding','reorient_equations','skolemize','ennf_transformation','negated_conjecture')): continue
        try:
            if h.formula_equality(formula) is not None: ids.append(fid)
        except Exception: pass
    wanted=h.extract_wanted(proof,target[2],m,ids)
    def alpha_pair(a,b):
        n={}; x=r.alpha_canonical_term(a,n); y=r.alpha_canonical_term(b,n); return min((x,y),(y,x))
    wanted_keys={fid:alpha_pair(*eq) for fid,eq in wanted.items()}
    ordered=[fid for fid in ids if fid in wanted_keys]
    def inline(t): return h.inline_engine_names(t,e.reverse_constants)
    def key_clause(c): return alpha_pair(inline(c.lhs),inline(c.rhs))
    def present(seq):
        ks={key_clause(c) for c in seq}; return [fid for fid in ordered if wanted_keys[fid] in ks]
    target_terms=[]
    for side in target[:2]: target_terms.extend(m.walk_subterms(side))
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

    retained=list(e.search.clauses)
    initial_present=present(retained)
    candidates=[]
    for c in list(retained): candidates.extend(cps(c,c,cap=12))
    candidates=sorted(candidates,key=score)[:256]
    frontier=[]
    for p in candidates:
        if e.search.add_clause(p): frontier.append(p); retained.append(p)
    bootstrap_present=present(retained)

    fs=sorted(frontier,key=score)[:96]; bank=sorted(retained,key=score)[:320]
    raw=[]; pair_attempts=0
    for f in fs:
        for b in bank:
            if time.monotonic()>=deadline: break
            raw.extend(cps(f,b,cap=1)); pair_attempts+=1
        if time.monotonic()>=deadline: break
    raw_present=present(raw)
    ranked=sorted(raw,key=score)[:1024]
    ranked_present=present(ranked)
    new=[]
    for p in ranked:
        if e.search.add_clause(p): new.append(p); retained.append(p)
    retained_present=present(retained)

    def earliest_missing(pres):
        s=set(pres)
        for fid in ordered:
            if fid not in s: return fid
        return None
    return {
      'id':rid,'warm_found':False,'vampire_derived_equality_ids':ordered,
      'initial_present':initial_present,'bootstrap_present':bootstrap_present,
      'round1_pair_attempts':pair_attempts,'round1_raw_count':len(raw),
      'round1_raw_present':raw_present,'round1_ranked_present':ranked_present,'round1_retained_present':retained_present,
      'earliest_missing_bootstrap':earliest_missing(bootstrap_present),
      'earliest_missing_raw':earliest_missing(raw_present),
      'earliest_missing_ranked':earliest_missing(ranked_present),
      'earliest_missing_retained':earliest_missing(retained_present)
    }

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--normal-input',required=True); ap.add_argument('--hard-input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load(SOLVER,'mg_transfer_div2'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_transfer_div2')
    trace=json.load(urllib.request.urlopen(TRACE_URL)); proofs={x['id']:x['proof'] for x in trace['rows']}
    rows=[]
    for rid in CASES:
        inp=a.normal_input if 'normal_' in rid else a.hard_input
        res=run_case(rid,inp,proofs[rid],m,h); rows.append(res); print('FAIR_PAIR_DIVERGENCE',json.dumps(res,sort_keys=True),flush=True)
    out={'policy':'frozen-fair-pair','diagnostic_oracle_only':True,'derived_only':True,'rows':rows}
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
if __name__=='__main__': main()
