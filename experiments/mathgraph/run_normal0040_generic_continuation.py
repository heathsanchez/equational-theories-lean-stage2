#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
RID='evaluation_normal_0040'

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True)
    a=ap.parse_args()
    m=load(SOLVER,'mg_generic_cont')
    h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_generic_cont')
    row=h.load_row(a.input,RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    lim=dict(m.COMPACT_SUPERPOSITION_PROBE)
    lim.update({'seconds':45.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    deadline=time.monotonic()+45.0
    e=m.TargetGroundedRefutation(source,target,deadline,lim)
    base=e.solve(); r=m.RigidSuperpositionModule()
    out={'id':RID,'baseline_found':bool(base),'oracle_free':True,'policy':'retain-new-pair-immediately-simplify'}
    if base:
        nodes,root=base; out.update(found=True,round=0,proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)))
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_GENERIC_CONTINUATION',json.dumps(out,sort_keys=True),flush=True); return

    target_terms=[]
    for side in target[:2]: target_terms.extend(m.walk_subterms(side))

    def inline(t): return h.inline_engine_names(t,e.reverse_constants)
    def score(c):
        x,y=inline(c.lhs),inline(c.rhs)
        d=min([m.structural_distance(x,t) for t in target_terms]+[m.structural_distance(y,t) for t in target_terms])
        return (d, max(m.term_size(x),m.term_size(y)), m.term_size(x)+m.term_size(y), m.render_term(x), m.render_term(y))
    def orientations(c):
        return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
    def cps(a0,b0,cap=32):
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
    # Phase 0: materialize every bounded self-overlap once. This is the smallest
    # generic operation needed to expose latent schematic continuations such as
    # the one that opened the observed 0040 corridor.
    candidates=[]
    for c in list(retained):
        if time.monotonic()>=deadline: break
        candidates.extend(cps(c,c,cap=12))
    candidates=sorted(candidates,key=score)[:256]
    frontier=[]; added0=0
    for p in candidates:
        if e.search.add_clause(p): frontier.append(p); retained.append(p); added0+=1
    out['self_overlap_added']=added0
    found=e.solve()
    if found:
        nodes,root=found; out.update(found=True,round=0,proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)))
    else:
        out['round_stats']=[]
        # Continuation closure: newly materialized clauses get priority to pair
        # against a target-ranked retained bank, then all survivors are kept for
        # the next round. No clause IDs or external proof trace are consulted.
        for rnd in range(1,9):
            if time.monotonic()>=deadline or not frontier: break
            bank=sorted(retained,key=score)[:320]
            raw=[]; pair_attempts=0
            for f in sorted(frontier,key=score)[:96]:
                for b in bank:
                    if time.monotonic()>=deadline: break
                    raw.extend(cps(f,b,cap=8)); pair_attempts+=1
                    if pair_attempts>=12000 or len(raw)>=5000: break
                if pair_attempts>=12000 or len(raw)>=5000 or time.monotonic()>=deadline: break
            raw=sorted(raw,key=score)[:512]
            new=[]
            for p in raw:
                if e.search.add_clause(p): new.append(p); retained.append(p)
            out['round_stats'].append({'round':rnd,'frontier_in':len(frontier),'pair_attempts':pair_attempts,'candidates':len(raw),'added':len(new),'clauses':len(e.search.clauses)})
            frontier=new
            found=e.solve()
            if found:
                nodes,root=found; out.update(found=True,round=rnd,proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)))
                break
        if not found: out.update(found=False,replay_ok=False)
    Path(a.output).parent.mkdir(parents=True,exist_ok=True)
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('NORMAL0040_GENERIC_CONTINUATION',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
