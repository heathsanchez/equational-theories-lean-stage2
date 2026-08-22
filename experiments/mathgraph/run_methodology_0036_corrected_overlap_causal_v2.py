#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT = Path(__file__).resolve().parents[2]
PROTO = ROOT / 'experiments/mathgraph/protocols/methodology-0036-corrected-overlap-causal-v2.json'
OUT = ROOT / 'experiments/mathgraph/results/methodology-0036-corrected-overlap-causal-v2.json'
RID = 'evaluation_normal_0036'
HIST = 'origin/mathgraph/superposition-selector-tournament-20260820'


def load_historical():
    text = subprocess.check_output(['git','show',f'{HIST}:submissions/mathgraph/solver.py'], text=True)
    p = Path(tempfile.gettempdir()) / 'mg0036_overlap_causal_hist.py'
    p.write_text(text)
    spec = importlib.util.spec_from_file_location('mg0036_overlap_causal_hist', p)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


def connected(search, target):
    comps = search.components()
    a,b = target[:2]
    return a in comps and b in comps and comps[a] == comps[b]


def replay_state(m, source, search):
    root = search.shortest_path()
    replay = bool(root is not None and m.replay_dag(source, search.nodes, root))
    return connected(search, search.target), root, replay


def make_search(m, source, target, cfg):
    captured=[]
    Base=m.ContextualSearch
    class Instrumented(Base):
        def add_node(self,node,graph_edge=True):
            nid=super().add_node(node,graph_edge=graph_edge)
            if nid is not None and getattr(node,'constructor',None)=='target-narrowing':
                captured.append(nid)
            return nid
    search=Instrumented(source,target,time.monotonic()+10.0,dict(cfg['limits']))
    search.solve_target_narrowing(cfg['maximum_depth'],cfg['branching'],cfg['maximum_terms'],cfg['maximum_context_depth'])
    return search, sorted(set(captured))


def add_nine_reentries(m, search, source, target, old_nodes):
    tr=target[1]
    rhs_parent_ids=sorted({nid for nid in old_nodes if search.nodes[nid].lhs==tr or search.nodes[nid].rhs==tr})
    source_vars=list(source[2])
    target_vars=[('var',v) for v in target[2]]
    before_nodes=len(search.nodes)
    before_edges=search.graph_edges
    admitted=0
    for xv,yv in product(target_vars, repeat=2):
        values=[None]*len(source_vars)
        values[source_vars.index('x')]=xv
        values[source_vars.index('y')]=yv
        values[source_vars.index('z')]=tr
        origins=tuple((var,val,tuple(rhs_parent_ids) if val==tr else ()) for var,val in zip(source_vars,values))
        if search.add_source_substitution(values,generation=1,origins=origins) is not None:
            admitted+=1
    new_nodes=[nid for nid in range(before_nodes,len(search.nodes)) if search.nodes[nid].kind=='source reentry']
    return admitted, search.graph_edges-before_edges, new_nodes, len(rhs_parent_ids)


def apply_candidates(m, source, search, labelled_candidates, cap):
    applied=0; first_join=None; first_replay=None
    for label,candidate in labelled_candidates:
        if applied>=cap: break
        before_join=search.components_joined
        nid=search.apply_overlap(candidate,1)
        if nid is None: continue
        applied+=1
        conn,root,replay=replay_state(m,source,search)
        if first_join is None and (search.components_joined>before_join or conn):
            first_join={'label':label,'applied_index':applied,'node_id':nid}
        if replay:
            first_replay={'label':label,'applied_index':applied,'node_id':nid,'root':root}
            break
    conn,root,replay=replay_state(m,source,search)
    return {'applied':applied,'first_join':first_join,'first_replay':first_replay,'final_connected':conn,'final_root':root,'final_replay':replay}


def main():
    protocol=json.loads(PROTO.read_text())
    assert protocol['frozen_before_execution'] is True
    m=load_historical()
    row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    cfg=m.CONTEXTUAL_PORTFOLIO[0]
    cap=protocol['constraints']['maximum_term_size']
    depth=protocol['constraints']['maximum_context_depth']
    perdir=protocol['constraints']['maximum_candidates_per_direction']
    appcap=protocol['constraints']['matched_overlap_application_cap']

    # Arm A: frozen old frontier, matched generic old-old overlap.
    A, oldA=make_search(m,source,target,cfg)
    operativeA=A.max_term_size
    A_pre=replay_state(m,source,A)
    old_forward=A.collect_overlap_candidates(oldA,oldA,depth,perdir) if oldA else []
    # Deduplicate deterministically by repr; the solver candidate objects are tuples.
    seen=set(); A_candidates=[]
    for c in old_forward:
        k=repr(c)
        if k in seen: continue
        seen.add(k); A_candidates.append(('OLD_OLD',c))
    A_result=apply_candidates(m,source,A,A_candidates,appcap)

    # Arm B: identical frozen frontier + exactly nine raw cap-19 re-entry substitutions,
    # then only overlaps crossing new and old frontiers.
    B, oldB=make_search(m,source,target,cfg)
    operativeB=B.max_term_size
    admitted, reentry_edges, newB, rhs_parents=add_nine_reentries(m,B,source,target,oldB)
    B_pre=replay_state(m,source,B)
    fw=B.collect_overlap_candidates(newB,oldB,depth,perdir) if newB and oldB else []
    rv=B.collect_overlap_candidates(oldB,newB,depth,perdir) if newB and oldB else []
    B_candidates=[('NEW_TO_OLD',c) for c in fw]+[('OLD_TO_NEW',c) for c in rv]
    B_result=apply_candidates(m,source,B,B_candidates,appcap)

    measurement_ok=(
        operativeA==cap and operativeB==cap and
        len(oldA)==45 and len(oldB)==45 and
        admitted==9 and reentry_edges==9 and not B_pre[0] and not B_pre[2]
    )
    if not measurement_ok:
        decision='MEASUREMENT_FAILURE'
    elif A_result['final_replay'] or A_result['final_connected'] or A_result['first_join'] is not None:
        decision='R2_GENERIC_OVERLAP_SUFFICIENT'
    elif B_result['final_replay'] or B_result['final_connected'] or B_result['first_join'] is not None:
        decision='R1_REENTRY_OVERLAP_CAUSAL'
    else:
        decision='R3_OVERLAP_INSUFFICIENT'

    out={
        'schema':protocol['schema'],'id':RID,'decision':decision,
        'measurement':{
            'operative_cap_A':operativeA,'operative_cap_B':operativeB,
            'old_frontier_nodes_A':len(oldA),'old_frontier_nodes_B':len(oldB),
            'admitted_reentries_B':admitted,'reentry_edges_B':reentry_edges,
            'literal_target_rhs_parent_nodes_B':rhs_parents,
            'B_pre_connected':B_pre[0],'B_pre_replay':B_pre[2],
            'measurement_ok':measurement_ok
        },
        'arm_A':{'candidate_count':len(A_candidates),**A_result},
        'arm_B':{'forward_candidates':len(fw),'reverse_candidates':len(rv),'candidate_count':len(B_candidates),**B_result},
        'sealed_transfer_ids_loaded':[]
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__': main()
