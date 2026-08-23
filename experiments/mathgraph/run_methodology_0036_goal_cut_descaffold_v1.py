#!/usr/bin/env python3
import json, sys
from pathlib import Path
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-goal-cut-descaffold-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-goal-cut-descaffold-v1.json'
RID='evaluation_normal_0036'

def simulate_goal_separation(m,s,target,c):
    comps=s.components(); g0,g1=target[:2]
    # Build component sets plus singleton candidate endpoints if absent, then union only this candidate edge.
    groups={}
    for t,lab in comps.items(): groups.setdefault(('old',lab),set()).add(t)
    def key_for(t):
        if t in comps:return ('old',comps[t])
        return ('new',t)
    k0,k1=key_for(c['lhs']),key_for(c['rhs'])
    allgroups=dict(groups)
    allgroups.setdefault(k0,set()).add(c['lhs']); allgroups.setdefault(k1,set()).add(c['rhs'])
    if k0!=k1:
        merged=allgroups[k0]|allgroups[k1]
        del allgroups[k0]
        if k1 in allgroups: del allgroups[k1]
        candidate_key=c.get('key',(m.render_term(c['lhs']),m.render_term(c['rhs'])))
        mk=('merged',repr(candidate_key))
        allgroups[mk]=merged
    term_to_group={t:k for k,ts in allgroups.items() for t in ts}
    if g0 not in term_to_group or g1 not in term_to_group:return None
    a,b=term_to_group[g0],term_to_group[g1]
    if a==b:return 0
    return min(m.structural_distance(x,y) for x in allgroups[a] for y in allgroups[b])

def rank_descaffolded(m,s,target,candidates):
    scored=[]
    for c in candidates:
        d=simulate_goal_separation(m,s,target,c)
        scored.append((999999 if d is None else d,c['key'],c))
    return [c for _,_,c in sorted(scored,key=lambda x:(x[0],x[1]))], {c['key']:d for d,_,c in scored}

def run_traj(m,source,target,cfg,ranking,budgets):
    out=[]
    for k in budgets:
        arm=tour.apply_arm(m,source,target,cfg,ranking[:k])
        out.append({'k':k,'post_cross_distance':arm['post_cross_distance'],'connected':arm['connected'],'replayable_closure':arm['replayable_closure'],'added':arm['added']})
    return out

def first(rows):
    for r in rows:
        d=0 if r['connected'] else r['post_cross_distance']
        if d is not None and d<10:return r['k']
    return None

def effective(r): return 0 if r['connected'] else r['post_cross_distance']

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=tour.cut.load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    s,old,new,admitted,edges,st=tour.frozen_state(m,source,target,cfg)
    candidates,anchors,fills=tour.make_pool(m,s,source,target,st,20000)
    A=tour.select(candidates,len(candidates),'cut')
    C=tour.select(candidates,len(candidates),'target')
    B,post_scores=rank_descaffolded(m,s,target,candidates)
    ok=(s.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and st is not None and st.get('cross_distance')==10 and st.get('lhs_size')==4 and st.get('rhs_size')==19 and len(candidates)==35 and sum(c['predicted_cut_distance']<10 for c in candidates)==15 and all(v is not None for v in post_scores.values()))
    budgets=p['prefix_budgets']; ta=run_traj(m,source,target,cfg,A,budgets) if ok else []; tb=run_traj(m,source,target,cfg,B,budgets) if ok else []; tc=run_traj(m,source,target,cfg,C,budgets) if ok else []
    fa,fb,fc=first(ta),first(tb),first(tc)
    overlaps={k:len({c['key'] for c in A[:k]} & {c['key'] for c in B[:k]}) for k in budgets} if ok else {}
    if not ok:decision='MEASUREMENT_FAILURE'
    elif fb==1 and all(effective(b)<=effective(a) for a,b in zip(ta,tb)):decision='DESCAFFOLD_SUCCESS'
    elif fb is not None and fb<=4:decision='DESCAFFOLD_DIFFERENT_BUT_USEFUL'
    else:decision='SCAFFOLD_DEPENDENT'
    def head(rank):
        return [{'lhs':m.render_term(c['lhs']),'rhs':m.render_term(c['rhs']),'labelled_predicted_distance':c['predicted_cut_distance'],'raw_goal_post_separation':post_scores[c['key']],'target_coverage':c['target_coverage']} for c in rank[:6]]
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,'first_contraction_k':{'A_LABELLED_CUT':fa,'B_RAW_GOAL_GRAPH':fb,'C_CUT_BLIND_TARGET':fc},'prefix_overlap_A_B':overlaps,'trajectory':{'A_LABELLED_CUT':ta,'B_RAW_GOAL_GRAPH':tb,'C_CUT_BLIND_TARGET':tc},'ranking_heads':{'A':head(A),'B':head(B),'C':head(C)},'pool':{'count':len(candidates),'contractors':sum(c['predicted_cut_distance']<10 for c in candidates)},'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
