#!/usr/bin/env python3
import json, statistics, random, importlib.util, hashlib
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
RESULTS=HERE/'results'
OUT=RESULTS/'adaptive-residual-factorization-closure.json'

spec=importlib.util.spec_from_file_location('rfo', HERE/'run_residual_factorization_optimum.py')
rfo=importlib.util.module_from_spec(spec); spec.loader.exec_module(rfo)
rrt=rfo.rrt
DATASETS=rfo.DATASETS


def mean(xs): return sum(xs)/len(xs) if xs else 0.0

def stdev(xs):
    if len(xs)<2:return 1.0
    s=statistics.pstdev(xs); return s if s>1e-12 else 1.0


def productive_action(dm):
    # Transferable intervention family, deliberately independent of solver-specific portfolio names.
    totals={k:sum(float(m.get(k,0) or 0) for m in dm) for k in (
        'components_joined','missing_target_introduced','narrowing_successors','overlaps_added')}
    # Prefer the most causally specific event when several occur in one trajectory.
    if totals['components_joined']>0: return 'COMPONENT_BRIDGE'
    if totals['missing_target_introduced']>0: return 'TARGET_STRUCTURE'
    if totals['narrowing_successors']>0: return 'NARROWING'
    if totals['overlaps_added']>0: return 'OVERLAP'
    return 'NO_PRODUCTIVE_OPERATOR'


def load_actions(paths):
    f={r['id']:r for r in json.loads(paths[0].read_text())}
    d={r['id']:r for r in json.loads(paths[1].read_text())}
    rows=[]
    for i in sorted(set(f)&set(d)):
        x,fm,dm=rrt.feat(f[i],d[i])
        rows.append({'id':i,'x':x,'action':productive_action(dm)})
    return rows


def fit_multi(rows,features):
    labels=sorted(set(r['action'] for r in rows))
    base={f:(mean([r['x'][f] for r in rows]),stdev([r['x'][f] for r in rows])) for f in features}
    centroids={}
    for y in labels:
        ys=[r for r in rows if r['action']==y]
        centroids[y]={f:mean([(r['x'][f]-base[f][0])/base[f][1] for r in ys]) for f in features}
    priors=Counter(r['action'] for r in rows)
    return {'base':base,'centroids':centroids,'priors':priors}


def predict_multi(row,model):
    if not model['centroids']:
        return max(model['priors'],key=model['priors'].get) if model['priors'] else None
    best=None
    for y,c in model['centroids'].items():
        dist=0.0
        for f,(m,s) in model['base'].items():
            z=(row['x'][f]-m)/s; dist+=(z-c[f])**2
        cand=(dist,-model['priors'][y],y)
        if best is None or cand<best: best=cand
    return best[2]


def macro_recall(rows,preds):
    labels=sorted(set(r['action'] for r in rows))
    rs=[]
    for y in labels:
        idx=[j for j,r in enumerate(rows) if r['action']==y]
        if idx: rs.append(sum(preds[j]==y for j in idx)/len(idx))
    return mean(rs)


def eval_features(train,test,features):
    model=fit_multi(train,features)
    preds=[predict_multi(r,model) for r in test]
    return macro_recall(test,preds),sum(p==r['action'] for p,r in zip(preds,test))/max(1,len(test))


def fold_of(row,folds):
    return int(hashlib.sha256(row['id'].encode()).hexdigest(),16)%folds


def cv_score(rows,features,folds=5):
    scores=[]
    for fold in range(folds):
        tr=[r for r in rows if fold_of(r,folds)!=fold]
        te=[r for r in rows if fold_of(r,folds)==fold]
        if not tr or not te: continue
        scores.append(eval_features(tr,te,features)[0])
    return mean(scores)


def adaptive_select(rows,features,min_gain=0.015,merge_eps=0.005,max_k=12):
    one=sorted(((cv_score(rows,[f]),f) for f in features),reverse=True)
    if not one:return [],[]
    selected=[one[0][1]]; history=[{'op':'seed','factor':selected[0],'score':round(one[0][0],4)}]
    current=one[0][0]; remaining=[f for f in features if f not in selected]
    while remaining and len(selected)<max_k:
        score,f=max((cv_score(rows,selected+[f]),f) for f in remaining); gain=score-current
        if gain < min_gain:
            history.append({'op':'stop_equivalent','candidate':f,'gain':round(gain,4),'score':round(score,4)})
            break
        selected.append(f); remaining.remove(f); current=score
        history.append({'op':'split','factor':f,'gain':round(gain,4),'score':round(score,4)})
        merged=True
        while merged and len(selected)>1:
            merged=False
            for g in list(selected):
                trial=[h for h in selected if h!=g]; s=cv_score(rows,trial); loss=current-s
                if loss <= merge_eps:
                    selected=trial; remaining.append(g); current=s; merged=True
                    history.append({'op':'merge','factor':g,'loss':round(loss,4),'score':round(s,4)})
                    break
    return selected,history


def corr(rows,a,b):
    xa=[r['x'][a] for r in rows]; xb=[r['x'][b] for r in rows]; ma,mb=mean(xa),mean(xb); sa,sb=stdev(xa),stdev(xb)
    return mean([(u-ma)*(v-mb)/(sa*sb) for u,v in zip(xa,xb)])


def fixed_diverse(rows,features,k=3):
    selected=[]; remaining=list(features)
    while remaining and len(selected)<k:
        best=None
        for f in remaining:
            sig=cv_score(rows,[f])-.5; red=max([abs(corr(rows,f,g)) for g in selected],default=0.0)
            cand=(sig-0.45*red,f)
            if best is None or cand>best: best=cand
        selected.append(best[1]); remaining.remove(best[1])
    return selected


def shuffled(rows,seed):
    rng=random.Random(seed); labs=[r['action'] for r in rows]; rng.shuffle(labs)
    return [{**r,'action':y} for r,y in zip(rows,labs)]


def main():
    raw={k:load_actions(v) for k,v in DATASETS.items()}
    raw_counts={k:dict(Counter(r['action'] for r in rows)) for k,rows in raw.items()}
    common=set(r['action'] for r in raw['contextual']) & set(r['action'] for r in raw['fin3'])
    common={y for y in common if all(sum(r['action']==y for r in rows)>=3 for rows in raw.values())}
    ds={k:[r for r in rows if r['action'] in common] for k,rows in raw.items()}
    if len(common)<2:
        out={'schema':'mathgraph.adaptive-residual-factorization-closure.v2','closure_pass':False,'hard_blocker':'fewer than two transferable operator families with >=3 examples per lineage','raw_action_counts':raw_counts,'common_actions':sorted(common)}
        OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True)); return
    all_static=[f for f in ds['contextual'][0]['x'] if f.startswith('static.') and f!='static.true_problem']
    structural=[f for f in all_static if f not in ('static.elapsed','static.search_persistence','static.replay_seconds','static.certificate_bytes')]
    tracks={}
    for family,features in [('all_static',all_static),('structural_only',structural)]:
        sels={}; histories={}
        for name,rows in ds.items(): sels[name],histories[name]=adaptive_select(rows,features)
        a_macro,a_acc=eval_features(ds['contextual'],ds['fin3'],sels['contextual']); b_macro,b_acc=eval_features(ds['fin3'],ds['contextual'],sels['fin3'])
        j=len(set(sels['contextual'])&set(sels['fin3']))/max(1,len(set(sels['contextual'])|set(sels['fin3'])))
        base={}
        for name,other in [('contextual','fin3'),('fin3','contextual')]:
            one,_=adaptive_select(ds[name],features,max_k=1); three=fixed_diverse(ds[name],features,3)
            base[name]={'k1_macro':round(eval_features(ds[name],ds[other],one)[0],4),'k3_diverse_macro':round(eval_features(ds[name],ds[other],three)[0],4),'k1_factors':one,'k3_factors':three}
        adaptive_macro=(a_macro+b_macro)/2; k1_macro=mean([base[d]['k1_macro'] for d in base]); k3_macro=mean([base[d]['k3_diverse_macro'] for d in base])
        shuffle=[]
        for seed in range(20):
            sc=shuffled(ds['contextual'],20260821+seed); sf,_=adaptive_select(sc,features); shuffle.append(eval_features(sc,ds['fin3'],sf)[0])
        tracks[family]={
            'selected':sels,'histories':histories,'selected_k':{k:len(v) for k,v in sels.items()},'factor_jaccard':round(j,4),
            'context_to_fin3_macro_recall':round(a_macro,4),'fin3_to_context_macro_recall':round(b_macro,4),'symmetric_adaptive_macro_recall':round(adaptive_macro,4),
            'context_to_fin3_accuracy':round(a_acc,4),'fin3_to_context_accuracy':round(b_acc,4),'baselines':base,
            'symmetric_k1_macro_recall':round(k1_macro,4),'symmetric_k3_diverse_macro_recall':round(k3_macro,4),
            'adaptive_gain_over_k1':round(adaptive_macro-k1_macro,4),'adaptive_gain_over_fixed_k3':round(adaptive_macro-k3_macro,4),
            'shuffle_ablation_mean_macro_recall':round(mean(shuffle),4),'shuffle_gap':round(adaptive_macro-mean(shuffle),4)}
    gates={
      'G1_self_stops':all(all(any(h['op']=='stop_equivalent' for h in t['histories'][d]) or t['selected_k'][d]>=12 for d in ds) for t in tracks.values()),
      'G2_sparse':all(all(t['selected_k'][d]<=4 for d in ds) for t in tracks.values()),
      'G3_cross_lineage_recurrence':all(t['factor_jaccard']>=0.25 for t in tracks.values()),
      'G4_beats_k1':all(t['adaptive_gain_over_k1']>0 for t in tracks.values()),
      'G5_competitive_with_fixed_k3':all(t['adaptive_gain_over_fixed_k3']>=-0.02 for t in tracks.values()),
      'G6_shuffle_ablation':all(t['shuffle_gap']>=0.10 for t in tracks.values()),
    }
    out={'schema':'mathgraph.adaptive-residual-factorization-closure.v2','datasets':{k:len(v) for k,v in ds.items()},'raw_action_counts':raw_counts,'common_actions':sorted(common),'tracks':tracks,'gates':gates,'closure_pass':all(gates.values())}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
