#!/usr/bin/env python3
from __future__ import annotations
import hashlib, importlib.util, itertools, json, math, random
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / 'results'
OUT = RESULTS / 'residual-constraint-graph-gate.json'
SEED = 20260821


def load(path, name):
    s = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


def num(x):
    return float(x) if isinstance(x, (int, float, bool)) else 0.0


def src_total(m):
    return sum(float(v) for v in m.get('source_instances', {}).values() if isinstance(v, (int, float)))


def accepted(row):
    return any(e.get('type') == 'judge' and e.get('response', {}).get('status') == 'accepted' for e in row.get('log', []))


def first_non_target_probe(ms):
    for m in ms:
        if m.get('portfolio') not in (None, 'initial-chain', 'target-narrowing'):
            return m
    return None


def quantile(vs, q):
    s = sorted(vs)
    if not s:
        return 0.0
    return s[min(len(s)-1, max(0, int(round(q*(len(s)-1)))))]


def bacc(y, pred):
    pos = [i for i, z in enumerate(y) if z]
    neg = [i for i, z in enumerate(y) if not z]
    if not pos or not neg:
        return 0.5
    tpr = sum(pred[i] for i in pos) / len(pos)
    tnr = sum(not pred[i] for i in neg) / len(neg)
    return 0.5 * (tpr + tnr)


def atom_key(a):
    return (a['feature'], a['direction'], a['threshold'])


def atom_holds(x, a):
    v = x.get(a['feature'], 0.0)
    return v >= a['threshold'] if a['direction'] == 'ge' else v <= a['threshold']


def conjunction_pred(rows, conj):
    return [all(atom_holds(r['x'], a) for a in conj) for r in rows]


def build_atoms(train, features):
    atoms = []
    for f in features:
        vs = [r['x'].get(f, 0.0) for r in train]
        if len(set(vs)) < 2:
            continue
        for q in (0.2, 0.35, 0.5, 0.65, 0.8):
            t = quantile(vs, q)
            for d in ('le', 'ge'):
                atoms.append({'feature': f, 'direction': d, 'threshold': t})
    # exact duplicate removal after quantile ties
    seen = set(); out = []
    for a in atoms:
        k = atom_key(a)
        if k not in seen:
            seen.add(k); out.append(a)
    return out


def score_conj(train, conj):
    y = [r['y'] for r in train]
    p = conjunction_pred(train, conj)
    support = sum(p)
    positives = sum(y)
    tp = sum(pi and yi for pi, yi in zip(p, y))
    precision = tp / max(1, support)
    recall = tp / max(1, positives)
    ba = bacc(y, p)
    # Sparse specifications are useful, but unsupported needles are not.
    if support < 3 or tp < 2:
        return -1.0, ba, precision, recall, support
    objective = ba + 0.04 * precision + 0.02 * recall - 0.015 * (len(conj)-1)
    return objective, ba, precision, recall, support


def mine(train, features, max_k=3):
    atoms = build_atoms(train, features)
    singles = sorted(((score_conj(train, (a,))[0], a) for a in atoms), reverse=True, key=lambda z: z[0])[:28]
    base = [a for s, a in singles if s >= 0]
    candidates = []
    for k in range(1, max_k+1):
        for conj in itertools.combinations(base, k):
            if len({a['feature'] for a in conj}) < k:
                continue
            sc = score_conj(train, conj)
            if sc[0] < 0:
                continue
            candidates.append((sc[0], sc, conj))
    candidates.sort(reverse=True, key=lambda z: z[0])
    return candidates[:80]


def evaluate_candidate(train, test, features, max_k):
    cand = mine(train, features, max_k=max_k)
    if not cand:
        return {'train_bacc': 0.5, 'heldout_bacc': 0.5, 'k': 0, 'atoms': [], 'support': 0}
    _, sc, conj = cand[0]
    return {
        'train_bacc': round(sc[1], 4),
        'heldout_bacc': round(bacc([r['y'] for r in test], conjunction_pred(test, conj)), 4),
        'k': len(conj),
        'support': sc[4],
        'precision': round(sc[2], 4),
        'recall': round(sc[3], 4),
        'atoms': list(conj),
    }


def nearest_neighbor(train, test, features):
    # Untyped numeric control: standardized nearest-neighbour over the same information.
    mu = {f: sum(r['x'][f] for r in train)/len(train) for f in features}
    sd = {}
    for f in features:
        v = sum((r['x'][f]-mu[f])**2 for r in train)/max(1, len(train)-1)
        sd[f] = math.sqrt(v) or 1.0
    pred=[]
    for r in test:
        best=None
        for t in train:
            d=sum(abs((r['x'][f]-t['x'][f])/sd[f]) for f in features)
            z=(d, t['id'], t['y'])
            if best is None or z < best: best=z
        pred.append(bool(best[2]))
    return bacc([r['y'] for r in test], pred)


def main():
    rrt = load(HERE/'run_residual_representation_tournament.py', 'rrt_constraint_graph')
    fp = RESULTS/'contextual_development_frozen/sample_200_development.json'
    dp = RESULTS/'contextual_development_all/sample_200_development.json'
    F={r['id']:r for r in json.loads(fp.read_text())}; D={r['id']:r for r in json.loads(dp.read_text())}

    examples=[]
    for rid in sorted(set(F)&set(D)):
        x0, fm, dm = rrt.feat(F[rid], D[rid])
        a = next((m for m in dm if m.get('portfolio')=='initial-chain'), {})
        p = first_non_target_probe(dm)
        static = {k:float(v) for k,v in x0.items() if k.startswith('static.') and k!='static.true_problem' and isinstance(v,(int,float,bool))}
        response = {
            'response.probe_present': float(p is not None),
            'response.nodes_delta': 0.0,
            'response.edges_delta': 0.0,
            'response.source_total_delta': 0.0,
            'response.generations_delta': 0.0,
            'response.max_term_size_delta': 0.0,
            'response.replay_seconds_delta': 0.0,
            'response.source_family_delta': 0.0,
            'response.exhaustion_changed': 0.0,
            'response.found': 0.0,
        }
        if p is not None:
            response.update({
                'response.nodes_delta': num(p.get('equality_nodes'))-num(a.get('equality_nodes')),
                'response.edges_delta': num(p.get('graph_edges'))-num(a.get('graph_edges')),
                'response.source_total_delta': src_total(p)-src_total(a),
                'response.generations_delta': num(p.get('generations'))-num(a.get('generations')),
                'response.max_term_size_delta': num(p.get('max_term_size'))-num(a.get('max_term_size')),
                'response.replay_seconds_delta': num(p.get('replay_seconds'))-num(a.get('replay_seconds')),
                'response.source_family_delta': float(len(p.get('source_instances',{}))-len(a.get('source_instances',{}))),
                'response.exhaustion_changed': float(p.get('exhaustion')!=a.get('exhaustion')),
                'response.found': float(bool(p.get('found'))),
            })
        later = [m for m in dm if m is not a and m is not p]
        labels = {
            'target_narrowing_closure': int(accepted(D[rid]) and any(m.get('portfolio')=='target-narrowing' and bool(m.get('found')) for m in dm)),
            'target_structure_introduced': int(any(num(m.get('missing_target_introduced'))>0 for m in later)),
            'component_bridge_activity': int(any(num(m.get('components_joined'))>0 for m in later)),
            'accepted_eventually': int(accepted(D[rid])),
        }
        examples.append({'id':rid, 'x':{**static, **response}, 'labels':labels})

    features=sorted(examples[0]['x'])
    ontology={
        'structural':[f for f in features if any(s in f for s in ('nodes','edges','term_size','generations'))],
        'source_identity':[f for f in features if any(s in f for s in ('source_','entropy','density'))],
        'operational':[f for f in features if any(s in f for s in ('elapsed','replay','exhaustion','probe_present','found'))],
        'response':[f for f in features if f.startswith('response.')],
        'static':[f for f in features if f.startswith('static.')],
    }
    ontology_hash=hashlib.sha256(json.dumps(ontology,sort_keys=True).encode()).hexdigest()

    targets={}
    for target in examples[0]['labels']:
        rows=[{'id':e['id'],'x':e['x'],'y':e['labels'][target]} for e in examples]
        if sum(r['y'] for r in rows)<5 or sum(not r['y'] for r in rows)<5:
            targets[target]={'eligible':False,'positives':sum(r['y'] for r in rows),'negatives':sum(not r['y'] for r in rows)}
            continue
        splits=[]
        for rep in range(24):
            train=[];test=[]
            for r in rows:
                h=int(hashlib.sha256((r['id']+'|constraint|'+str(rep)).encode()).hexdigest(),16)
                (test if h%5==0 else train).append(r)
            if sum(r['y'] for r in train)<3 or sum(not r['y'] for r in train)<3 or sum(r['y'] for r in test)<1 or sum(not r['y'] for r in test)<1:
                continue
            single=evaluate_candidate(train,test,features,1)
            graph=evaluate_candidate(train,test,features,3)
            nn=nearest_neighbor(train,test,features)
            # shuffle complete typed views across residual nodes while preserving marginals
            rng=random.Random(SEED+rep)
            perm=list(range(len(train))); rng.shuffle(perm)
            shtrain=[]
            for i,r in enumerate(train):
                donor=train[perm[i]]
                shtrain.append({'id':r['id'],'x':donor['x'],'y':r['y']})
            shuffled=evaluate_candidate(shtrain,test,features,3)
            splits.append({'rep':rep,'train':len(train),'test':len(test),'single':single,'graph':graph,'nearest_neighbor_bacc':round(nn,4),'shuffled_graph':shuffled})
        if not splits:
            targets[target]={'eligible':False,'reason':'no valid disjoint splits'}
            continue
        def med(vals):
            s=sorted(vals); return s[len(s)//2]
        gb=[z['graph']['heldout_bacc'] for z in splits]
        sb=[z['single']['heldout_bacc'] for z in splits]
        nb=[z['nearest_neighbor_bacc'] for z in splits]
        hb=[z['shuffled_graph']['heldout_bacc'] for z in splits]
        ks=[z['graph']['k'] for z in splits]
        recurring={}
        for z in splits:
            sig=' & '.join(sorted(a['feature']+':'+a['direction'] for a in z['graph']['atoms']))
            recurring[sig]=recurring.get(sig,0)+1
        targets[target]={
            'eligible':True,'positives':sum(r['y'] for r in rows),'negatives':sum(not r['y'] for r in rows),'valid_splits':len(splits),
            'median_graph_bacc':round(med(gb),4),'median_singleton_bacc':round(med(sb),4),'median_nearest_neighbor_bacc':round(med(nb),4),'median_shuffled_graph_bacc':round(med(hb),4),'median_graph_k':med(ks),
            'median_gain_vs_singleton':round(med([g-s for g,s in zip(gb,sb)]),4),
            'median_gain_vs_nearest':round(med([g-n for g,n in zip(gb,nb)]),4),
            'median_gain_vs_shuffled':round(med([g-h for g,h in zip(gb,hb)]),4),
            'nontrivial_combo_rate':round(sum(k>=2 for k in ks)/len(ks),4),
            'recurring_specs':[{'signature':k,'count':v} for k,v in sorted(recurring.items(), key=lambda kv:(-kv[1],kv[0]))[:8]],
            'splits':splits,
        }

    eligible=[v for v in targets.values() if v.get('eligible')]
    passing=[v for v in eligible if v['median_graph_bacc']>=.60 and v['median_gain_vs_singleton']>=.03 and v['median_gain_vs_shuffled']>=.05 and v['nontrivial_combo_rate']>=.5]
    gates={
        'G1_ontology_frozen_and_hashed':True,
        'G2_problem_disjoint_repeated_holdout':all(v['valid_splits']>=12 for v in eligible) if eligible else False,
        'G3_at_least_two_future_targets':len(eligible)>=2,
        'G4_graph_beats_single_types_on_one_target':any(v['median_gain_vs_singleton']>=.03 for v in eligible),
        'G5_graph_beats_shuffled_types_on_one_target':any(v['median_gain_vs_shuffled']>=.05 for v in eligible),
        'G6_nontrivial_intersection_recurs':any(v['nontrivial_combo_rate']>=.5 for v in eligible),
        'G7_full_specification_synthesis_pass':len(passing)>=1,
    }
    out={
        'schema':'mathgraph.residual-constraint-graph.v1',
        'protocol':{
            'ontology_sha256':ontology_hash,'ontology':ontology,
            'feature_timing':'static initial-chain + first non-target pre-outcome intervention response only',
            'thresholds_learned_on_train_only':True,'problem_disjoint_hash_holdout':True,'repeated_splits':24,
            'max_conjunction_size':3,'minimum_conjunction_support':3,'minimum_positive_support':2,
            'controls':['best singleton type','standardized raw nearest-neighbour','whole-view shuffled type graph'],
            'no_target_portfolio_identity_in_features':True,'no_later_target_metrics_in_features':True,
            'interpretation_rule':'latent specification credit requires a held-out conjunction advantage, not merely a strong individual atom',
        },
        'targets':targets,'gates':gates,
        'decision':'RESIDUAL_CONSTRAINT_GRAPH_PASS' if gates['G7_full_specification_synthesis_pass'] else 'PARTIAL_OR_FAIL',
        'next_required':'If pass, freeze recurring conjunctions as provisional specifications and test operator-family elimination/induction with ablation. If fail, enrich relational cross-residual views rather than adding more scalar residual features.'
    }
    RESULTS.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
