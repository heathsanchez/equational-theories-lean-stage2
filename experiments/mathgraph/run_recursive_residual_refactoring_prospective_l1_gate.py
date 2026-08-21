#!/usr/bin/env python3
from __future__ import annotations
import hashlib, importlib.util, inspect, json, random
from pathlib import Path

HERE=Path(__file__).resolve().parent
RESULTS=HERE/'results'
OUT=RESULTS/'recursive-residual-refactoring-prospective-l1-gate.json'
EXPECTED_CORE_HASH='3525a3b605dad3ec19022a61389748baccbb077dfb6eceab2d585119b40920dd'
SCHEMA_ID='mathgraph.l1.preoutcome-response.v1'
SEED=20260821


def load(path,name):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def num(x): return float(x) if isinstance(x,(int,float,bool)) else 0.0

def src_total(m):
    return sum(float(v) for v in m.get('source_instances',{}).values() if isinstance(v,(int,float)))

def first_non_target_probe(ms):
    # Strictly pre-outcome: initial-chain is state; the first subsequent portfolio
    # that is not target-narrowing is the bounded intervention response.
    for m in ms:
        if m.get('portfolio') not in (None,'initial-chain','target-narrowing'):
            return m
    return None

def accepted(row):
    for e in row.get('log',[]):
        if e.get('type')=='judge' and e.get('response',{}).get('status')=='accepted': return True
    return False

def main():
    base=load(HERE/'run_recursive_residual_refactoring_gate.py','rrr_prospective')
    rrt=load(HERE/'run_residual_representation_tournament.py','rrt_prospective')
    core_hash=hashlib.sha256(inspect.getsource(base.refactor).encode()).hexdigest()
    if core_hash!=EXPECTED_CORE_HASH: raise SystemExit(f'FROZEN CORE HASH MISMATCH {core_hash}')

    fp=RESULTS/'contextual_development_frozen/sample_200_development.json'
    dp=RESULTS/'contextual_development_all/sample_200_development.json'
    F={r['id']:r for r in json.loads(fp.read_text())};D={r['id']:r for r in json.loads(dp.read_text())}
    examples=[]
    for rid in sorted(set(F)&set(D)):
        # Restrict to theorem episodes so the later target-narrowing outcome is
        # not merely a true-vs-false classifier.
        if D[rid].get('verdict')!='true': continue
        x,fm,dm=rrt.feat(F[rid],D[rid])
        a=next((m for m in dm if m.get('portfolio')=='initial-chain'),{})
        p=first_non_target_probe(dm)
        static={k:float(v) for k,v in x.items() if k.startswith('static.') and k!='static.true_problem' and isinstance(v,(int,float,bool))}
        if p is None:
            response={
              'pre.probe_present':0.0,'pre.nodes_delta':0.0,'pre.source_total_delta':0.0,
              'pre.generations_delta':0.0,'pre.edges_delta':0.0,'pre.max_term_size_delta':0.0,
              'pre.replay_seconds_delta':0.0,'pre.source_family_delta':0.0,
              'pre.exhaustion_changed':0.0,'pre.found':0.0,
            }
        else:
            response={
              'pre.probe_present':1.0,
              'pre.nodes_delta':num(p.get('equality_nodes'))-num(a.get('equality_nodes')),
              'pre.source_total_delta':src_total(p)-src_total(a),
              'pre.generations_delta':num(p.get('generations'))-num(a.get('generations')),
              'pre.edges_delta':num(p.get('graph_edges'))-num(a.get('graph_edges')),
              'pre.max_term_size_delta':num(p.get('max_term_size'))-num(a.get('max_term_size')),
              'pre.replay_seconds_delta':num(p.get('replay_seconds'))-num(a.get('replay_seconds')),
              'pre.source_family_delta':float(len(p.get('source_instances',{}))-len(a.get('source_instances',{}))),
              'pre.exhaustion_changed':float(p.get('exhaustion')!=a.get('exhaustion')),
              'pre.found':float(bool(p.get('found'))),
            }
        # Later verifier-visible outcome. No target-narrowing metric or portfolio
        # identity is allowed into x.
        y=int(accepted(D[rid]) and any(m.get('portfolio')=='target-narrowing' and bool(m.get('found')) for m in dm))
        examples.append({'id':rid,'static':static,'response':response,'y':y})

    if not examples: raise SystemExit('no theorem examples')
    static_fs=sorted(examples[0]['static']); response_fs=sorted(examples[0]['response'])
    schema_hash=hashlib.sha256(json.dumps({'id':SCHEMA_ID,'features':response_fs},sort_keys=True).encode()).hexdigest()

    def rows_for(mode):
        rows=[]
        rng=random.Random(SEED)
        shuffled=[e['response'] for e in examples]; rng.shuffle(shuffled)
        structural={'pre.nodes_delta','pre.edges_delta','pre.source_total_delta','pre.source_family_delta','pre.generations_delta','pre.max_term_size_delta'}
        operational={'pre.replay_seconds_delta','pre.exhaustion_changed','pre.probe_present','pre.found'}
        for i,e in enumerate(examples):
            if mode=='static': xx=dict(e['static'])
            elif mode=='response': xx=dict(e['response'])
            elif mode=='enriched': xx={**e['static'],**e['response']}
            elif mode=='shuffled_response': xx={**e['static'],**shuffled[i]}
            elif mode=='response_no_structural': xx={k:v for k,v in e['response'].items() if k not in structural}
            elif mode=='response_no_operational': xx={k:v for k,v in e['response'].items() if k not in operational}
            elif mode=='response_no_presence': xx={k:v for k,v in e['response'].items() if k!='pre.probe_present'}
            else: raise ValueError(mode)
            rows.append({'id':e['id'],'x':xx,'y':e['y']})
        return rows

    modes=['static','response','enriched','shuffled_response','response_no_structural','response_no_operational','response_no_presence']
    arms={}
    for mode in modes:
        rows=rows_for(mode); fs=sorted(rows[0]['x'])
        arms[mode]=base.evaluate(rows,fs,max_splits=3)

    e=arms['enriched']; s=arms['static']; sh=arms['shuffled_response']; r=arms['response']
    gates={
      'G1_frozen_core_hash':core_hash==EXPECTED_CORE_HASH,
      'G2_problem_disjoint_hash_holdout':True,
      'G3_preoutcome_schema_only':True,
      'G4_enriched_bacc_ge_065':e['heldout_bacc']>=.65,
      'G5_enriched_beats_static_5pp':e['heldout_bacc']>=s['heldout_bacc']+.05,
      'G6_enriched_beats_shuffled_response_5pp':e['heldout_bacc']>=sh['heldout_bacc']+.05,
      'G7_response_has_signal':r['heldout_bacc']>=.60 and r['heldout_bacc']>=r['shuffled_bacc']+.05,
    }
    # Facet necessity is diagnostic, not required: we want to know what part of
    # the intervention response carries the predictive constraint.
    ablation_drop={m:e['heldout_bacc']-arms[m]['heldout_bacc'] for m in ('response_no_structural','response_no_operational','response_no_presence')}
    out={
      'schema':'mathgraph.recursive-residual-refactoring.prospective-l1.v1',
      'protocol':{
        'core_refactor_sha256':core_hash,'expected_core_refactor_sha256':EXPECTED_CORE_HASH,
        'residual_schema_id':SCHEMA_ID,'residual_schema_sha256':schema_hash,
        'problem_disjoint_hash_holdout':True,'same_refactor_all_arms':True,
        'theorem_episodes_only':True,'preoutcome_features_only':True,
        'target_portfolio_identity_excluded_from_features':True,
        'target_metrics_excluded_from_features':True,
        'later_outcome':'accepted theorem eventually closed by target-narrowing',
        'note':'sealed prospective-style replay on previously collected episodes; not yet a newly generated online episode set',
      },
      'counts':{'episodes':len(examples),'positives':sum(e['y'] for e in examples),'negatives':sum(not e['y'] for e in examples)},
      'feature_counts':{'static':len(static_fs),'preoutcome_response':len(response_fs)},
      'arms':arms,'ablation_drop_from_enriched':ablation_drop,'gates':gates,
      'decision':'PROSPECTIVE_L1_REPLAY_PASS' if all(gates.values()) else 'PARTIAL_OR_FAIL',
      'next_required':'If pass, freeze this exact schema hash and collect a genuinely fresh online problem-disjoint episode set before claiming prospective developmental self-application.'
    }
    RESULTS.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
