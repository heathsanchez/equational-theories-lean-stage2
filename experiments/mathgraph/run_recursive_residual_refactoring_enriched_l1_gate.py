#!/usr/bin/env python3
from __future__ import annotations
import hashlib, importlib.util, inspect, json, subprocess, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
RESULTS=HERE/'results'
OUT=RESULTS/'recursive-residual-refactoring-enriched-l1-gate.json'
EXPECTED_CORE_HASH='3525a3b605dad3ec19022a61389748baccbb077dfb6eceab2d585119b40920dd'


def load(path,name):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def main():
    base=load(HERE/'run_recursive_residual_refactoring_gate.py','rrr_base')
    rrt=load(HERE/'run_residual_representation_tournament.py','rrt_enriched')
    core_hash=hashlib.sha256(inspect.getsource(base.refactor).encode()).hexdigest()
    if core_hash!=EXPECTED_CORE_HASH:
        raise SystemExit(f'FROZEN CORE HASH MISMATCH: {core_hash} != {EXPECTED_CORE_HASH}')

    fp=RESULTS/'contextual_development_frozen/sample_200_development.json'
    dp=RESULTS/'contextual_development_all/sample_200_development.json'
    if not fp.exists() or not dp.exists():
        raise SystemExit('required contextual development result files missing')
    F={r['id']:r for r in json.loads(fp.read_text())}; D={r['id']:r for r in json.loads(dp.read_text())}

    examples=[]
    for rid in sorted(set(F)&set(D)):
        x,fm,dm=rrt.feat(F[rid],D[rid])
        pf=[m.get('portfolio') for m in fm]; pd=[m.get('portfolio') for m in dm]
        labels={
          'new_portfolio': any(p not in pf for p in pd),
          'target_narrowing': any(m.get('portfolio')=='target-narrowing' for m in dm),
          'target_structure_introduced': any(rrt.num(m.get('missing_target_introduced'))>0 for m in dm),
          'residual_trajectory_changed': pd!=pf or any(x[k]!=0 for k in ('diff.nodes','diff.source_total','diff.components_joined','diff.narrowing_successors','diff.overlaps_added')),
        }
        static={k:float(v) for k,v in x.items() if k.startswith('static.') and k!='static.true_problem' and isinstance(v,(int,float,bool))}
        response={k:float(v) for k,v in x.items() if (k.startswith('diff.') or k.startswith('rel.')) and isinstance(v,(int,float,bool))}
        enriched={**static,**response}
        examples.append({'id':rid,'static':static,'response':response,'enriched':enriched,'labels':labels})

    arms={}
    target_rows={}
    for target in sorted(examples[0]['labels']):
        target_rows[target]={}
        for arm in ('static','response','enriched'):
            rows=[{'id':e['id'],'x':e[arm],'y':int(e['labels'][target])} for e in examples]
            target_rows[target][arm]=base.evaluate(rows,sorted(rows[0]['x']),max_splits=3)
        s=target_rows[target]['static']; e=target_rows[target]['enriched']; r=target_rows[target]['response']
        arms[target]={
          'static':s,'response':r,'enriched':e,
          'enriched_gain_vs_static':e['heldout_bacc']-s['heldout_bacc'],
          'enriched_shuffle_gap':e['heldout_bacc']-e['shuffled_bacc'],
          'closed_old_l1_failure': bool(target=='target_narrowing' and s['heldout_bacc']<.65 and e['heldout_bacc']>=.65 and e['heldout_bacc']>=e['shuffled_bacc']+.05),
        }

    # Main gate: original failed L1 target closes without touching refactor core.
    tn=arms['target_narrowing']
    main_pass=tn['closed_old_l1_failure']
    # Breadth gate: enriched object shows real signal on >=2 residual outcomes.
    breadth=sum(v['enriched']['heldout_bacc']>=.65 and v['enriched_shuffle_gap']>=.05 for v in arms.values())
    # Improvement gate: median-like conservative count, at least two targets improve over static by >=5pp.
    improved=sum(v['enriched_gain_vs_static']>=.05 for v in arms.values())
    out={
      'schema':'mathgraph.recursive-residual-refactoring.enriched-l1.v1',
      'protocol':{
        'frozen_core_refactor_sha256':core_hash,
        'expected_core_refactor_sha256':EXPECTED_CORE_HASH,
        'core_unchanged':core_hash==EXPECTED_CORE_HASH,
        'same_hash_holdout_and_shuffle_falsifier':True,
        'representation_change_only_at_l1':True,
        'enriched_object':'static + intervention-response diff + relational response ratios',
        'no_true_problem_feature':True,
        'retrospective_response_features':True,
        'prospective_claim':False,
      },
      'feature_counts':{
        'static':len(examples[0]['static']),
        'response':len(examples[0]['response']),
        'enriched':len(examples[0]['enriched']),
      },
      'targets':arms,
      'gates':{
        'G1_frozen_core_hash':core_hash==EXPECTED_CORE_HASH,
        'G2_old_target_narrowing_l1_closes':main_pass,
        'G3_enriched_signal_on_at_least_two_outcomes':breadth>=2,
        'G4_enriched_improves_at_least_two_outcomes_by_5pp':improved>=2,
      },
      'counts':{'outcomes_with_enriched_signal':breadth,'outcomes_improved_ge_5pp':improved},
      'decision':'ENRICHED_L1_RETROSPECTIVE_PASS' if main_pass and breadth>=2 and improved>=2 else 'PARTIAL_OR_FAIL',
      'next_required':'If pass, freeze both core hash and enriched residual schema, then run prospective problem-disjoint episodes with causal ablation of response facets.'
    }
    RESULTS.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':main()
