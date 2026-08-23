#!/usr/bin/env python3
import copy, json, sys
from collections import Counter
from pathlib import Path
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour
import run_methodology_0036_goal_cut_descaffold_v1 as desc
import run_methodology_0036_postcontractor_factorization_v1 as post

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-plateau-invariant-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-plateau-invariant-v1.json'
RID='evaluation_normal_0036'

FEATURES=('lhs_kind','rhs_kind','size_gap','variable_count_gap','subterm_relation')

def relaxed_pool(m,s,source,target,st,cap=19,limit=100000):
    anchors,fills=post.l1_terms(m,s,target,st)
    cands,_=post.enumerate_candidates(m,s,source,target,st,anchors,fills,cap,limit)
    return cands

def score(m,s,target,c):
    return desc.simulate_goal_separation(m,s,target,c)

def apply_direct(s,c,step):
    return s.ensure_source_mapping(c['mapping'],False,'plateau-invariant',step)

def signature(m,a,b):
    if m.is_subterm(a,b): sub='L_IN_R'
    elif m.is_subterm(b,a): sub='R_IN_L'
    else: sub='NONE'
    return {
        'lhs_kind':a[0],
        'rhs_kind':b[0],
        'size_gap':abs(m.term_size(a)-m.term_size(b)),
        'variable_count_gap':abs(len(m.term_variables(a))-len(m.term_variables(b))),
        'subterm_relation':sub,
    }

def boundary_profile(m,s,target):
    st=tour.cut.component_state(m,s,target,1000000)
    if st is None: return None
    if st.get('connected'):
        return {'connected':True,'cross_distance':0,'pair_count':0,'signatures':[],'state':st}
    sigs=[]
    for rec in st.get('boundary_pairs',[]):
        # Recover exact terms by matching rendered strings against live members.
        la=rec['lhs_component_term']; rb=rec['rhs_component_term']
        aa=next((t for t in st['lhs_members'] if m.render_term(t)==la),None)
        bb=next((t for t in st['rhs_members'] if m.render_term(t)==rb),None)
        if aa is not None and bb is not None: sigs.append(signature(m,aa,bb))
    return {'connected':False,'cross_distance':st.get('cross_distance'),'pair_count':len(sigs),'signatures':sigs,'state':st}

def sig_key(sig):
    return tuple(sig[k] for k in FEATURES)

def summarize_profiles(profiles):
    all_sigs=[sig for p in profiles for sig in p['signatures']]
    domains={f:sorted({str(sig[f]) for sig in all_sigs}) for f in FEATURES}
    invariant={f:vals[0] for f,vals in domains.items() if len(vals)==1}
    counts=Counter(sig_key(sig) for sig in all_sigs)
    return {
        'profile_count':len(profiles),
        'boundary_signature_count':len(all_sigs),
        'unique_full_signatures':len(counts),
        'signature_counts':{repr(k):v for k,v in counts.items()},
        'feature_domains':domains,
        'invariant_features':invariant,
    }

def main():
    p=json.loads(PROTO.read_text())
    assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=tour.cut.load_hist()
    row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    base,old,new,admitted,edges,first,nid,st=post.reconstruct_post_step(m,source,target,cfg)
    parent_ok=(base.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and nid is not None and st is not None and not st.get('connected') and st.get('cross_distance')==8)
    if not parent_ok:
        out={'schema':p['schema'],'id':RID,'decision':'MEASUREMENT_FAILURE','measurement_ok':False,'sealed_transfer_ids_loaded':[]}
    else:
        profiles=[]; examples=[]; strict_found=0; depth1_count=0; depth2_count=0
        p0=boundary_profile(m,base,target); profiles.append(p0)
        pool=relaxed_pool(m,base,source,target,st,19,100000)
        firsts=sorted([(score(m,base,target,c),c) for c in pool if score(m,base,target,c) is not None],key=lambda x:(x[0],x[1]['key']))
        firsts=[x for x in firsts if x[0]<=8][:p['constraints']['maximum_first_steps']]
        for i,(d1,c1) in enumerate(firsts):
            s1=copy.deepcopy(base)
            if apply_direct(s1,c1,2) is None: continue
            q1=boundary_profile(m,s1,target)
            if q1 is None: continue
            if q1['connected'] or q1['cross_distance']<8:
                strict_found+=1
            else:
                profiles.append(q1); depth1_count+=1
                if len(examples)<p['constraints']['report_examples']:
                    examples.append({'depth':1,'move':tour.public_candidate(m,c1),'cross_distance':q1['cross_distance'],'signatures':q1['signatures'][:5]})
            if q1['connected']: continue
            pool2=relaxed_pool(m,s1,source,target,q1['state'],19,100000)
            seconds=sorted([(score(m,s1,target,c2),c2) for c2 in pool2 if score(m,s1,target,c2) is not None],key=lambda x:(x[0],x[1]['key']))
            seconds=[x for x in seconds if x[0]<=8][:p['constraints']['maximum_second_steps_per_first']]
            for d2,c2 in seconds:
                s2=copy.deepcopy(s1)
                if apply_direct(s2,c2,3) is None: continue
                q2=boundary_profile(m,s2,target)
                if q2 is None: continue
                if q2['connected'] or q2['cross_distance']<8:
                    strict_found+=1
                else:
                    profiles.append(q2); depth2_count+=1
                    if len(examples)<p['constraints']['report_examples']:
                        examples.append({'depth':2,'first':tour.public_candidate(m,c1),'second':tour.public_candidate(m,c2),'cross_distance':q2['cross_distance'],'signatures':q2['signatures'][:5]})
        summary=summarize_profiles(profiles)
        nontrivial={k:v for k,v in summary['invariant_features'].items() if k in FEATURES}
        if strict_found:
            decision='MEASUREMENT_FAILURE'
        elif nontrivial:
            decision='PLATEAU_SIGNATURE_INVARIANT'
        else:
            decision='PLATEAU_SIGNATURE_MULTIMODAL'
        out={
            'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':decision!='MEASUREMENT_FAILURE',
            'parent':{'cross_distance':8,'old_nodes':len(old),'reentry_edges':edges,'first_contractor':tour.public_candidate(m,first)},
            'exploration':{'depth0_states':1,'depth1_states':depth1_count,'depth2_states':depth2_count,'strict_contractions_observed':strict_found},
            'plateau':summary,'examples':examples,'sealed_transfer_ids_loaded':[]
        }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
