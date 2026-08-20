#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions/mathgraph/solver.py'

def load_solver():
    spec=importlib.util.spec_from_file_location('mg_selector',SOLVER)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',type=Path,required=True); ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    m=load_solver(); rows=json.loads(args.input.read_text());
    if isinstance(rows,dict): rows=rows.get('rows',[])
    original=m.CompactSuperposition.target_score

    def stats(self,r):
        sl=self.m.term_size(r.lhs); sr=self.m.term_size(r.rhs)
        vl=len(self.m.term_variables(r.lhs)); vr=len(self.m.term_variables(r.rhs))
        targets=self.target[:2]
        dist=min([self.m.structural_distance(r.lhs,t) for t in targets]+[self.m.structural_distance(r.rhs,t) for t in targets])
        occ=0
        for t in targets:
            for st in self.m.walk_subterms(t):
                mp={}
                if self.m.match_term(r.lhs,st,mp): occ+=1
        return sl,sr,vl,vr,dist,occ

    def size_score(self,r):
        sl,sr,vl,vr,dist,occ=stats(self,r)
        return (sl+sr,max(sl,sr),r.cost,dist,-occ,self.m.render_term(r.lhs))
    def collapse_score(self,r):
        sl,sr,vl,vr,dist,occ=stats(self,r)
        reduction=abs(sl-sr); bare=int(r.lhs[0]=='var' or r.rhs[0]=='var')
        return (-bare,-reduction,min(sl,sr),vl+vr,r.cost,dist,-occ,self.m.render_term(r.lhs))
    def lowvar_score(self,r):
        sl,sr,vl,vr,dist,occ=stats(self,r)
        return (vl+vr,min(vl,vr),sl+sr,r.cost,dist,-occ,self.m.render_term(r.lhs))
    def hybrid_score(self,r):
        sl,sr,vl,vr,dist,occ=stats(self,r)
        compression=max(sl,sr)-min(sl,sr)
        return (0 if min(sl,sr)<=3 else 1,vl+vr,-compression,dist,r.cost,sl+sr,-occ,self.m.render_term(r.lhs))

    selectors={'baseline':original,'size':size_score,'collapse':collapse_score,'lowvar':lowvar_score,'hybrid':hybrid_score}
    out={'conditions':{},'summary':{}}
    base=dict(m.COMPACT_SUPERPOSITION_PROBE)
    base.update({'maximum_term_size':55,'maximum_replay_term_size':220,'maximum_depth':12,'maximum_rules':384,'maximum_rounds':32,'new_clauses_per_round':256,'maximum_clauses':5000,'normalization_steps':160,'maximum_proof_nodes':30000})
    for name,fn in selectors.items():
        m.CompactSuperposition.target_score=fn
        results=[]
        for row in rows:
            source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
            started=time.monotonic(); engine=m.TargetGroundedRefutation(source,target,time.monotonic()+5.0,dict(base)); found=engine.solve(); elapsed=time.monotonic()-started
            ok=False; nodes_count=None
            if found is not None:
                nodes,root=found; nodes_count=len(m.proof_node_ids(nodes,root)); ok=m.replay_dag(source,nodes,root,maximum_term_size=base['maximum_replay_term_size'],maximum_nodes=base['maximum_proof_nodes']) and (nodes[root].lhs,nodes[root].rhs)==target[:2]
            rec={'id':row['id'],'found':bool(found),'replay_ok':bool(ok),'elapsed':round(elapsed,6),'clauses':len(engine.search.clauses),'rounds':engine.search.rounds,'superpositions':engine.search.superpositions,'reductions':engine.search.reductions,'proof_nodes':nodes_count,'max_recipe_cost':engine.search.maximum_recipe_cost}
            print(name,json.dumps(rec,sort_keys=True),flush=True); results.append(rec)
        hits=[r['id'] for r in results if r['found'] and r['replay_ok']]
        out['conditions'][name]=results; out['summary'][name]={'count':len(hits),'hits':hits}
    m.CompactSuperposition.target_score=original
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(json.dumps(out,indent=2,sort_keys=True)); print(json.dumps(out['summary'],indent=2,sort_keys=True))
if __name__=='__main__': main()
