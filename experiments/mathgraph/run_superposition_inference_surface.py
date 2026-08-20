#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'

def load_solver():
    spec=importlib.util.spec_from_file_location('mg_surface',SOLVER)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',type=Path,required=True); ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    m=load_solver(); rows=json.loads(args.input.read_text()); rows=rows.get('rows',rows) if isinstance(rows,dict) else rows
    Base=m.CompactSuperposition

    class BothOuter(Base):
        def critical_pair_side(self, outer, inner, oi, ii, side, path):
            left=self.freshen(outer,f'o{oi}_'); right=self.freshen(inner,f'i{ii}_')
            root=left.lhs if side==0 else left.rhs
            selected=self.m.get_subterm(root,path)
            unifier=self.m.unify_terms(selected,right.lhs)
            if unifier is None: return None
            left=self.instantiate(left,unifier); right=self.instantiate(right,unifier)
            root=left.lhs if side==0 else left.rhs
            changed=self.m.replace_subterm(root,path,right.rhs)
            other=left.rhs if side==0 else left.lhs
            if changed==other: return None
            lifted=self.lift(right,root,path)
            if side==0:
                rev= m.Recipe(left.rhs,left.lhs,'symmetry',(left,))
                return m.Recipe(left.rhs,changed,'transitivity',(rev,lifted))
            return m.Recipe(left.lhs,changed,'transitivity',(left,lifted))

        def solve(self):
            for round_index in range(self.limits['maximum_rounds']):
                self.rounds=round_index+1; rules=self.rules(); goal=self.target_proof(rules)
                if goal is not None: return goal
                proposals=[]; snapshot=rules
                for oi,outer in enumerate(snapshot):
                    for ii,inner in enumerate(snapshot):
                        for side,root in ((0,outer.lhs),(1,outer.rhs)):
                            for path in self.m.nonvariable_positions(root,maximum_depth=self.limits['maximum_depth'],include_root=True):
                                if self.expired(): return None
                                p=self.critical_pair_side(outer,inner,oi,ii,side,path)
                                if p is None: continue
                                p=self.interreduce(p,rules); proposals.append((self.target_score(p),p))
                proposals.sort(key=lambda x:x[0]); added=0
                for _,p in proposals:
                    if self.add_clause(p):
                        self.superpositions+=1; added+=1
                        if added>=self.limits['new_clauses_per_round']: break
                if not added or len(self.clauses)>=self.limits['maximum_clauses']: break
            return self.target_proof(self.rules())

    class AllOrientations(BothOuter):
        def rules(self):
            out=[]
            for c in self.clauses:
                if c.lhs[0] != 'var': out.append(c)
                if c.rhs[0] != 'var': out.append(m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
            out.sort(key=self.target_score)
            return out[:self.limits['maximum_rules']]

    conditions=[('baseline',Base),('both_outer',BothOuter),('all_orientations',AllOrientations)]
    out={'conditions':{},'summary':{}}
    base=dict(m.COMPACT_SUPERPOSITION_PROBE)
    base.update({'maximum_term_size':55,'maximum_replay_term_size':220,'maximum_depth':10,'maximum_rules':256,'maximum_rounds':24,'new_clauses_per_round':192,'maximum_clauses':4000,'normalization_steps':128,'maximum_proof_nodes':30000})
    for name,Cls in conditions:
        rr=[]
        for row in rows:
            source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
            seconds=5.0; started=time.monotonic()
            engine=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,dict(base))
            engine.search=Cls(m.RigidSuperpositionModule(),source,(engine.name_target(target[0],'Lx'),engine.name_target(target[1],'Rx'),target[2]),time.monotonic()+seconds,dict(base))
            # restore definitions for the newly named target
            for const,term in sorted(engine.reverse_constants.items()): engine.search.add_clause(m.Recipe(term,('var',const),'reflexivity'))
            found=engine.solve(); elapsed=time.monotonic()-started
            replay=False; pn=None
            if found is not None:
                nodes,root=found; pn=len(m.proof_node_ids(nodes,root)); replay=m.replay_dag(source,nodes,root,maximum_term_size=base['maximum_replay_term_size'],maximum_nodes=base['maximum_proof_nodes']) and (nodes[root].lhs,nodes[root].rhs)==target[:2]
            rec={'id':row['id'],'found':bool(found),'replay_ok':bool(replay),'elapsed':round(elapsed,6),'clauses':len(engine.search.clauses),'rounds':engine.search.rounds,'superpositions':engine.search.superpositions,'reductions':engine.search.reductions,'proof_nodes':pn}
            print(name,json.dumps(rec,sort_keys=True),flush=True); rr.append(rec)
        out['conditions'][name]=rr; hits=[r['id'] for r in rr if r['found'] and r['replay_ok']]; out['summary'][name]={'count':len(hits),'hits':hits}
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(json.dumps(out,indent=2,sort_keys=True)); print(json.dumps(out['summary'],indent=2,sort_keys=True))

if __name__=='__main__': main()
