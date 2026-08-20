#!/usr/bin/env python3
import collections,importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]; SOLVER=ROOT/'submissions/mathgraph/solver.py'; RID='evaluation_hard_0196'; OUT=ROOT/'experiments/mathgraph/results/given-clause-certificate-analysis.json'

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def main():
 m=load(SOLVER,'mg_cert_analysis'); gate=load(ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py','given_gate_analysis')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_hard',split='train') if r.get('id')==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); recipe,stats=gate.solve_given(m,eng.search)
 rr=eng.inline_recipe(recipe); cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+3.0,eng.search.limits); nodes,root=cc.compile(rr)
 needed=m.proof_node_ids(nodes,root); code,proof_nodes=m.make_dag_certificate(target,nodes,root)
 kinds=collections.Counter(nodes[i].kind for i in needed)
 constructors=collections.Counter(str(nodes[i].constructor) for i in needed)
 term_sizes=[m.term_size(nodes[i].lhs)+m.term_size(nodes[i].rhs) for i in needed]
 lines=code.splitlines()
 report={
  'id':RID,'proof_nodes':proof_nodes,'needed_nodes':len(needed),'certificate_bytes':len(code.encode()),'lines':len(lines),
  'kinds':dict(kinds),'constructors':dict(constructors),'term_size_sum':sum(term_sizes),'term_size_max':max(term_sizes),'term_size_mean':sum(term_sizes)/len(term_sizes),
  'line_length_max':max(map(len,lines)),'line_length_mean':sum(map(len,lines))/len(lines),
  'certificate_head':code[:12000],
  'stats':stats,
 }
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='certificate_head'},indent=2,sort_keys=True))
if __name__=='__main__':main()
