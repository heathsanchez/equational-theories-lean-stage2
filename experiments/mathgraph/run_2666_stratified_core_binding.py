import importlib.util,json,sys,time
from pathlib import Path
from itertools import product
HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_corebind',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)

def main():
  eqs=h.load_equations(); m=h.load_solver(); source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860])
  key=lambda t:(m.term_size(t),m.render_term(t)); tl,tr=target[:2]
  base=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))|{('var',v) for v in target[2]}; base=sorted(base,key=key)
  gen1=[]; seen=set(base)
  for a in base:
    for b in base:
      t=('op',a,b)
      if m.term_size(t)<=21 and t not in seen: seen.add(t); gen1.append(t)
  squares=[]; attachments=[]
  for a in gen1:
    sq=('op',a,a)
    if m.term_size(sq)<=31 and sq not in seen: seen.add(sq); squares.append(sq)
    for b in base:
      for t in (('op',a,b),('op',b,a)):
        if m.term_size(t)<=31 and t not in seen: seen.add(t); attachments.append(t)
  dist=lambda t:(min(m.structural_distance(t,tl),m.structural_distance(t,tr)),m.term_size(t),m.render_term(t))
  pool=[]
  def take(items,n):
    for t in sorted(items,key=dist)[:n]:
      if t not in pool: pool.append(t)
  take(base,len(base)); take(gen1,60); take(squares,70); take(attachments,80); pool=pool[:220]
  # Core is stratified too: preserve variable-binding capacity for each constructor family.
  core=[]
  def ctake(items,n):
    for t in sorted(items,key=dist)[:n]:
      if t in pool and t not in core: core.append(t)
  ctake(base,16); ctake(gen1,16); ctake(squares,12); ctake(attachments,12)
  x,y,z=(('var','x'),('var','y'),('var','z')); M=lambda a,b:('op',a,b); v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
  # Ensure the exact retained witnesses are in the binding core if generated.
  for t in (M(v3,v3),M(v6,v6)):
    if t in pool and t not in core: core.append(t)
  limits={'max_term_size':35,'max_pool_terms':220,'max_core_terms':len(core),'max_source_attempts':900000,'max_source_edges':50000,'max_graph_edges':90000,'max_derivation_nodes':100000,'max_congruence_rounds':5}
  s=m.EqualitySearch(source,target,time.monotonic()+65,limits=limits); s.initial_pool=tuple(pool)
  # Reproduce instantiate_sources but use our explicit stratified core for fair enumeration.
  sv=source[2]; attempts=0
  for pattern in source[:2]:
    for concrete in pool:
      partial={}
      if not m.match_term(pattern,concrete,partial): continue
      missing=[v for v in sv if v not in partial]
      for fill in product(core[:18],repeat=len(missing)):
        mp=dict(partial); mp.update(zip(missing,fill)); s.add_source_substitution([mp[v] for v in sv]); attempts+=1
        if attempts>=s.max_source_attempts or s.graph_edges>=s.max_source_edges or s.expired(): break
      if attempts>=s.max_source_attempts or s.graph_edges>=s.max_source_edges or s.expired(): break
    if attempts>=s.max_source_attempts or s.graph_edges>=s.max_source_edges or s.expired(): break
  if not s.expired() and s.graph_edges<s.max_source_edges:
    for layer in range(len(core)):
      for indexes in product(range(layer+1),repeat=len(sv)):
        if layer and max(indexes)!=layer: continue
        s.add_source_substitution([core[i] for i in indexes]); attempts+=1
        if attempts>=s.max_source_attempts or s.graph_edges>=s.max_source_edges or s.expired(): break
      if attempts>=s.max_source_attempts or s.graph_edges>=s.max_source_edges or s.expired(): break
  teacher_args=[(v3,v0,v0),(v2,z,z),(v1,z,z),(M(v3,v3),z,z),(M(v6,v6),v0,v0),(x,v0,y)]
  sl,sr,vs=source; present=set()
  for n in s.nodes:
    if n.kind=='source instance': present.add((n.lhs,n.rhs)); present.add((n.rhs,n.lhs))
  rows=[]
  for i,args in enumerate(teacher_args,1):
    mp=dict(zip(vs,args)); eq=(m.substitute(sl,mp),m.substitute(sr,mp)); rows.append({'teacher_atom':i,'present':eq in present})
  root=s.shortest_path(); first=0
  for _ in range(5):
    if root is not None or s.expired(): break
    before=len(s.nodes); s.add_congruence_round(core[:56],first); first=before; root=s.shortest_path()
  out={'schema':'mathgraph.2666-stratified-core-binding.v1','pool':len(pool),'core':len(core),'contains_v3_square_core':M(v3,v3) in core,'contains_v6_square_core':M(v6,v6) in core,'teacher_atoms_present':sum(r['present'] for r in rows),'teacher_atoms_total':6,'rows':rows,'attempts':attempts,'graph_edges':s.graph_edges,'nodes':len(s.nodes),'exhaustion':s.exhaustion,'found':root is not None,'replayed':False}
  if root is not None:
    try: out['replayed']=bool(m.replay_dag(source,s.nodes,root,maximum_term_size=35,maximum_nodes=100000))
    except Exception as e: out['replay_error']=type(e).__name__+': '+str(e)
    out['proof']=h.proof_summary(s.nodes,root)
  p=Path('experiments/mathgraph/results/2666-stratified-core-binding.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
