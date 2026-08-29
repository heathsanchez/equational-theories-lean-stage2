import importlib.util,json,sys
from pathlib import Path

HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_intercov',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)
BASE=Path('experiments/mathgraph/run_2666_six_atom_program_search.py')
s2=importlib.util.spec_from_file_location('sixatom_base',BASE)
b=importlib.util.module_from_spec(s2); sys.modules[s2.name]=b; s2.loader.exec_module(b)

# This audit replays the same non-teacher search logic, but checks whether the equality
# endpoints of the known 32-node proof ever appear. Teacher intermediates are observations,
# never injected into the search.
def main():
  eqs=h.load_equations(); m=h.load_solver(); source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860]); tl,tr=target[:2]
  nodes=[]; best={}; depths=[]
  def add(node,d):
    if len(nodes)>=b.MAX_NODES:return None
    k=(node.lhs,node.rhs); old=best.get(k)
    if old is not None and depths[old]<=d:return old
    nodes.append(node);depths.append(d);i=len(nodes)-1;best[k]=i;return i
  V=lambda n:('var',n); M=lambda a,c:('op',a,c)
  def H(args):
    sl,sr,vs=source;mp=dict(zip(vs,args));return add(m.EqualityNode(m.substitute(sl,mp),m.substitute(sr,mp),'source instance',substitution=tuple((v,mp[v]) for v in vs),constructor='six-atom-intermediate-audit'),0)
  def R(t):return add(m.EqualityNode(t,t,'reflexivity',constructor='six-atom-intermediate-audit'),0)
  def S(i,d):
    p=nodes[i];return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='six-atom-intermediate-audit'),d)
  def T(i,j,d):
    a,c=nodes[i],nodes[j]
    if a.rhs!=c.lhs:return None
    return add(m.EqualityNode(a.lhs,c.rhs,'transitivity',parents=(i,j),constructor='six-atom-intermediate-audit'),d)
  def C(i,j,d):
    a,c=nodes[i],nodes[j];lhs=M(a.lhs,c.lhs);rhs=M(a.rhs,c.rhs)
    if m.term_size(lhs)>b.MAX_TERM_SIZE or m.term_size(rhs)>b.MAX_TERM_SIZE:return None
    q1=add(m.EqualityNode(M(a.lhs,c.lhs),M(a.rhs,c.lhs),'congruence on left child',parents=(i,),context=('left',c.lhs),constructor='six-atom-intermediate-audit'),d)
    q2=add(m.EqualityNode(M(a.rhs,c.lhs),M(a.rhs,c.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='six-atom-intermediate-audit'),d)
    return T(q1,q2,d) if q1 is not None and q2 is not None else None

  x,y,z=V('x'),V('y'),V('z');v0=M(x,y);v1=M(x,v0);v2=M(v1,z);v3=M(v2,z);v6=M(v3,v0)
  args=[(v3,v0,v0),(v2,z,z),(v1,z,z),(M(v3,v3),z,z),(M(v6,v6),v0,v0),(x,v0,y)]
  atoms=[H(a) for a in args]
  visible=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
  for i in atoms: visible.update(m.walk_subterms(nodes[i].lhs));visible.update(m.walk_subterms(nodes[i].rhs))
  rids={t:R(t) for t in sorted(visible,key=lambda q:(m.term_size(q),m.render_term(q)))}

  # Build teacher equality endpoints in a private shadow DAG solely for comparison.
  shadow=[]
  def sa(lhs,rhs,name):shadow.append((lhs,rhs,name));return len(shadow)-1
  def sH(args,name):
    sl,sr,vs=source;mp=dict(zip(vs,args));return sa(m.substitute(sl,mp),m.substitute(sr,mp),name)
  def sR(t,name):return sa(t,t,name)
  def sS(i,name):a=shadow[i];return sa(a[1],a[0],name)
  def sT(i,j,name):a,c=shadow[i],shadow[j];assert a[1]==c[0];return sa(a[0],c[1],name)
  def sC(i,j,name):a,c=shadow[i],shadow[j];return sa(M(a[0],c[0]),M(a[1],c[1]),name)
  sh4=sH((v3,v0,v0),'h4'); sh5=sR(v0,'R(v0)'); sh7=sH((v2,z,z),'h7'); shv=sH((v1,z,z),'h(v1,z,z)')
  q1=sC(sh7,sh7,'C(h7,h7)'); q2=sC(q1,sR(z,'R(z)'),'C(C(h7,h7),R(z))'); p1=sT(shv,q2,'p1')
  p2=sT(p1,sS(sH((M(v3,v3),z,z),'h(v3²,z,z)'),'S(h(v3²,z,z))'),'p2')
  p3=sT(p2,sC(sh4,sh4,'C(h4,h4)'),'p3'); p4=sC(p3,sh5,'p4')
  p5=sT(p4,sS(sH((M(v6,v6),v0,v0),'h(v6²,v0,v0)'),'S(h(v6²,v0,v0))'),'p5')
  p6=sC(p5,sh5,'p6'); p7=sT(sH((x,v0,y),'h(x,v0,y)'),p6,'p7'); root=sT(p7,sS(sh4,'S(h4)'),'root')
  teacher=[x for x in shadow if not x[2].startswith('h') and not x[2].startswith('R') and not x[2].startswith('S(h')]

  target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
  def score(i):
    n=nodes[i];d=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr);rv=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
    return (0 if (n.lhs,n.rhs)==(tl,tr) else 1,min(d,rv),depths[i],m.term_size(n.lhs)+m.term_size(n.rhs),i)
  snapshots=[]
  def snap(r):
    rows=[];first=None
    for lhs,rhs,name in teacher:
      ok=(lhs,rhs) in best or (rhs,lhs) in best
      rows.append({'name':name,'present':ok})
      if first is None and not ok:first=name
    snapshots.append({'round':r,'nodes':len(nodes),'first_missing':first,'present':sum(x['present'] for x in rows),'total':len(rows),'rows':rows})
  snap(0)
  for r in range(1,b.ROUNDS+1):
    ranked=sorted(best.values(),key=score)[:b.BEAM]
    for i in ranked:S(i,r)
    ranked=sorted(best.values(),key=score)[:b.BEAM]; by_lhs={};by_rhs={}
    for i in ranked:by_lhs.setdefault(nodes[i].lhs,[]).append(i);by_rhs.setdefault(nodes[i].rhs,[]).append(i)
    for mid,lefts in list(by_rhs.items()):
      for i in lefts[:20]:
        for j in by_lhs.get(mid,())[:20]:T(i,j,r)
    ranked=sorted(best.values(),key=score);cset=[];seen=set()
    for i in atoms+ranked[:b.C_BEAM]:
      if i not in seen:seen.add(i);cset.append(i)
    for i in cset:
      for j in cset:
        C(i,j,r)
        if len(nodes)>=b.MAX_NODES:break
      if len(nodes)>=b.MAX_NODES:break
    snap(r);print(json.dumps(snapshots[-1],sort_keys=True),flush=True)
    if len(nodes)>=b.MAX_NODES or (tl,tr) in best:break
  out={'schema':'mathgraph.2666-six-atom-intermediate-coverage.v1','snapshots':snapshots,'nodes':len(nodes),'found':(tl,tr) in best}
  p=Path('experiments/mathgraph/results/2666-six-atom-intermediate-coverage.json');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('SUMMARY',json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
