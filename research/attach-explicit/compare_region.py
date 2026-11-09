import sys,json,gzip,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'experiments/kl-for-mathlib'))
from compare_types import load,compare,CHILDREN
actual=Path(sys.argv[1]);out=Path(sys.argv[2]);expected=ROOT/'results/attach-explicit/reference-full.tsv'
a=load(expected,3947);b=load(actual);owners={v['module'] for v in b.values()}-{'ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties'}
wanted={k:v for k,v in a.items() if v['module'] in owners or k=='OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1'}
r=compare(wanted,b)
r['unexpected_names']=sorted(b.keys()-a.keys());r['passed']=r['passed'] and not r['unexpected_names']
def dag(p):
 nodes={};roots={}
 for line in p.read_text().splitlines():
  tag,*f=line.split('\t')
  if tag=='NODE':nodes[int(f[0])]=json.loads(f[1])
  if tag=='TYPE':roots[f[0]]=int(f[2])
 return nodes,roots
x,xr=dag(expected);y,yr=dag(actual)
def diff(i,j,path=()):
 u,v=x[i],y[j]
 if u[0]!=v[0]:return [{'path':path,'old':u,'new':v}]
 found=[]
 for k in range(len(u)):
  if k in CHILDREN.get(u[0],()):found+=diff(int(u[k]),int(v[k]),path+(k,))
  elif u[k]!=v[k]:found.append({'path':path+(k,),'old':u[k],'new':v[k]})
 return found
r['stalk_differences']=diff(xr['OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1'],yr['OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1'])
out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));sys.exit(0 if r['passed'] else 1)
