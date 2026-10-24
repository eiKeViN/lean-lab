from pathlib import Path
import json,gzip,hashlib
CH={'app':(1,2),'lam':(3,4),'forall':(3,4),'let':(2,3,4),'proj':(3,),'proof':(1,)}
def read(s):
 nodes={};hs={};roots={}
 for line in s.splitlines():
  tag,*f=line.split('\t')
  if tag=='NODE':
   i=int(f[0]);v=json.loads(f[1]);nodes[i]=v;flat=v[:]
   for k in CH.get(v[0],()):flat[k]=hs[int(v[k])]
   hs[i]=hashlib.sha256(json.dumps(flat,separators=(',',':')).encode()).hexdigest()
  if tag=='TYPE':roots[f[0]]=int(f[2])
 return nodes,hs,roots
r=Path('results/module-final');a,ah,ar=read((r/'final-public-v2.tsv').read_text());b,bh,br=read(gzip.decompress((r/'failed-full-1/migrated-types.tsv.gz').read_bytes()).decode());out=[]
def walk(i,j,path):
 if ah[i]==bh[j]:return
 x,y=a[i],b[j]
 if x[0]!=y[0] or len(x)!=len(y) or any(x[k]!=y[k] for k in range(len(x)) if k not in CH.get(x[0],())):out.append(dict(path=path,regional=x,complete=y));return
 for k in CH.get(x[0],()):walk(int(x[k]),int(y[k]),path+[k])
n='OAI.KLInvariance.TitsSpace.Represents.extendedAction_eq';walk(ar[n],br[n],[]);(r/'ordinary-full-expression-diff.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
