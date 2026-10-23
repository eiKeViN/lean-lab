import gzip,json,hashlib
from pathlib import Path
CHILDREN={'app':(1,2),'lam':(3,4),'forall':(3,4),'let':(2,3,4),'proj':(3,),'proof':(1,)}
def read(s):
 nodes={};hs={};roots={}
 for line in s.splitlines():
  tag,*f=line.split('\t')
  if tag=='NODE':
   i=int(f[0]);v=json.loads(f[1]);nodes[i]=v;flat=v[:]
   for k in CHILDREN.get(v[0],()):flat[k]=hs[int(v[k])]
   hs[i]=hashlib.sha256(json.dumps(flat,separators=(',',':')).encode()).hexdigest()
  if tag=='TYPE':roots[f[0]]=int(f[2])
 return nodes,hs,roots
def app(nodes,i):
 args=[]
 while nodes[i][0]=='app':args.append(int(nodes[i][2]));i=int(nodes[i][1])
 return nodes[i],list(reversed(args))
a,ah,ar=read(gzip.open('reports/evidence/attach-module/stages/migrated-types.tsv.gz','rt').read());b,bh,br=read(Path('results/module-next/region-types.tsv').read_text())
out={}
for n in ['OAI.KLInvariance.MomentGraph.splitVertex.eq_1','OAI.KLInvariance.MomentGraph.splitEdge.eq_1']:
 i,j=ar[n],br[n]
 while a[i][0]=='forall' and b[j][0]=='forall':i=int(a[i][4]);j=int(b[j][4])
 head,x=app(a,i);head2,y=app(b,j)
 assert head[0]==head2[0]=='const' and head[1]==head2[1]=='`Eq'
 ha,x=app(a,x[-1]);hb,y=app(b,y[-1]);assert ha[1]==hb[1]=='`Equiv.mk'
 assert len(x)==len(y)==6
 out[n]={'constructor':ha[1],'fields':{label:{'canonical_equal':ah[u]==bh[v],'old_tag':a[u][0],'new_tag':b[v][0]} for label,u,v in zip(['domain','codomain','toFun','invFun','left_inv','right_inv'],x,y)},'interpretation':'RHS Equiv.mk data-field hashes agree and inverse-proof-field hashes differ. This probe does not classify the rest of the type or perform live defeq/ordinary historical-type acceptance. VertexDeletion restored legacy.'}
Path('results/module-next/vertex-expression-classification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
