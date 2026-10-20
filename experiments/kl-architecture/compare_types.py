#!/usr/bin/env python3
"""Compare complete public mathematical types, up to documented alpha metadata."""
import hashlib,json,sys
from pathlib import Path

def load(path):
 nodes={};raw={};roots=[];types={};owner=None
 for line in Path(path).read_text().splitlines():
  tag,*fields=line.rstrip('\n').split('\t')
  if tag=='NODE':
   ident,s=fields;v=json.loads(s);raw[int(ident)]=v[:];k=v[0]
   children={'app':(1,2),'lam':(3,4),'forall':(3,4),'let':(2,3,4),'proj':(3,),'proof':(1,)}.get(k,())
   for i in children:v[i]=nodes[int(v[i])]
   nodes[int(ident)]=hashlib.sha256(json.dumps(v,separators=(',',':')).encode()).hexdigest()
  elif tag=='MODULE':owner=fields[0]
  elif tag=='TYPE':
   name,levels,node,kind=fields
   if name in types:raise ValueError('Duplicate public name: '+name)
   types[name]=dict(levels=levels,type=nodes[int(node)],kind=kind,module=owner)
   roots.append((int(node),False))
 # Check scope on the exported DAG, including shared nodes reached in both
 # contexts. Kernel-only binder metadata may never leak to a public type.
 seen=set()
 while roots:
  ident,proof=roots.pop()
  if (ident,proof) in seen:continue
  seen.add((ident,proof));v=raw[ident];k=v[0]
  if k in ('forall','lam') and ((v[2]=='kernel')!=proof):
   raise ValueError('Binder metadata crossed the compiler-proof boundary')
  children={'app':(1,2),'lam':(3,4),'forall':(3,4),'let':(2,3,4),'proj':(3,),'proof':(1,)}.get(k,())
  roots.extend((int(v[i]),True if k=='proof' else proof) for i in children)
 return types

def compare(old,new):
 missing=sorted(old.keys()-new.keys());added=sorted(new.keys()-old.keys());changed=[]
 for n in sorted(old.keys()&new.keys()):
  for field in ('levels','type','kind'):
   if old[n][field]!=new[n][field]:changed.append({'name':n,'field':field,'old':old[n],'new':new[n]})
 return dict(old_count=len(old),new_count=len(new),missing=missing,added=added,changed=changed,relocated=sum(old[n]['module']!=new[n]['module'] for n in old.keys()&new.keys()),passed=not(missing or added or changed))

def main():
 old=json.loads(Path(sys.argv[1]).read_text())['types'] if sys.argv[1].endswith('.json') else load(sys.argv[1])
 result=compare(old,load(sys.argv[2]));print(json.dumps(result,indent=2));sys.exit(0 if result['passed'] else 1)
if __name__=='__main__':main()
