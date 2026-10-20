#!/usr/bin/env python3
"""Fail-closed public-type DAG reader and mathematical type comparator."""
import hashlib,json,re,sys
from pathlib import Path

FORMAT='kl-public-types-v3'
EXPECTED_PUBLIC_COUNT=3902
CHILDREN={'app':(1,2),'lam':(3,4),'forall':(3,4),'let':(2,3,4),'proj':(3,),'proof':(1,)}
ARITIES={'bvar':2,'sort':2,'const':3,'app':3,'lam':5,'forall':5,'let':6,'lit':2,'proj':4,'proof':2}
KINDS={'axiom','def','theorem','opaque','quotient','inductive','constructor','recursor'}

def load(path,expected_count=None):
 lines=Path(path).read_text().splitlines()
 if not lines or lines[0]!='FORMAT\t'+FORMAT:raise ValueError('Missing or unsupported export format')
 nodes={};raw={};roots=[];types={};owner=None;pending_owner=False
 copies=[];aliases=set();private_maps={};private_summary=None;summary=None
 for line in lines[1:]:
  if summary is not None:raise ValueError('Records after final SUMMARY')
  tag,*fields=line.split('\t')
  if tag=='NODE':
   if len(fields)!=2:raise ValueError('Malformed NODE')
   ident,s=fields;ident=int(ident)
   if ident<0 or ident in nodes:raise ValueError('Duplicate or negative node ID')
   v=json.loads(s)
   if not isinstance(v,list) or not v or v[0] not in ARITIES or len(v)!=ARITIES[v[0]] or not all(isinstance(x,str) for x in v):
    raise ValueError('Malformed expression node')
   raw[ident]=v[:];k=v[0]
   for i in CHILDREN.get(k,()):v[i]=nodes[int(v[i])]
   nodes[ident]=hashlib.sha256(json.dumps(v,separators=(',',':')).encode()).hexdigest()
  elif tag=='MODULE':
   if len(fields)!=1 or not fields[0] or pending_owner:raise ValueError('Malformed or orphan MODULE')
   owner=fields[0];pending_owner=True
  elif tag=='TYPE':
   if len(fields)!=4 or not pending_owner:raise ValueError('Malformed TYPE or missing MODULE')
   name,levels,node,kind=fields
   if not name or name in types or kind not in KINDS:raise ValueError('Duplicate or malformed public declaration')
   types[name]=dict(levels=levels,type=nodes[int(node)],kind=kind,module=owner)
   roots.append((int(node),False));pending_owner=False
  elif tag=='SERIALIZED_COPY':
   if len(fields)!=2 or fields[0] not in types:raise ValueError('Malformed serialization-copy record')
   copies.append(fields)
  elif tag=='PROOF_ALIAS':
   if len(fields)!=1 or not fields[0] or fields[0] in aliases:raise ValueError('Malformed proof-alias record')
   aliases.add(fields[0])
  elif tag=='PRIVATE_CANONICAL':
   if len(fields)!=2 or fields[0] in private_maps or fields[1] in private_maps.values():raise ValueError('Malformed or noninjective private mapping')
   private_maps[fields[0]]=fields[1]
  elif tag=='PRIVATE_SUMMARY':
   if len(fields)!=4 or private_summary is not None:raise ValueError('Malformed private summary')
   private_summary=tuple(map(int,fields))
  elif tag=='SUMMARY':
   if len(fields)!=3 or pending_owner:raise ValueError('Malformed SUMMARY or pending MODULE')
   summary=tuple(map(int,fields))
  else:raise ValueError('Unknown or empty record: '+tag)
 if summary is None or summary!=(len(types),len(copies),len(aliases)) or not types:
  raise ValueError('Missing SUMMARY, empty export, or incomplete export counts')
 if private_summary is None or private_summary[0]!=len(private_maps) or any(x<0 for x in private_summary) or private_summary[2:]!=(0,0):
  raise ValueError('Missing private summary, incomplete mappings, or private/public collision')
 if private_maps:raise ValueError('Nonempty private rewriting is outside this accepted experiment policy')
 if expected_count is not None and len(types)!=expected_count:raise ValueError('Unexpected public declaration coverage')
 # Scope is checked for each (node, context), including shared subexpressions.
 seen=set()
 while roots:
  ident,proof=roots.pop()
  if (ident,proof) in seen:continue
  seen.add((ident,proof));v=raw[ident];k=v[0]
  if k in ('forall','lam') and ((v[2]=='kernel')!=proof):raise ValueError('Binder metadata crossed the compiler-proof boundary')
  roots.extend((int(v[i]),True if k=='proof' else proof) for i in CHILDREN.get(k,()))
 return types

def load_snapshot(path,expected_count=EXPECTED_PUBLIC_COUNT):
 obj=json.loads(Path(path).read_text())
 if obj.get('private_canonical_rewrites')!=[]:raise ValueError('Reference snapshot requires an explicitly empty private rewrite map')
 if obj.get('schema')!=3 or obj.get('public_count')!=expected_count:raise ValueError('Invalid reference snapshot schema or count')
 types=obj.get('types')
 if not isinstance(types,dict) or len(types)!=expected_count or not types:raise ValueError('Incomplete reference snapshot')
 for name,item in types.items():
  if not isinstance(name,str) or not name or not isinstance(item,dict) or set(item)!={'levels','type','kind','module'}:raise ValueError('Malformed reference declaration')
  if not all(isinstance(v,str) and v for v in item.values()) or item['kind'] not in KINDS or not re.fullmatch('[0-9a-f]{64}',item['type']):raise ValueError('Malformed reference declaration fields')
 return types

def compare(old,new):
 missing=sorted(old.keys()-new.keys());added=sorted(new.keys()-old.keys());changed=[]
 for n in sorted(old.keys()&new.keys()):
  for field in ('levels','type','kind'):
   if old[n][field]!=new[n][field]:changed.append({'name':n,'field':field,'old':old[n],'new':new[n]})
 return dict(old_count=len(old),new_count=len(new),missing=missing,added=added,changed=changed,relocated=sum(old[n]['module']!=new[n]['module'] for n in old.keys()&new.keys()),passed=bool(old) and bool(new) and not(missing or added or changed))

def main():
 old=load_snapshot(sys.argv[1]) if sys.argv[1].endswith('.json') else load(sys.argv[1],EXPECTED_PUBLIC_COUNT)
 result=compare(old,load(sys.argv[2],EXPECTED_PUBLIC_COUNT));print(json.dumps(result,indent=2));sys.exit(0 if result['passed'] else 1)
if __name__=='__main__':main()
