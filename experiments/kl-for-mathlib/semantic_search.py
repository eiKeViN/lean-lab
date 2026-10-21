#!/usr/bin/env python3
"""Small reproducible lexical search over Lean-exported names and docstrings."""
from pathlib import Path
import argparse,collections,json,math,re
HERE=Path(__file__).resolve().parent

def terms(text):
 text=re.sub(r'([a-z])([A-Z])',r'\1 \2',text)
 return set(re.findall(r'[a-z]+',text.lower()))

def search(corpus,query):
 q=terms(query);records=corpus['records'];docs=[terms(x['name']+' '+x['doc']) for x in records]
 freq=collections.Counter(t for d in docs for t in d)
 ranked=[]
 for row,d in zip(records,docs):
  matched=q&d
  score=sum(math.log(1+len(records)/(1+freq[t])) for t in matched)
  if score:ranked.append(dict(name=row['name'],score=round(score,8),matched=sorted(matched)))
 return sorted(ranked,key=lambda x:(-x['score'],x['name']))

def main():
 parser=argparse.ArgumentParser();parser.add_argument('corpus');parser.add_argument('--ablate-new-docs',action='store_true');parser.add_argument('--out',required=True);args=parser.parse_args()
 corpus=json.loads(Path(args.corpus).read_text())
 if corpus.get('schema')!=1 or corpus['count']!=len(corpus['records']) or not corpus['records'] or len({x['name'] for x in corpus['records']})!=len(corpus['records']):raise RuntimeError('Invalid/incomplete semantic corpus')
 if args.ablate_new_docs:
  additions=set(json.loads((HERE/'lemma-pilot.json').read_text())['additions'])
  for row in corpus['records']:
   if row['name'] in additions:row['doc']=''
 plan=json.loads((HERE.parents[1]/'reports/evidence/lemma-granularity/plan.json').read_text())
 results=[dict(id=q['id'],query=q['text'],ranking=search(corpus,q['text'])) for q in plan['queries']]
 Path(args.out).write_text(json.dumps(dict(schema=1,method='IDF-weighted set-token overlap; names and docstrings only; alphabetical tie-break',count=corpus['count'],ablate_new_docs=args.ablate_new_docs,queries=results),indent=2)+'\n')
if __name__=='__main__':main()
