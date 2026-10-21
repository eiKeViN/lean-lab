#!/usr/bin/env python3
"""Every non-context source line must belong to a verbatim transported span."""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]

def uncomment(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   if s[i]=='\\':out.extend(s[i:i+2]);i+=2
   else:
    out.append(s[i]);string=s[i]!='"';i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:
   string=s[i]=='"';out.append(s[i]);i+=1
 if depth or string:raise RuntimeError('Unbalanced source lexical context')
 return ''.join(out)

def check():
 m=json.loads((HERE/'migration.json').read_text());missing=[];total=0
 for f in m['source_hashes']:
  source=(ROOT/m['reference']/f).read_text();raw=source.splitlines();lines=uncomment(source).splitlines();units=[u for u in m['units'] if u['source']==f]
  covered={i for u in units for i in range(u['start'],u['end']+1)}
  context={s.strip() for u in units for s in (u['prefix']+u['suffix']).splitlines()}
  for i,line in enumerate(lines,1):
   if not line.strip():continue
   total+=1
   if i in covered:continue
   if re.fullmatch(r'\s*(?:import\s+.+|namespace\s+[\w.]+|end(?:\s+[\w.]+)?|(?:noncomputable\s+)?section(?:\s+\w+)?)\s*',line):continue
   if raw[i-1].strip() in context:continue
   missing.append((f,i,raw[i-1]))
 if missing:raise RuntimeError('Untransported source lines: '+json.dumps(missing,ensure_ascii=False))
 print(f'Covered all {total} non-comment source lines across {len(m["source_hashes"])} reference files; only original import/scope context is replaced or replicated.')
if __name__=='__main__':check()
