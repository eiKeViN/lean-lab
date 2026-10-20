#!/usr/bin/env python3
"""Replay or verify an exact source-span file migration; never edits the reference."""
from pathlib import Path
import argparse,hashlib,json,sys,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def digest(b):return hashlib.sha256(b).hexdigest()
def products():
 m=json.loads((HERE/'migration.json').read_text());ref=ROOT/m['reference'];parts={}
 for p,h in {**m['source_hashes'],**m['fixed']}.items():
  if digest((ref/p).read_bytes())!=h:raise RuntimeError('Frozen reference changed: '+p)
 # Only existing instance-name insertions are permitted as body annotations.
 public=json.loads((HERE/'reference-public-types.json').read_text())['types']
 for patch in m.get('instance_annotations',[]):
  expected=re.sub(r'\binstance(?=\s*[:({\[])','instance _root_.'+patch['name'],patch['old'],count=1)
  if patch['new']!=expected or patch['old']==expected or patch['name'] not in public:
   raise RuntimeError('Invalid instance-name-only annotation')
 for u in m['units']:
  body=''.join((ref/u['source']).read_text().splitlines(True)[u['start']-1:u['end']])
  if digest(body.encode())!=u['sha256']:raise RuntimeError('Changed span: '+u['id'])
  bodylines=body.splitlines(True);prefix=u['prefix'];suffix=u['suffix']
  for patch in m.get('instance_annotations',[]):
   if patch['source']!=u['source']:continue
   if u['start']<=patch['line']<=u['end']:
    offset=patch['line']-u['start']
    if bodylines[offset]!=patch['old']:raise RuntimeError('Instance annotation mismatch')
    bodylines[offset]=patch['new']
   else:
    prefix=prefix.replace(patch['old'],patch['new'])
    suffix=suffix.replace(patch['old'],patch['new'])
  text=prefix+''.join(bodylines)+suffix
  parts[u['id']]=text
 files={p:(ref/p).read_bytes() for p in m['fixed']}
 for name,item in m['modules'].items():
  text='import Mathlib\n'+''.join('import '+d+'\n' for d in item['imports'])
  text+='\n/-! Semantic home: '+name+'. Source spans: '+', '.join(item['units'])+'.\nSee migration.json and MIGRATION.md for exact provenance. -/\n\nnamespace OAI\n\n'
  text+='\n\n'.join(parts[i] for i in item['units'])+'\nend OAI\n'
  files[name.replace('.','/')+'.lean']=text.encode()
 for name,imports in m['legacy_shims'].items():
  files[name.replace('.','/')+'.lean']=(''.join('import '+d+'\n' for d in imports)+'\n/-! Compatibility import for the pre-migration module. No declarations live here. -/\n').encode()
 files['OAI/Architecture.lean']=(''.join('import '+n+'\n' for n in sorted(m['modules']))+'import OAI.LinearAlgebra.KernelTransport\nimport OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat\n').encode()
 # The human index is derived from the same exact source-span manifest.
 byid={u['id']:u for u in m['units']}
 lines=['# Source migration index','','Reference: `../kl-kernel-transport` at `'+m['reference_commit']+'`.','Ranges below are inclusive, 1-based reference lines. Mathematical bodies are unchanged.','Existing anonymous instance names are pinned explicitly; Hecke inverse proofs restore their original local instance attribute.','Old module paths are import-only compatibility entries.','','## Old file → semantic homes','']
 for f in sorted(m['source_hashes']):
  lines+=['### '+Path(f).name,'']
  for name,x in sorted(m['modules'].items()):
   spans=[str(byid[i]['start'])+'–'+str(byid[i]['end']) for i in x['units'] if byid[i]['source']==f]
   if spans:lines.append('- `'+name.replace('.','/')+'.lean` ← '+', '.join(spans))
  lines.append('')
 lines+=['## Semantic modules → direct OAI imports','','Every implementation also imports the pinned Mathlib.','']
 for name,x in sorted(m['modules'].items()):
  lines.append('- `'+name+'`: '+(', '.join('`'+n+'`' for n in x['imports']) or '(Mathlib only)'))
 files['MIGRATION.md']=('\n'.join(lines)+'\n').encode()
 return files

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args();files=products()
 for path,data in files.items():
  dest=HERE/path
  if args.check:
   if not dest.exists() or dest.read_bytes()!=data:raise RuntimeError('Migration mismatch: '+path)
  elif not dest.exists() or dest.read_bytes()!=data:
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 actual={str(p.relative_to(HERE)) for p in (HERE/'OAI').rglob('*.lean')}
 expected={p for p in files if p.startswith('OAI/')}
 if actual!=expected:raise RuntimeError('Unexpected/missing OAI sources: '+str(actual^expected))
 print(('Verified' if args.check else 'Generated')+f' {len(expected)} OAI modules; exact moved source spans and fixed files.')
if __name__=='__main__':main()
