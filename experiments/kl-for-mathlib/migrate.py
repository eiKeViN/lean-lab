#!/usr/bin/env python3
"""Replay or verify an exact source-span file migration; never edits the reference."""
from pathlib import Path
import argparse,hashlib,json,sys,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from baseline import snapshot
from source_partitions import expand_units
def digest(b):return hashlib.sha256(b).hexdigest()
def pristine_products():
 m=json.loads((HERE/'migration.json').read_text());ref=snapshot('transport');parts={}
 if ref.commit!=m['reference_commit'] or ref.prefix!=m['reference']:raise RuntimeError('Unexpected immutable source baseline')
 for p,h in {**m['source_hashes'],**m['fixed']}.items():
  if digest(ref.read_bytes(p))!=h:raise RuntimeError('Frozen reference changed: '+p)
 # Only existing instance-name insertions are permitted as body annotations.
 public=json.loads((HERE/'reference-public-types.json').read_text())['types']
 for patch in m.get('instance_annotations',[]):
  expected=re.sub(r'\binstance(?=\s*[:({\[])','instance _root_.'+patch['name'],patch['old'],count=1)
  if patch['new']!=expected or patch['old']==expected or patch['name'] not in public:
   raise RuntimeError('Invalid instance-name-only annotation')
 expanded=expand_units(m['units'],m.get('unit_partitions',{}),ref.read_text)
 for parent in m['units']:
  if parent['id'] in m.get('unit_partitions',{}) and any(a['source']==parent['source'] and parent['start']<=a['line']<=parent['end'] for a in m['instance_annotations']):raise RuntimeError('Partitioned instance annotations require explicit review')
 for u in expanded:
  body=''.join(ref.read_text(u['source']).splitlines(True)[u['start']-1:u['end']])
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
 files={}
 for p in m['fixed']:
  dest=m.get('fixed_destinations',{}).get(p,p)
  b=ref.read_bytes(p)
  if p.endswith('.lean'):
   text=b.decode()
   def rewrite_import(match):
    name=match[1]
    destinations=m.get('split_module_imports',{}).get(name,[m['module_renames'].get(name,name)])
    return '\n'.join('import '+d for d in destinations)
   text=re.sub(r'^import (\S+)$',rewrite_import,text,flags=re.M)
   if p in ('KernelChecks.lean','CompatChecks.lean'):
    # Preserve exact module-set assertions across a physical module rename.
    # Watch both local library prefixes; all behavior examples stay verbatim.
    old='env.header.moduleNames.filter (·.toString.startsWith "OAI.")'
    new='env.header.moduleNames.filter (fun n => n.toString.startsWith "OAI." || n.toString.startsWith "ForMathlib.")'
    if old not in text:raise RuntimeError('Expected inherited import assertion')
    text=text.replace(old,new)
    for oldname in ('OAI.LinearAlgebra.KernelTransport','OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat'):
     text=text.replace('`'+oldname,'`'+m['module_renames'][oldname])
   b=text.encode()
  elif p=='lakefile.toml':
   b=b.replace(b'defaultTargets = ["OAI"]',b'defaultTargets = ["ForMathlib", "OAI"]')
   b+=b'\n[[lean_lib]]\nname = "ForMathlib"\nglobs = ["ForMathlib", "ForMathlib.+"]\n'
  files[dest]=b
 for name,item in m['modules'].items():
  text='import Mathlib\n'+''.join('import '+d+'\n' for d in item['imports'])
  description=item.get('description','')
  if '-/' in description:raise RuntimeError('Invalid module description')
  text+='\n/-! Semantic home: '+name+'. Source spans: '+', '.join(item['units'])+'.\nSee migration.json and MIGRATION.md for exact provenance.\n'+description+' -/\n\nnamespace OAI\n\n' if description else '\n/-! Semantic home: '+name+'. Source spans: '+', '.join(item['units'])+'.\nSee migration.json and MIGRATION.md for exact provenance. -/\n\nnamespace OAI\n\n'
  text+='\n\n'.join(parts[i] for i in item['units'])+'\nend OAI\n'
  files[name.replace('.','/')+'.lean']=text.encode()
 for name,imports in m['legacy_shims'].items():
  files[name.replace('.','/')+'.lean']=(''.join('import '+d+'\n' for d in imports)+'\n/-! Compatibility import for the pre-migration module. No declarations live here. -/\n').encode()
 files['ForMathlib.lean']=(''.join('import '+n+'\n' for n in sorted(m['modules']) if n.startswith('ForMathlib.'))+'import ForMathlib.LinearAlgebra.KernelTransport\n').encode()
 files['OAI/Architecture.lean']=(''.join('import '+n+'\n' for n in sorted(m['modules']))+'import ForMathlib.LinearAlgebra.KernelTransport\nimport OAI.KL.Compatibility.KernelTransport\n').encode()
 for name,imports in m.get('entrypoints',{}).items():
  files[name.replace('.','/')+'.lean']=(''.join('import '+n+'\n' for n in imports)).encode()
 # The human index is derived from the same exact source-span manifest.
 byid={u['id']:u for u in expanded}
 lines=['# Source migration index','','Reference: Git `'+m['reference_commit']+':'+m['reference']+'` (historical source, no checkout required).','Ranges below index the unchanged pristine reconstruction. The active extraction rounds have explicit proof-evolution exceptions; see proof-evolution.json and proof-evolution.patch. Partition records cover their immutable parent exactly.','Existing anonymous instance names are pinned explicitly; Hecke inverse proofs restore their original local instance attribute.','Original 34 KL entrypoints and kernel entrypoints are compatibility imports. Earlier semantic paths are recoverable from the pinned Git history, not maintained checkouts.','','## Old file → semantic homes','']
 for f in sorted(m['source_hashes']):
  lines+=['### '+Path(f).name,'']
  for name,x in sorted(m['modules'].items()):
   spans=[str(byid[i]['start'])+'–'+str(byid[i]['end']) for i in x['units'] if byid[i]['source']==f]
   if spans:lines.append('- `'+name.replace('.','/')+'.lean` ← '+', '.join(spans))
  lines.append('')
 lines+=['## Implementation modules → direct local imports','','Every implementation also imports the pinned Mathlib. This is the pristine import list; active proof-evolution integration edges are recorded in the hash-bound plan and DEPENDENCIES.dot.','']
 for name,x in sorted(m['modules'].items()):
  lines.append('- `'+name+'`: '+(', '.join('`'+n+'`' for n in x['imports']) or '(Mathlib only)'))
 files['MIGRATION.md']=('\n'.join(lines)+'\n').encode()
 return files

def products():
 from proof_evolution import overlay
 from module_integration import overlay as modules
 from module_rollout import overlay as rollout
 from attach_module import overlay as attach
 from module_next import overlay as next_modules
 from module_final import overlay as final_modules
 from module_all import overlay as all_modules
 from semantic_api import overlay as semantic_api
 from api_evolution import overlay as evolution
 from api_families import overlay as families
 from api_reflection import overlay as reflection
 from api_support import overlay as support
 return support(reflection(families(evolution(semantic_api(all_modules(final_modules(next_modules(attach(rollout(modules(overlay(pristine_products()))))))))))))

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args();files=products()
 for path,data in files.items():
  dest=HERE/path
  if args.check:
   if not dest.exists() or dest.read_bytes()!=data:raise RuntimeError('Migration mismatch: '+path)
  elif not dest.exists() or dest.read_bytes()!=data:
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 actual={str(p.relative_to(HERE)) for p in HERE.rglob('*.lean') if p.parts[len(HERE.parts)] in ('OAI','ForMathlib') or p==HERE/'ForMathlib.lean'}
 expected={p for p in files if p.startswith(('OAI/','ForMathlib/')) or p=='ForMathlib.lean'}
 if actual!=expected:raise RuntimeError('Unexpected/missing OAI sources: '+str(actual^expected))
 print(('Verified' if args.check else 'Generated')+f' {len(expected)} Lean modules; pristine reconstruction plus hash-bound proof evolution.')
if __name__=='__main__':main()
