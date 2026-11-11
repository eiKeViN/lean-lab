"""Check unmodified Lean sources in dependency order with independently built oleans.
Input is a reviewer-curated module -> relative source path map, never a participant command."""
import hashlib, json, os, re, shlex, shutil, sys, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
SUP=HERE.parent.parent/'supervision'
sys.path.insert(0,str(SUP))
import check_submission as checker
from room import execute

def hash_bytes(data):
 return hashlib.sha256(data).hexdigest()

def run(src, mapping, out):
 out.mkdir(parents=True,exist_ok=False)
 room=out/'room'
 project=room/'project'
 shutil.copytree(SUP/'lean-project',project)
 (project/'HGPExperiment.lean').unlink()
 cache=out.parent/'grade-cache';cache.mkdir(exist_ok=True)
 build=project/'.lake/build/lib/lean';build.mkdir(parents=True)
 records={}; mapping={checker.checked_name(m):f for m,f in mapping.items()}
 for m,f in mapping.items():
  source=src/checker.relative_path(f)
  if source.is_symlink() or not source.resolve().is_relative_to(src.resolve()):raise ValueError(str(source))
  data=source.read_bytes()
  dest=project/Path(*m.split('.')).with_suffix('.lean')
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
  imports=[]
  for match in re.finditer(r'(?m)^[ \t]*(?:(?:public|meta)\s+)*import\s+([^\n]+)',checker.strip_comments(data.decode())):
   imports.extend(x for x in match.group(1).split() if x.split('.')[0] not in checker.TRUSTED_ROOTS)
  records[m]={'origin':f,'sha256':hash_bytes(data),'imports':list(dict.fromkeys(imports))}
 def build_module(m,chain):
  r=records[m]
  if 'status' in r:return r['status']=='built'
  if m in chain:raise ValueError('circular local imports')
  missing=[d for d in r['imports'] if d not in records or not build_module(d,chain+[m])]
  if missing:r.update(status='blocked_by_local_dependency',blocked=missing);return False
  key=hash_bytes(json.dumps([m,r['sha256'],[records[d]['closure'] for d in r['imports']]]).encode())
  r['closure']=key
  rel=Path(*m.split('.'))
  target=build/rel.with_suffix('.olean')
  target.parent.mkdir(parents=True,exist_ok=True)
  cached=cache/key
  if (cache/(key+'.error')).is_file():
   r.update(status='failed',cached=True)
   shutil.copy2(cache/(key+'.error'),out/(m+'.build.log'))
   return False
  if cached.exists():
   for f in cached.iterdir():shutil.copy2(f,target.parent/f.name)
   r.update(status='built',cached=True);return True
  srcfile=rel.with_suffix('.lean').as_posix()
  cmd='cd project && lake env lean -o '+shlex.quote(str(target.relative_to(project)))+' '+shlex.quote(srcfile)
  start=time.monotonic()
  result=execute(room,cmd,360)
  (out/(m+'.build.log')).write_text(result)
  r['seconds']=round(time.monotonic()-start,2)
  passed=result.startswith('[exit 0]') and target.is_file() and not target.is_symlink()
  r['status']='built' if passed else ('timeout' if 'timed out' in result[:100] else 'failed')
  if not passed and result.startswith('[exit 1]') and re.search(r'\.lean:\d+:\d+: error',result):
   (cache/(key+'.error')).write_text(result)
  if passed:
   cached.mkdir()
   for f in target.parent.glob(target.stem+'.olean*'):
    if f.is_file() and not f.is_symlink():shutil.copy2(f,cached/f.name)
  (out/'progress.json').write_text(json.dumps(records,indent=2))
  print(out.name,m,r['status'],r['seconds'],flush=True)
  return passed
 for m in records:build_module(m,[])
 valid=[m for m,r in records.items() if r.get('status')=='built']
 if valid:
  audit=(HERE/'Audit.template.lean').read_text().replace('import Toy','\n'.join('import '+m for m in valid)).replace('[`Toy]', '['+', '.join('`'+m for m in valid)+']')
  (project/'IndependentAudit.lean').write_text(audit)
  result=execute(room,'cd project && lake env lean IndependentAudit.lean > /work/audit.log 2>&1',360)
  (out/'audit.exit').write_text(result)
  if result.startswith('[exit 0]'):
   log=room/'audit.log'
   if log.is_symlink():raise ValueError('unsafe log')
   for line in log.read_text().splitlines():
    if line.startswith('AUDIT '):
     row=json.loads(line[6:]);r=records[row.pop('module')]
     r.setdefault('declarations',[]).append(row)
 for m,r in records.items():
  source=project/Path(*m.split('.')).with_suffix('.lean')
  assert hash_bytes(source.read_bytes())==r['sha256']
 (out/'grade.json').write_text(json.dumps(records,indent=2)+'\n')
if __name__=='__main__':run(Path(sys.argv[1]),json.loads(Path(sys.argv[2]).read_text()),Path(sys.argv[3]))
