from pathlib import Path
import json,subprocess,re
r=Path('results/module-final');data=json.loads((r/'batch-old.json').read_text())['groups'];result={}
def name(a):return '' if not a else (name(a[0])+'.' if a[0] else '')+str(a[1])
for owner,d in data.items():
 ns=[name(x[0]) for x in d['records']];p=r/(owner+'.lean');s=p.read_text();s=s[:s.index('open Lean\n')]+'''open Lean Meta Elab Command
run_elab do
  let env ← getEnv
  let names : Array Name := #[NAMES]
  for n in names do
    let actual ← realizeGlobalConstNoOverload (mkIdent n)
    logInfo m!"OLD_ATTR {n} defeq={defeqAttr.hasTag env actual} backward_defeq={backwardDefeqAttr.hasTag env actual}"
'''.replace('NAMES',', '.join('`'+n for n in ns));f=r/(owner+'.attrs.lean');f.write_text(s)
 with (r/(owner+'.attrs.log')).open('w') as log:status=subprocess.call(['lake','env','lean',str(f.resolve())],cwd='experiments/kl-for-mathlib',stdout=log,stderr=subprocess.STDOUT)
 if status:print((r/(owner+'.attrs.log')).read_text());raise SystemExit(status)
 for n,a,b in re.findall(r'OLD_ATTR (\S+) defeq=(true|false) backward_defeq=(true|false)',(r/(owner+'.attrs.log')).read_text()):result[n]={'defeq':a=='true','backward_defeq':b=='true'}
 print(owner,status,flush=True)
assert len(result)==9
(r/'old-equation-attrs.json').write_text(json.dumps(result,indent=2)+'\n')
