from pathlib import Path
import json,sys,subprocess
sys.path.insert(0,'experiments/kl-for-mathlib');from compare_types import load
root=Path.cwd();p=root/'experiments/kl-for-mathlib';r=root/'results/module-final';D=load('results/for-mathlib/migrated-types.tsv',3947);names=json.loads((r/'probe-names.json').read_text());groups={}
for n in names:groups.setdefault(D[n]['module'],[]).append(n)
s=(p/'BoundaryOldCapture.lean').read_text();codec=s[s.index('open Lean\n'):s.index('run_elab do')];body=s[s.index('run_elab do'):];body=body.replace('let some v := ci.value? | throwError "no old value {n}"','let some v := ci.value? | continue')
for owner,ns in groups.items():
 old=(p/(owner.replace('.','/')+'.lean')).read_text();fixture='import Lean\n'+old+'\n'+codec+body
 a=fixture.index('  let names : Array Name := #[');b=fixture.index('\n  let env',a);fixture=fixture[:a]+'  let names : Array Name := #['+', '.join('`'+n for n in ns)+']'+fixture[b:]
 fixture=fixture.replace('../../results/module-final/old-expressions.json',str(r/(owner+'.json')))
 f=r/(owner+'.lean');f.write_text(fixture)
 with (r/(owner+'.capture.log')).open('w') as out:status=subprocess.call(['lake','env','lean',str(f)],cwd=p,stdout=out,stderr=subprocess.STDOUT)
 print(owner,status,flush=True)
 if status:print((r/(owner+'.capture.log')).read_text()[-2000:]);raise SystemExit(status)
