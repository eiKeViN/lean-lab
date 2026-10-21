#!/usr/bin/env python3
"""Two paired direct elaborations of old/new modules with the same warm dependencies.

No baseline checkout or second Lean project: one temporary input file is reused.
The input itself is elaborated on every command; no input .olean is accepted.
Run without another build competing for the compiler lock.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
from migrate import pristine_products
from proof_evolution import policy
HERE=Path(__file__).resolve().parent;OUT=HERE.parents[1]/'results/lemma-granularity';OUT.mkdir(exist_ok=True)
p=policy();pristine=pristine_products();input_path=OUT/'direct-input.lean'
profiles=[]
for label,path in zip(['sums','scaling','interval'],p['pristine_files']):
 before=pristine[path];after=(HERE/path).read_bytes()
 if hashlib.sha256(before).hexdigest()!=p['pristine_files'][path]:raise RuntimeError('Wrong direct baseline')
 profiles.append(dict(label=label,path=path,before=before,after=after))
protocol=[]
for repeat in (1,2):
 for sample in profiles:
  for side in (('before','after') if repeat==1 else ('after','before')):
   data=sample[side];input_path.write_bytes(data)
   label=f"direct-r{repeat}-{side}-{sample['label']}"
   command=[sys.executable,str(HERE/'pilot_measure.py'),label,'lake','env','lean',str(input_path)]
   result=subprocess.run(command,cwd=HERE)
   protocol.append(dict(label=label,source=sample['path'],side=side,repeat=repeat,input_sha256=hashlib.sha256(data).hexdigest(),exit_code=result.returncode))
   (OUT/'direct-protocol.json').write_text(json.dumps(protocol,indent=2)+'\n')
   if result.returncode:raise SystemExit(result.returncode)
