#!/usr/bin/env python3
"""Two paired direct elaborations of old/new modules with the same warm dependencies.

No baseline checkout or second Lean project: one temporary input file is reused.
The input itself is elaborated on every command; no input .olean is accepted.
Run without another build competing for the compiler lock.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
from migrate import pristine_products
from proof_evolution import policy
HERE=Path(__file__).resolve().parent;OUT=HERE.parents[1]/'results/lemma-granularity';OUT.mkdir(exist_ok=True)
args=argparse.ArgumentParser();args.add_argument('--expansion',action='store_true');args.add_argument('--comparison',action='store_true');args=args.parse_args()
if args.expansion and args.comparison:raise SystemExit('Choose one round')
p=policy();pristine=pristine_products();input_path=OUT/'direct-input.lean'
if args.expansion or args.comparison:
 round_path='lemma-granularity-comparison' if args.comparison else 'lemma-granularity-expansion'
 plan=json.loads((HERE.parents[1]/('reports/evidence/'+round_path+'/plan.json')).read_text())
 chosen=dict.fromkeys(x['path'] for x in plan['samples'])
 profile_paths=list(zip(['transport','propagation','suffix'] if args.comparison else ['reflection','support','images','coset'],chosen))
else:profile_paths=list(zip(['sums','scaling','interval'],p['pristine_files']))
profiles=[]
for label,path in profile_paths:
 before=pristine[path];after=(HERE/path).read_bytes()
 if hashlib.sha256(before).hexdigest()!=p['pristine_files'][path]:raise RuntimeError('Wrong direct baseline')
 profiles.append(dict(label=label,path=path,before=before,after=after))
protocol=[]
for repeat in ((1,) if args.expansion or args.comparison else (1,2)):
 for sample in profiles:
  for side in (('before','after') if repeat==1 else ('after','before')):
   data=sample[side];input_path.write_bytes(data)
   label=("comparison-" if args.comparison else "expansion-" if args.expansion else "")+f"direct-r{repeat}-{side}-{sample['label']}"
   command=[sys.executable,str(HERE/'pilot_measure.py'),label,'lake','env','lean',str(input_path)]
   result=subprocess.run(command,cwd=HERE)
   protocol.append(dict(label=label,source=sample['path'],side=side,repeat=repeat,input_sha256=hashlib.sha256(data).hexdigest(),exit_code=result.returncode))
   (OUT/('comparison-direct-protocol.json' if args.comparison else 'expansion-direct-protocol.json' if args.expansion else 'direct-protocol.json')).write_text(json.dumps(protocol,indent=2)+'\n')
   if result.returncode:raise SystemExit(result.returncode)
