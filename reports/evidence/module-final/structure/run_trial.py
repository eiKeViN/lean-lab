from pathlib import Path
import json,hashlib,subprocess,re,sys,time
root=Path.cwd();h=root/'experiments/kl-for-mathlib';r=root/'results/module-final/structure';before=json.loads((r/'before-sources.json').read_text());first=json.loads((root/'results/module-final/first-scope.json').read_text())['files'];ledger=[]
assert json.loads((root/'results/module-final/checks-acceptance.json').read_text())['exit_code']==0
for p,s in before.items():assert (h/p).read_text()==s,p
sha=lambda b:hashlib.sha256(b).hexdigest()
old_artifacts={p:sha((h/'.lake/build/lib/lean'/p.replace('.lean','.olean')).read_bytes()) for p in before}
manifest={'base_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'files':{},'old_olean_hashes':old_artifacts}
for p,old in before.items():
 if p in first:
  t=old
  for e in sorted(first[p]['edits'],key=lambda e:e['start'],reverse=True):
   assert t[e['start']:e['start']+len(e['old'])]==e['old'];t=t[:e['start']]+e['new']+t[e['start']+len(e['old']):]
 else:
  t=re.sub(r'(?m)^import ','public import ',old);end=list(re.finditer(r'(?m)^public import [^\n]+',t))[-1].end();t=t[:end]+'\n\npublic section'+t[end:];t=re.sub(r'(?m)^([ \t]*)(?=(?:(?:noncomputable|protected|unsafe)\s+)*def\s)',r'\1@[expose] ',t);t='module\n'+t
  assert t.count('(quotientLinear α e)')==2
  t=t.replace('(quotientLinear α e)','((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap)')
 manifest['files'][p]={'before_sha256':sha(old.encode()),'trial_sha256':sha(t.encode())};(r/(p.rsplit('/',1)[-1]+'.trial')).write_text(t)
 manifest['files'][p]['trial_source']=t
(r/'trial-inputs.json').write_text(json.dumps(manifest,indent=2)+'\n')
def run(label,args):
 status=subprocess.call([sys.executable,str(root/'scripts/recorded_run.py'),str(r/(label+'.log')),*args],cwd=root)
 ledger.append({'label':label,'exit_code':status});(r/'trial-steps.json').write_text(json.dumps(ledger,indent=2)+'\n');return status
status=0
try:
 for p,v in manifest['files'].items():(h/p).write_text(v['trial_source'])
 status=run('candidate-build',['bash','-c','source scripts/env.sh && cd experiments/kl-for-mathlib && lake build ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure'])
 if status==0:
  status=run('ordinary-consumer',['bash','results/module-final/structure/run-lean.sh',str(r/'ModernConsumer.lean'),'--input',str(r/'old-ordered.json')])
  # Preserve raw export even if the independently tested consumer rejects a boundary.
  export=run('candidate-region',['bash','results/module-final/structure/run-lean.sh',str(r/'Region.lean'),'--types-out',str(r/'candidate-region.tsv')]);status=status or export
finally:
 for p,s in before.items():(h/p).write_text(s)
 restored=run('restore-build',['bash','-c','source scripts/env.sh && cd experiments/kl-for-mathlib && lake build ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure'])
 for p,s in before.items():assert (h/p).read_text()==s
 final_artifacts={p:sha((h/'.lake/build/lib/lean'/p.replace('.lean','.olean')).read_bytes()) for p in before}
 out={'production_sources_restored':True,'restored_build_exit':restored,'original_olean_hashes':old_artifacts,'restored_olean_hashes':final_artifacts,'artifact_bytes_identical':old_artifacts==final_artifacts,'trial_exit':status}
 (r/'restoration.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
raise SystemExit(status or restored)
