from pathlib import Path
import json,subprocess,sys
root=Path.cwd();h=root/'experiments/kl-for-mathlib';r=root/'results/matcher-compat';groups={}
known={x['name'] for x in json.loads((r/'ordinary-library-v3-raw-diff.json').read_text())['changed']}
for x in json.loads((r/'ordinary-complete-raw-diff.json').read_text())['changed']:
 if x['name'] not in known:groups.setdefault(x['old']['module'],[]).append(x['name'])

source=(root/'results/module-final/BoundaryOldCapture.lean').read_text();codec=source[source.index('open Lean\n'):source.index('run_elab do')];body=source[source.index('run_elab do'):];body=body.replace('ci.value? | throwError "no old value {n}"','ci.value? (allowOpaque := true) | continue')
export=(h/'ImplementationPublicTypes.lean').read_text();export=export[export.index('open Lean\n'):export.index('run_elab do')]
for owner,ns in groups.items():
 p=r/(owner+'.ordinary-old.lean');out=r/(owner+'.ordinary-old.json');tsv=r/(owner+'.ordinary-old.tsv')
 old=subprocess.check_output(['git','show','382d29d94aaa8e32bcdeb24633f070d29695dcc3:experiments/kl-for-mathlib/'+('OAI.KL.Localization.GraphEmbedding' if owner=='OAI.KL.Localization.Edge' else owner).replace('.','/')+'.lean'],text=True)
 # These sources may already be modern in the accepted156 tree. Retain their
 # existing isolated legacy captures instead of removing module syntax ad hoc.
 if old.startswith('module\n'):
  print('already modern baseline',owner,flush=True);continue
 if owner=='OAI.KL.Localization.Edge':old+='\nopen Lean Meta Elab Command in\nrun_elab do\n  discard <| getEqnsFor? `OAI.KLInvariance.TitsSpace.embedLinear\n'
 b=body;a=b.index('  let names : Array Name := #[');z=b.index('\n  let env',a);b=b[:a]+'  let names : Array Name := #['+', '.join('`'+n for n in ns)+']'+b[z:];b=b.replace('../../results/module-final/old-expressions.json',str(out))
 b=b.replace('toJson ti])','toJson ti, toJson (Lean.Meta.defeqAttr.hasTag env n), toJson (Lean.Meta.backwardDefeqAttr.hasTag env n)])')
 e='''\nrun_elab do
  let env := (← Lean.getEnv).setExporting false
  let out ← IO.FS.Handle.mk "TSV" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\\tkl-public-types-v3"
    for n in NAMES do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\\tOWNER"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\\t{n}\\t{(toJson (reprStr ci.levelParams)).compress}\\t{id}\\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\\t{st.privateOwners.size}\\t{st.unrenamed.size}\\t0\\t0"
    out.putStrLn s!"SUMMARY\\tCOUNT\\t0\\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
'''.replace('TSV',str(tsv)).replace('OWNER',owner).replace('COUNT',str(len(ns))).replace('NAMES','#['+', '.join('`'+n for n in ns)+']')
 p.write_text('import Lean\n'+old+'\n'+codec+b+'\n'+export+e)
 cmd=[sys.executable,'scripts/recorded_run.py',str(r/(owner+'.ordinary-capture.log')),'bash','results/module-final/structure/run-lean.sh',str(p)]
 code=subprocess.call(cmd,cwd=root);print(owner,code,flush=True)
 if code:raise SystemExit(code)
