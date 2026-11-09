#!/usr/bin/env python3
"""Use the unchanged production serializer on one freshly realized equation."""
import gzip,importlib.util,json,os,subprocess,sys,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];PROJECT=ROOT/'experiments/kl-for-mathlib'
shadow=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve()
if out.exists():raise SystemExit('Use a fresh output directory')
out.mkdir(parents=True)
source=(PROJECT/'PublicTypes.lean').read_text().split('run_elab do\n  let env ← getEnv',1)[0]
source=source.replace('import OAI.Architecture','import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic',1)
source+='''
run_elab do
  let some eqs ← Lean.Meta.getEqnsFor? ``OAI.KLInvariance.MomentGraph.Sheaf.stalkMap | throwError "no equation"
  let actual ← getConstInfo eqs[0]!
  let env ← getEnv
  let some path ← IO.getEnv "LEAN_TYPES_OUT" | throwError "output missing"
  let out ← IO.FS.Handle.mk path .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\\tkl-public-types-v3"
    out.putStrLn "MODULE\\tdiagnostic"
    let id ← dumpType env out actual.type
    out.putStrLn s!"TYPE\\t{actual.name}\\t{(toJson (reprStr actual.levelParams)).compress}\\t{id}\\ttheorem"
    let st ← get
    unless st.privateOwners.isEmpty do throw <| IO.userError "unexpected private rewrite"
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\\t0\\t{st.unrenamed.size}\\t0\\t0"
    out.putStrLn s!"SUMMARY\\t1\\t0\\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
'''
f=out/'FocusedStalkTypes.lean';f.write_text(source)
lean=ROOT/'.cache/lean-4.34.1-linux/bin/lean';lake=lean.with_name('lake')
path=subprocess.check_output([str(lake),'env','printenv','LEAN_PATH'],cwd=PROJECT,text=True).strip()
spec=importlib.util.spec_from_file_location('comparator',PROJECT/'compare_types.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
name='OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1';records={}
for label,prefix in [('old',''),('new',str(shadow)+os.pathsep)]:
 env=os.environ.copy();env.update(LEAN_PATH=prefix+path,LEAN_TYPES_OUT=str(out/(label+'.tsv')),LEAN_NUM_THREADS='4')
 (out/(label+'.environment.json')).write_text(json.dumps({k:env[k] for k in ['LEAN_PATH','LEAN_TYPES_OUT','LEAN_NUM_THREADS']},indent=2)+'\n')
 subprocess.run([sys.executable,str(ROOT/'scripts/measure.py'),str(out/(label+'.log')),str(lean),str(f)],env=env,cwd=PROJECT,check=True)
 records[label]=m.load(out/(label+'.tsv'),1)[name]
expected={}
for label,p in [('old','final-validation/migrated-types.tsv.gz'),('new','rejected-131/migrated-types.tsv.gz')]:
 text=gzip.open(ROOT/'reports/evidence/module-rollout'/p,'rt').read();tmp=out/(label+'-historical.tsv');tmp.write_text(text)
 expected[label]=m.load(tmp)[name]
 tmp.unlink()
 for field in ['levels','type','kind']:assert records[label][field]==expected[label][field],(label,field,records[label],expected[label])
(out/'comparison.json').write_text(json.dumps({'passed':True,'fresh':records,'historical':expected,'serializer_source_sha256':hashlib.sha256((PROJECT/'PublicTypes.lean').read_bytes()).hexdigest()},indent=2)+'\n')
print('Both fresh equation fingerprints exactly match the rejected-131 historical old/new records.')
