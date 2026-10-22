#!/usr/bin/env python3
"""Bounded in-place module experiment; always restore exact product sources.
Run after setup: source scripts/env.sh; python3 scripts/module_pilot.py
Raw logs and generated consumers stay under ignored results/. No second project.
"""
import hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
P = ROOT/'experiments/kl-for-mathlib'
OUT = ROOT/'results/module-pilot'
BASE = '999bdb033bf54abf48ff2bf9d5c12a514fdc9576'
S = 'ForMathlib.Algebra.BigOperators.SingleCoordinate'
K = 'ForMathlib.LinearAlgebra.KernelTransport'
C = 'OAI.KL.Compatibility.KernelTransport'
NAMES = ['OAI.KLInvariance.weighted_sum_exchange', 'OAI.KLInvariance.weighted_sum_single',
 'OAI.KLInvariance.finite_character_cancellation', 'OAI.KLInvariance.Comparison.matrix_difference_single',
 'OAI.KLInvariance.Comparison.matrix_difference_le']
KNAMES = [f'OAI.{ns}.{n}' for ns in ['LinearEquiv','KLInvariance'] for n in
 ['kernelSourceEquiv','kernelTargetEquiv','kernelMixedEquiv']]
records = []
def path(m): return P/(m.replace('.','/')+'.lean')
def run(label, args, expect=0, error_contains=None):
    log = OUT/(label+'.log')
    r = subprocess.run([sys.executable, str(ROOT/'scripts/measure.py'), str(log), *args], cwd=P)
    data = json.loads(log.with_suffix('.json').read_text()); data['label']=label
    records.append(data); (OUT/'measurements.json').write_text(json.dumps(records,indent=2)+'\n')
    if (expect == 0 and r.returncode != 0) or (expect != 0 and r.returncode == 0):
        raise RuntimeError(f'{label}: unexpected status {r.returncode}')
    text = log.read_text()
    if expect != 0 and (error_contains is None or error_contains not in text):
        raise RuntimeError("Missing expected diagnostic: "+label)
    types = [line for line in text.splitlines() if line.startswith('TYPE_RAW ')]
    if label.startswith('kernel-') and label.endswith('-modern') and len(types) != len(KNAMES):
        raise RuntimeError('Incomplete modern kernel type audit: '+label)
    if types:
        reference = OUT/('kernel-types.json' if label.startswith('kernel') else 'single-types.json')
        if reference.exists() and types != json.loads(reference.read_text()):
            raise RuntimeError('Type drift: '+label)
    return text
def artifact(m):
    stem=P/'.lake/build/lib/lean'/m.replace('.','/')
    return {str(f.relative_to(P)): {'sha256': hashlib.sha256(f.read_bytes()).hexdigest(), 'bytes':f.stat().st_size}
            for f in stem.parent.glob(stem.name+'.*') if f.is_file()}
def audit(names):
    ns=', '.join('`'+n for n in names)
    return '''\nopen Lean in
private partial def pilotType (e : Expr) : Expr :=
  match e with
  | .forallE _ t b bi => .forallE `_ (pilotType t) (pilotType b) bi
  | .lam _ t b bi => .lam `_ (pilotType t) (pilotType b) bi
  | .letE _ t v b nd => .letE `_ (pilotType t) (pilotType v) (pilotType b) nd
  | .app f a => .app (pilotType f) (pilotType a)
  | .proj n i b => .proj n i (pilotType b)
  | .mdata _ b => pilotType b
  | other => other

set_option pp.universes true in
run_elab do
  let env ← Lean.getEnv
  Lean.logInfo m!"MODULES {env.header.moduleNames.size}"
  for n in #[NAMES] do
    let ci ← Lean.getConstInfo n
    unless Lean.getOriginalConstKind? env n == some (if THM then .thm else .defn) do
      throwError "Wrong original kind: {n}"
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => #[`propext, `Quot.sound, `Classical.choice].contains a) do
      throwError "Unexpected axioms: {n}: {axs}"
    Lean.logInfo m!"TYPE_RAW {n}: {(Lean.toJson (reprStr ci.levelParams, reprStr (pilotType ci.type))).compress}"
    Lean.logInfo m!"KIND {n}: {repr ci.toConstantVal.name} theorem={ci matches .thmInfo _} axiom={ci matches .axiomInfo _}"
    Lean.logInfo m!"AXIOMS {n}: {axs}"
'''.replace('NAMES',ns).replace('THM','true' if names == NAMES else 'false')
def consumer(label,m,names,modern=False,all_=False,body=''):
    f=OUT/(label+'.lean')
    f.write_text(('module\n' if modern else '')+('import all ' if all_ else 'import ')+m+'\n'+body+audit(names))
    text=run(label,['lake','env','lean',str(f)])
    types=[line for line in text.splitlines() if line.startswith('TYPE_RAW ')]
    key='single-types' if names == NAMES else 'kernel-types'
    reference=OUT/(key+'.json')
    if not reference.exists():reference.write_text(json.dumps(types,indent=2))
    elif types!=json.loads(reference.read_text()):raise RuntimeError('Type drift: '+label)
    if len(types)!=len(names):raise RuntimeError('Incomplete type audit: '+label)
    return text
def variant(original, modern, narrow=None, expose=False):
    head, body=original.split('\n',1)
    imports=narrow or [head.removeprefix('import ')]
    if expose: body=body.replace('\ndef ', '\n@[expose] def ')
    return ('module\n' if modern else '')+'\n'.join(('public import ' if modern else 'import ')+x for x in imports)+'\n'+ ('\npublic section\n' if modern else '')+body

def main():
    if (OUT/'measurements.json').exists():raise RuntimeError('Archive existing results before a fresh run: '+str(OUT))
    OUT.mkdir(parents=True,exist_ok=True)
    originals={m:path(m).read_text() for m in [S,K,C]}
    for m,t in originals.items():
        ref=subprocess.check_output(['git','show',BASE+':'+str(path(m).relative_to(ROOT))],cwd=ROOT,text=True)
        if t!=ref: raise RuntimeError('Refusing to overwrite changed source: '+m)
    (OUT/'sources.json').write_text(json.dumps({m:hashlib.sha256(t.encode()).hexdigest() for m,t in originals.items()},indent=2))
    ready = False
    try:
        run('pins',['python3',str(ROOT/'scripts/verify.py')])
        run('upstream-ready',['lake','--no-build','build','Mathlib'])
        ready = True
        run('target-ready',['lake','build',S,K,C])
        # First prepare every target, then repeat target and consumer costs.
        consumer('kernel-baseline',C,KNAMES,body=(P/'CompatChecks.lean').read_text().split('\n',1)[1])
        snapshots={}
        for modern,narrow,label in [(False,False,'legacy-wide'),(False,True,'legacy-narrow'),(True,False,'module-wide'),(True,True,'module-narrow')]:
            imports=['Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Basic.Real.Basic','Mathlib.Algebra.Polynomial.Basic','Mathlib.Tactic.Ring'] if narrow else None
            path(S).write_text(variant(originals[S],modern,imports))
            run(label+'-build',['lake','build',S])
            snapshots[label]=artifact(S)
            for i in range(3):
                run(f'{label}-warm-{i}',['lake','build',S])
                run(f'{label}-elab-{i}',['lake','env','lean',str(path(S))])
                consumer(f'{label}-legacy-{i}',S,NAMES)
                if modern: consumer(f'{label}-modern-{i}',S,NAMES,True)
            if modern:consumer(label+'-all',S,NAMES,True,True)
            if not modern:
                f=OUT/(label+'-modern-rejected.lean');f.write_text('module\nimport '+S+'\n')
                run(label+'-modern-rejected',['lake','env','lean',str(f)],expect=1,error_contains='cannot import non-`module`')
        (OUT/'artifacts.json').write_text(json.dumps(snapshots,indent=2))
        # Keep the original exact rfl, .val and inverse tests; only header differs.
        compat=(P/'CompatChecks.lean').read_text().split('\n',1)[1]
        for expose,label in [(True,'kernel-exposed'),(False,'kernel-hidden')]:
            for m in [K,C]:path(m).write_text(variant(originals[m],True,expose=expose))
            run(label+'-build',['lake','build',C])
            consumer(label+'-legacy',C,KNAMES,body=compat)
            f=OUT/(label+'-modern.lean'); f.write_text('module\nimport '+C+'\n'+compat+audit(KNAMES))
            run(label+'-modern',['lake','env','lean',str(f)],expect=0 if expose else 1,error_contains=None if expose else 'definition is not exposed')
            if expose:
                consumer(label+'-all',C,KNAMES,True,True,compat)
            else:
                f=OUT/(label+'-all-wrapper.lean')
                f.write_text('module\nimport all '+C+'\n'+compat)
                run(label+'-all-wrapper',['lake','env','lean',str(f)],expect=1,error_contains='definition is not exposed')
                consumer(label+'-all-both',C,KNAMES,True,True,'import all '+K+'\n'+compat)
    finally:
        for m,t in originals.items():path(m).write_text(t)
        if ready:run('restored-targets',['lake','build',S,K,C])
if __name__=='__main__':main()
