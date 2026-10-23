"""Exact three-file module overlay over the existing proof-evolution layer."""
from pathlib import Path
import hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE='3beae71a3edd8a817821d6f84eb49a9bb1a4681c'
S='ForMathlib/Algebra/BigOperators/SingleCoordinate.lean'
K='ForMathlib/LinearAlgebra/KernelTransport.lean'
C='OAI/KL/Compatibility/KernelTransport.lean'
NARROW=['Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Basic.Real.Basic',
        'Mathlib.Algebra.Polynomial.Basic','Mathlib.Tactic.Ring']
EXPOSE=['kernelSourceEquiv','kernelTargetEquiv','kernelMixedEquiv']
SPEC={S:dict(imports=NARROW,expose=[]),K:dict(imports=['Mathlib'],expose=EXPOSE),
      C:dict(imports=['ForMathlib.LinearAlgebra.KernelTransport'],expose=EXPOSE)}

def sha(data):return hashlib.sha256(data).hexdigest()
def baseline(path):
    return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def policy():
    record=json.loads((HERE/'module-integration.json').read_text())
    if record['schema']!=1 or record['base_commit']!=BASE or set(record['files'])!=set(SPEC):
        raise RuntimeError('Changed three-file module allowlist/baseline')
    for path,spec in SPEC.items():
        item=record['files'][path]
        original=baseline(path)
        if item!=dict(**spec,before_sha256=sha(original),after_sha256=sha(convert(path,original))):
            raise RuntimeError('Changed exact module transformation: '+path)
    return record

def convert(path,data):
    """Only replace the import header, insert public section, expose six named defs."""
    spec=SPEC[path]; head,body=data.decode().split('\n',1)
    expected='import '+('ForMathlib.LinearAlgebra.KernelTransport' if path==C else 'Mathlib')
    if head!=expected:raise RuntimeError('Unexpected legacy header: '+path)
    for name in spec['expose']:
        old='\ndef '+name+' '
        if body.count(old)!=1:raise RuntimeError('Missing/ambiguous expose declaration: '+name)
        body=body.replace(old,'\n@[expose] def '+name+' ',1)
    return ('module\n'+'\n'.join('public import '+n for n in spec['imports'])+
            '\n\npublic section\n'+body).encode()

def legacy_source(path,data):
    """Undo only the selected syntax for the unchanged, hash-bound proof audit.

No private-name, declaration-kind, statement, or proof normalization occurs here.
Legacy bytes remain accepted as inputs to reconstruction/adversarial tests; final
product equality separately requires the integrated form.
"""
    from attach_module import legacy_source as attach_legacy
    data=attach_legacy(path,data)
    from module_rollout import legacy_source as rollout_legacy
    data=rollout_legacy(path,data)
    if path not in SPEC or not data.startswith(b'module\n'):return data
    spec=SPEC[path]
    prefix=('module\n'+'\n'.join('public import '+n for n in spec['imports'])+'\n\npublic section\n').encode()
    if not data.startswith(prefix):raise RuntimeError('Unapproved module header: '+path)
    body=data[len(prefix):].decode()
    for name in spec['expose']:
        old='\n@[expose] def '+name+' '
        if body.count(old)!=1:raise RuntimeError('Unapproved expose boundary: '+path+' '+name)
        body=body.replace(old,'\ndef '+name+' ',1)
    head='import '+('ForMathlib.LinearAlgebra.KernelTransport' if path==C else 'Mathlib')+'\n'
    return (head+body).encode()

def overlay(files):
    policy()
    for path in SPEC:
        if files[path]!=baseline(path):raise RuntimeError('Pre-module source changed: '+path)
        files[path]=convert(path,files[path])
    return files

def imports(text):
    """Read source header edges with independent public/meta/import-all flags."""
    from source_check import uncomment
    edges=[];modern=False
    for line_no,line in enumerate(uncomment(text).splitlines(),1):
        line=line.strip()
        if not line:continue
        if line=='module':modern=True;continue
        if line=='prelude':continue
        m=re.fullmatch(r'((?:(?:public|meta)\s+)*)import\s+(all\s+)?([A-Za-z_][\w.]*)',line)
        if not m:break
        mods=m[1].split()
        if len(mods)!=len(set(mods)):raise RuntimeError('Duplicate import modifier')
        edges.append(dict(module=m[3],public='public' in mods,meta='meta' in mods,
                          all=bool(m[2]),line=line_no))
    return dict(module=modern,imports=edges)

def graph():
    paths=sorted([*(HERE/'ForMathlib').rglob('*.lean'),*(HERE/'OAI').rglob('*.lean'),HERE/'ForMathlib.lean'])
    records={str(p.relative_to(HERE))[:-5].replace('/','.'):imports(p.read_text()) for p in paths}
    from module_rollout import plan as rollout_plan, effective_imports
    rollout=rollout_plan()
    from attach_module import PATHS as attach_paths, plan as attach_plan
    attach=attach_plan()
    for name,record in records.items():
        path=name.replace('.','/')+'.lean'
        if record['module']!=(path in SPEC or path in rollout['files'] or path in attach_paths):raise RuntimeError('Unlisted module migration: '+name)
        spec=SPEC.get(path) or rollout['files'].get(path)
        if path in attach_paths:
            if any(e['all'] or e['meta'] or not e['public'] for e in record['imports']):raise RuntimeError('Changed attach-module flags')
            if (HERE/path).read_bytes()!=__import__('attach_module').convert(path,__import__('attach_module').baseline(path)):raise RuntimeError('Changed attach-module source')
            continue
        if spec is not None:
            want=[dict(module=n,public=True,meta=False,all=False) for n in effective_imports(path,spec['imports'])]
            actual=[{k:v for k,v in e.items() if k!='line'} for e in record['imports']]
            if actual!=want:raise RuntimeError('Changed selected import flags: '+name)
        elif any(e['public'] or e['meta'] or e['all'] for e in record['imports']):
            raise RuntimeError('Unlisted import modifier: '+name)
    return records

PUBLIC_THEOREMS=['OAI.KLInvariance.'+n for n in [
    'weighted_sum_exchange','weighted_sum_single','finite_character_cancellation',
    'Comparison.matrix_difference_single','Comparison.matrix_difference_le']]
PUBLIC_DEFS=['OAI.'+ns+'.'+n for ns in ['LinearEquiv','KLInvariance'] for n in EXPOSE]

def modern_exporter():
    # Reuse the immutable implementation type serializer and its adversarial guards.
    original=(HERE/'PublicTypes.lean').read_text()
    prefix=original.split('run_elab do\n  let env ← getEnv',1)[0]
    prefix=prefix.replace('import OAI.Architecture',
        'module\nimport ForMathlib.Algebra.BigOperators.SingleCoordinate\nimport OAI.KL.Compatibility.KernelTransport',1)
    names=',\n    '.join('(`'+n+', '+('true' if n in PUBLIC_THEOREMS else 'false')+')'
                         for n in PUBLIC_THEOREMS+PUBLIC_DEFS)
    return prefix+'''run_elab do
  let env ← getEnv
  let some path ← IO.getEnv "LEAN_TYPES_OUT" | throwError "Set LEAN_TYPES_OUT"
  let out ← IO.FS.Handle.mk (System.FilePath.mk path) .write
  let mut axiomClosures : Std.HashMap Name (Array Name) := {}
  for n in #[AXIOM_NAMES] do
    axiomClosures := axiomClosures.insert n (← Lean.collectAxioms n)
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\\tkl-public-types-v3"
    for (n, isThm) in #[NAMES] do
      let some ci := env.find? n | throw <| IO.userError s!"Missing public name: {n}"
      unless getOriginalConstKind? env n == some (if isThm then .thm else .defn) do
        throw <| IO.userError s!"Unexpected original kind: {n}"
      -- Only the five named module theorems may use the hidden-proof representation.
      let kind ← match ci, isThm with
        | .axiomInfo _, true => pure "theorem"
        | .defnInfo _, false => pure "def"
        | _, _ => throw <| IO.userError s!"Unexpected public representation: {n}"
      -- Producer-exported closures are collected in CoreM before serialization.
      let axs := axiomClosures[n]!
      unless axs.all (fun a => #[`propext, `Quot.sound, `Classical.choice].contains a) do
        throw <| IO.userError s!"Unapproved public axiom closure: {n}: {axs}"
      out.putStrLn s!"MODULE\\t{env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!}"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\\t{n}\\t{(toJson (reprStr ci.levelParams)).compress}\\t{id}\\t{kind}"
      IO.println s!"Public view: {n}; visible={declarationKind ci}; original={kind}; axioms={axs}"
    let st ← get
    unless st.privateOwners.isEmpty && st.proofAliases.isEmpty do
      throw <| IO.userError "Unexpected private/proof alias in selected public types"
    out.putStrLn s!"PRIVATE_SUMMARY\\t0\\t{st.unrenamed.size}\\t0\\t0"
    out.putStrLn "SUMMARY\\t11\\t0\\t0"
  discard <| action.run {}
  out.flush
'''.replace('AXIOM_NAMES',', '.join('`'+n for n in PUBLIC_THEOREMS+PUBLIC_DEFS)).replace('NAMES',names)

def generated_checks():
    compat=(HERE/'CompatChecks.lean').read_text()
    old_entries="""import OAI.LinearAlgebra.KernelTransport
import OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat

run_elab do
  let env ← Lean.getEnv
  let actual := env.header.moduleNames.filter (fun n =>
    n.toString.startsWith "OAI." || n.toString.startsWith "ForMathlib.")
  let expected := #[`ForMathlib.LinearAlgebra.KernelTransport,
    `OAI.KL.Compatibility.KernelTransport, `OAI.LinearAlgebra.KernelTransport,
    `OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat]
  unless actual.size == expected.size && actual.all (fun n => expected.contains n) do
    throwError "Unexpected legacy kernel entry closure: {actual}"

"""+compat[compat.index('section\nvariable'):]
    return {'ModernCompatChecks.lean':'module\n'+compat,
            'LegacyKernelEntryChecks.lean':old_entries,
            'ModernPublicTypes.lean':modern_exporter()}

def compare_public(path):
    from compare_types import load,load_snapshot,compare
    wanted={**load_snapshot(HERE/'reference-public-types.json'),
            **json.loads((HERE/'additional-types.json').read_text())}
    selected=PUBLIC_THEOREMS+PUBLIC_DEFS
    actual=load(path,11)
    if set(actual)!=set(selected):raise RuntimeError('Incomplete or extra modern public API')
    result=compare({n:wanted[n] for n in selected},actual)
    if not result['passed']:raise RuntimeError('Modern public type drift: '+json.dumps(result))
    return result

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--compare');mode.add_argument('--write-checks',action='store_true')
    args=parser.parse_args()
    if args.write_checks:
        for path,text in generated_checks().items():(HERE/path).write_text(text)
    else:print(json.dumps(compare_public(args.compare),indent=2))
