"""Hash-bound 181-node dependency-closed compatibility rollout (178 new modules)."""
from pathlib import Path
from functools import lru_cache
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='45cc0cfcf699b7acd17a48d867c5f28bdb30bc5d'
PLAN_SHA='4fd3444602225d27c48ddd186e5c02cd17849e1dcb2d926d39e7a10fd453674c'
TYPES_SHA='03a814dc84adb45bea3b396dd0092d3c2b39760d6b1af6988b7da21f0f42f4b8'
def sha(b):return hashlib.sha256(b).hexdigest()
def plan():
    data=(HERE/'module-rollout.json').read_bytes()
    if sha(data)!=PLAN_SHA:raise RuntimeError('Changed rollout allowlist')
    d=json.loads(data)
    if d['base_commit']!=BASE or len(d['files'])!=178 or len(d['selected'])!=181:
        raise RuntimeError('Changed rollout scope')
    return d
@lru_cache(None)
def baseline(path):
    return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def convert(path,data):
    item=plan()['files'][path]
    if sha(data)!=item['before_sha256']:raise RuntimeError('Changed rollout input: '+path)
    text=data.decode()
    for e in sorted(item['edits'],key=lambda e:e['start'],reverse=True):
        if text[e['start']:e['start']+len(e['old'])]!=e['old']:raise RuntimeError('Rollout edit mismatch')
        text=text[:e['start']]+e['new']+text[e['start']+len(e['old']):]
    if sha(text.encode())!=item['after_sha256']:raise RuntimeError('Changed rollout output')
    return narrow_apply(path,text.encode())
def legacy_source(path,data):
    data=narrow_legacy(path,data)
    items=plan()['files']
    if path not in items or not data.startswith(b'module\n'):return data
    delta=0;undo=[]
    for e in sorted(items[path]['edits'],key=lambda e:e['start']):
        undo.append((e['start']+delta,e['new'],e['old']))
        delta+=len(e['new'])-len(e['old'])
    text=data.decode()
    for start,new,old in reversed(undo):
        if text[start:start+len(new)]!=new:raise RuntimeError('Unapproved rollout syntax: '+path)
        text=text[:start]+old+text[start+len(new):]
    return text.encode()
def overlay(files):
    for path,item in plan()['files'].items():
        if files[path]!=baseline(path):raise RuntimeError('Pre-rollout source differs: '+path)
        files[path]=convert(path,files[path])
    return files

def policy():
    d=plan();selected=set(d['selected'])
    for path,item in d['files'].items():
        if sha(baseline(path))!=item['before_sha256']:raise RuntimeError('Changed baseline binding')
        convert(path,baseline(path))
        if any(n.startswith(('OAI.','ForMathlib.')) and n not in selected for n in item['imports']):
            raise RuntimeError('Not a dependency-closed module region: '+path)
    raw=(HERE/'module-rollout-types.json').read_bytes()
    if sha(raw)!=TYPES_SHA:raise RuntimeError('Changed rollout type/name allowlist')
    return d

def expected_types():
    policy();return json.loads((HERE/'module-rollout-types.json').read_text())

def generated_checks():
    from module_integration import PUBLIC_THEOREMS
    selected=plan()['selected']
    imports=''.join('import '+n+'\n' for n in selected)
    # Explicit implementation access is confined to this independent audit root.
    full='import OAI.Architecture\n'+imports
    exporter=(HERE/'PublicTypes.lean').read_text().replace('import OAI.Architecture','import ImplementationImports',1)
    corpus=(HERE/'SemanticCorpus.lean').read_text().replace('import OAI.Architecture','import ImplementationImports',1)
    return {'ImplementationImports.lean':full,'ImplementationPublicTypes.lean':exporter,
            'ImplementationSemanticCorpus.lean':corpus,'ModernRolloutTypes.lean':modern_exporter(), 'ImplementationMatcherChecks.lean':matcher_checks()}

ALIASES_SHA='2bb66d2e7594feea4c0eaec7f6cf0f9de28e39b96675054943c8dfe46af24d51'
HIDDEN_SHA='9bc339b0f6a4af4be5d8dc406ca0f15973c4a7d3fcfd691bf4ac272109c0a05d'
@lru_cache(None)
def hidden_matchers():
    raw=(HERE/'module-rollout-hidden-matchers.json').read_bytes()
    if sha(raw)!=HIDDEN_SHA:raise RuntimeError('Changed exact hidden matcher policy')
    names=json.loads(raw)['names']
    if len(names)!=6 or len(set(names))!=6 or not all('.match_' in n and n in json.loads((HERE/'module-rollout-types.json').read_text()) for n in names):raise RuntimeError('Invalid hidden matcher policy')
    return names

def modern_exporter():
    aliases_raw=(HERE/'module-rollout-aliases.json').read_bytes()
    if sha(aliases_raw)!=ALIASES_SHA:raise RuntimeError('Unbound compiler-proof alias list')
    aliases=json.loads(aliases_raw)['names']
    if len(aliases)!=len(set(aliases)) or any(not __import__('re').fullmatch(r'OAI\..+\._proof_\d+',n) for n in aliases):
        raise RuntimeError('Unexpected compiler-proof alias')
    prefix=(HERE/'PublicTypes.lean').read_text().split('run_elab do\n  let env ← getEnv',1)[0]
    prefix=prefix.replace('import OAI.Architecture','module\n'+''.join('import '+n+'\n' for n in plan()['selected']).rstrip(),1)
    support='''
private def rolloutProofAliases : Array Name := #[ALIASES]
private def rolloutOwners : Array Name := #[OWNERS]
private def rolloutHiddenMatchers : Array Name := #[HIDDEN]
private def rolloutOriginalKind : ConstantKind → String
  | .defn => "def" | .thm => "theorem" | .«axiom» => "axiom"
  | .«opaque» => "opaque" | .quot => "quotient" | .induct => "inductive"
  | .ctor => "constructor" | .recursor => "recursor"
'''.replace('ALIASES',', '.join('`'+n for n in aliases)).replace('HIDDEN',', '.join('`'+n for n in hidden_matchers())).replace('OWNERS',', '.join('`'+n for n in plan()['selected']))
    prefix=prefix.replace('open Lean\n','open Lean\n'+support,1)
    old='''        else pure ["const", reprStr n, reprStr us]
      else'''
    new='''        else if let some (.axiomInfo info) := env.find? n then
          let owned := (env.getModuleIdxFor? n).any fun i => rolloutOwners.contains env.header.moduleNames[i.toNat]!
          if owned && rolloutProofAliases.contains n && getOriginalConstKind? env n == some .thm then
            let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
            modify fun st => { st with proofAliases := st.proofAliases.insert n }
            pure ["proof", toString proposition]
          else pure ["const", reprStr n, reprStr us]
        else pure ["const", reprStr n, reprStr us]
      else'''
    if prefix.count(old)!=1:raise RuntimeError('Unexpected inherited serializer branch')
    prefix=prefix.replace(old,new,1)
    return prefix+'''run_elab do
  let env ← getEnv
  let policy ← IO.ofExcept <| Json.parse (← IO.FS.readFile "module-rollout-types.json")
  let allEntries := (← IO.ofExcept policy.getObj?).toList
  unless allEntries.length == 2609 do throwError "Unexpected rollout coverage"
  for n in rolloutHiddenMatchers do
    if env.contains n then throwError "Unexpectedly public compiler matcher: {n}"
    IO.println s!"EXPECTED_HIDDEN_MATCHER {n}"
  let entries := allEntries.filter fun (s, _) => !rolloutHiddenMatchers.contains s.toName
  unless entries.length == 2603 do throwError "Unexpected positive coverage"
  let some path ← IO.getEnv "LEAN_TYPES_OUT" | throwError "Set LEAN_TYPES_OUT"
  let out ← IO.FS.Handle.mk (System.FilePath.mk path) .write
  let mut closures : Std.HashMap Name (Array Name) := {}
  for (str, _) in entries do
    let n := str.toName
    let axioms ← Lean.collectAxioms n
    unless axioms.all (fun a => #[`propext, `Quot.sound, `Classical.choice].contains a) do
      throwError "Unexpected axiom closure: {n}: {axioms}"
    closures := closures.insert n axioms
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\\tkl-public-types-v3"
    for (str, record) in entries do
      let n := str.toName
      let want ← IO.ofExcept <| record.getObjValAs? String "kind"
      let some ci := env.find? n | throw <| IO.userError s!"Missing rollout public name: {n}"
      unless (getOriginalConstKind? env n).map rolloutOriginalKind == some want do
        throw <| IO.userError s!"Wrong original kind: {n}"
      let visible := declarationKind ci
      unless visible == want || (want == "theorem" && visible == "axiom") do
        throw <| IO.userError s!"Unexpected public representation: {n}: {visible}, wanted {want}"
      let some owner := env.getModuleIdxFor? n | throw <| IO.userError "Missing owner"
      unless rolloutOwners.contains env.header.moduleNames[owner.toNat]! do
        throw <| IO.userError s!"Wrong rollout owner: {n}"
      out.putStrLn s!"MODULE\\t{env.header.moduleNames[owner.toNat]!}"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\\t{n}\\t{(toJson (reprStr ci.levelParams)).compress}\\t{id}\\t{want}"
      IO.println s!"PUBLIC {n}: visible={visible}; original={want}; axioms={closures[n]!}"
    let st ← get
    unless st.privateOwners.isEmpty do throw <| IO.userError "Private rewriting is not allowed"
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\\t0\\t{st.unrenamed.size}\\t0\\t0"
    out.putStrLn s!"SUMMARY\\t2603\\t0\\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
'''

def compare_public(path):
    from compare_types import load,compare
    wanted={n:t for n,t in expected_types().items() if n not in hidden_matchers()};actual=load(path,2603)
    if set(actual)!=set(wanted):raise RuntimeError('Incomplete rollout public API')
    result=compare(wanted,actual)
    if not result['passed']:raise RuntimeError('Rollout public types changed: '+json.dumps(result))
    return result

NARROW_SHA='91f6692d08efe3998f044734caf56de9d581cb2b17060e89837b8443e001772f'
def narrow_plan():
    raw=(HERE/'module-rollout-imports.json').read_bytes()
    if sha(raw)!=NARROW_SHA:raise RuntimeError('Unrecorded import narrowing')
    d=json.loads(raw)
    if len(d['files'])!=14 or not set(d['files'])<=set(plan()['files']):raise RuntimeError('Invalid narrowing scope')
    return d

def effective_imports(path,original):return narrow_plan()['files'].get(path,{}).get('imports',original)
def narrow_apply(path,data):
    item=narrow_plan()['files'].get(path)
    if item is None:return data
    if sha(data)!=item['before_sha256'] or not data.startswith(item['old_header'].encode()):raise RuntimeError('Changed narrowing baseline: '+path)
    result=item['new_header'].encode()+data[len(item['old_header'].encode()):]
    if sha(result)!=item['after_sha256']:raise RuntimeError('Changed narrowed source: '+path)
    return result

def narrow_legacy(path,data):
    item=narrow_plan()['files'].get(path)
    if item is None or not data.startswith(b'module\n'):return data
    if not data.startswith(item['new_header'].encode()):raise RuntimeError('Unapproved narrowed header: '+path)
    return item['old_header'].encode()+data[len(item['new_header'].encode()):]

def matcher_checks():
    names=', '.join('`'+n for n in hidden_matchers())
    return "import ImplementationImports\nimport Lean\nopen Lean\nrun_elab do\n  let env ← getEnv\n  for n in #["+names+"] do\n    unless env.contains n && Lean.isMatcherCore env n do throwError \"Missing compiler matcher implementation: {n}\"\n    unless Lean.getOriginalConstKind? env n == some .defn do throwError \"Wrong compiler matcher kind: {n}\"\n    IO.println s!\"IMPLEMENTATION_MATCHER {n}\"\n"

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--apply',action='store_true');p.add_argument('--write-checks',action='store_true');p.add_argument('--compare');a=p.parse_args()
    policy()
    if a.apply:
        for path in plan()['files']:(HERE/path).write_bytes(convert(path,baseline(path)))
    if a.write_checks:
        for path,text in generated_checks().items():(HERE/path).write_text(text)

    if a.compare:print(json.dumps(compare_public(a.compare),indent=2))

