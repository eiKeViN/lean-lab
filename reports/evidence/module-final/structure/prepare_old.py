from pathlib import Path
import json,sys,hashlib
root=Path.cwd();h=root/'experiments/kl-for-mathlib';r=root/'results/module-final/structure';sys.path.insert(0,str(h));from compare_types import load
paths=['ForMathlib/Algebra/Module/Cover/Local.lean','ForMathlib/Combinatorics/MomentGraph/Sheaf/Iso.lean','ForMathlib/Combinatorics/MomentGraph/Sheaf/BaseChange.lean','ForMathlib/Combinatorics/MomentGraph/Sheaf/Structure.lean'];owners=[p[:-5].replace('/','.') for p in paths];D=load(root/'results/for-mathlib/migrated-types.tsv',3947);names=sorted(n for n,d in D.items() if d['module'] in owners);names=sorted(set(names)|{'OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf.eq_1','OAI.KLInvariance.MomentGraph.Sheaf.structureBaseChangeIso.eq_1'});(r/'before-sources.json').write_text(json.dumps({p:(h/p).read_text() for p in paths},indent=2)+'\n');(r/'old-producer-records.json').write_text(json.dumps({n:d for n,d in D.items() if d['module'] in owners},indent=2)+'\n')
s=(h/'ModernFinalCompat.lean').read_text();codec=s[s.index('open Lean\n'):s.index('run_elab do')];s='import ImplementationImports\nimport Lean\n'+codec+'''run_elab do
  let users : Array Name := #[NAMES]
  let mut targets : Array (Name × Name) := #[]
  for user in users do
    let n ← realizeGlobalConstNoOverload (mkIdent user)
    targets := targets.push (user,n)
  let env := (← getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending := targets.map Prod.snd
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old declaration missing {n}"
    let (ti, ds) := (encode ci.type).run dump
    dump := ds
    if let some target := targets.find? (fun x => x.2==n) then
      records := records.push (toJson #[nameJson target.1,toJson (ci.levelParams.map nameJson),toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" ||
        (isPrivateName n && n.toString.contains ".OAI.") then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" ||
        (isPrivateName n && n.toString.contains ".OAI.") then
      let some value := ci.value? (allowOpaque := true) | throwError "no actual old value {n}"
      pending := pending ++ visit value
      let (vi, ds) := (encode value).run dump
      dump := ds
      let (kind,hints) ← match ci with
        | .thmInfo _ => pure ("theorem",Json.null)
        | .defnInfo info => do
          unless info.safety == .safe do throwError "unexpected unsafe helper {n}"
          let hints := match info.hints with
            | .opaque => toJson #[toJson "opaque"]
            | .abbrev => toJson #[toJson "abbrev"]
            | .regular n => toJson #[toJson "regular",toJson n.toNat]
          pure ("def",hints)
        | _ => throwError "unsupported actual helper kind {n}"
      aux := aux.push (toJson #[nameJson n,toJson (ci.levelParams.map nameJson),toJson ti,toJson vi,toJson kind,hints])
  IO.FS.writeFile "../../results/module-final/structure/old-expressions.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  logInfo m!"Captured {records.size} actual old public types and {aux.size} actual old helper definitions/proofs"
'''.replace('NAMES',', '.join('`'+n for n in names));(r/'CaptureOld.lean').write_text(s);print('targets',len(names))
