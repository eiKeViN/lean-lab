import ImplementationImports
import Lean
open Lean
namespace BoundaryCodec
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => toJson (#[nameJson p, toJson s])
  | .num p n => toJson (#[nameJson p, toJson n, Json.null])
partial def levelJson : Level → Json
  | .zero => toJson (#[toJson "zero"])
  | .succ u => toJson (#[toJson "succ", levelJson u])
  | .max u v => toJson (#[toJson "max", levelJson u, levelJson v])
  | .imax u v => toJson (#[toJson "imax", levelJson u, levelJson v])
  | .param n => toJson (#[toJson "param", nameJson n])
  | .mvar _ => panic! "unclosed level"
structure Dump where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def encode (e : Expr) : StateM Dump Nat := do
  if let .mdata _ b := e then return ← encode b
  if let some i := (← get).ids[ExprStructEq.mk e]? then return i
  let node : Array Json ← match e with
    | .bvar n => pure #[toJson "bvar", toJson n]
    | .sort u => pure #[toJson "sort", levelJson u]
    | .const n us => pure #[toJson "const", nameJson n, toJson (us.map levelJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi | .forallE n t b bi => do
      let tag := if e.isLambda then "lam" else "forall"
      let bi := match bi with | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
      pure #[toJson tag, nameJson n, toJson (← encode t), toJson (← encode b), toJson bi]
    | .letE n t v b nondep => do pure #[toJson "let", nameJson n, toJson (← encode t), toJson (← encode v), toJson (← encode b), toJson nondep]
    | .lit (.natVal n) => pure #[toJson "nat", toJson n]
    | .lit (.strVal s) => pure #[toJson "str", toJson s]
    | .proj n i b => do pure #[toJson "proj", nameJson n, toJson i, toJson (← encode b)]
    | _ => panic! "unclosed expression"
  let s ← get
  set ({ids := s.ids.insert (ExprStructEq.mk e) s.nodes.size, nodes := s.nodes.push (toJson node)} : Dump)
  return s.nodes.size
partial def readName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size == 2 then return .str (← readName a[0]!) (← a[1]!.getStr?)
  if a.size == 3 then return .num (← readName a[0]!) (← fromJson? a[1]!)
  throw "bad name"
partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => do pure (.zero)
  | "succ" => do pure (.succ (← readLevel a[1]!))
  | "max" => do pure (.max (← readLevel a[1]!) (← readLevel a[2]!))
  | "imax" => do pure (.imax (← readLevel a[1]!) (← readLevel a[2]!))
  | "param" => do pure (.param (← readName a[1]!))
  | _ => throw "bad level"
def decode (nodes : Array Json) : Except String (Array Expr) := do
  let mut es := #[]
  for j in nodes do
    let a ← j.getArr?
    let child := fun (i : Nat) => (show Except String Expr from do
      let n : Nat ← fromJson? a[i]!
      if n < es.size then return es[n]! else throw "non-topological DAG")
    let e : Expr ← match ← a[0]!.getStr? with
      | "bvar" => do pure (.bvar (← fromJson? a[1]!))
      | "sort" => do pure (.sort (← readLevel a[1]!))
      | "const" => do pure (.const (← readName a[1]!) (← (← a[2]!.getArr?).toList.mapM readLevel))
      | "app" => do pure (.app (← child 1) (← child 2))
      | "lam" | "forall" => do
        let bi : Nat ← fromJson? a[4]!
        let bi ← match bi with | 0 => pure BinderInfo.default | 1 => pure .implicit | 2 => pure .strictImplicit | 3 => pure .instImplicit | _ => throw "bad binder"
        if (← a[0]!.getStr?) == "lam" then pure (.lam (← readName a[1]!) (← child 2) (← child 3) bi)
        else pure (.forallE (← readName a[1]!) (← child 2) (← child 3) bi)
      | "let" => do pure (.letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← fromJson? a[5]!))
      | "nat" => do pure (.lit (.natVal (← fromJson? a[1]!)))
      | "str" => do pure (.lit (.strVal (← fromJson? a[1]!)))
      | "proj" => do pure (.proj (← readName a[1]!) (← fromJson? a[2]!) (← child 3))
      | _ => throw "bad expression"
    es := es.push e
  return es
end BoundaryCodec

open Lean Meta Elab Command BoundaryCodec
run_elab do
  let users : Array Name := #[`OAI.KLInvariance.LocalCover.exists_split_minimal_cover, `OAI.KLInvariance.LocalCover.lift_surjective, `OAI.KLInvariance.LocalCover.splitEquiv, `OAI.KLInvariance.LocalCover.splitEquiv.match_3, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.boundary, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.boundaryMap, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.casesOn, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.compatible, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.ctorIdx, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.edge, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.edge.congr_simp, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.extend_stalk, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.lower, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mapAssignment, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mapAssignment.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mapAssignment_at, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.map_boundaryImage, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.map_stalk_image, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mk, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mk.inj, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mk.injEq, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mk.noConfusion, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mk.sizeOf_spec, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.noConfusion, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.noConfusionType, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.rec, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.recOn, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.symm, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.upper, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.vertex, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.vertex.congr_simp, `OAI.KLInvariance.MomentGraph.Sheaf.Iso, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.assignments, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.boundary, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.boundaryMap, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.casesOn, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.compatible_iff, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.ctorIdx, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.edge, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.flabby, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.generated, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.lower, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.map_boundaryRange, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.map_lowerImage, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.map_sections, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.map_upperImage, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.map_upwardKernel, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mk, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mk.inj, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mk.injEq, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mk.noConfusion, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mk.sizeOf_spec, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.noConfusion, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.noConfusionType, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.rec, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.recOn, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.sections, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.stalkMap, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.symm, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.upper, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.upwardKernel_iff, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.vertex, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.above, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.casesOn, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.ctorIdx, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.edge, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.edge.congr_simp, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.extend, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.lower, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.mk, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.mk.inj, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.mk.injEq, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.mk.noConfusion, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.mk.sizeOf_spec, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.noConfusion, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.noConfusionType, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.ofUniv, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.rec, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.recOn, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.upper, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.vertex, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.vertex.congr_simp, `OAI.KLInvariance.MomentGraph.Sheaf.UpperQuotient, `OAI.KLInvariance.MomentGraph.Sheaf.baseChange, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangePiQuotient, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangePiQuotient_tmul, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangePiScalar, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangePiScalar_tmul, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangePi_natural, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient_tmul, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeScalar, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeScalar_tmul, `OAI.KLInvariance.MomentGraph.Sheaf.baseChange_flabby, `OAI.KLInvariance.MomentGraph.Sheaf.baseChange_generated, `OAI.KLInvariance.MomentGraph.Sheaf.baseChange_tmul_compatible, `OAI.KLInvariance.MomentGraph.Sheaf.baseChange_upperQuotient, `OAI.KLInvariance.MomentGraph.Sheaf.baseChange_vertex_finite, `OAI.KLInvariance.MomentGraph.Sheaf.baseChange_vertex_free, `OAI.KLInvariance.MomentGraph.Sheaf.castStalkIso, `OAI.KLInvariance.MomentGraph.Sheaf.castStalkIso.congr_simp, `OAI.KLInvariance.MomentGraph.Sheaf.castStalkIso.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.constraint, `OAI.KLInvariance.MomentGraph.Sheaf.constraint_tensorAssignments, `OAI.KLInvariance.MomentGraph.Sheaf.ker_constraint, `OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback, `OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback.congr_simp, `OAI.KLInvariance.MomentGraph.Sheaf.span_map, `OAI.KLInvariance.MomentGraph.Sheaf.structureBaseChangeIso, `OAI.KLInvariance.MomentGraph.Sheaf.structureBaseChangeIso.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf_finite, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf_flat_flabby, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf_free, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf_generated, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf_minimal, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf_support, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf_upperQuotient, `OAI.KLInvariance.MomentGraph.Sheaf.structureVertexIso, `OAI.KLInvariance.MomentGraph.Sheaf.tensorAssignments, `OAI.KLInvariance.MomentGraph.Sheaf.tensorAssignments_bijective, `OAI.KLInvariance.MomentGraph.Sheaf.tensorAssignments_mem_sections_iff, `OAI.KLInvariance.MomentGraph.Sheaf.tensorAssignments_tmul, `OAI.KLInvariance.MomentGraph.Sheaf.tensorSection_extend, `OAI.KLInvariance.MomentGraph.Sheaf.tensorSections, `OAI.KLInvariance.MomentGraph.Sheaf.tensorSectionsEquiv, `OAI.KLInvariance.MomentGraph.Sheaf.tensorSections_injective, `OAI.KLInvariance.MomentGraph.Sheaf.tensorSections_surjective, `OAI.KLInvariance.MomentGraph.Sheaf.tensorSections_tmul, `OAI.KLInvariance.MomentGraph.Sheaf.upperQuotient_exact, `OAI.KLInvariance.MomentGraph.Sheaf.upwardKernel, `OAI.KLInvariance.QuotientEdge.iso.congr_simp]
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
