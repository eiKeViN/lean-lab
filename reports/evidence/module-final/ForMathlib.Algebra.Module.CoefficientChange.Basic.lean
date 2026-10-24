import Lean
import Mathlib

/-! Semantic home: ForMathlib.Algebra.Module.CoefficientChange.Basic. Source spans: BottSamelson:27.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe uk ua ub um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {B : Type ub} [CommRing B] [Algebra k B]

@[ext] structure CoefficientChange (_e : A ≃ₐ[k] B) (M : Type um) where
  val : M

namespace CoefficientChange
variable (e : A ≃ₐ[k] B) (M : Type um) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

 def equivVal : CoefficientChange e M ≃ M where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

 instance _root_.OAI.KLInvariance.CoefficientChange.instAddCommGroup : AddCommGroup (CoefficientChange e M) := (equivVal e M).addCommGroup
 instance _root_.OAI.KLInvariance.CoefficientChange.instModule : Module B (CoefficientChange e M) := by
   letI : Module B M := Module.compHom M e.symm.toRingHom
   exact ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module B
 instance _root_.OAI.KLInvariance.CoefficientChange.instModule_1 : Module k (CoefficientChange e M) :=
   ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module k
 instance _root_.OAI.KLInvariance.CoefficientChange.instIsScalarTower : IsScalarTower k B (CoefficientChange e M) where
   smul_assoc c b m := by
     apply CoefficientChange.ext
     change e.symm (c • b) • m.val=c • (e.symm b • m.val)
     rw [map_smul,smul_assoc]

 local instance _root_.OAI.KLInvariance.CoefficientChange.instRingHomInvPairToRingHomToRingEquivSymm : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e.toRingEquiv
 local instance _root_.OAI.KLInvariance.CoefficientChange.instRingHomInvPairToRingHomToRingEquivSymm_1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv

 def equiv : M ≃ₛₗ[e.toRingHom] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' a m := by
     change mk (a • m)=mk (e.symm (e a) • m)
     rw [e.symm_apply_apply]

 def kEquiv : M ≃ₗ[k] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' _ _ := rfl

 instance _root_.OAI.KLInvariance.CoefficientChange.instFree [Module.Free A M] : Module.Free B (CoefficientChange e M) :=
   Module.Free.of_equiv (equiv e M)
 instance _root_.OAI.KLInvariance.CoefficientChange.instFinite [Module.Finite A M] : Module.Finite B (CoefficientChange e M) :=
   Module.Finite.of_surjective (equiv e M).toLinearMap (equiv e M).surjective

 variable {M} {N : Type un} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
 def map (f : M →ₗ[A] N) : CoefficientChange e M →ₗ[B] CoefficientChange e N where
   toFun m := mk (f m.val)
   map_add' m n := CoefficientChange.ext (map_add f m.val n.val)
   map_smul' b m := CoefficientChange.ext (map_smul f (e.symm b) m.val)

 omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
 theorem map_injective (f : M →ₗ[A] N) (hf : Function.Injective f) :
     Function.Injective (map e f) := fun _m _n h => CoefficientChange.ext (hf (congrArg val h))
 omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
 theorem map_surjective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
     Function.Surjective (map e f) := by
   intro n
   obtain ⟨m,hm⟩ := hf n.val
   exact ⟨mk m,CoefficientChange.ext hm⟩

end CoefficientChange
end KLInvariance
end

end OAI

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
  let names : Array Name := #[`OAI.KLInvariance.CoefficientChange.ext.match_1]
  let env := (← Lean.getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending : Array Name := names
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.Algebra.Module.CoefficientChange.Basic.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
