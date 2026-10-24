import Lean
import Mathlib

/-! Semantic home: ForMathlib.Algebra.Module.Cover.Local. Source spans: ModuleAlgebra:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.LocalCover

variable {R B P N : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

/-- A lift through a minimal free cover is automatically surjective. This
is the exact Nakayama step of plane-localized BMP decomposition. -/
theorem lift_surjective [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N) (g : B →ₗ[R] P)
    (hφ : Function.Surjective φ) (hg : π.comp g = φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    Function.Surjective g := by
  apply LinearMap.surjective_of_surjective_comp_mkQ g (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro q
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨b, hb⟩ := hφ (π p)
  refine ⟨b, ?_⟩
  change Submodule.Quotient.mk (g b) = Submodule.Quotient.mk p
  apply (Submodule.Quotient.eq _).mpr
  apply hmin
  change π (g b - p) = 0
  rw [map_sub, ← LinearMap.comp_apply, hg, hb, sub_self]

/-- An explicit linear equivalence for a split surjection, with the kernel
as the second summand. It is used below to produce the local sheaf summand. -/
noncomputable def splitEquiv (g : B →ₗ[R] P) (s : P →ₗ[R] B)
    (hs : g.comp s = LinearMap.id) : B ≃ₗ[R] P × LinearMap.ker g := by
  have hs' (p : P) : g (s p) = p := LinearMap.congr_fun hs p
  let k : B →ₗ[R] LinearMap.ker g :=
    { toFun := fun b => ⟨b - s (g b), by simp [LinearMap.mem_ker, hs']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_sub]) }
  exact
    { toFun := fun b => (g b, k b)
      invFun := fun p => s p.1 + p.2
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp
      left_inv := fun b => by simp [k]
      right_inv := fun ⟨p, b⟩ => by
        apply Prod.ext
        · simp [hs']
        · apply Subtype.ext
          simp [k, hs'] }

/-- The full minimal-cover splitting required at each descending vertex.
The new kernel is proved finite free over the local ring, not introduced
as a free summand hypothesis. -/
theorem exists_split_minimal_cover [Module.Free R B] [Module.Finite R B]
    [Module.Free R P] [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N)
    (hπ : Function.Surjective π) (hφ : Function.Surjective φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    ∃ (g : B →ₗ[R] P) (e : B ≃ₗ[R] P × LinearMap.ker g),
      Function.Surjective g ∧ π.comp g = φ ∧
      Module.Free R (LinearMap.ker g) ∧ Module.Finite R (LinearMap.ker g) ∧
      ∀ b, (e b).1 = g b ∧ π (e b).1 = φ b := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property π φ hπ
  have hsurj := lift_surjective π φ g hφ hg hmin
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let e := splitEquiv g s hs
  let k : B →ₗ[R] LinearMap.ker g := (LinearMap.snd R P (LinearMap.ker g)).comp e.toLinearMap
  have hk : Function.Surjective k := by
    intro b
    exact ⟨e.symm (0, b), by simp [k]⟩
  have hki : k.comp (LinearMap.ker g).subtype = LinearMap.id := by
    ext b
    change ((b : B) - s (g b)) = b
    simp []
  let : Module.Finite R (LinearMap.ker g) := Module.Finite.of_surjective k hk
  let : Module.Projective R (LinearMap.ker g) :=
    Module.Projective.of_split (LinearMap.ker g).subtype k hki
  let : Module.Free R (LinearMap.ker g) := Module.free_of_flat_of_isLocalRing
  refine ⟨g, e, hsurj, hg, inferInstance, inferInstance, ?_⟩
  intro b
  exact ⟨rfl, LinearMap.congr_fun hg b⟩

end KLInvariance.LocalCover
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
  let names : Array Name := #[`OAI.KLInvariance.LocalCover.splitEquiv.match_3]
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
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.Algebra.Module.Cover.Local.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
