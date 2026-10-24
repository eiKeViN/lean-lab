import Lean
import Mathlib

/-! Semantic home: ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic. Source spans: Decomposition:9.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionFrobenius
universe uk ua uv
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]

noncomputable section

def fixed (τ : A ≃ₐ[k] A) : Subalgebra k A :=
  AlgHom.equalizer τ.toAlgHom (AlgHom.id k A)

omit [CharZero k] [IsDomain A] in
@[simp] theorem mem_fixed (τ : A ≃ₐ[k] A) (a : A) :
    a ∈ fixed τ ↔ τ a = a := Iff.rfl

omit [CharZero k] [IsDomain A] in
 theorem fixed_val (τ : A ≃ₐ[k] A) (a : fixed τ) : τ (a : A) = a := a.property

variable (τ : A ≃ₐ[k] A) (α : A)

def expand : (fixed τ × fixed τ) →ₗ[fixed τ] A where
  toFun a := (a.1 : A) + α * (a.2 : A)
  map_add' a b := by simp; ring
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Subalgebra.coe_mul, Subalgebra.smul_def, RingHom.id_apply]; ring

omit [CharZero k] [IsDomain A] in
@[simp] theorem expand_apply (a : fixed τ × fixed τ) :
    expand τ α a = (a.1 : A) + α * (a.2 : A) := rfl

variable (hinv : Function.Involutive τ) (hα : α ≠ 0) (hanti : τ α = -α)
  (hdiv : ∀ a : A, α ∣ a - τ a)

omit [CharZero k] in
include hinv hα hanti in
 theorem quotient_fixed {a d : A} (hd : a - τ a = α * d) : τ d = d := by
  have hh := congrArg τ hd
  simp only [map_sub, map_mul, hinv a, hanti] at hh
  apply mul_left_cancel₀ hα
  linear_combination hh + hd

include hα hanti in
 theorem expand_injective : Function.Injective (expand τ α) := by
  intro a b hab
  have ht := congrArg τ hab
  simp only [expand_apply, map_add, map_mul, fixed_val, hanti] at ht
  have he : (2 : A) * α * ((a.2 : A) - (b.2 : A)) = 0 := by
    simp only [expand_apply] at hab
    linear_combination hab - ht
  have htwo : (2 : A) ≠ 0 := by
    have hi : Function.Injective (algebraMap k A) := (algebraMap k A).injective
    exact fun h => two_ne_zero (hi (by simpa only [map_ofNat, map_zero] using h : algebraMap k A (2:k) = algebraMap k A 0))
  have h2 : (a.2 : A) = (b.2 : A) := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (mul_ne_zero htwo hα))
  have h1 : (a.1 : A) = (b.1 : A) := by
    simpa only [expand_apply, h2, add_left_inj] using hab
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

include hinv hα hanti hdiv in
 theorem expand_surjective : Function.Surjective (expand τ α) := by
  intro a
  obtain ⟨d, hd⟩ := hdiv a
  have hdf : τ d = d := quotient_fixed τ α hinv hα hanti hd
  let h : k := (2:k)⁻¹
  have htwo : (2:A) * algebraMap k A h = 1 := by
    rw [show (2:A) = algebraMap k A (2:k) by exact (map_ofNat (algebraMap k A) 2).symm, ← map_mul]
    simp [h]
  let c₀ : fixed τ := ⟨algebraMap k A h * (a + τ a), by
    simp only [mem_fixed, map_mul, AlgEquiv.commutes, map_add, hinv a]
    ring⟩
  let c₁ : fixed τ := ⟨algebraMap k A h * d, by
    simp only [mem_fixed, map_mul, AlgEquiv.commutes, hdf]⟩
  refine ⟨(c₀,c₁), ?_⟩
  change algebraMap k A h * (a + τ a) + α * (algebraMap k A h * d) = a
  linear_combination a * htwo - (algebraMap k A h) * hd

/-- The actual invariant-ring basis `1, α`, with no finiteness assumption. -/
def coordinates : A ≃ₗ[fixed τ] (fixed τ × fixed τ) :=
  (LinearEquiv.ofBijective (expand τ α)
    ⟨expand_injective τ α hα hanti, expand_surjective τ α hinv hα hanti hdiv⟩).symm

@[simp] theorem expand_coordinates (a : A) :
    expand τ α (coordinates τ α hinv hα hanti hdiv a) = a :=
  (coordinates τ α hinv hα hanti hdiv).symm_apply_apply a

@[simp] theorem coordinates_expand (a : fixed τ × fixed τ) :
    coordinates τ α hinv hα hanti hdiv (expand τ α a) = a :=
  (coordinates τ α hinv hα hanti hdiv).apply_symm_apply a


def trace : A →ₗ[fixed τ] fixed τ :=
  (LinearMap.snd _ _ _).comp (coordinates τ α hinv hα hanti hdiv).toLinearMap

 theorem trace_expand (a : fixed τ × fixed τ) :
    trace τ α hinv hα hanti hdiv (expand τ α a) = a.2 := by
  change (coordinates τ α hinv hα hanti hdiv (expand τ α a)).2 = a.2
  rw [coordinates_expand]

omit [CharZero k] [IsDomain A] in
include hanti in
 theorem square_fixed : α * α ∈ fixed τ := by
  simp only [mem_fixed, map_mul, hanti, neg_mul_neg]

 theorem trace_mul (a b : A) :
    trace τ α hinv hα hanti hdiv (a*b) =
      (coordinates τ α hinv hα hanti hdiv a).1 *
        (coordinates τ α hinv hα hanti hdiv b).2 +
      (coordinates τ α hinv hα hanti hdiv a).2 *
        (coordinates τ α hinv hα hanti hdiv b).1 := by
  let c := coordinates τ α hinv hα hanti hdiv a
  let d := coordinates τ α hinv hα hanti hdiv b
  let α₂ : fixed τ := ⟨α*α, square_fixed τ α hanti⟩
  have he : a*b = expand τ α
      (c.1*d.1+α₂*c.2*d.2, c.1*d.2+c.2*d.1) := by
    rw [← expand_coordinates τ α hinv hα hanti hdiv a,
      ← expand_coordinates τ α hinv hα hanti hdiv b]
    change ((c.1:A)+α*(c.2:A))*((d.1:A)+α*(d.2:A)) =
      (c.1:A)*(d.1:A)+(α*α)*(c.2:A)*(d.2:A)+
        α*((c.1:A)*(d.2:A)+(c.2:A)*(d.1:A))
    ring
  rw [he,trace_expand]

section Pair
variable (R : Type*) [CommRing R]

def crossPair : (R × R) →ₗ[R] Module.Dual R (R × R) where
  toFun a :=
    { toFun := fun b => a.1*b.2+a.2*b.1
      map_add' := by intro b c; simp; ring
      map_smul' := by intro r b; simp; ring }
  map_add' := by intro a b; apply LinearMap.ext; intro c; simp; ring
  map_smul' := by intro r a; apply LinearMap.ext; intro b; simp; ring

 theorem crossPair_bijective : Function.Bijective (crossPair R) := by
  constructor
  · intro a b hab
    have h₁ := congrArg (fun f : Module.Dual R (R×R) => f (0,1)) hab
    have h₂ := congrArg (fun f : Module.Dual R (R×R) => f (1,0)) hab
    exact Prod.ext (by simpa [crossPair] using h₁) (by simpa [crossPair] using h₂)
  · intro f
    refine ⟨(f (0,1), f (1,0)), ?_⟩
    apply LinearMap.ext
    intro a
    have ha : a = a.1 • (1,0) + a.2 • (0,1) := by simp
    change f (0,1)*a.2 + f (1,0)*a.1 = f a
    calc
      _ = a.1 * f (1,0) + a.2 * f (0,1) := by ring
      _ = f (a.1 • (1,0) + a.2 • (0,1)) := by rw [map_add,map_smul,map_smul]; rfl
      _ = f a := congrArg f ha.symm

def crossPairEquiv : (R × R) ≃ₗ[R] Module.Dual R (R × R) :=
  LinearEquiv.ofBijective (crossPair R) (crossPair_bijective R)

end Pair

/-- The Frobenius duality over the invariant ring is integral and perfect. -/
def duality : A ≃ₗ[fixed τ] Module.Dual (fixed τ) A :=
  (coordinates τ α hinv hα hanti hdiv).trans
    ((crossPairEquiv (fixed τ)).trans
      (coordinates τ α hinv hα hanti hdiv).dualMap)

 theorem duality_apply (a b : A) :
    duality τ α hinv hα hanti hdiv a b = trace τ α hinv hα hanti hdiv (a*b) := by
  rw [trace_mul]
  rfl

 theorem duality_balanced (a b c : A) :
    duality τ α hinv hα hanti hdiv (c*a) b =
      duality τ α hinv hα hanti hdiv a (c*b) := by
  rw [duality_apply,duality_apply]
  congr 1
  ring


section Symmetric
variable {V : Type uv} [AddCommGroup V] [Module k V]

def symmetricMap (e : V ≃ₗ[k] V) : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k V).comp e.toLinearMap)

omit [CharZero k] in
@[simp] theorem symmetricMap_ι (e : V ≃ₗ[k] V) (v : V) :
    symmetricMap e (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k V (e v) := by
  simp [symmetricMap]

omit [CharZero k] in
 theorem symmetricMap_comp (e d : V ≃ₗ[k] V) :
    (symmetricMap d).comp (symmetricMap e) = symmetricMap (e.trans d) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

omit [CharZero k] in
 theorem symmetricMap_refl : symmetricMap (LinearEquiv.refl k V) =
    AlgHom.id k (SymmetricAlgebra k V) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

/-- The algebra action is induced by the linear reflection, not postulated. -/
def symmetricAction (e : V ≃ₗ[k] V) : SymmetricAlgebra k V ≃ₐ[k] SymmetricAlgebra k V :=
  AlgEquiv.ofAlgHom (symmetricMap e) (symmetricMap e.symm)
    (by rw [symmetricMap_comp,LinearEquiv.symm_trans_self,symmetricMap_refl])
    (by rw [symmetricMap_comp,LinearEquiv.self_trans_symm,symmetricMap_refl])

omit [CharZero k] in
@[simp] theorem symmetricAction_ι (e : V ≃ₗ[k] V) (v : V) :
    symmetricAction e (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k V (e v) :=
  symmetricMap_ι e v

variable (root : V) (coroot : Module.Dual k V) (hroot : coroot root = 2)

abbrev reflectionAction : SymmetricAlgebra k V ≃ₐ[k] SymmetricAlgebra k V :=
  symmetricAction (Module.reflection hroot)

omit [CharZero k] in
 theorem reflectionAction_involutive : Function.Involutive (reflectionAction root coroot hroot) := by
  intro a
  have he : (reflectionAction root coroot hroot).toAlgHom.comp
      (reflectionAction root coroot hroot).toAlgHom =
        AlgHom.id k (SymmetricAlgebra k V) := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [Module.involutive_reflection hroot v]
  exact congrArg (fun f : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V => f a) he

omit [CharZero k] in
 theorem reflectionAction_anti :
    reflectionAction root coroot hroot (SymmetricAlgebra.ι k V root) =
      -SymmetricAlgebra.ι k V root := by
  simp

include hroot in
 theorem reflectionRoot_ne_zero : SymmetricAlgebra.ι k V root ≠ 0 := by
  intro he
  have hh := congrArg (SymmetricAlgebra.lift coroot) he
  rw [SymmetricAlgebra.lift_ι_apply,map_zero,hroot] at hh
  exact two_ne_zero hh

omit [CharZero k] in
 theorem reflectionAction_divisible (a : SymmetricAlgebra k V) :
    SymmetricAlgebra.ι k V root ∣ a-reflectionAction root coroot hroot a := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι v =>
    refine ⟨algebraMap k (SymmetricAlgebra k V) (coroot v), ?_⟩
    rw [reflectionAction,symmetricAction_ι,Module.reflection_apply,map_sub,map_smul]
    simp only [sub_sub_cancel,Algebra.smul_def]
    ring
  | mul a b ha hb =>
    obtain ⟨c,hc⟩ := ha
    obtain ⟨d,hd⟩ := hb
    refine ⟨c*b+(reflectionAction root coroot hroot a)*d, ?_⟩
    rw [map_mul]
    linear_combination b*hc+(reflectionAction root coroot hroot a)*hd
  | add a b ha hb =>
    simpa only [map_add, add_sub_add_comm] using dvd_add ha hb

/-- A genuine simple-reflection integral Frobenius extension in characteristic
zero, for the symmetric algebra of any representation carrying the reflection. -/
def reflectionDuality :
    SymmetricAlgebra k V ≃ₗ[fixed (reflectionAction root coroot hroot)]
      Module.Dual (fixed (reflectionAction root coroot hroot)) (SymmetricAlgebra k V) :=
  duality (reflectionAction root coroot hroot) (SymmetricAlgebra.ι k V root)
    (reflectionAction_involutive root coroot hroot) (reflectionRoot_ne_zero root coroot hroot)
    (reflectionAction_anti root coroot hroot) (reflectionAction_divisible root coroot hroot)

end Symmetric

end
end KLInvariance.ReflectionFrobenius
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
  let names : Array Name := #[`OAI.KLInvariance.ReflectionFrobenius.crossPair.eq_1]
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
    let some ci := env.checked.get.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
