import Lean
import Mathlib
import ForMathlib.LinearAlgebra.PairProjection

/-! Semantic home: ForMathlib.Algebra.Module.ReflectionPair.Twist. Source spans: Frobenius:28.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionPairTranslation
universe u v w z
variable {R : Type u} [CommRing R]

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Restriction of the scalar action along a ring automorphism. -/
@[ext] structure Twist (_τ : R ≃+* R) (Y : Type z) where
  val : Y
namespace Twist
variable (τ : R ≃+* R) (Y : Type z) [AddCommGroup Y] [Module R Y]
local instance _root_.OAI.KLInvariance.ReflectionPairTranslation.Twist.instRingHomInvPairToRingHomSymm : RingHomInvPair τ.symm.toRingHom τ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm τ
local instance _root_.OAI.KLInvariance.ReflectionPairTranslation.Twist.instRingHomInvPairToRingHomSymm_1 : RingHomInvPair τ.toRingHom τ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv τ
def equivVal : Twist τ Y ≃ Y where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
instance _root_.OAI.KLInvariance.ReflectionPairTranslation.Twist.instAddCommGroup : AddCommGroup (Twist τ Y) := (equivVal τ Y).addCommGroup
instance _root_.OAI.KLInvariance.ReflectionPairTranslation.Twist.instModule : Module R (Twist τ Y) := by
  letI : Module R Y := Module.compHom Y τ.toRingHom
  exact ({ equivVal τ Y with map_add' := fun _ _ => rfl } : Twist τ Y ≃+ Y).module R

def equiv : Y ≃ₛₗ[τ.symm.toRingHom] Twist τ Y where
  toFun := mk
  invFun := val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r y := by
    change mk (r • y) = mk (τ (τ.symm r) • y)
    rw [τ.apply_symm_apply]

instance _root_.OAI.KLInvariance.ReflectionPairTranslation.Twist.instFree [Module.Free R Y] : Module.Free R (Twist τ Y) :=
  Module.Free.of_equiv (equiv τ Y)
end Twist

variable {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y) (τ : R ≃+* R) (α : R)
  (hdiv : ∀ r : R, α ∣ τ r-r)
  (hinc : ∀ y : Y, ∃ n : N, f n=0 ∧ g n=α • y)

/-- The old pair relation with the scalar action on its second factor twisted.
Alpha-annihilation of the old edge is what makes this an R-submodule. -/
def lattice : Submodule R (X × Twist τ Y) where
  carrier := {p | ∃ n : N, f n=p.1 ∧ g n=p.2.val}
  zero_mem' := ⟨0,map_zero _,map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨m,hm,hm'⟩ ⟨n,hn,hn'⟩
    exact ⟨m+n,by rw [map_add,hm,hn]; rfl,by rw [map_add,hm',hn']; rfl⟩
  smul_mem' := by
    rintro r ⟨x,y⟩ ⟨n,hn,hn'⟩
    obtain ⟨c,hc⟩ := hdiv r
    obtain ⟨m,hm,hm'⟩ := hinc (c • y.val)
    have hm'' : g m=(τ r-r) • y.val := by rw [hm',hc,mul_smul]
    refine ⟨r • n+m,?_,?_⟩
    · change f (r • n+m)=r • x
      rw [map_add,map_smul,hn,hm,add_zero]
    · change g (r • n+m)=τ r • y.val
      rw [map_add,map_smul,hn',hm'',sub_smul]
      abel

/-- Saturation away from the simple wall. Regularity on the old edge module,
not an unjustified reflexivity assertion, removes a non-wall factor. -/
theorem lattice_saturated (β : R)
    (hann : ∀ e : PairProjection.Edge f g, α • e=0)
    (hreg : Function.Injective (fun e : PairProjection.Edge f g => β • e))
    (p : X × Twist τ Y) :
    β • p ∈ lattice f g τ α hdiv hinc ↔ p ∈ lattice f g τ α hdiv hinc := by
  constructor
  · rintro ⟨n,hn,hn'⟩
    apply (PairProjection.compatible_iff f g p.1 p.2.val).mp
    apply hreg
    have hn'' : g n=τ β • p.2.val := hn'
    have h := PairProjection.compatible f g n
    have hn1 : f n=β • p.1 := hn
    rw [hn1,hn'',map_smul,map_smul] at h
    obtain ⟨c,hc⟩ := hdiv β
    have he : (τ β-β) • PairProjection.upper f g p.2.val=0 := by
      rw [hc,mul_smul,smul_comm,hann,smul_zero]
    rw [sub_smul,sub_eq_zero] at he
    exact h.trans he
  · exact (lattice f g τ α hdiv hinc).smul_mem β

/-- Surjective projection to the untwisted (lower) stalk. -/
def left : lattice f g τ α hdiv hinc →ₗ[R] X :=
  (LinearMap.fst R X (Twist τ Y)).comp (lattice f g τ α hdiv hinc).subtype

 theorem left_surjective (hf : Function.Surjective f) :
    Function.Surjective (left f g τ α hdiv hinc) := by
  intro x
  obtain ⟨n,rfl⟩ := hf x
  exact ⟨⟨(f n,⟨g n⟩),n,rfl,rfl⟩,rfl⟩

/-- Its kernel is the alpha-multiple of the twisted upper stalk. -/
def kernelMap : Twist τ Y →ₗ[R] LinearMap.ker (left f g τ α hdiv hinc) where
  toFun y := ⟨⟨(0,⟨α • y.val⟩),hinc y.val⟩,rfl⟩
  map_add' y z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change (0 : X)=0+0; simp
    · change Twist.mk (α • (y.val+z.val)) = Twist.mk (α • y.val+α • z.val)
      rw [smul_add]
  map_smul' r y := by
    apply Subtype.ext
    apply Subtype.ext
    change (0,Twist.mk (α • (τ r • y.val)))=(r • (0 : X),Twist.mk (τ r • (α • y.val)))
    rw [smul_zero,smul_comm α (τ r)]

 variable (hker : ∀ y : Y, (∃ n : N, f n=0 ∧ g n=y) ↔ ∃ z : Y, y=α • z)

 include hker in
 theorem kernelMap_surjective : Function.Surjective (kernelMap f g τ α hdiv hinc) := by
  rintro ⟨⟨⟨x,y⟩,n,hn,hn'⟩,hx⟩
  change x=0 at hx
  subst x
  obtain ⟨z,hz⟩ := (hker y.val).mp ⟨n,hn,hn'⟩
  refine ⟨⟨z⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl (congrArg Twist.mk hz.symm)

 theorem kernelMap_injective (hinj : Function.Injective (fun y : Y => α • y)) :
    Function.Injective (kernelMap f g τ α hdiv hinc) := by
  intro y z h
  apply Twist.ext
  exact hinj (congrArg (fun p => p.val.val.2.val) h)

noncomputable def kernelEquiv (hinj : Function.Injective (fun y : Y => α • y)) :
    Twist τ Y ≃ₗ[R] LinearMap.ker (left f g τ α hdiv hinc) :=
  LinearEquiv.ofBijective (kernelMap f g τ α hdiv hinc)
    ⟨kernelMap_injective f g τ α hdiv hinc hinj,kernelMap_surjective f g τ α hdiv hinc hker⟩

/-- A split extension of free modules is free. This does not assert the
false statement that every submodule of a free polynomial module is free. -/
theorem free_of_surjective_of_ker_free {P : Type*} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (π : P →ₗ[R] Q) (hπ : Function.Surjective π)
    [Module.Free R Q] [Module.Free R (LinearMap.ker π)] : Module.Free R P := by
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  let e : (LinearMap.ker π × Q) →ₗ[R] P :=
    (LinearMap.ker π).subtype.coprod s
  have hps (q : Q) : π (s q)=q := DFunLike.congr_fun hs q
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨k,q⟩ ⟨k',q'⟩ h
      have hq : q=q' := by
        have hh := congrArg π h
        simpa only [e,LinearMap.coprod_apply,Submodule.subtype_apply,map_add,LinearMap.mem_ker.mp k.property,
          LinearMap.mem_ker.mp k'.property,hps,zero_add] using hh
      subst q'
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact add_right_cancel h
    · intro p
      refine ⟨(⟨p-s (π p),?_⟩,π p),?_⟩
      · change π (p-s (π p))=0
        rw [map_sub,hps,sub_self]
      · change p-s (π p)+s (π p)=p
        abel
  exact Module.Free.of_equiv (LinearEquiv.ofBijective e he)

 include hker in
 theorem lattice_free (hf : Function.Surjective f)
    (hinj : Function.Injective (fun y : Y => α • y))
    [Module.Free R X] [Module.Free R Y] :
    Module.Free R (lattice f g τ α hdiv hinc) := by
  let : Module.Free R (LinearMap.ker (left f g τ α hdiv hinc)) :=
    Module.Free.of_equiv (kernelEquiv f g τ α hdiv hinc hker hinj)
  exact free_of_surjective_of_ker_free (left f g τ α hdiv hinc)
    (left_surjective f g τ α hdiv hinc hf)

end KLInvariance.ReflectionPairTranslation
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
  let names : Array Name := #[`OAI.KLInvariance.ReflectionPairTranslation.Twist.ext.match_1]
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
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.Algebra.Module.ReflectionPair.Twist.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
