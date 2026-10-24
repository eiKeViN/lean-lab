import Lean
import Mathlib
import ForMathlib.GroupTheory.Coxeter.Roots.Basic
import ForMathlib.GroupTheory.Coxeter.Roots.Order
import ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis
import ForMathlib.LinearAlgebra.Avoidance

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder. Source spans: ReflectionOrders:2, ReflectionOrders:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_9 (p : Prop) : Decidable p := Classical.propDecidable p

@[simp] theorem normalizedRoot_height (a : PositiveRoot M cs) :
    height (normalizedRoot a) = 1 := by
  simp [normalizedRoot,a.height_pos.ne']

@[simp] theorem dual_normalizedRoot (f : Module.Dual ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    f (normalizedRoot a) = f a.val / height a.val := by
  simp [normalizedRoot,div_eq_mul_inv,mul_comm]

@[simp] theorem geometricFunctional_normalizedRoot (a : PositiveRoot M cs) :
    geometricFunctional (M := M) (cs := cs) (normalizedRoot a) = geometricSlope a :=
  dual_normalizedRoot _ a

theorem normalizedRoot_mem_iff (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    normalizedRoot a ∈ P ↔ a.val ∈ P := by
  constructor
  · intro h
    have hh := P.smul_mem (height a.val) h
    simpa [normalizedRoot,smul_smul,a.height_pos.ne'] using hh
  · exact fun h => P.smul_mem _ h

theorem rootPlane_eq_normalized_span (a b : PositiveRoot M cs) :
    rootPlane a b = Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mp (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mp (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mpr (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mpr (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The intersection of a root-plane with the height-one hyperplane is the
actual affine line through the two normalized roots. -/
theorem normalizedRoot_affine {a b c : PositiveRoot M cs}
    (hc : c.val ∈ rootPlane a b) :
    ∃ t : ℝ, normalizedRoot c = t • normalizedRoot a + (1-t) • normalizedRoot b := by
  have hcn : normalizedRoot c ∈ Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
    rw [← rootPlane_eq_normalized_span]
    exact (normalizedRoot_mem_iff _ _).mpr hc
  obtain ⟨t,s,he⟩ := Submodule.mem_span_pair.mp hcn
  have hh := congrArg (height (I := I)) he
  simp only [map_add,map_smul,normalizedRoot_height,smul_eq_mul,mul_one] at hh
  refine ⟨t,?_⟩
  have hs : s=1-t := by linarith
  exact hs ▸ he.symm

/-- On each genuine root plane, every height-normalized linear functional
is an affine function of the fixed angular slope. -/
theorem exists_affine_rootPlane (f : Module.Dual ℝ (I → ℝ))
    (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  let A := geometricSlope a
  let B := geometricSlope b
  let fa := f (normalizedRoot a)
  let fb := f (normalizedRoot b)
  have hAB : A-B ≠ 0 := sub_ne_zero.mpr (fun h => hab (geometricSlope_injective h))
  let c := (fa-fb)/(A-B)
  let d := fb-c*B
  have ha : fa=c*A+d := by
    dsimp [d,c]
    field_simp
    ring
  have hb : fb=c*B+d := by dsimp [d]; ring
  refine ⟨c,d,fun r hr => ?_⟩
  obtain ⟨t,ht⟩ := normalizedRoot_affine hr
  have hf : f (normalizedRoot r) = t*fa+(1-t)*fb := by
    rw [ht]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hg : geometricSlope r = t*A+(1-t)*B := by
    rw [← geometricFunctional_normalizedRoot,ht]
    simp only [map_add,map_smul,geometricFunctional_normalizedRoot,smul_eq_mul]
    rfl
  rw [hf,hg,ha,hb]
  ring

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
theorem exists_affine (f : Module.Dual ℝ (I → ℝ)) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ P →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  simpa only [B.plane_eq] using exists_affine_rootPlane f B.left B.right B.distinct

end PlaneBasis
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_11 (p : Prop) : Decidable p := Classical.propDecidable p

def pencil (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) : Module.Dual ℝ (I → ℝ) :=
  (1-t) • f + t • g

omit [Fintype I] in
@[simp] theorem pencil_zero (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 0=f := by
  simp [pencil]
omit [Fintype I] in
@[simp] theorem pencil_one (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 1=g := by
  simp [pencil]

omit [Fintype I] in
theorem pencil_apply (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) (v : I → ℝ) :
    pencil f g t v=(1-t)*f v+t*g v := rfl

def rootDifference (a b : PositiveRoot M cs) : I → ℝ := normalizedRoot b-normalizedRoot a

def wallVector (f : Module.Dual ℝ (I → ℝ)) (a b c : PositiveRoot M cs) : I → ℝ :=
  f (rootDifference a b) • rootDifference a c -
    f (rootDifference a c) • rootDifference a b

/-- This is an actual genericity condition on linear functionals, not
an assumed path or Hecke identity. -/
def Transverse (f g : Module.Dual ℝ (I → ℝ)) : Prop :=
  ∀ a b c : PositiveRoot M cs, g (wallVector f a b c)=0 → wallVector f a b c=0

theorem pencil_tie_plane (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (t : ℝ)
    (a b : PositiveRoot M cs) (hab : a ≠ b)
    (he : pencil f g t (normalizedRoot a)=pencil f g t (normalizedRoot b)) :
    ∀ c : PositiveRoot M cs,
      pencil f g t (normalizedRoot c)=pencil f g t (normalizedRoot a) ↔
        c.val ∈ rootPlane a b := by
  let v := rootDifference a b
  have hv : f v ≠ 0 := by
    change f (normalizedRoot b-normalizedRoot a) ≠ 0
    rw [map_sub,sub_ne_zero]
    exact fun h => hab (hf h).symm
  have hvt : (1-t)*f v+t*g v=0 := by
    rw [← pencil_apply]
    change pencil f g t (normalizedRoot b-normalizedRoot a)=0
    rw [map_sub,he,sub_self]
  have ht : t ≠ 0 := by
    intro h
    subst t
    simp only [sub_zero,one_mul,zero_mul,add_zero] at hvt
    exact hv hvt
  intro c
  constructor
  · intro hc
    let w := rootDifference a c
    have hwt : (1-t)*f w+t*g w=0 := by
      rw [← pencil_apply]
      change pencil f g t (normalizedRoot c-normalizedRoot a)=0
      rw [map_sub,hc,sub_self]
    have hz : g (wallVector f a b c)=0 := by
      change g (f v • w-f w • v)=0
      rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      apply (mul_eq_zero.mp (show t * (f v*g w-f w*g v)=0 by
        calc
          _ = f v*((1-t)*f w+t*g w)-f w*((1-t)*f v+t*g v) := by ring
          _ = 0 := by rw [hwt,hvt]; ring)).resolve_left ht
    have heq : f v • w=f w • v := sub_eq_zero.mp (hg a b c hz)
    let P := rootPlane a b
    have haP : normalizedRoot a ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert _ _))
    have hbP : normalizedRoot b ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hvP : v ∈ P := P.sub_mem hbP haP
    have hwP : w ∈ P := by
      have hh := P.smul_mem (f v)⁻¹ (heq ▸ P.smul_mem (f w) hvP)
      simpa only [smul_smul,inv_mul_cancel₀ hv,one_smul] using hh
    apply (normalizedRoot_mem_iff P c).mp
    have hh := P.add_mem hwP haP
    simpa only [w,rootDifference,sub_add_cancel] using hh
  · intro hc
    obtain ⟨s,hs⟩ := normalizedRoot_affine hc
    rw [hs,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,← he]
    ring

/-- One intermediate functional is simultaneously transverse to any two
specified generic endpoints, even with infinitely many positive roots. -/
theorem exists_common_transverse (f h : Module.Dual ℝ (I → ℝ)) :
    ∃ g : Module.Dual ℝ (I → ℝ),
      Function.Injective (fun a : PositiveRoot M cs => g (normalizedRoot a)) ∧
      Transverse (M := M) (cs := cs) f g ∧ Transverse (M := M) (cs := cs) h g := by
  let := countable_Positiveroot M cs
  let E := PositiveRoot M cs
  let A := (E × E) ⊕ (Bool × E × E × E)
  let v : A → (I → ℝ) := fun x => match x with
    | .inl (a,b) => rootDifference a b
    | .inr (i,a,b,c) => wallVector (if i then f else h) a b c
  obtain ⟨g,hg⟩ := ReflectionSchedules.exists_avoiding_functional v
  refine ⟨g,?_,?_,?_⟩
  · intro a b he
    by_contra hab
    have hn : rootDifference a b ≠ 0 := by
      exact fun hz => hab (normalizedRoot_injective (sub_eq_zero.mp hz)).symm
    apply hg (.inl (a,b)) hn
    simp only [v,rootDifference,map_sub,he,sub_self]
  · intro a b c he
    by_contra hz
    exact hg (.inr (true,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)
  · intro a b c he
    by_contra hz
    exact hg (.inr (false,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)

end
end KLInvariance.TitsSpace
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
  let names : Array Name := #[`OAI.KLInvariance.TitsSpace.exists_common_transverse.match_1_1]
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
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
