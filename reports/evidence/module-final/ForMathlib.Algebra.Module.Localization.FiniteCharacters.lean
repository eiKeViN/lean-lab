import Lean
import Mathlib

/-! Semantic home: ForMathlib.Algebra.Module.Localization.FiniteCharacters. Source spans: IntegralPairings:25.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.FiniteCharacterLocalization
universe u v w
variable {R : Type u} [CommRing R] {X : Type v}
  {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
noncomputable section

 def diagonal (f : X → R) : (∀ x, E x) →ₗ[R] (∀ x, E x) where
  toFun m x := f x • m x
  map_add' := by intro m n; funext x; exact smul_add _ _ _
  map_smul' := by intro r m; funext x; exact smul_comm _ _ _

 def stabilizer (L : Submodule R (∀ x, E x)) : Subalgebra R (X → R) where
  carrier := {f | ∀ m ∈ L, diagonal f m ∈ L}
  mul_mem' := by
    intro f g hf hg m hm
    have h := hf _ (hg m hm)
    simpa only [diagonal,LinearMap.coe_mk,AddHom.coe_mk,Pi.mul_apply,mul_smul] using h
  one_mem' := by intro m hm; simpa [diagonal] using hm
  add_mem' := by
    intro f g hf hg m hm
    have he : diagonal (f+g) m = diagonal f m+diagonal g m := by
      funext x
      exact add_smul _ _ _
    rw [he]
    exact L.add_mem (hf m hm) (hg m hm)
  zero_mem' := by
    intro m _
    have he : diagonal (0 : X → R) m=0 := by
      funext x
      exact zero_smul _ _
    rw [he]
    exact L.zero_mem
  algebraMap_mem' := by
    intro r m hm
    exact L.smul_mem r hm

 theorem diagonal_mem {L : Submodule R (∀ x, E x)} {f : X → R}
    (hf : f ∈ stabilizer L) {m : ∀ x, E x} (hm : m ∈ L) :
    diagonal f m ∈ L := hf m hm

/-- The vanishing polynomial of the finite weights is zero on the chosen
block and equals their product off that block when the weight vanishes there.
This pointwise calculation is independent of any stable lattice. -/
theorem projector_product_values (C : Finset X) (f : X → R)
    (hz : ∀ x ∉ C, f x = 0) :
    (∀ x ∈ C, (∏ y ∈ C, (algebraMap R (X → R) (f y)-f)) x = 0) ∧
    (∀ x ∉ C, (∏ y ∈ C, (algebraMap R (X → R) (f y)-f)) x = ∏ y ∈ C, f y) := by
  classical
  constructor
  · intro x hx
    rw [Finset.prod_apply]
    apply Finset.prod_eq_zero hx
    simp
  · intro x hx
    rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro y _
    simp [hz x hx]

/-- A polynomial in stable diagonal weights which kills the complement of
`C` and is a common scalar on `C`. Its scalar is a product, not a quotient. -/
 theorem uniform_projector (L : Submodule R (∀ x, E x)) (C : Finset X)
    (f : X → R) (hf : f ∈ stabilizer L) (hz : ∀ x ∉ C, f x=0) :
    ∃ g ∈ stabilizer L,
      (∀ x ∈ C, g x=∏ y ∈ C, f y) ∧ (∀ x ∉ C, g x=0) := by
  classical
  let d : R := ∏ y ∈ C, f y
  let h : X → R := ∏ y ∈ C, (algebraMap R (X → R) (f y)-f)
  have hh : h ∈ stabilizer L := by
    exact (stabilizer L).prod_mem fun y _ =>
      (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem (f y)) hf
  refine ⟨algebraMap R (X → R) d-h,
    (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem d) hh,?_,?_⟩
  · intro x hx
    change d-h x=d
    suffices h x=0 by rw [this,sub_zero]
    exact (projector_product_values C f hz).1 x hx
  · intro x hx
    change d-h x=0
    suffices h x=d by rw [this,sub_self]
    exact (projector_product_values C f hz).2 x hx

/-- The product of separating test values on a residue block is not divisible
by the prime when each test is nondivisible at the reference point and congruent
throughout the block. Only coordinate congruences enter this product argument. -/
theorem class_product_not_dvd [Fintype X] [DecidableEq X] (p : R) (hp : Prime p)
    (C : Finset X) (x : X) (test : X → X → R)
    (hunit : ∀ y ∉ C, ¬ p ∣ test y x)
    (hcongr : ∀ z ∈ C, ∀ y, p ∣ test y z-test y x)
    (z : X) (hz : z ∈ C) : ¬ p ∣ (∏ y ∈ Finset.univ \ C, test y) z := by
  classical
  rw [Finset.prod_apply]
  apply hp.not_dvd_finsetProd
  intro y hy
  have hyC := (Finset.mem_sdiff.mp hy).2
  intro h
  apply hunit y hyC
  simpa only [sub_sub_cancel] using dvd_sub h (hcongr z hz y)

/-- Separate one residue-character class from its complement without
inverting any element of the coefficient domain. -/
 theorem class_projector [Fintype X] (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (C : Finset X) (x : X)
    (test : X → X → R) (htest : ∀ y, test y ∈ stabilizer L)
    (hzero : ∀ y ∉ C, test y y=0)
    (hunit : ∀ y ∉ C, ¬ p ∣ test y x)
    (hcongr : ∀ z ∈ C, ∀ y, p ∣ test y z-test y x) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z ∈ C, g z=d) ∧ (∀ z ∉ C, g z=0) := by
  classical
  let f : X → R := ∏ y ∈ Finset.univ \ C, test y
  have hf : f ∈ stabilizer L :=
    (stabilizer L).prod_mem fun y _ => htest y
  have hfu (z : X) (hz : z ∈ C) : ¬ p ∣ f z :=
    class_product_not_dvd p hp C x test hunit hcongr z hz
  have hfz (z : X) (hz : z ∉ C) : f z=0 := by
    dsimp [f]
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩) (hzero z hz)
  obtain ⟨g,hg,hgc,hgz⟩ := uniform_projector L C f hf hfz
  refine ⟨∏ z ∈ C, f z,?_,g,hg,hgc,hgz⟩
  exact hp.not_dvd_finsetProd (fun z hz => hfu z hz)

/-- The complementary denominator products assemble disjoint character-block
lifts into one scalar multiple of the target. Primality and stable lattice
membership are deliberately absent from this pointwise partition identity. -/
theorem partition_diagonal_sum {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : X → Q) (z : ∀ x, E x) (d : Q → R) (g : Q → X → R)
    (hgin : ∀ j x, q x=j → g j x=d j)
    (hgout : ∀ j x, q x≠j → g j x=0)
    (m : Q → ∀ x, E x) (hmatch : ∀ j x, q x=j → m j x=z x) :
    (∏ j, d j) • z = ∑ j : Q, (∏ k ∈ Finset.univ.erase j, d k) • diagonal (g j) (m j) := by
  classical
  funext x
  simp only [Pi.smul_apply,Finset.sum_apply]
  rw [Finset.sum_eq_single (q x)]
  · change (∏ j, d j) • z x = (∏ k ∈ Finset.univ.erase (q x),d k) •
      (g (q x) x • m (q x) x)
    rw [hgin _ _ rfl,hmatch _ _ rfl,← mul_smul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  · intro j _ hj
    change (∏ k ∈ Finset.univ.erase j,d k) • (g j x • m j x)=0
    rw [hgout j x (Ne.symm hj),zero_smul,smul_zero]
  · simp

/-- Local lifts on each finite character block assemble after a single
scalar denominator away from the prime. -/
 theorem partition_local_denominator {Q : Type*} [Fintype Q]
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p) (q : X → Q)
    (z : ∀ x, E x) (d : Q → R) (hd : ∀ j, ¬ p ∣ d j)
    (g : Q → X → R) (hg : ∀ j, g j ∈ stabilizer L)
    (hgin : ∀ j x, q x=j → g j x=d j)
    (hgout : ∀ j x, q x≠j → g j x=0)
    (m : Q → ∀ x, E x) (hm : ∀ j, m j ∈ L)
    (hmatch : ∀ j x, q x=j → m j x=z x) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  refine ⟨∏ j, d j,hp.not_dvd_finsetProd (fun j _ => hd j),?_⟩
  rw [partition_diagonal_sum q z d g hgin hgout m hmatch]
  exact L.sum_mem fun j _ => L.smul_mem _ (hg j _ (hm j))

 def residueSetoid {A : Type*} (p : R) (χ : A → X → R) : Setoid X where
  r x y := ∀ a, p ∣ χ a x-χ a y
  iseqv := ⟨fun x a => by rw [sub_self]; exact dvd_zero _,
    fun h a => by simpa only [neg_sub] using dvd_neg.mpr (h a),
    fun h h' a => by simpa only [sub_add_sub_cancel] using dvd_add (h a) (h' a)⟩

/-- A point outside a residue-character class admits a stable test that
vanishes there and is prime-nondivisible at the reference point. The chosen tests
remain congruent across the class; finiteness and primeness are not needed here. -/
theorem exists_character_separators {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (χ : A → X → R)
    (hχ : ∀ a, χ a ∈ stabilizer L) (x : X) :
    ∃ test : X → X → R,
      (∀ y, test y ∈ stabilizer L) ∧
      (∀ y, ¬ (residueSetoid p χ).r x y → test y y=0) ∧
      (∀ y, ¬ (residueSetoid p χ).r x y → ¬ p ∣ test y x) ∧
      (∀ z, (residueSetoid p χ).r x z → ∀ y, p ∣ test y z-test y x) := by
  classical
  have ha : ∀ y : {y : X // ¬ (residueSetoid p χ).r x y}, ∃ a, ¬ p ∣ χ a x-χ a y.val := by
    intro y
    exact not_forall.mp y.property
  choose a ha using ha
  let test (y : X) : X → R := if hy : ¬ (residueSetoid p χ).r x y then
    χ (a ⟨y,hy⟩)-algebraMap R (X → R) (χ (a ⟨y,hy⟩) y) else 0
  refine ⟨test,?_,?_,?_,?_⟩
  · intro y
    by_cases hy : ¬ (residueSetoid p χ).r x y
    · simp only [test,dite_eq_left hy]
      exact (stabilizer L).sub_mem (hχ _) ((stabilizer L).algebraMap_mem _)
    · simp only [test,dite_eq_right hy]
      exact (stabilizer L).zero_mem
  · intro y hy
    simp [test,hy]
  · intro y hy
    simpa [test,hy] using ha ⟨y,hy⟩
  · intro z hz y
    by_cases hy : ¬ (residueSetoid p χ).r x y
    · simp only [test,dite_eq_left hy]
      change p ∣ (χ (a ⟨y,hy⟩) z-χ (a ⟨y,hy⟩) y)-
        (χ (a ⟨y,hy⟩) x-χ (a ⟨y,hy⟩) y)
      rw [sub_sub_sub_cancel_right]
      exact (residueSetoid p χ).symm hz _
    · simp only [test,dite_eq_right hy,Pi.zero_apply,sub_self]
      exact dvd_zero _

 theorem character_class_projector [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (x : X) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z, (residueSetoid p χ).r x z → g z=d) ∧
      (∀ z, ¬ (residueSetoid p χ).r x z → g z=0) := by
  classical
  let C : Finset X := Finset.univ.filter ((residueSetoid p χ).r x)
  have hc (z : X) : z ∈ C ↔ (residueSetoid p χ).r x z := by simp [C]
  obtain ⟨test,ht,hz,hu,hcon⟩ := exists_character_separators L p χ hχ x
  obtain ⟨d,hd,g,hg,hgc,hgz⟩ := class_projector L p hp C x test ht
    (fun y hy => hz y (fun h => hy ((hc y).mpr h)))
    (fun y hy => hu y (fun h => hy ((hc y).mpr h)))
    (fun z hz y => hcon z ((hc z).mp hz) y)
  exact ⟨d,hd,g,hg,fun z h => hgc z ((hc z).mpr h),
    fun z h => hgz z (fun hz => h ((hc z).mp hz))⟩

/-- Pair/blockwise liftability at a prime suffices for integral local
membership in a finite character-stable lattice. -/
 theorem character_local_denominator [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (z : ∀ x, E x)
    (hlift : ∀ x, ∃ m ∈ L, ∀ y, (residueSetoid p χ).r x y → m y=z y) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  let Q := Quotient (residueSetoid p χ)
  let : Fintype Q := Fintype.ofFinite Q
  let q : X → Q := Quotient.mk''
  have hq (j : Q) (y : X) : q y=j ↔ (residueSetoid p χ).r j.out y := by
    constructor
    · intro h
      exact (residueSetoid p χ).symm (Quotient.exact (h.trans (Quotient.out_eq j).symm))
    · intro h
      exact (Quotient.sound ((residueSetoid p χ).symm h)).trans (Quotient.out_eq j)
  have hproj (j : Q) := character_class_projector L p hp χ hχ j.out
  choose d hd g hg hgin hgout using hproj
  have hm (j : Q) := hlift j.out
  choose m hm hmatch using hm
  exact partition_local_denominator L p hp q z d hd g hg
    (fun j y h => hgin j y ((hq j y).mp h))
    (fun j y h => hgout j y (fun hh => h ((hq j y).mpr hh)))
    m hm (fun j y h => hmatch j y ((hq j y).mp h))

end
end KLInvariance.FiniteCharacterLocalization
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
  let names : Array Name := #[`OAI.KLInvariance.FiniteCharacterLocalization.diagonal.eq_1]
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
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.Algebra.Module.Localization.FiniteCharacters.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
