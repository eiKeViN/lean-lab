import Lean
import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic
import ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown
import ForMathlib.GroupTheory.Coxeter.Bruhat.Descent
import ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds
import ForMathlib.GroupTheory.Coxeter.Roots.Splines
import ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel. Source spans: DihedralIntervals:3, DihedralIntervals:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Dihedral
open Module TitsSpace
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem reflection_of_parity {x y : H} (hp : ds.length x % 2 ≠ ds.length y % 2) :
    ds.IsReflection (x*y⁻¹) := by
  rw [reflection_iff_odd,Nat.odd_iff]
  have h := ds.length_mul_mod_two x y⁻¹
  rw [ds.length_inv] at h
  omega

 def oppositeExternal (x c : H) : Finset H := by
  classical
  exact (externalLower ds x c).filter (fun z => ds.length z % 2 ≠ ds.length x % 2)

 def sameExternal (x c : H) : Finset H := by
  classical
  exact (externalLower ds x c).filter (fun z => ds.length z % 2 = ds.length x % 2)

 theorem oppositeExternal_reflection {x c y : H} (hy : y ∈ oppositeExternal ds x c) :
    ds.IsReflection (y*x⁻¹) := by
  classical
  exact reflection_of_parity ds (Finset.mem_filter.mp hy).2

 def interpolationRoot (x c : H) (y : oppositeExternal ds x c) : PositiveRoot M cs :=
  positiveRoot M cs ⟨φ (y.val*x⁻¹), hφ _ (oppositeExternal_reflection ds y.property)⟩

 theorem interpolation_exists (hφinj : Function.Injective φ) {x c : H}
    (hxc : BruhatLE ds x c) : ∃ F : H → MvPolynomial σ ℝ,
      (∀ t, ds.IsReflection t → ∀ (a : I → ℝ), Represents M cs (φ t) a → ∀ v,
        linearPolynomial basis (embed M a) ∣ F v-F (t*v)) ∧
      F x = ∏ y : oppositeExternal ds x c,
        linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x c y).val) ∧
      ∀ z, BruhatLE ds z c → ¬ BruhatLE ds z x → F z = 0 := by
  classical
  let Y := {y // y ∈ oppositeExternal ds x c}
  let Z := {z // z ∈ sameExternal ds x c}
  have hc : Fintype.card Z ≤ Fintype.card Y := by
    change Fintype.card ↥(sameExternal ds x c) ≤ Fintype.card ↥(oppositeExternal ds x c)
    rw [Fintype.card_coe,Fintype.card_coe]
    exact external_parity_card_le ds hxc
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hc
  have hfac (y : Y) : ∃ v₀ : Extended M,
      orbitSpline cs basis (φ y.val) v₀ (φ x) =
        linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x c y).val) ∧
      orbitSpline cs basis (φ y.val) v₀ (φ y.val) = 0 ∧
      ∀ z : Z, j z = y → orbitSpline cs basis (φ y.val) v₀ (φ z.val) = 0 := by
    have ht := oppositeExternal_reflection ds y.property
    have ha := positiveRoot_represents M cs
      ⟨φ (y.val*x⁻¹),hφ _ ht⟩
    have hxy₀ : x*y.val⁻¹=y.val*x⁻¹ := by simpa only [mul_inv_rev,inv_inv] using ht.inv
    have hxy : φ x*(φ y.val)⁻¹=φ (y.val*x⁻¹) := by
      rw [← map_inv,← map_mul,hxy₀]
    by_cases hex : ∃ z : Z, j z = y
    · obtain ⟨z,hz⟩ := hex
      have hzprop := Finset.mem_filter.mp z.property
      have hyprop := Finset.mem_filter.mp y.property
      have hr : ds.IsReflection (z.val*y.val⁻¹) := reflection_of_parity ds (by omega)
      let d := positiveRoot M cs ⟨φ (z.val*y.val⁻¹),hφ _ hr⟩
      have hd : Represents M cs (φ (z.val*y.val⁻¹)) d.val := positiveRoot_represents M cs ⟨φ (z.val*y.val⁻¹),hφ _ hr⟩
      have hxz : φ x ≠ φ z.val := by
        intro he
        have he' := hφinj he
        have hh := (mem_externalLower ds x c z.val).mp hzprop.1
        exact hh.2 (he' ▸ bruhat_refl ds x)
      obtain ⟨v₀,ha',hy',hz0'⟩ := orbitSpline_pair_factor cs basis ha hd hxy
        (by rw [map_mul,map_inv]) hxz
      refine ⟨v₀,ha',hy',?_⟩
      intro z' hz'
      have he := j.injective (hz'.trans hz.symm)
      simpa only [he] using hz0'
    · obtain ⟨v₀,ha',hy'⟩ := orbitSpline_single_factor cs basis ha hxy
      exact ⟨v₀,ha',hy',fun z hz => (hex ⟨z,hz⟩).elim⟩
  choose v₀ hv₀ hy₀ hz₀ using hfac
  let F : H → MvPolynomial σ ℝ := fun v => ∏ y : Y,
    orbitSpline cs basis (φ y.val) (v₀ y) (φ v)
  refine ⟨F,?_,?_,?_⟩
  · intro t _ht a ha v
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq.mp
    change Ideal.Quotient.mk _ (∏ y : Y, orbitSpline cs basis (φ y.val) (v₀ y) (φ v)) =
      Ideal.Quotient.mk _ (∏ y : Y, orbitSpline cs basis (φ y.val) (v₀ y) (φ (t*v)))
    simp only [map_prod]
    apply Finset.prod_congr rfl
    intro y _
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    rw [map_mul]
    exact orbitSpline_reflection cs basis ha _ _ _
  · exact Finset.prod_congr rfl (fun y _ => hv₀ y)
  · intro z hzc hzx
    have hz : z ∈ externalLower ds x c := (mem_externalLower ds x c z).mpr ⟨hzc,hzx⟩
    by_cases hp : ds.length z % 2 = ds.length x % 2
    · let z' : Z := ⟨z,Finset.mem_filter.mpr ⟨hz,hp⟩⟩
      exact Finset.prod_eq_zero (Finset.mem_univ (j z')) (hz₀ (j z') z' rfl)
    · let y : Y := ⟨z,Finset.mem_filter.mpr ⟨hz,hp⟩⟩
      exact Finset.prod_eq_zero (Finset.mem_univ y) (hy₀ y)

end
end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
open Module TitsSpace BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def inducedRoot (b : H) (e : Edge ds 1 b) : PositiveRoot M cs :=
  positiveRoot M cs ⟨φ (label ds 1 b e),hφ _ (label_isReflection ds 1 b e)⟩

 def inducedLabel (b : H) (e : Edge ds 1 b) : MvPolynomial σ ℝ :=
  linearPolynomial basis (embed M (inducedRoot ds cs φ hφ b e).val)

 theorem external_step {x c y : H} (hy : y ∈ oppositeExternal ds x c) :
    BruhatStep ds x y := by
  classical
  obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hy
  obtain ⟨_,hn⟩ := (mem_externalLower ds x c y).mp hm
  have hl : ds.length x < ds.length y := by
    have hh : ¬ ds.length y < ds.length x := fun h => hn (shorter_bruhat ds h)
    omega
  exact ⟨hl,y*x⁻¹,oppositeExternal_reflection ds hy,by group⟩

 theorem step_external {x c y : H} (hy : BruhatStep ds x y) (hyc : BruhatLE ds y c) :
    y ∈ oppositeExternal ds x c := by
  classical
  refine Finset.mem_filter.mpr ⟨(mem_externalLower ds x c y).mpr ⟨hyc,?_⟩,?_⟩
  · exact fun h => (length_le_of_bruhat ds h).not_gt hy.1
  · have hh := (step_iff_odd ds x y).mp hy
    rw [Nat.odd_iff] at hh
    omega

 variable (b : H) [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)]

 def externalEdge (x c : Interval ds 1 b) (y : oppositeExternal ds x.val c.val) : Edge ds 1 b :=
  ⟨(x,⟨y.val,one_bruhat ds y.val,
    bruhat_trans ds ((mem_externalLower ds x.val c.val y.val).mp
      (Finset.mem_filter.mp y.property).1).1 c.property.2⟩),external_step ds y.property⟩

 theorem externalEdge_mem (x c : Interval ds 1 b) (y : oppositeExternal ds x.val c.val) :
    externalEdge ds b x c y ∈ modelOutgoing (graph ds 1 b) c x := by
  classical
  apply (mem_modelOutgoing _ _ _ _).mpr
  exact ⟨rfl,((mem_externalLower ds x.val c.val y.val).mp
    (Finset.mem_filter.mp y.property).1).1⟩

 def outgoingEquiv (x c : Interval ds 1 b) :
    ↥(oppositeExternal ds x.val c.val) ≃ ↥(modelOutgoing (graph ds 1 b) c x) where
  toFun y := ⟨externalEdge ds b x c y,externalEdge_mem ds b x c y⟩
  invFun e := ⟨(target ds 1 b e.val).val,by
    obtain ⟨hs,ht⟩ := (mem_modelOutgoing _ _ _ _).mp e.property
    have hh := e.val.property
    change BruhatStep ds (source ds 1 b e.val).val (target ds 1 b e.val).val at hh
    change source ds 1 b e.val = x at hs
    rw [hs] at hh
    exact step_external ds hh ht⟩
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_modelOutgoing _ _ _ _).mp e.property).1.symm
    · rfl

 theorem interpolation_product (x c : Interval ds 1 b) :
    (∏ y : oppositeExternal ds x.val c.val,
      linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x.val c.val y).val)) =
      modelProduct (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c x := by
  classical
  calc
    _ = ∏ e : ↥(modelOutgoing (graph ds 1 b) c x), inducedLabel ds cs φ hφ basis b e.val :=
      (outgoingEquiv ds b x c).prod_comp _
    _ = _ := Finset.prod_coe_sort _ _

 theorem hasFlowDown (hφinj : Function.Injective φ) (c : Interval ds 1 b) :
    HasFlowDown (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c := by
  classical
  intro x hxc
  obtain ⟨F,hF,hFx,hFzero⟩ := interpolation_exists ds cs φ hφ basis hφinj hxc
  let f : (structureSheaf (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c).Assignment :=
    fun v _ => F v.val
  refine ⟨f,?_,?_,?_⟩
  · apply (structureCompatible_iff _ _ _ _ _).mpr
    intro e _ _ h
    have hdiv := hF (label ds 1 b e) (label_isReflection ds 1 b e)
      (inducedRoot ds cs φ hφ b e).val (positiveRoot_represents M cs
        ⟨φ (label ds 1 b e),hφ _ (label_isReflection ds 1 b e)⟩)
      (source ds 1 b e).val
    rw [label_mul_source] at hdiv
    exact hdiv
  · intro _
    exact hFx.trans (interpolation_product ds cs φ hφ basis b x c)
  · intro y hy
    funext h
    exact hFzero y.val h.down hy

omit [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)] in
 theorem inducedLabel_prime (e : Edge ds 1 b) : Prime (inducedLabel ds cs φ hφ basis b e) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact (inducedRoot ds cs φ hφ b e).property.1.ne_zero (congrArg Prod.fst h)

omit [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)] in
 theorem label_eq_of_induced_dvd (hφinj : Function.Injective φ) {e f : Edge ds 1 b}
    (h : inducedLabel ds cs φ hφ basis b e ∣ inducedLabel ds cs φ hφ basis b f) :
    label ds 1 b e = label ds 1 b f := by
  apply hφinj
  suffices he : inducedRoot ds cs φ hφ b e = inducedRoot ds cs φ hφ b f from
    congrArg Subtype.val ((positiveRootEquiv M cs).injective he)
  by_contra hn
  have hd : SymmetricAlgebra.ι ℝ (Extended M) (embed M (inducedRoot ds cs φ hφ b e).val) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (inducedRoot ds cs φ hφ b f).val) := by
    obtain ⟨z,hz⟩ := h
    exact ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z,by
      apply (SymmetricAlgebra.equivMvPolynomial basis).injective
      simpa only [map_mul,AlgEquiv.apply_symm_apply,inducedLabel,linearPolynomial,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply] using hz⟩
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp ((EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp hd)
  have he : r • (inducedRoot ds cs φ hφ b e).val = (1:ℝ) • (inducedRoot ds cs φ hφ b f).val := by
    have hh := congrArg Prod.fst hr
    exact hh.trans (one_smul ℝ _).symm
  exact one_ne_zero ((positiveRoots_independent _ _ hn).eq_zero_of_pair' he).2

 theorem model_flabby (hφinj : Function.Injective φ) (c : Interval ds 1 b) :
    (structureSheaf (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c).Flabby := by
  classical
  let : Finite (Interval ds 1 b) := interval_finite ds 1 b
  apply flowDown_flabby
  · intro x e he f hf hne
    apply ((inducedLabel_prime ds cs φ hφ basis b e).irreducible.isRelPrime_iff_not_dvd).mpr
    intro hdiv
    apply hne
    apply eq_of_label_source_eq ds 1 b (label_eq_of_induced_dvd ds cs φ hφ basis b hφinj hdiv)
    exact ((mem_modelOutgoing _ _ _ _).mp he).1.trans ((mem_modelOutgoing _ _ _ _).mp hf).1.symm
  · exact hasFlowDown ds cs φ hφ basis b hφinj c

end
end KLInvariance.Dihedral
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
  let names : Array Name := #[`OAI.KLInvariance.Dihedral.inducedLabel.eq_1]
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
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."

open Lean

structure TypeDumpState where
  ids : ExprStructMap Nat := {}
  proofIds : ExprStructMap Nat := {}
  next : Nat := 0
  privateOwners : Std.HashMap Name Name := {}
  proofAliases : NameHashSet := {}
  unrenamed : NameHashSet := {}

-- Alpha equivalence ignores binder display names. Only compiler-private OAI
-- owner prefixes are erased from constant names; their user names stay exact.
-- There are no duplicate private user names in the pinned source.
private def canonicalConstant (n : Name) : Name :=
  if n.toString.startsWith "_private.OAI." then
    (privateToUserName? n).getD n
  else n

-- Keep every mathematical expression constructor, universe, binder info,
-- constant, application and de Bruijn index. Metadata and binder display names
-- have no effect on the mathematical type. A local compiler theorem auxiliary
-- is represented by its full proposition, using kernel proof irrelevance.
-- No proof body, general definition, data instance or user theorem is unfolded.
partial def dumpType (env : Environment) (out : IO.FS.Handle) (e : Expr)
    (proofContext := false) : StateT TypeDumpState IO Nat := do
  let cached : TypeDumpState ← get
  let cache := if proofContext then cached.proofIds else cached.ids
  if let some id := cache[ExprStructEq.mk e]? then return id
  if let .mdata _ body := e then return ← dumpType env out body proofContext
  let fields ← match e with
    | .bvar i => pure ["bvar", toString i]
    | .sort u => pure ["sort", reprStr u]
    | .const n us =>
      let proofName := match n with
        | .str _ s => s.startsWith "_proof_"
        | _ => false
      if n.isInternal && n.toString.startsWith "OAI." && proofName then
        if let some (.thmInfo info) := env.find? n then
          -- Kernel theorem declarations prove propositions. Their full
          -- proposition, including parameters, is retained; only its binder
          -- display/implicitness metadata is irrelevant to the proof value.
          let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
          modify fun st => { st with proofAliases := st.proofAliases.insert n }
          pure ["proof", toString proposition]
        else pure ["const", reprStr n, reprStr us]
      else
        let canonical := canonicalConstant n
        if canonical != n then
          if env.contains canonical then
            throw <| IO.userError "Private canonical name collides with an unrenamed global constant"
          if let some previous := (← get).privateOwners[canonical]? then
            if previous != n then throw <| IO.userError "Ambiguous private type constant"
          modify fun st => { st with privateOwners := st.privateOwners.insert canonical n }
        pure ["const", reprStr canonical, reprStr us]
    | .app f a => do
      let f ← dumpType env out f proofContext; let a ← dumpType env out a proofContext
      pure ["app", toString f, toString a]
    | .lam _ t b bi | .forallE _ t b bi => do
      let t ← dumpType env out t proofContext; let b ← dumpType env out b proofContext
      pure [if e.isLambda then "lam" else "forall", "_", if proofContext then "kernel" else reprStr bi, toString t, toString b]
    | .letE _ t v b nondep => do
      let t ← dumpType env out t proofContext; let v ← dumpType env out v proofContext; let b ← dumpType env out b proofContext
      pure ["let", "_", toString t, toString v, toString b, toString nondep]
    | .lit v => pure ["lit", reprStr v]
    | .proj n i b => do
      let b ← dumpType env out b proofContext
      pure ["proj", reprStr n, toString i, toString b]
    | .fvar _ | .mvar _ => throw <| IO.userError "Non-closed declaration type"
    | .mdata _ _ => unreachable!
  match e with
  | .const n _ =>
    if fields.head! == "const" && canonicalConstant n == n then
      modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | .proj n _ _ => modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | _ => pure ()
  let state : TypeDumpState ← get
  if proofContext then
    set { state with proofIds := state.proofIds.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  else
    set { state with ids := state.ids.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  out.putStrLn s!"NODE\t{state.next}\t{(toJson fields).compress}"
  return state.next

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

-- This experiment accepts duplicate serialized theorem records only.
-- Other ConstantInfo variants fail closed; their safety/hints are not omitted
-- from a purported full-record comparison. ExprStructEq retains binder names
-- and annotations, unlike BEq Expr (Expr.eqv).
private def sameSerializedTheorem (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams &&
      ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
      ExprStructEq.mk a.value == ExprStructEq.mk b.value && a.all == b.all
  | _, _ => false


run_elab do
  let env := (← Lean.getEnv).setExporting false
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.Dihedral.inducedLabel.eq_1] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t1\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
