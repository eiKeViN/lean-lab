import Lean
import Mathlib
import ForMathlib.GroupTheory.Coxeter.Roots.Splines
import ForMathlib.LinearAlgebra.PlaneReduction
import ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient
import OAI.KL.Localization.Ambient

/-! Semantic home: OAI.KL.Localization.GraphEmbedding. Source spans: PlaneLocalization:7, PlaneLocalization:24, PlaneLocalization:27.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def embedLinear : (I → ℝ) →ₗ[ℝ] Extended M where
  toFun := embed M
  map_add' _ _ := by simp [embed]
  map_smul' _ _ := by simp [embed]

 theorem embedLinear_injective : Function.Injective (embedLinear (M := M)) := by
  intro a b hab
  exact congrArg Prod.fst hab

 def planePrime (P : Submodule ℝ (I → ℝ)) : Ideal (MvPolynomial σ ℝ) :=
  Ideal.map (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))))

 instance planePrime_isPrime (P : Submodule ℝ (I → ℝ)) : (planePrime basis P).IsPrime :=
  Ideal.map_isPrime_of_equiv (SymmetricAlgebra.equivMvPolynomial basis)

 theorem linear_mem_planePrime_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    linearPolynomial basis (embed M a) ∈ planePrime basis P ↔ a ∈ P := by
  rw [planePrime,Ideal.mem_map_iff_of_surjective (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricAlgebra.equivMvPolynomial basis).surjective]
  change (∃ z, z ∈ SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))) ∧
    SymmetricAlgebra.equivMvPolynomial basis z =
      SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι ℝ (Extended M) (embed M a))) ↔ _
  constructor
  · rintro ⟨z,hz,he⟩
    have h := (SymmetricAlgebra.equivMvPolynomial basis).injective he
    subst z
    have ha := (SymmetricPlaneIdeal.ι_mem_iff _ _).mp hz
    obtain ⟨b,hb,he⟩ := ha
    have he' : b = a := embedLinear_injective he
    exact he' ▸ hb
  · intro ha
    refine ⟨_,(SymmetricPlaneIdeal.ι_mem_iff _ _).mpr ?_,rfl⟩
    exact ⟨a,ha,rfl⟩

 abbrev PlaneRing (P : Submodule ℝ (I → ℝ)) := Localization.AtPrime (planePrime basis P)

 theorem linear_mem_maximal_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (linearPolynomial basis (embed M a)) ∈
      IsLocalRing.maximalIdeal (PlaneRing basis P) ↔ a ∈ P := by
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (planePrime basis P),
    linear_mem_planePrime_iff]

 theorem linear_isUnit_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (linearPolynomial basis (embed M a))) ↔ a ∉ P := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (planePrime basis P)]
  change _ ∉ planePrime basis P ↔ _
  rw [linear_mem_planePrime_iff]

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def localizedLinear (P : Submodule ℝ (I → ℝ)) : (I → ℝ) →ₗ[ℝ] PlaneRing basis P :=
  (IsScalarTower.toAlgHom ℝ (MvPolynomial σ ℝ) (PlaneRing basis P)).toLinearMap.comp
    ((linearPolynomial basis).comp (embedLinear (M := M)))

 def localizedEdgeIdeal (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) : Ideal (PlaneRing basis P) :=
  Ideal.span {localizedLinear basis P a}

 abbrev LocalizedEdgeRing (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :=
  PlaneRing basis P ⧸ localizedEdgeIdeal basis P a

 def localizedReduction (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    (I → ℝ) →ₗ[ℝ] LocalizedEdgeRing basis P a :=
  (Ideal.Quotient.mkₐ ℝ (localizedEdgeIdeal basis P a)).toLinearMap.comp
    (localizedLinear basis P)

 theorem localizedReduction_self (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    localizedReduction basis P a a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

 theorem positiveRoot_not_line {a c : PositiveRoot M cs} (hca : c ≠ a) :
    c.val ∉ Submodule.span ℝ ({a.val} : Set (I → ℝ)) := by
  intro h
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp h
  exact (linearIndependent_fin2.mp (positiveRoots_independent c a hca)).2 r hr

 theorem localizedReduction_associated (P : Submodule ℝ (I → ℝ))
    (a b c : PositiveRoot M cs) (hc : c.val ∈ rootPlane a b) (hca : c ≠ a) :
    Associated (localizedReduction basis P a.val c.val)
      (localizedReduction basis P a.val b.val) :=
by
  exact @PlaneReduction.associated_reduction ℝ _ (I → ℝ) _ _
    (LocalizedEdgeRing basis P a.val) _ _ (localizedReduction basis P a.val)
    a.val b.val c.val (localizedReduction_self basis P a.val) hc
    (positiveRoot_not_line hca)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module BruhatGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem polynomialRoot_localized (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialRoot cs basis a) =
      localizedLinear basis P a.val := rfl

 theorem polynomialRoot_reduced (P : Submodule ℝ (I → ℝ)) (a c : PositiveRoot M cs) :
    algebraMap (PlaneRing basis P) (LocalizedEdgeRing basis P a.val)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialRoot cs basis c)) =
      localizedReduction basis P a.val c.val := rfl

 theorem planeRoot_outside {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    (planeRoot x a Q).val ∉ rootPlane a b := by
  intro h
  apply hQ
  rw [← planeRoot_plane x a Q]
  exact rootPlane_eq_of_mem a b a (planeRoot x a Q) hab
    (Submodule.subset_span (Set.mem_insert _ _)) h (planeRoot_ne x a Q).symm

 theorem reduced_planeRoot_other_isUnit {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    IsUnit (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val) := by
  have h := (linear_isUnit_iff basis (rootPlane a b) (planeRoot x a Q).val).mpr
    (planeRoot_outside hab Q hQ)
  exact h.map (algebraMap (PlaneRing basis (rootPlane a b))
    (LocalizedEdgeRing basis (rootPlane a b) a.val))

/-- The actual integral edge factor reduces, in each actual plane, to precisely
its plane weight. All other factors are proven units, not discarded formally. -/
 theorem edgeFactor_local_associated (x : W) (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Associated
      (algebraMap (PlaneRing basis (rootPlane a b)) (LocalizedEdgeRing basis (rootPlane a b) a.val)
        (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis (rootPlane a b)) (edgeFactorLift cs basis x a)))
      ((localizedReduction basis (rootPlane a b) a.val b.val)^((planeWeight x a (rootPlane a b)).toNat)) := by
  classical
  let p := localizedReduction basis (rootPlane a b) a.val b.val
  have hfactor (Q : (planeWeight x a).support) :
      Associated
        ((localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
        (if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) := by
    by_cases hQ : Q.val=rootPlane a b
    · rw [ite_eq_left hQ]
      have hc : (planeRoot x a Q).val ∈ rootPlane a b := by
        rw [← hQ,← planeRoot_plane x a Q]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have h := localizedReduction_associated basis (rootPlane a b) a b (planeRoot x a Q)
        hc (planeRoot_ne x a Q)
      simpa only [hQ] using (Associated.pow_pow (M := LocalizedEdgeRing basis (rootPlane a b) a.val) h (n := (planeWeight x a Q.val).toNat))
    · rw [ite_eq_right hQ]
      exact associated_one_iff_isUnit.mpr ((reduced_planeRoot_other_isUnit basis hab Q hQ).pow _)
  have hprod := Associated.prod Finset.univ
    (fun Q : (planeWeight x a).support =>
      (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
    (fun Q => if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1)
    (fun Q _ => hfactor Q)
  have hp : (∏ Q : (planeWeight x a).support,
      if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) =
      p^((planeWeight x a (rootPlane a b)).toNat) := by
    rw [Fintype.prod_ite_eq_ite_exists _ (fun i j hi hj => Subtype.ext (hi.trans hj.symm))]
    by_cases hP : rootPlane a b ∈ (planeWeight x a).support
    · rw [ite_eq_left ⟨⟨rootPlane a b,hP⟩,rfl⟩]
    · have hz := Finsupp.notMem_support_iff.mp hP
      rw [hz,Int.toNat_zero,pow_zero]
      split_ifs <;> rfl
  rw [hp] at hprod
  simpa only [edgeFactorLift,map_prod,map_pow,polynomialRoot_reduced] using hprod

end
end KLInvariance.TitsSpace
end

end OAI

open Lean Meta Elab Command in
run_elab do
  discard <| getEqnsFor? `OAI.KLInvariance.TitsSpace.embedLinear

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
  let names : Array Name := #[`OAI.KLInvariance.TitsSpace.embedLinear.eq_1]
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
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson (Lean.defeqAttr.hasTag env n), toJson (Lean.backwardDefeqAttr.hasTag env n)])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/OAI.KL.Localization.Edge.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
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
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/OAI.KL.Localization.Edge.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.TitsSpace.embedLinear.eq_1] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tOAI.KL.Localization.Edge"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t1\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
