import Lean
import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure. Source spans: MinimalExtensions:14, MinimalExtensions:18.
See migration.json and MIGRATION.md for exact provenance.
The scalar-quotient structure sheaf, its defining properties, natural base-change isomorphism and preservation of flabbiness. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

private def quotientLinear (e : E) : R →ₗ[R] R ⧸ Ideal.span {α e} :=
  (Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap

 def structureSheaf : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (PLift (x ≤ c) → R)
  edge e := ModuleCat.of R (PLift (G.target e ≤ c) → R ⧸ Ideal.span {α e})
  upper e := LinearMap.pi (fun h => (quotientLinear α e).comp (LinearMap.proj h))
  lower e := LinearMap.pi (fun h => (quotientLinear α e).comp
    (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩))

 theorem structureSheaf_free (x : V) : Module.Free R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Free R (PLift (x ≤ c) → R))

 theorem structureSheaf_finite (x : V) : Module.Finite R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Finite R (PLift (x ≤ c) → R))

 theorem structureSheaf_support (x : V) (hx : ¬ x ≤ c) :
    Subsingleton ((structureSheaf G α c).vertex x) := by
  refine ⟨fun f g => funext fun h => False.elim (hx h.down)⟩

 def structureVertexIso (x : V) (hx : x ≤ c) :
    (structureSheaf G α c).vertex x ≃ₗ[R] R where
  toFun f := f ⟨hx⟩
  invFun r := fun _ => r
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem structureSheaf_generated : (structureSheaf G α c).Generated := by
  classical
  intro x v
  by_cases hx : x ≤ c
  · refine ⟨fun _ _ => v ⟨hx⟩, fun _ _ _ => rfl, rfl⟩
  · let _ := structureSheaf_support G α c x hx
    exact ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩

 theorem structureSheaf_upperQuotient : (structureSheaf G α c).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose r hr using fun h : PLift (G.target e ≤ c) => Ideal.Quotient.mk_surjective (v h)
    exact ⟨r,funext hr⟩
  · intro v
    constructor
    · intro hv
      have hh (h : PLift (G.target e ≤ c)) :
          v h ∈ Ideal.span {α e} := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv h)
      choose r hr using fun h => Ideal.mem_span_singleton.mp (hh h)
      exact ⟨r,funext hr⟩
    · rintro ⟨w,rfl⟩
      funext h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨w h,rfl⟩)

 theorem structureSheaf_minimal [IsLocalRing R]
    (hα : ∀ e, α e ∈ IsLocalRing.maximalIdeal R)
    (hreach : ∀ x, x < c → ∃ e, G.source e = x ∧ G.target e ≤ c)
    (x : V) (hxc : x ≠ c) :
    LinearMap.ker ((structureSheaf G α c).stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R ((structureSheaf G α c).vertex x)) := by
  classical
  intro v hv
  by_cases hx : x ≤ c
  · obtain ⟨e,he,het⟩ := hreach x (lt_of_le_of_ne hx hxc)
    subst x
    have heq := congrFun (LinearMap.mem_ker.mp hv) ⟨e,rfl⟩
    have hvα : v ⟨hx⟩ ∈ Ideal.span {α e} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (congrFun heq ⟨het⟩)
    have hm : v ⟨hx⟩ ∈ IsLocalRing.maximalIdeal R :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hα e))) hvα
    let one : (structureSheaf G α c).vertex (G.source e) := fun _ => 1
    have hs : v ⟨hx⟩ • one ∈ IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) :=
      Submodule.smul_mem_smul hm (show one ∈
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) from Submodule.mem_top)
    have heqv : v = v ⟨hx⟩ • one := by
      funext h
      exact (mul_one _).symm
    rw [heqv]
    exact hs
  · let _ := structureSheaf_support G α c x hx
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um un
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}
noncomputable section

namespace Iso
variable {B : Sheaf.{ur,uv,ue,um} (R := R) G}
  {C : Sheaf.{ur,uv,ue,un} (R := R) G} (j : Iso B C)
include j

 theorem flabby (hb : B.Flabby) : C.Flabby := by
  intro Ω hΩ f hf
  have hsf : B.CompatibleOn Ω (j.symm.assignments f) :=
    (j.symm.compatible_iff Ω f).mpr hf
  obtain ⟨g,hg,hgf⟩ := hb Ω hΩ (j.symm.assignments f) hsf
  refine ⟨j.assignments g,(j.compatible_iff Set.univ g).mpr hg,?_⟩
  intro x hx
  change j.vertex x (g x) = f x
  rw [hgf x hx]
  exact (j.vertex x).apply_symm_apply _

 theorem generated (hb : B.Generated) : C.Generated := by
  intro x v
  obtain ⟨f,hf,hfv⟩ := hb x ((j.vertex x).symm v)
  refine ⟨j.assignments f,(j.compatible_iff Set.univ f).mpr hf,?_⟩
  change j.vertex x (f x) = v
  rw [hfv,LinearEquiv.apply_symm_apply]

end Iso

variable (S : Type us) [CommRing S] [Algebra R S]

def baseChangeScalar : S ⊗[R] R ≃ₗ[S] S := AlgebraTensorModule.rid R S S

@[simp] theorem baseChangeScalar_tmul (s : S) (r : R) :
    baseChangeScalar S (s ⊗ₜ[R] r) = s * algebraMap R S r := by
  change r • s = s * algebraMap R S r
  rw [Algebra.smul_def,mul_comm]

 theorem span_map (a : R) :
    (Ideal.span {a}).map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
  rw [Ideal.map_span,Set.image_singleton]

 def baseChangeQuotient (a : R) :
    S ⊗[R] (R ⧸ Ideal.span {a}) ≃ₗ[S] S ⧸ Ideal.span {algebraMap R S a} :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {a})).symm.toLinearEquiv.trans
    (Ideal.quotientEquivAlgOfEq S (span_map S a)).toLinearEquiv

@[simp] theorem baseChangeQuotient_tmul (a r : R) (s : S) :
    baseChangeQuotient S a (s ⊗ₜ[R] Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (s * algebraMap R S r) := by
  simp only [baseChangeQuotient,LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_apply,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk _ (r • s) = Ideal.Quotient.mk _ (s * algebraMap R S r)
  rw [Algebra.smul_def,mul_comm]


 def baseChangePiScalar (p : Prop) :
    S ⊗[R] (PLift p → R) ≃ₗ[S] (PLift p → S) := by
  classical
  exact (TensorProduct.piRight R S S (fun _ : PLift p => R)).trans
    (LinearEquiv.piCongrRight (fun _ => baseChangeScalar S))

 def baseChangePiQuotient (a : R) (p : Prop) :
    S ⊗[R] (PLift p → R ⧸ Ideal.span {a}) ≃ₗ[S]
      (PLift p → S ⧸ Ideal.span {algebraMap R S a}) := by
  classical
  exact (TensorProduct.piRight R S S
    (fun _ : PLift p => R ⧸ Ideal.span {a})).trans
      (LinearEquiv.piCongrRight (fun _ => baseChangeQuotient S a))

 theorem baseChangePiScalar_tmul (p : Prop) (s : S) (v : PLift p → R) (h : PLift p) :
    baseChangePiScalar S p (s ⊗ₜ v) h = s * algebraMap R S (v h) :=
  baseChangeScalar_tmul S s (v h)

 theorem baseChangePiQuotient_tmul (a : R) (p : Prop)
    (s : S) (v : PLift p → R ⧸ Ideal.span {a}) (h : PLift p) :
    baseChangePiQuotient S a p (s ⊗ₜ v) h = baseChangeQuotient S a (s ⊗ₜ v h) := rfl

 def quotientPullback (a : R) (p q : Prop) (h : q → p) :
    (PLift p → R) →ₗ[R] (PLift q → R ⧸ Ideal.span {a}) :=
  LinearMap.pi fun t => (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap.comp
    (LinearMap.proj ⟨h t.down⟩)

 theorem baseChangePi_natural (a : R) (p q : Prop) (h : q → p)
    (v : S ⊗[R] (PLift p → R)) :
    baseChangePiQuotient S a q
      (AlgebraTensorModule.lTensor S S (quotientPullback a p q h) v) =
      quotientPullback (algebraMap R S a) p q h (baseChangePiScalar S p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    funext hh
    change baseChangePiQuotient S a q (s ⊗ₜ quotientPullback a p q h v) hh = _
    rw [baseChangePiQuotient_tmul]
    change baseChangeQuotient S a (s ⊗ₜ Ideal.Quotient.mk _ (v ⟨h hh.down⟩)) = _
    rw [baseChangeQuotient_tmul]
    exact congrArg (Ideal.Quotient.mk _) (baseChangePiScalar_tmul S p s v _).symm
  | add v w hv hw => simp only [map_add,hv,hw]

 def structureBaseChangeIso (G : OrderedGraph V E) (α : E → R) (c : V) :
    Iso ((structureSheaf G α c).baseChange S)
      (structureSheaf G (fun e => algebraMap R S (α e)) c) where
  vertex x := baseChangePiScalar S (x ≤ c)
  edge e := baseChangePiQuotient S (α e) (G.target e ≤ c)
  lower e v := baseChangePi_natural S (α e) (G.source e ≤ c) (G.target e ≤ c)
    ((G.increasing e).le.trans ·) v
  upper e v := baseChangePi_natural S (α e) (G.target e ≤ c) (G.target e ≤ c) id v

 theorem structureSheaf_flat_flabby [Finite V] [Finite E] [Module.Flat R S]
    (G : OrderedGraph V E) (α : E → R) (c : V) (hf : (structureSheaf G α c).Flabby) :
    (structureSheaf G (fun e => algebraMap R S (α e)) c).Flabby :=
  (structureBaseChangeIso S G α c).flabby ((structureSheaf G α c).baseChange_flabby S hf)

end
end KLInvariance.MomentGraph.Sheaf
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
  let names : Array Name := #[`OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient.eq_1]
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
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
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
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient.eq_1] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tForMathlib.Combinatorics.MomentGraph.Sheaf.Structure"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t1\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
