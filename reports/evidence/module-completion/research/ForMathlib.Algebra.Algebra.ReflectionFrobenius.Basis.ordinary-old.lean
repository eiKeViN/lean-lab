import Lean
import Mathlib
import ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic
import ForMathlib.Algebra.Module.Graded.Basis
import ForMathlib.Algebra.Module.Graded.PolynomialMap
import ForMathlib.Algebra.Module.Graded.HomogeneousMul

/-! Semantic home: ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis. Source spans: Frobenius:17, Frobenius:9, Frobenius:8, Frobenius:12.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionFrobenius
open scoped Matrix
universe ua ui
variable {A : Type ua} [CommRing A] [IsDomain A] [CharZero A]
  {ι : Type ui} [Fintype ι] (τ : A ≃+* A) (α : A)
noncomputable section

 def wallCoordinate (E : Matrix ι ι A) (v : Fin 2 × ι → A) : Fin 2 × ι → A := fun e =>
  if e.1=0 then (E *ᵥ (fun j => v (0,j)+α*v (1,j))) e.2
  else ((E.map τ) *ᵥ (fun j => v (0,j)-α*v (1,j))) e.2

 def wallMatrix (E : Matrix ι ι A) : Matrix (Fin 2 × ι) (Fin 2 × ι) A := fun e f =>
  if e.1=0 then (if f.1=0 then E e.2 f.2 else α*E e.2 f.2)
  else if f.1=0 then τ (E e.2 f.2) else -α*τ (E e.2 f.2)

omit [IsDomain A] [CharZero A] in
 theorem wallMatrix_mulVec (E : Matrix ι ι A) (v : Fin 2 × ι → A) :
    wallMatrix τ α E *ᵥ v = wallCoordinate τ α E v := by
  classical
  funext ⟨r,j⟩
  change (∑ c : Fin 2 × ι, wallMatrix τ α E (r,j) c * v c) = _
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  fin_cases r <;>
    simp [wallMatrix,wallCoordinate,Matrix.mulVec,dotProduct,
      Finset.sum_add_distrib,mul_add,
      mul_left_comm,mul_assoc,sub_eq_add_neg]

omit [IsDomain A] [CharZero A] in
 theorem matrixTwist_injective (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (Matrix.mulVec (E.map τ)) := by
  intro v w hv
  have hh : E *ᵥ (fun j => τ.symm (v j)) = E *ᵥ (fun j => τ.symm (w j)) := by
    funext i
    have h := congrArg τ.symm (congrFun hv i)
    simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply,
      RingEquiv.symm_apply_apply] using h
  have hh' := hE hh
  funext i
  exact τ.symm.injective (congrFun hh' i)

 theorem wallCoordinate_injective (hα : α ≠ 0) (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (wallCoordinate τ α E) := by
  intro v w hv
  have h₀ : (fun j => v (0,j)+α*v (1,j)) = (fun j => w (0,j)+α*w (1,j)) := by
    apply hE
    funext j
    simpa only [wallCoordinate,ite_eq_left rfl,ite_true] using congrFun hv (0,j)
  have h₁ : (fun j => v (0,j)-α*v (1,j)) = (fun j => w (0,j)-α*w (1,j)) := by
    apply matrixTwist_injective τ E hE
    funext j
    simpa only [wallCoordinate,show (1:Fin 2) ≠ 0 by decide,ite_false] using congrFun hv (1,j)
  funext ⟨ε,j⟩
  have h0 := congrFun h₀ j
  have h1 := congrFun h₁ j
  have hi1 : v (1,j)=w (1,j) := by
    have hh : (2:A)*α*(v (1,j)-w (1,j))=0 := by linear_combination h0-h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero two_ne_zero hα))
  have hi0 : v (0,j)=w (0,j) := by simpa only [hi1,add_left_inj] using h0
  fin_cases ε
  · exact hi0
  · exact hi1

end
end KLInvariance.ReflectionFrobenius
end


section
namespace KLInvariance.ReflectionFrobenius
open Module
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 def reflectionBasis : Basis (Fin 2) (fixed τ) A :=
  (Basis.finTwoProd (fixed τ)).map (coordinates τ α hinv hα hanti hdiv).symm

 theorem reflectionBasis_zero : reflectionBasis τ α hinv hα hanti hdiv 0 = 1 := by
  change expand τ α (Basis.finTwoProd (fixed τ) 0) = 1
  simp [expand_apply]

 theorem reflectionBasis_one : reflectionBasis τ α hinv hα hanti hdiv 1 = α := by
  change expand τ α (Basis.finTwoProd (fixed τ) 1) = α
  simp [expand_apply]

 theorem reflectionBasis_homogeneous (𝓐 : ℤ → Submodule k A)
    [SetLike.GradedOne 𝓐] (hroot : α ∈ 𝓐 1) (i : Fin 2) :
    reflectionBasis τ α hinv hα hanti hdiv i ∈ 𝓐 (i.val : ℤ) := by
  fin_cases i
  · change reflectionBasis τ α hinv hα hanti hdiv (0 : Fin 2) ∈ 𝓐 0
    rw [reflectionBasis_zero]
    exact SetLike.one_mem_graded 𝓐
  · change reflectionBasis τ α hinv hα hanti hdiv (1 : Fin 2) ∈ 𝓐 1
    rw [reflectionBasis_one]
    exact hroot

end
end KLInvariance.ReflectionFrobenius
end


section
namespace KLInvariance.ReflectionFrobenius
open KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 theorem trace_difference (a : A) :
    2*α*(trace τ α hinv hα hanti hdiv a : A) = a-τ a := by
  have h := expand_coordinates τ α hinv hα hanti hdiv a
  have ht := congrArg τ h
  simp only [expand_apply,map_add,map_mul,fixed_val,hanti] at h ht
  change 2*α*((coordinates τ α hinv hα hanti hdiv a).2 : A) = a-τ a
  linear_combination h-ht

 theorem trace_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedSMul 𝓐 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    {n : ℤ} {a : A} (ha : a ∈ 𝓐 n) :
    (trace τ α hinv hα hanti hdiv a : A) ∈ 𝓐 (n-1) := by
  apply homogeneous_of_mul 𝓐 hroot hα
  have hd := (𝓐 n).sub_mem ha (hτ n a ha)
  have hal := (𝓐 n).smul_mem ((2:k)⁻¹) hd
  have ht := trace_difference τ α hinv hα hanti hdiv a
  have htwo : (2:A)*algebraMap k A ((2:k)⁻¹) = 1 := by
    rw [show (2:A)=algebraMap k A (2:k) by exact (map_ofNat (algebraMap k A) 2).symm, ← map_mul]
    simp
  have he : α*(trace τ α hinv hα hanti hdiv a : A) =
      (2:k)⁻¹ • (a-τ a) := by
    rw [Algebra.smul_def]
    linear_combination (algebraMap k A ((2:k)⁻¹))*ht -
      (α*(trace τ α hinv hα hanti hdiv a : A))*htwo
  exact he ▸ hal

 theorem coordinates_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedSMul 𝓐 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    {n : ℤ} {a : A} (ha : a ∈ 𝓐 n) :
    ((coordinates τ α hinv hα hanti hdiv a).1 : A) ∈ 𝓐 n ∧
    ((coordinates τ α hinv hα hanti hdiv a).2 : A) ∈ 𝓐 (n-1) := by
  have ht := trace_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot hτ ha
  constructor
  · have hp : α*(trace τ α hinv hα hanti hdiv a : A) ∈ 𝓐 n := by
      simpa only [smul_eq_mul,vadd_eq_add,show (1:ℤ)+(n-1)=n by omega] using
        SetLike.GradedSMul.smul_mem hroot ht
    have he : ((coordinates τ α hinv hα hanti hdiv a).1 : A) =
        a-α*(trace τ α hinv hα hanti hdiv a : A) := by
      have h := expand_coordinates τ α hinv hα hanti hdiv a
      change ((coordinates τ α hinv hα hanti hdiv a).1 : A) +
        α*(trace τ α hinv hα hanti hdiv a : A)=a at h
      linear_combination h
    exact he ▸ (𝓐 n).sub_mem ha hp
  · exact ht

end
end KLInvariance.ReflectionFrobenius
end


section
namespace KLInvariance.ReflectionFrobenius
open Module KLInvariance.Graded
universe uk uv us
variable {k : Type uk} [Field k] [CharZero k]
  {V : Type uv} [AddCommGroup V] [Module k V]
  {σ : Type us} [Fintype σ] (basis : Basis σ k V)
noncomputable section

 def polynomialLinear (v : V) : MvPolynomial σ k :=
  SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V v)

omit [CharZero k] in
 theorem polynomialLinear_homogeneous (v : V) :
    polynomialLinear basis v ∈ polynomialGrading k σ 1 := by
  classical
  unfold polynomialLinear
  rw [← basis.sum_repr v]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading k σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => (1:ℤ)) i)

 def polynomialAction (e : V ≃ₗ[k] V) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  ((SymmetricAlgebra.equivMvPolynomial basis).symm.trans (symmetricAction e)).trans
    (SymmetricAlgebra.equivMvPolynomial basis)

omit [CharZero k] [Fintype σ] in
@[simp] theorem polynomialAction_linear (e : V ≃ₗ[k] V) (v : V) :
    polynomialAction basis e (polynomialLinear basis v) = polynomialLinear basis (e v) := by
  simp [polynomialAction,polynomialLinear]

omit [CharZero k] in
 theorem polynomialAction_homogeneous (e : V ≃ₗ[k] V) {n : ℤ}
    {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    polynomialAction basis e p ∈ polynomialGrading k σ n := by
  apply algHom_polynomialGrading (polynomialAction basis e).toAlgHom _ hp
  intro i
  change polynomialAction basis e (MvPolynomial.X i) ∈ _
  have hx : MvPolynomial.X i = polynomialLinear basis (basis i) := by
    simp [polynomialLinear]
  rw [hx,polynomialAction_linear]
  exact polynomialLinear_homogeneous basis _

variable (root : V) (coroot : Dual k V) (hroot : coroot root=2)

 abbrev polynomialReflection : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  polynomialAction basis (Module.reflection hroot)

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_involutive : Function.Involutive
    (polynomialReflection basis root coroot hroot) := by
  intro p
  change SymmetricAlgebra.equivMvPolynomial basis
    (reflectionAction root coroot hroot
      ((SymmetricAlgebra.equivMvPolynomial basis).symm
        (SymmetricAlgebra.equivMvPolynomial basis
          (reflectionAction root coroot hroot
            ((SymmetricAlgebra.equivMvPolynomial basis).symm p)))))=p
  rw [AlgEquiv.symm_apply_apply,reflectionAction_involutive,AlgEquiv.apply_symm_apply]

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_anti : polynomialReflection basis root coroot hroot
    (polynomialLinear basis root) = -polynomialLinear basis root := by
  change SymmetricAlgebra.equivMvPolynomial basis
    (reflectionAction root coroot hroot
      ((SymmetricAlgebra.equivMvPolynomial basis).symm
        (SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V root)))) = _
  rw [AlgEquiv.symm_apply_apply,reflectionAction_anti,map_neg]
  rfl

omit [Fintype σ] in
include coroot hroot in
 theorem polynomialLinear_ne_zero : polynomialLinear basis root ≠ 0 := by
  intro h
  apply reflectionRoot_ne_zero root coroot hroot
  exact (SymmetricAlgebra.equivMvPolynomial basis).injective (by simpa [polynomialLinear] using h)

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_divisible (p : MvPolynomial σ k) :
    polynomialLinear basis root ∣ p-polynomialReflection basis root coroot hroot p := by
  obtain ⟨d,hd⟩ := reflectionAction_divisible root coroot hroot
    ((SymmetricAlgebra.equivMvPolynomial basis).symm p)
  refine ⟨SymmetricAlgebra.equivMvPolynomial basis d,?_⟩
  simpa [polynomialLinear,polynomialReflection,polynomialAction] using
    congrArg (SymmetricAlgebra.equivMvPolynomial basis) hd

 def polynomialTrace : MvPolynomial σ k →ₗ[fixed (polynomialReflection basis root coroot hroot)]
    fixed (polynomialReflection basis root coroot hroot) :=
  trace _ _ (polynomialReflection_involutive basis root coroot hroot)
    (polynomialLinear_ne_zero basis root coroot hroot)
    (polynomialReflection_anti basis root coroot hroot)
    (polynomialReflection_divisible basis root coroot hroot)

 theorem polynomialTrace_homogeneous {n : ℤ} {p : MvPolynomial σ k}
    (hp : p ∈ polynomialGrading k σ n) :
    (polynomialTrace basis root coroot hroot p : MvPolynomial σ k) ∈ polynomialGrading k σ (n-1) :=
  trace_homogeneous _ _ _ _ _ _ (polynomialGrading k σ)
    (polynomialLinear_homogeneous basis root)
    (fun _ _ h => polynomialAction_homogeneous basis (Module.reflection hroot) h) hp

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
  let names : Array Name := #[`OAI.KLInvariance.ReflectionFrobenius.polynomialAction.eq_1, `OAI.KLInvariance.ReflectionFrobenius.polynomialLinear.eq_1, `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate.eq_1, `OAI.KLInvariance.ReflectionFrobenius.wallMatrix.eq_1]
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
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
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
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.ReflectionFrobenius.polynomialAction.eq_1, `OAI.KLInvariance.ReflectionFrobenius.polynomialLinear.eq_1, `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate.eq_1, `OAI.KLInvariance.ReflectionFrobenius.wallMatrix.eq_1] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t4\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
