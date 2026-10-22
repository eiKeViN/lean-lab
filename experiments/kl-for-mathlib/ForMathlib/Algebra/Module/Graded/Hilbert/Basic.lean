module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.Hilbert.Basic. Source spans: ModuleAlgebra:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Hilbert
universe uk um
variable {k : Type uk} {M : Type um} [Field k] [AddCommGroup M] [Module k M]

/-- The actual degree-n vector space of a submodule, expressed in the fixed
ambient homogeneous piece. -/
@[expose] def piece (𝓜 : ℤ → Submodule k M) (S : Submodule k M) (n : ℤ) :
    Submodule k (𝓜 n) := S.comap (𝓜 n).subtype

@[expose] noncomputable def term (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    (q : ℝ) (n : ℤ) : ℝ := (Module.finrank k (piece 𝓜 S n) : ℝ)*q^n

@[expose] noncomputable def value (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    (q : ℝ) : ℝ := ∑' n : ℤ, term 𝓜 S q n

lemma piece_mono (𝓜 : ℤ → Submodule k M) {S T : Submodule k M}
    (h : S ≤ T) (n : ℤ) : piece 𝓜 S n ≤ piece 𝓜 T n :=
  Submodule.comap_mono h

lemma term_nonneg (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    {q : ℝ} (hq : 0 < q) (n : ℤ) : 0 ≤ term 𝓜 S q n := by
  exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos hq _))

lemma term_mono (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q) (n : ℤ) :
    term 𝓜 S q n ≤ term 𝓜 T q n := by
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos hq _))
  exact_mod_cast Submodule.finrank_mono (piece_mono 𝓜 h n)

lemma summable_of_le (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) : Summable (term 𝓜 S q) :=
  Summable.of_nonneg_of_le (term_nonneg 𝓜 S hq) (term_mono 𝓜 h hq) hT

/-- A strict rank defect in one homogeneous piece makes the convergent
Hilbert value strictly smaller. Only inclusion and positivity of the evaluation
parameter are used; neither submodule must itself be homogeneous. -/
theorem value_lt_of_piece_finrank_lt (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M} (h : S ≤ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q)) (n : ℤ)
    (hlt : Module.finrank k (piece 𝓜 S n) < Module.finrank k (piece 𝓜 T n)) :
    value 𝓜 S q < value 𝓜 T q := by
  have hterm : term 𝓜 S q n < term 𝓜 T q n := by
    apply mul_lt_mul_of_pos_right _ (zpow_pos hq n)
    exact_mod_cast hlt
  exact (summable_of_le 𝓜 h hq hT).tsum_lt_tsum (term_mono 𝓜 h hq) hterm hT

/-- Equality at one positive convergent parameter, with actual inclusion,
forces equality of each homogeneous piece. -/
theorem pieces_eq_of_value_eq (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) (hv : value 𝓜 S q = value 𝓜 T q) :
    ∀ n, piece 𝓜 S n = piece 𝓜 T n := by
  intro n
  apply Submodule.eq_of_le_of_finrank_eq (piece_mono 𝓜 h n)
  by_contra hne
  have hlt : Module.finrank k (piece 𝓜 S n) < Module.finrank k (piece 𝓜 T n) :=
    lt_of_le_of_ne (Submodule.finrank_mono (piece_mono 𝓜 h n)) hne
  exact (ne_of_lt (value_lt_of_piece_finrank_lt 𝓜 h hq hT n hlt)) hv

/-- Componentwise inclusion reconstructs T ≤ S when the source submodule T
is homogeneous. This algebraic gluing step needs neither finiteness nor Hilbert
convergence, and makes no homogeneity assumption on the target S. -/
theorem le_of_homogeneous_pieces_le (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    {S T : Submodule k M}
    (hhom : ∀ n m, m ∈ T → (DirectSum.decompose 𝓜 m n : M) ∈ T)
    (hpieces : ∀ n, piece 𝓜 T n ≤ piece 𝓜 S n) : T ≤ S := by
  classical
  intro m hm
  rw [← DirectSum.sum_support_decompose 𝓜 m]
  apply Submodule.sum_mem
  intro n hn
  have hmem : DirectSum.decompose 𝓜 m n ∈ piece 𝓜 T n := hhom n m hm
  exact hpieces n hmem

/-- No assumption on support codimension is involved. Equality of convergent
Hilbert values detects equality with a homogeneous target globally. -/
theorem eq_of_value_eq (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) (hhom : ∀ n m, m ∈ T → (DirectSum.decompose 𝓜 m n : M) ∈ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q))
    (hv : value 𝓜 S q = value 𝓜 T q) : S = T := by
  apply le_antisymm h
  exact le_of_homogeneous_pieces_le 𝓜 hhom (fun n => (pieces_eq_of_value_eq 𝓜 h hq hT hv n).ge)

lemma value_mono (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) : value 𝓜 S q ≤ value 𝓜 T q :=
  (summable_of_le 𝓜 h hq hT).tsum_le_tsum (term_mono 𝓜 h hq) hT

/-- The degree-n piece of the actual quotient T/S. -/
abbrev defectPiece (𝓜 : ℤ → Submodule k M) (S T : Submodule k M) (n : ℤ) :=
  piece 𝓜 T n ⧸ (piece 𝓜 S n).comap (piece 𝓜 T n).subtype

@[expose] noncomputable def defectTerm (𝓜 : ℤ → Submodule k M) (S T : Submodule k M)
    (q : ℝ) (n : ℤ) : ℝ := (Module.finrank k (defectPiece 𝓜 S T n) : ℝ)*q^n

lemma defectTerm_eq_sub (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M} (h : S ≤ T)
    (q : ℝ) (n : ℤ) : defectTerm 𝓜 S T q n = term 𝓜 T q n-term 𝓜 S q n := by
  have heq := ((piece 𝓜 S n).comap (piece 𝓜 T n).subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe (piece_mono 𝓜 h n)).finrank_eq] at heq
  have hc : (Module.finrank k (defectPiece 𝓜 S T n) : ℝ)+
      (Module.finrank k (piece 𝓜 S n) : ℝ) =
        Module.finrank k (piece 𝓜 T n) := by exact_mod_cast heq
  unfold defectTerm term
  rw [←hc]
  ring

/-- Additivity of convergent Hilbert values for the actual degreewise quotient. -/
theorem defect_value_eq_sub (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M} (h : S ≤ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q)) :
    Summable (defectTerm 𝓜 S T q) ∧
      ∑' n, defectTerm 𝓜 S T q n = value 𝓜 T q-value 𝓜 S q := by
  have hf : defectTerm 𝓜 S T q = fun n => term 𝓜 T q n-term 𝓜 S q n :=
    funext (defectTerm_eq_sub 𝓜 h q)
  rw [hf]
  exact ⟨hT.sub (summable_of_le 𝓜 h hq hT),
    hT.tsum_sub (summable_of_le 𝓜 h hq hT)⟩

/-- All proper homogeneous defects have a strictly positive Hilbert series;
there is no exception for support in codimension ≥2 or finite length. -/
theorem defect_value_pos (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) (hne : S ≠ T)
    (hhom : ∀ n m, m ∈ T → (DirectSum.decompose 𝓜 m n : M) ∈ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q)) :
    0 < ∑' n, defectTerm 𝓜 S T q n := by
  rw [(defect_value_eq_sub 𝓜 h hq hT).2]
  apply sub_pos.mpr
  apply lt_of_le_of_ne (value_mono 𝓜 h hq hT)
  intro heq
  exact hne (eq_of_value_eq 𝓜 h hhom hq hT heq)

end KLInvariance.Hilbert
end

end OAI
