module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder
public import ForMathlib.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder

public section

/-! Semantic home: ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall. Source spans: ReflectionOrders:8, ReflectionOrders:9.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
open scoped Topology
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.WallDyer.instDecidable_oAI (p : Prop) : Decidable p := Classical.propDecidable p

@[expose] def rootValue (f : Module.Dual ℝ (I → ℝ)) (e : Edge cs) : ℝ :=
  f (normalizedRoot (rootLabel cs e))

@[expose] def rootPlaneTies (f : Module.Dual ℝ (I → ℝ)) : Prop :=
  ∀ a b : PositiveRoot M cs, a ≠ b → f (normalizedRoot a)=f (normalizedRoot b) →
    ∀ c : PositiveRoot M cs, f (normalizedRoot c)=f (normalizedRoot a) ↔
      c.val ∈ rootPlane a b

@[expose] def schedule (f : Module.Dual ℝ (I → ℝ)) (b : W) : List (Edge cs) :=
  sortedSchedule (edgeFinset cs b) (lexEdgeScore f)

@[expose] def entry {R : Type*} [Semiring R] (T : R) (f : Module.Dual ℝ (I → ℝ))
    (b x y : W) : R :=
  dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) (schedule f b) x

/-- The complete tied block at any genuine simple wall has an actual
operator independent of the linear tie-breaking functional. -/
theorem block_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (a : ℝ) (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g) a) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h) a) x := by
  let F := (edgeFinset cs b).filter (fun e => rootValue f e=a)
  let p := sortedSchedule F (lexEdgeScore g)
  let q := sortedSchedule F (lexEdgeScore h)
  let r := sortedSchedule F (fun e => geometricSlope (rootLabel cs e))
  change dispatch (source cs) (target cs) T _ p x = dispatch (source cs) (target cs) T _ q x
  have hmem (k : Edge cs) : k ∈ F ↔ BruhatLE cs (target cs k) b ∧ rootValue f k=a := by
    simp only [F,Finset.mem_filter,mem_edgeFinset]
  by_cases hex : ∃ e ∈ F, ∃ e' ∈ F, rootLabel cs e ≠ rootLabel cs e'
  · obtain ⟨e,he,e',he',hne⟩ := hex
    obtain ⟨B⟩ := nonempty_planeBasis (rootLabel cs e) (rootLabel cs e') hne
    have hv := hf (rootLabel cs e) (rootLabel cs e') hne
      (((hmem e).mp he).2.trans ((hmem e').mp he').2.symm)
    have hfull (k : Edge cs) : k ∈ F ↔
        (rootLabel cs k).val ∈ rootPlane (rootLabel cs e) (rootLabel cs e') ∧
        BruhatLE cs (target cs k) b := by
      rw [hmem,← hv,show f (normalizedRoot (rootLabel cs e))=a from ((hmem e).mp he).2]
      exact and_comm
    have hp := B.dispatch_plane_functional T b g p r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    have hq := B.dispatch_plane_functional T b h q r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    exact hp.trans hq.symm
  · have heq (e : Edge cs) (he : e ∈ F) (e' : Edge cs) (he' : e' ∈ F) :
        rootLabel cs e=rootLabel cs e' := by
      by_contra hn
      exact hex ⟨e,he,e',he',hn⟩
    let L : Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
    have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
      intro e e' he hj
      exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
    have hs (s : Module.Dual ℝ (I → ℝ)) :
        (sortedSchedule F (lexEdgeScore s)).Pairwise (fun e e' => L e' ≤ L e) := by
      apply (sortedSchedule_pairwise F (lexEdgeScore s)).imp_of_mem
      intro e e' he he' _
      have hr := heq e ((mem_sortedSchedule _ _ _).mp he) e' ((mem_sortedSchedule _ _ _).mp he')
      exact (congrArg geometricSlope hr).symm.le
    exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties p q
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _) (hs g) (hs h)
      (fun e => (mem_sortedSchedule _ _ e).trans (mem_sortedSchedule _ _ e).symm) x y

/-- All blocks may be replaced simultaneously on the finite lower region. -/
theorem grouped_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (x y : W) (hx : BruhatLE cs x b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore h)) x := by
  let K := lowerFinset cs b
  have ht (s : Module.Dual ℝ (I → ℝ)) (a : ℝ) (e : Edge cs)
      (he : e ∈ scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore s) a) :
      target cs e ∈ K := by
    exact (mem_lowerFinset cs b _).mpr ((mem_edgeFinset cs b e).mp
      ((mem_scheduleBlock _ _ _ _ _).mp he).1)
  apply dispatch_flatMap_eq_on (source cs) (target cs) T (K : Set W)
    (blockValues (edgeFinset cs b) (rootValue f))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h))
    (fun a _ e he => ht g a e he) _ _ x ((mem_lowerFinset cs b x).mpr hx)
  intro a _ v z hz
  apply dispatch_eq_of_entries_on (source cs) (target cs) T K _ _ (ht g a) (ht h a) _ v z hz
  intro l _ k hk
  exact block_entry_independent T b f hf g h a l k ((mem_lowerFinset cs b k).mp hk)

/-- Stable strict primary comparisons identify the genuine sorted schedule
with the corresponding product of tied blocks. -/
theorem entry_eq_grouped {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (h : ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue f e' < rootValue f e → rootValue g e' < rootValue g e)
    (x y : W) :
    entry (cs := cs) T g b x y =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x := by
  apply dispatch_entries_eq_of_sorted (source cs) (target cs) T (lexEdgeScore g)
    (lexEdgeScore_ties g) _ _ (sortedSchedule_nodup _ _) (groupedSchedule_nodup _ _ _)
    (sortedSchedule_pairwise _ _)
  · apply groupedSchedule_pairwise
    intro e he e' he' hlt
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (h e he e' he' hlt))
  · intro e
    simp only [mem_sortedSchedule,mem_groupedSchedule]

theorem pencil_strict_stable (b : W) (f g : Module.Dual ℝ (I → ℝ)) (t₀ : ℝ) :
    ∀ᶠ t in 𝓝 t₀, ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e →
        rootValue (pencil f g t) e' < rootValue (pencil f g t) e := by
  apply (Filter.eventually_all_finset _).mpr
  intro e _
  apply (Filter.eventually_all_finset _).mpr
  intro e' _
  have hc (k : Edge cs) : Continuous (fun t : ℝ => rootValue (pencil f g t) k) := by
    change Continuous (fun t : ℝ => (1-t)*f (normalizedRoot (rootLabel cs k))+
      t*g (normalizedRoot (rootLabel cs k)))
    fun_prop
  by_cases hlt : rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e
  · filter_upwards [(isOpen_lt (hc e') (hc e)).mem_nhds hlt] with t ht
    exact fun _ => ht
  · exact Filter.Eventually.of_forall (fun _ h => (hlt h).elim)

/-- Crossing all actual root-plane walls leaves the full path matrix fixed,
not merely a single adapted endpoint column. -/
theorem locally_constant_pencil {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (x y : W) (hx : BruhatLE cs x b) :
    IsLocallyConstant (fun t : ℝ => entry (cs := cs) T (pencil f g t) b x y) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t₀
  filter_upwards [pencil_strict_stable b f g t₀] with t ht
  have hp : rootPlaneTies (M := M) (cs := cs) (pencil f g t₀) := by
    intro a d had he
    exact pencil_tie_plane f g hf hg t₀ a d had he
  rw [entry_eq_grouped T b (pencil f g t₀) (pencil f g t) ht,
    entry_eq_grouped T b (pencil f g t₀) (pencil f g t₀) (fun _ _ _ _ h => h)]
  exact grouped_entry_independent T b (pencil f g t₀) hp (pencil f g t) (pencil f g t₀) x y hx

/-- Full matrix order independence for genuine finite geometric orders. -/
theorem entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f h : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hh : Function.Injective (fun a : PositiveRoot M cs => h (normalizedRoot a)))
    (x y : W) (hx : BruhatLE cs x b) : entry (cs := cs) T f b x y=entry (cs := cs) T h b x y := by
  obtain ⟨g,_,hfg,hhg⟩ := exists_common_transverse (M := M) (cs := cs) f h
  have he := (locally_constant_pencil T b f g hf hfg x y hx).apply_eq_of_preconnectedSpace 0 1
  have he' := (locally_constant_pencil T b h g hh hhg x y hx).apply_eq_of_preconnectedSpace 0 1
  simp only [pencil_zero,pencil_one] at he he'
  exact he.trans he'.symm

end
end KLInvariance.WallDyer
end


section
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.WallDyer.instDecidable_oAI_1 (p : Prop) : Decidable p := Classical.propDecidable p

theorem neg_numerator_normalized (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (a : PositiveRoot M cs) :
    (-O.numerator) (normalizedRoot a) = -O.slope a := by
  simp only [LinearMap.neg_apply,dual_normalizedRoot,RatioOrder.slope,hh]

/-- An upper bound larger than the path endpoint creates no extra paths:
every actual directed path stays inside its endpoint interval. -/
theorem subpaths_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    subpaths (source cs) (target cs) (WallDyer.schedule (-O.numerator) b) x y =
      paths O x y := by
  have hscore (e : Edge cs) : rootValue (-O.numerator) e = -score O e :=
    neg_numerator_normalized O hh (rootLabel cs e)
  ext p
  rw [mem_subpaths,mem_paths]
  constructor
  · rintro ⟨hsub,hpath⟩
    refine ⟨hpath,?_⟩
    have hs := (sortedSchedule_pairwise (edgeFinset cs b) (lexEdgeScore (-O.numerator))).sublist hsub
    have hs' : p.Pairwise (fun e e' => score O e ≤ score O e') := by
      apply hs.imp
      intro e e' he
      have hm := Prod.Lex.monotone_fst _ _ he
      change rootValue (-O.numerator) e' ≤ rootValue (-O.numerator) e at hm
      rw [hscore e',hscore e] at hm
      exact neg_le_neg_iff.mp hm
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e e' he => score_ties O e e' he) hpath hs'
  · rintro ⟨hpath,hord⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset (lexEdgeScore (-O.numerator))
    · apply hord.imp
      intro e e' he
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      change rootValue (-O.numerator) e' < rootValue (-O.numerator) e
      rw [hscore e',hscore e]
      exact neg_lt_neg he
    · exact sortedSchedule_pairwise _ _
    · intro e he
      apply (mem_sortedSchedule _ _ _).mpr
      exact (mem_edgeFinset cs b e).mpr ((path_targets_le cs hpath e he).trans hy)

theorem entry_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (-O.numerator) b x y =
      polynomial O x y := by
  unfold entry
  rw [dispatch_eq_subpaths_sum _ _ _ _ (show (WallDyer.schedule (-O.numerator) b).Nodup from sortedSchedule_nodup _ _),
    subpaths_neg_numerator O hh b x y hy]
  rfl


theorem entry_eq_rTilde (f : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) f b x y = Hecke.rTilde cs x y := by
  obtain ⟨O,hO,hh⟩ := exists_ratioOrder_chamber_height (M := M) (cs := cs) y
  have hn : Function.Injective (fun a : PositiveRoot M cs => (-O.numerator) (normalizedRoot a)) := by
    intro a b he
    change (-O.numerator) (normalizedRoot a) = (-O.numerator) (normalizedRoot b) at he
    rw [neg_numerator_normalized O hh a,neg_numerator_normalized O hh b] at he
    exact O.slope_injective (neg_injective he)
  rw [entry_independent (Polynomial.X : Polynomial ℤ) b f (-O.numerator) hf hn x y hx,
    entry_neg_numerator O hh b x y hy,polynomial_eq_rTilde O x y hO]

/-- The manuscript's fixed geometric functional provides such a genuine
full Dyer schedule for every finite lower Bruhat region. -/
theorem geometric_entry_eq_rTilde (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (geometricFunctional (M := M) (cs := cs)) b x y =
      Hecke.rTilde cs x y := by
  apply entry_eq_rTilde _ _ b x y hx hy
  simpa only [geometricFunctional_normalizedRoot] using
    (geometricSlope_injective (M := M) (cs := cs))

end
end KLInvariance.WallDyer
end

end OAI
