/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Routing certificates and layout semantics

A routing trace inserts edge SWAPs and consumes logical gates in source order. Its checker
tracks layouts explicitly and verifies the layout attached to every emitted gate. The algebraic
correctness theorem works in any monoid, in particular in the full complex matrix algebra.
The concrete representation `wireMatrix` permutes computational-basis bit strings.

## Main results

* `checkTrace_sound`: every accepted trace preserves semantics up to its final layout.
* `checkTrace_hardware`: every operation in an accepted trace meets the hardware predicate.
* `wireMatrix_mulVec`: the matrix representation transports computational-basis coordinates.
* `boundedRoute_checked`: finite heuristic prefixes followed by path fallback are accepted.
* `boundedRoute_swapCount`: at most `m₂ (B + N - 2)` SWAPs are emitted.

The supplied gate semantics must interpret its ordered wire annotations correctly; the theorem
establishes routing independently of any search heuristic.
-/

@[expose] public section

namespace Giallar.Routing

open Equiv

variable {W : Type*}

/-- Push a computational-basis bit string along a wire permutation. -/
def wireBits : Perm W →* Perm (W → Bool) where
  toFun p :=
    { toFun := fun x i => x (p.symm i)
      invFun := fun x i => x (p i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  map_one' := by ext x i; rfl
  map_mul' p q := by ext x i; rfl

@[simp]
theorem wireBits_apply (p : Perm W) (x : W → Bool) (i : W) :
    wireBits p x (p i) = x i := by
  simp [wireBits]

variable [Fintype W] [DecidableEq W]

/-- The full complex matrix representation of wire layouts on computational-basis states. -/
noncomputable def wireMatrix : Perm W →* Matrix (W → Bool) (W → Bool) ℂ :=
  (Matrix.permMatrixHom (R := ℂ)).comp wireBits

/-- Matrix multiplication by a layout is exactly pushforward of basis amplitudes. -/
theorem wireMatrix_mulVec (p : Perm W) (v : (W → Bool) → ℂ) :
    (wireMatrix p).mulVec v = v ∘ (wireBits p).symm := by
  change (((wireBits p)⁻¹).permMatrix ℂ).mulVec v = v ∘ (wireBits p).symm
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- The inverse layout matrix is the conjugate transpose of the forward layout matrix. -/
theorem wireMatrix_conjTranspose (p : Perm W) :
    (wireMatrix p).conjTranspose = wireMatrix p⁻¹ := by
  change (((wireBits p)⁻¹).permMatrix ℂ).conjTranspose =
    ((wireBits p⁻¹)⁻¹).permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  simp

/-- Concrete layout matrices satisfy both unitary identities. -/
theorem wireMatrix_unitary (p : Perm W) :
    (wireMatrix p).conjTranspose * wireMatrix p = 1 ∧
      wireMatrix p * (wireMatrix p).conjTranspose = 1 := by
  rw [wireMatrix_conjTranspose]
  constructor <;> rw [← map_mul] <;> simp

section Algebra

variable {M Gate : Type*} [Monoid M]
variable (repr : Perm W →* M) (denote : Gate → M)

/-- Evaluate a chronologically ordered list; the first operation is the rightmost factor. -/
def eval : List M → M
  | [] => 1
  | x :: xs => eval xs * x

@[simp]
theorem eval_nil : eval ([] : List M) = 1 := rfl

@[simp]
theorem eval_cons (x : M) (xs : List M) : eval (x :: xs) = eval xs * x := rfl

@[simp]
theorem eval_append (xs ys : List M) : eval (xs ++ ys) = eval ys * eval xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

/-- A physical routing action. The layout on an emitted gate is part of the certificate. -/
inductive Action (W Gate : Type*) where
  /-- Insert an undirected edge SWAP. -/
  | swap (a b : W)
  /-- Emit the next source gate using the recorded layout. -/
  | emit (layout : Perm W) (gate : Gate)

/-- Operator denoted by a physical routing action. -/
def actionSem : Action W Gate → M
  | .swap a b => repr (Equiv.swap a b)
  | .emit p g => repr p * denote g * repr p⁻¹

/-- Hardware availability of one action. Source-gate availability includes direction and arity. -/
def Legal (adj : W → W → Prop) (available : Perm W → Gate → Prop) :
    Action W Gate → Prop
  | .swap a b => adj a b
  | .emit p g => available p g

/-- Run the finite routing checker, returning the final layout after consuming all source gates.
The layout and gate equality checks also ensure that the returned trace is the one evaluated. -/
def checkTrace [DecidableEq Gate] (adj : W → W → Prop) [DecidableRel adj]
    (available : Perm W → Gate → Prop) [∀ p g, Decidable (available p g)] :
    List Gate → Perm W → List (Action W Gate) → Option (Perm W)
  | [], p, [] => some p
  | _ :: _, _, [] => none
  | src, p, .swap a b :: rest =>
    if adj a b then checkTrace adj available src (Equiv.swap a b * p) rest else none
  | [], _, .emit _ _ :: _ => none
  | g :: src, p, .emit q h :: rest =>
    if q = p ∧ h = g ∧ available p g then checkTrace adj available src p rest else none

/-- The physical semantics of every accepted routing trace equals the logical source semantics,
with the initial and final layouts retained explicitly. -/
theorem checkTrace_sound [DecidableEq Gate]
    (adj : W → W → Prop) [DecidableRel adj]
    (available : Perm W → Gate → Prop) [∀ p g, Decidable (available p g)]
    (src : List Gate) (p q : Perm W) (trace : List (Action W Gate))
    (h : checkTrace adj available src p trace = some q) :
    eval (trace.map (actionSem repr denote)) * repr p =
      repr q * eval (src.map denote) := by
  induction trace generalizing src p with
  | nil =>
    cases src with
    | nil =>
      simp only [checkTrace, Option.some.injEq] at h
      subst q
      simp
    | cons g src => simp [checkTrace] at h
  | cons act rest ih =>
    cases act with
    | swap a b =>
      simp only [checkTrace] at h
      split at h
      next ha =>
        have hr := ih src (Equiv.swap a b * p) h
        simpa [actionSem, map_mul, mul_assoc] using hr
      next ha => contradiction
    | emit r g =>
      cases src with
      | nil => simp [checkTrace] at h
      | cons s src =>
        simp only [checkTrace] at h
        split at h
        next hh =>
          obtain ⟨hr, hg, hav⟩ := hh
          subst r
          subst g
          have hc : repr p⁻¹ * repr p = 1 := by rw [← map_mul]; simp
          simpa [actionSem, mul_assoc, hc] using
            congrArg (fun z => z * denote s) (ih src p h)
        next hh => contradiction

/-- The same checker validates the hardware constraint for every action in the returned trace. -/
theorem checkTrace_hardware [DecidableEq Gate]
    (adj : W → W → Prop) [DecidableRel adj]
    (available : Perm W → Gate → Prop) [∀ p g, Decidable (available p g)]
    (src : List Gate) (p q : Perm W) (trace : List (Action W Gate))
    (h : checkTrace adj available src p trace = some q) :
    ∀ a ∈ trace, Legal adj available a := by
  induction trace generalizing src p with
  | nil => simp
  | cons act rest ih =>
    cases act with
    | swap a b =>
      simp only [checkTrace] at h
      split at h
      next ha =>
        have hr := ih src (Equiv.swap a b * p) h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hr x hx
      next ha => contradiction
    | emit r g =>
      cases src with
      | nil => simp [checkTrace] at h
      | cons s src =>
        simp only [checkTrace] at h
        split at h
        next hh =>
          obtain ⟨hr, hg, hav⟩ := hh
          subst r
          subst g
          have hr := ih src p h
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hav
          · exact hr x hx
        next hh => contradiction

end Algebra

end Giallar.Routing

namespace Giallar.Routing

open Equiv SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}

/-- Swap along a walk except for its last edge, leaving the other target at the endpoint. -/
def fallbackSwaps : {a b : W} → G.Walk a b → List (W × W)
  | _, _, .nil => []
  | _, _, .cons _ .nil => []
  | a, _, .cons (v := c) _ (.cons h p) => (a, c) :: fallbackSwaps (.cons h p)

/-- The wire permutation produced by a chronological list of physical SWAPs. -/
def swapLayout (swaps : List (W × W)) : Perm W :=
  eval (swaps.map fun e => Equiv.swap e.1 e.2)

omit [Fintype W] in
@[simp]
theorem swapLayout_nil : swapLayout ([] : List (W × W)) = 1 := rfl

omit [Fintype W] in
@[simp]
theorem swapLayout_cons (a b : W) (swaps : List (W × W)) :
    swapLayout ((a, b) :: swaps) = swapLayout swaps * Equiv.swap a b := rfl

omit [Fintype W] [DecidableEq W] in
/-- Fallback emits exactly one fewer SWAP than the walk has edges. -/
theorem fallbackSwaps_length {a b : W} (p : G.Walk a b) :
    (fallbackSwaps p).length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    cases p with
    | nil => rfl
    | cons h' p => simpa [fallbackSwaps] using congrArg Nat.succ ih

omit [Fintype W] [DecidableEq W] in
/-- Every fallback SWAP is an actual hardware edge. -/
theorem fallbackSwaps_adj {a b : W} (p : G.Walk a b) :
    ∀ e ∈ fallbackSwaps p, G.Adj e.1 e.2 := by
  induction p with
  | nil => simp [fallbackSwaps]
  | cons h p ih =>
    cases p with
    | nil => simp [fallbackSwaps]
    | cons h' p =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h
      · exact ih e he

omit [Fintype W] [DecidableEq W] in
/-- A nonempty simple path has distinct endpoints. -/
theorem path_start_ne_end {a b : W} {p : G.Walk a b} (hp : p.IsPath)
    (hlen : 0 < p.length) : a ≠ b := by
  intro h
  have hn : p.Nil := hp.nil_iff_eq.mpr h
  have hz := hn.length_eq_zero
  omega

omit [Fintype W] in
/-- Along a simple path fallback fixes the second target and moves the first next to it. -/
theorem fallbackSwaps_spec {a b : W} (p : G.Walk a b) (hp : p.IsPath) :
    swapLayout (fallbackSwaps p) b = b ∧
      (a ≠ b → G.Adj (swapLayout (fallbackSwaps p) a) b) := by
  induction p with
  | nil => simp [fallbackSwaps]
  | @cons a c b h p ih =>
    cases p with
    | nil =>
      simp only [fallbackSwaps, swapLayout_nil, Equiv.Perm.one_apply]
      exact ⟨trivial, fun _ => h⟩
    | @cons c d b h' p =>
      have htail := hp.of_cons
      have hcb : c ≠ b := path_start_ne_end htail (by simp)
      have hab : a ≠ b := path_start_ne_end hp (by simp)
      obtain ⟨hfix, hadj⟩ := ih htail
      have hswap : Equiv.swap a c b = b :=
        Equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm
      constructor
      · simpa [fallbackSwaps, Equiv.Perm.mul_apply, hswap] using hfix
      · intro _
        simpa [fallbackSwaps, Equiv.Perm.mul_apply] using hadj hcb

/-- On a finite connected device a fallback certificate always exists, uses only edges,
fixes the second target, and uses at most `N - 2` SWAPs. -/
theorem exists_fallback (hG : G.Connected) (a b : W) (hab : a ≠ b) :
    ∃ swaps : List (W × W),
      (∀ e ∈ swaps, G.Adj e.1 e.2) ∧
      swapLayout swaps b = b ∧ G.Adj (swapLayout swaps a) b ∧
      swaps.length ≤ Fintype.card W - 2 := by
  obtain ⟨p, hp⟩ := hG.exists_isPath a b
  refine ⟨fallbackSwaps p, fallbackSwaps_adj p, ?_⟩
  obtain ⟨hfix, hadj⟩ := fallbackSwaps_spec p hp
  refine ⟨hfix, hadj hab, ?_⟩
  have hlen := hp.length_lt
  rw [fallbackSwaps_length]
  omega

/-- A bounded heuristic heuristic followed by fallback retains an explicit finite cost bound. -/
theorem heuristic_fallback_length (hG : G.Connected) (heuristic : List (W × W))
    (budget : ℕ) (hbudget : heuristic.length ≤ budget) (a b : W) (hab : a ≠ b) :
    ∃ fallback : List (W × W),
      (∀ e ∈ fallback, G.Adj e.1 e.2) ∧
      G.Adj (swapLayout fallback (swapLayout heuristic a))
        (swapLayout heuristic b) ∧
      (heuristic ++ fallback).length ≤ budget + Fintype.card W - 2 := by
  have hne : swapLayout heuristic a ≠ swapLayout heuristic b :=
    (swapLayout heuristic).injective.ne hab
  obtain ⟨swaps, hedges, hfix, hadj, hlen⟩ :=
    exists_fallback hG (swapLayout heuristic a) (swapLayout heuristic b) hne
  refine ⟨swaps, hedges, hadj, ?_⟩
  have hcard : 2 ≤ Fintype.card W :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  simp only [List.length_append]
  omega

end Giallar.Routing

namespace Giallar.Routing

open Equiv

variable {W Gate : Type*} [Fintype W] [DecidableEq W]

/-- Ordered wire annotations for a one- or two-qubit primitive. -/
structure Support (W : Type*) where
  /-- The first wire, also used for one-qubit gates. -/
  first : W
  /-- The optional second wire. -/
  second : Option W
  /-- A two-qubit gate has distinct wires. -/
  distinct : ∀ b, second = some b → first ≠ b

/-- Graph availability for the ordered support. On an undirected architecture the local
primitive is assumed implementable in either direction of every edge. -/
def Available (G : SimpleGraph W) (support : Gate → Support W) (p : Perm W) (g : Gate) :
    Prop :=
  match (support g).second with
  | none => True
  | some b => G.Adj (p (support g).first) (p b)

instance availableDecidable (G : SimpleGraph W) [DecidableRel G.Adj]
    (support : Gate → Support W) (p : Perm W) (g : Gate) :
    Decidable (Available G support p g) := by
  unfold Available
  cases (support g).second <;> infer_instance

/-- On a connected architecture each annotated primitive admits an edge-SWAP heuristic
that makes it available, without changing the other target. -/
theorem exists_gate_fallback (G : SimpleGraph W) (hG : G.Connected)
    (support : Gate → Support W) (p : Perm W) (g : Gate) :
    ∃ swaps : List (W × W),
      (∀ e ∈ swaps, G.Adj e.1 e.2) ∧
      Available G support (swapLayout swaps * p) g ∧
      swaps.length ≤ if (support g).second.isSome then Fintype.card W - 2 else 0 := by
  cases hs : (support g).second with
  | none =>
    refine ⟨[], by simp, ?_, by simp⟩
    simp [Available, hs]
  | some b =>
    have hne := (p.injective.ne ((support g).distinct b hs))
    obtain ⟨swaps, hedge, hfix, hadj, hlen⟩ :=
      exists_fallback hG (p (support g).first) (p b) hne
    refine ⟨swaps, hedge, ?_, by simpa [hs] using hlen⟩
    simpa [Available, hs, Equiv.Perm.mul_apply, hfix] using hadj

section Checker

variable [DecidableEq Gate]
variable (G : SimpleGraph W) [DecidableRel G.Adj] (support : Gate → Support W)

/-- Turn physical SWAP pairs into routing actions. -/
def swapActions (swaps : List (W × W)) : List (Action W Gate) :=
  swaps.map fun e => Action.swap e.1 e.2

/-- Prefixing a trace by legal SWAPs updates exactly its initial layout. -/
theorem checkTrace_swapActions (src : List Gate) (p : Perm W)
    (swaps : List (W × W)) (rest : List (Action W Gate))
    (hedges : ∀ e ∈ swaps, G.Adj e.1 e.2) :
    checkTrace G.Adj (Available G support) src p (swapActions swaps ++ rest) =
      checkTrace G.Adj (Available G support) src (swapLayout swaps * p) rest := by
  induction swaps generalizing p with
  | nil => simp [swapActions]
  | cons e swaps ih =>
    rcases e with ⟨a, b⟩
    have ha := hedges (a, b) (by simp)
    have ht : ∀ e ∈ swaps, G.Adj e.1 e.2 := by
      intro e he
      exact hedges e (by simp [he])
    simpa [swapActions, checkTrace, ha, mul_assoc] using
      ih (Equiv.swap a b * p) ht

/-- The selected finite fallback SWAP list. Its existence comes from a simple graph path. -/
noncomputable def gateFallback (hG : G.Connected) (p : Perm W) (g : Gate) :
    List (W × W) :=
  Classical.choose (exists_gate_fallback G hG support p g)

omit [DecidableEq Gate] [DecidableRel G.Adj] in
/-- Properties of the selected fallback SWAP list. -/
theorem gateFallback_spec (hG : G.Connected) (p : Perm W) (g : Gate) :
    (∀ e ∈ gateFallback G support hG p g, G.Adj e.1 e.2) ∧
      Available G support (swapLayout (gateFallback G support hG p g) * p) g ∧
      (gateFallback G support hG p g).length ≤
        if (support g).second.isSome then Fintype.card W - 2 else 0 :=
  Classical.choose_spec (exists_gate_fallback G hG support p g)

/-- Route every primitive using a finite fallback SWAP list and then consume it. Recursion is on
source length, so there is no unbounded search loop in this semantic reference compiler. -/
noncomputable def routeCircuit (hG : G.Connected) :
    List Gate → Perm W → List (Action W Gate) × Perm W
  | [], p => ([], p)
  | g :: src, p =>
    let swaps := gateFallback G support hG p g
    let q := swapLayout swaps * p
    let result := routeCircuit hG src q
    (swapActions swaps ++ .emit q g :: result.1, result.2)

/-- Every trace produced by the terminating fallback compiler is accepted by the checker. -/
theorem routeCircuit_checked (hG : G.Connected) (src : List Gate) (p : Perm W) :
    checkTrace G.Adj (Available G support) src p (routeCircuit G support hG src p).1 =
      some (routeCircuit G support hG src p).2 := by
  induction src generalizing p with
  | nil => rfl
  | cons g src ih =>
    obtain ⟨hedges, havail, hlen⟩ := gateFallback_spec G support hG p g
    simp only [routeCircuit]
    rw [checkTrace_swapActions G support _ _ _ _ hedges]
    simpa [checkTrace, havail] using
      ih (swapLayout (gateFallback G support hG p g) * p)

omit [DecidableEq Gate] [DecidableRel G.Adj] in
/-- End-to-end semantic correctness of the terminating reference router. -/
theorem routeCircuit_sound {M : Type*} [Monoid M] (repr : Perm W →* M)
    (denote : Gate → M) (hG : G.Connected) (src : List Gate) (p : Perm W) :
    eval ((routeCircuit G support hG src p).1.map (actionSem repr denote)) * repr p =
      repr (routeCircuit G support hG src p).2 * eval (src.map denote) := by
  classical
  exact checkTrace_sound repr denote G.Adj (Available G support) _ _ _ _
    (routeCircuit_checked G support hG src p)

omit [DecidableEq Gate] [DecidableRel G.Adj] in
/-- Every physical operation emitted by the reference router meets the graph constraint. -/
theorem routeCircuit_hardware (hG : G.Connected) (src : List Gate) (p : Perm W) :
    ∀ a ∈ (routeCircuit G support hG src p).1, Legal G.Adj (Available G support) a := by
  classical
  exact checkTrace_hardware G.Adj (Available G support) _ _ _ _
    (routeCircuit_checked G support hG src p)

/-- Number of physical SWAP actions in a trace. -/
def swapCount (trace : List (Action W Gate)) : ℕ :=
  (trace.filter fun a => match a with | .swap _ _ => true | .emit _ _ => false).length

omit [Fintype W] [DecidableEq W] [DecidableEq Gate] in
@[simp]
theorem swapCount_append (xs ys : List (Action W Gate)) :
    swapCount (xs ++ ys) = swapCount xs + swapCount ys := by
  simp [swapCount, List.filter_append]

omit [Fintype W] [DecidableEq W] [DecidableEq Gate] in
@[simp]
theorem swapCount_swapActions (xs : List (W × W)) :
    swapCount (swapActions (Gate := Gate) xs) = xs.length := by
  simp [swapCount, swapActions, List.filter_map, Function.comp_def]

omit [Fintype W] [DecidableEq W] [DecidableEq Gate] in
@[simp]
theorem swapCount_emit_cons (p : Perm W) (g : Gate) (xs : List (Action W Gate)) :
    swapCount (.emit p g :: xs) = swapCount xs := rfl

/-- Number of two-qubit source gates. -/
def twoQubitCount (support : Gate → Support W) (src : List Gate) : ℕ :=
  (src.filter fun g => (support g).second.isSome).length

omit [DecidableEq Gate] [DecidableRel G.Adj] in
/-- The fallback compiler uses at most `m₂ (N - 2)` SWAPs. -/
theorem routeCircuit_swapCount (hG : G.Connected) (src : List Gate) (p : Perm W) :
    swapCount (routeCircuit G support hG src p).1 ≤
      twoQubitCount support src * (Fintype.card W - 2) := by
  induction src generalizing p with
  | nil => simp [routeCircuit, swapCount, twoQubitCount]
  | cons g src ih =>
    obtain ⟨hedges, havail, hlen⟩ := gateFallback_spec G support hG p g
    have hi := ih (swapLayout (gateFallback G support hG p g) * p)
    cases hs : (support g).second with
    | none =>
      have he : (gateFallback G support hG p g).length = 0 :=
        Nat.eq_zero_of_le_zero (by simpa [hs] using hlen)
      simpa [routeCircuit, twoQubitCount, hs, he] using hi
    | some b =>
      have he : (gateFallback G support hG p g).length ≤ Fintype.card W - 2 :=
        by simpa [hs] using hlen
      simpa [routeCircuit, twoQubitCount, hs, Nat.add_mul, Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add he hi

end Checker

end Giallar.Routing

namespace Giallar.Routing

open Equiv

variable {W Gate : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] in
/-- Concatenating SWAP lists composes their layouts in chronological order. -/
theorem swapLayout_append (xs ys : List (W × W)) :
    swapLayout (xs ++ ys) = swapLayout ys * swapLayout xs := by
  simp [swapLayout, List.map_append]

/-- A source-recursive router parameterized by a finite per-gate SWAP plan. -/
def routePlan (plan : Perm W → Gate → List (W × W)) :
    List Gate → Perm W → List (Action W Gate) × Perm W
  | [], p => ([], p)
  | g :: src, p =>
    let swaps := plan p g
    let q := swapLayout swaps * p
    let result := routePlan plan src q
    (swapActions swaps ++ .emit q g :: result.1, result.2)

/-- Any per-gate plan consisting of legal edges and ending with an available gate is accepted.
The recursion consumes a source gate at every step, independently of the planning heuristic. -/
theorem routePlan_checked [DecidableEq Gate] (G : SimpleGraph W) [DecidableRel G.Adj]
    (support : Gate → Support W) (plan : Perm W → Gate → List (W × W))
    (hplan : ∀ p g, (∀ e ∈ plan p g, G.Adj e.1 e.2) ∧
      Available G support (swapLayout (plan p g) * p) g)
    (src : List Gate) (p : Perm W) :
    checkTrace G.Adj (Available G support) src p (routePlan plan src p).1 =
      some (routePlan plan src p).2 := by
  induction src generalizing p with
  | nil => rfl
  | cons g src ih =>
    obtain ⟨hedges, havail⟩ := hplan p g
    simp only [routePlan]
    rw [checkTrace_swapActions G support _ _ _ _ hedges]
    simpa [checkTrace, havail] using ih (swapLayout (plan p g) * p)

omit [Fintype W] in
/-- A local per-gate budget gives a total SWAP budget proportional to the two-qubit gate count. -/
theorem routePlan_swapCount (support : Gate → Support W)
    (plan : Perm W → Gate → List (W × W)) (bound : ℕ)
    (hbound : ∀ p g, (plan p g).length ≤ if (support g).second.isSome then bound else 0)
    (src : List Gate) (p : Perm W) :
    swapCount (routePlan plan src p).1 ≤ twoQubitCount support src * bound := by
  induction src generalizing p with
  | nil => simp [routePlan, swapCount, twoQubitCount]
  | cons g src ih =>
    have hlen := hbound p g
    have hi := ih (swapLayout (plan p g) * p)
    cases hs : (support g).second with
    | none =>
      have he : (plan p g).length = 0 := Nat.eq_zero_of_le_zero (by simpa [hs] using hlen)
      simpa [routePlan, twoQubitCount, hs, he] using hi
    | some b =>
      have he : (plan p g).length ≤ bound := by simpa [hs] using hlen
      simpa [routePlan, twoQubitCount, hs, Nat.succ_mul, Nat.add_mul, Nat.add_comm] using
        Nat.add_le_add he hi

variable (G : SimpleGraph W) (support : Gate → Support W)

/-- A bounded heuristic SWAP prefix followed by a guaranteed finite path fallback.
One-qubit gates need no planning. -/
noncomputable def boundedPlan (hG : G.Connected)
    (heuristic : Perm W → Gate → List (W × W)) (p : Perm W) (g : Gate) :
    List (W × W) :=
  if (support g).second.isSome then
    heuristic p g ++ gateFallback G support hG (swapLayout (heuristic p g) * p) g
  else []

/-- The bounded plan discharges every local routing obligation and its `B + N - 2` cost bound. -/
theorem boundedPlan_spec (hG : G.Connected)
    (heuristic : Perm W → Gate → List (W × W)) (budget : ℕ)
    (hlegal : ∀ p g e, e ∈ heuristic p g → G.Adj e.1 e.2)
    (hbudget : ∀ p g, (heuristic p g).length ≤ budget) (p : Perm W) (g : Gate) :
    (∀ e ∈ boundedPlan G support hG heuristic p g, G.Adj e.1 e.2) ∧
      Available G support (swapLayout (boundedPlan G support hG heuristic p g) * p) g ∧
      (boundedPlan G support hG heuristic p g).length ≤
        if (support g).second.isSome then budget + Fintype.card W - 2 else 0 := by
  cases hs : (support g).second with
  | none =>
    simp [boundedPlan, hs, Available]
  | some b =>
    obtain ⟨hedges, havail, hlen⟩ :=
      gateFallback_spec G support hG (swapLayout (heuristic p g) * p) g
    have hc : 2 ≤ Fintype.card W :=
      Fintype.one_lt_card_iff.mpr ⟨(support g).first, b, (support g).distinct b hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      simp only [boundedPlan, hs, Option.isSome_some, ↓reduceIte, List.mem_append] at he
      exact he.elim (hlegal p g e) (hedges e)
    · simpa [boundedPlan, hs, swapLayout_append, mul_assoc] using havail
    · have hb := hbudget p g
      simp only [boundedPlan, hs, Option.isSome_some, ↓reduceIte, List.length_append] at *
      omega

/-- The bounded-heuristic router is accepted by the semantic and hardware checker. -/
theorem boundedRoute_checked [DecidableEq Gate] [DecidableRel G.Adj]
    (hG : G.Connected) (heuristic : Perm W → Gate → List (W × W)) (budget : ℕ)
    (hlegal : ∀ p g e, e ∈ heuristic p g → G.Adj e.1 e.2)
    (hbudget : ∀ p g, (heuristic p g).length ≤ budget) (src : List Gate) (p : Perm W) :
    checkTrace G.Adj (Available G support) src p
        (routePlan (boundedPlan G support hG heuristic) src p).1 =
      some (routePlan (boundedPlan G support hG heuristic) src p).2 := by
  apply routePlan_checked
  intro q g
  exact (boundedPlan_spec G support hG heuristic budget hlegal hbudget q g).imp_right
    (fun h => h.1)

/-- Complete finite cost bound for the bounded-heuristic router. -/
theorem boundedRoute_swapCount (hG : G.Connected)
    (heuristic : Perm W → Gate → List (W × W)) (budget : ℕ)
    (hlegal : ∀ p g e, e ∈ heuristic p g → G.Adj e.1 e.2)
    (hbudget : ∀ p g, (heuristic p g).length ≤ budget) (src : List Gate) (p : Perm W) :
    swapCount (routePlan (boundedPlan G support hG heuristic) src p).1 ≤
      twoQubitCount support src * (budget + Fintype.card W - 2) := by
  apply routePlan_swapCount
  intro q g
  exact (boundedPlan_spec G support hG heuristic budget hlegal hbudget q g).2.2

end Giallar.Routing
