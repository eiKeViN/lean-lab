/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FQCExternal.Vendor.Shared

@[expose] public section

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

set_option exponentiation.threshold 256
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Expand a 53-bit compact Stage-1 word into its full `evalWordStage1Fast` word. -/
noncomputable def expandStage1Word (cw : Nat) : Nat :=
  let clast := Nat.land cw (nat_lit 15)
  let lo8 := Nat.lor (Nat.shiftLeft clast (nat_lit 4)) (nat_lit 1)
  let s0 := Nat.land (Nat.shiftRight cw (nat_lit 4)) (nat_lit 3)
  let s14 := spread16 (Nat.land (Nat.shiftRight cw (nat_lit 6)) (nat_lit 15))
  let lo18 := Nat.lor lo8 (Nat.lor (Nat.shiftLeft s0 (nat_lit 8)) (Nat.shiftLeft s14 (nat_lit 10)))
  let idx := Nat.land (Nat.shiftRight cw (nat_lit 10)) (nat_lit 7)
  let ku := Nat.mul idx (nat_lit 3)
  let body := Nat.shiftRight cw (nat_lit 13)
  let maskK := Nat.sub (Nat.shiftLeft (nat_lit 1) ku) (nat_lit 1)
  let mid := Nat.land body maskK
  let tail := Nat.shiftRight body ku
  let smid := Nat.lor (spread16 mid) (Nat.shiftLeft (spread16 (Nat.shiftRight mid (nat_lit 16))) (nat_lit 32))
  let u := Nat.lor smid (Nat.shiftLeft tail (Nat.mul ku (nat_lit 2)))
  Nat.lor lo18 (Nat.shiftLeft u (nat_lit 18))

/-- Evaluate a 53-bit compact Stage-1 word in CPS. -/
noncomputable def evalWordStage1Compact (cw : Nat) (k : (Bool × Box2DS) → Bool) : Bool :=
  forceNatCBV (expandStage1Word cw) (fun wd => evalWordStage1Fast wd k)

/-- Single-check `tCap=26` diagonal leaf check in a 27-word Stage-1 forest. -/
noncomputable def checkS1Diag32 (dict : BTree (BTree (Bool × Box2DS)))
    (wid x0 y0 w sym : Nat) : Bool :=
  forestKWithFast (nat_lit 27) dict wid (fun p =>
    @Prod.rec Bool Box2DS (fun _ => Bool) (fun isLo bx =>
      @Bool.rec (fun _ => Bool) false
        (checkDetBoxForced x0 y0 w (nat_lit 13456) (nat_lit 1000000000000) bx sym)
        isLo) p)

/-- Single parity-indexed Stage-1 leaf entry check in a 27-word forest. -/
noncomputable def checkS1Entry32 (reqPar : Nat) (dict : BTree (BTree (Bool × Box2DS)))
    (x0 y0 w e : Nat) : Bool :=
  let wid := Nat.shiftRight e (nat_lit 3)
  let s := Nat.land e (nat_lit 7)
  forestKWithFast (nat_lit 27) dict wid (fun p =>
    @Prod.rec Bool Box2DS (fun _ => Bool) (fun isLo bx =>
      @Bool.rec (fun _ => Bool) false
        (checkDetBoxForced x0 y0 w (nat_lit 13456) (nat_lit 1000000000000) bx s)
        (@Bool.rec (fun _ => Bool)
          (Nat.beq (Nat.land (Nat.shiftRight s (nat_lit 1)) (nat_lit 1)) reqPar)
          true
          isLo)) p)

/-- Dual-parity Stage-1 leaf check in a 34-word forest. -/
noncomputable def checkS1Dual32 (dict : BTree (BTree (Bool × Box2DS)))
    (x0 y0 w e0 e1 : Nat) : Bool :=
  @Bool.rec (fun _ => Bool) false
    (checkS1Entry32 (nat_lit 1) dict x0 y0 w e1)
    (checkS1Entry32 (nat_lit 0) dict x0 y0 w e0)

/-- Expand a 31-bit inline Stage-1 `Lo` payload with 25 even-only syllables. -/
noncomputable def expandS1Even25 (pay : Nat) : Nat :=
  let clast := Nat.land pay (nat_lit 15)
  let s0 := Nat.land (Nat.shiftRight pay (nat_lit 4)) (nat_lit 3)
  let ev := Nat.shiftRight pay (nat_lit 6)
  let lo10 := Nat.lor (Nat.lor (Nat.shiftLeft clast (nat_lit 4)) (nat_lit 1))
    (Nat.shiftLeft s0 (nat_lit 8))
  let evLo := spread16 (Nat.land ev (nat_lit 0xFFFF))
  let evHi := spread16 (Nat.shiftRight ev (nat_lit 16))
  Nat.lor lo10 (Nat.lor (Nat.shiftLeft evLo (nat_lit 10)) (Nat.shiftLeft evHi (nat_lit 42)))

/-- Expand an inline Stage-1 `Lo` payload with `kEven` leading even-only syllables (`kEven ≤ 16`). -/
noncomputable def expandS1Split (kEven pay : Nat) : Nat :=
  let clast := Nat.land pay (nat_lit 15)
  let s0 := Nat.land (Nat.shiftRight pay (nat_lit 4)) (nat_lit 3)
  let body := Nat.shiftRight pay (nat_lit 6)
  let maskK := Nat.sub (Nat.shiftLeft (nat_lit 1) kEven) (nat_lit 1)
  let ev := spread16 (Nat.land body maskK)
  let rem := Nat.shiftRight body kEven
  let lo10 := Nat.lor (Nat.lor (Nat.shiftLeft clast (nat_lit 4)) (nat_lit 1))
    (Nat.shiftLeft s0 (nat_lit 8))
  Nat.lor lo10 (Nat.lor (Nat.shiftLeft ev (nat_lit 10))
    (Nat.shiftLeft rem (Nat.add (nat_lit 10) (Nat.mul kEven (nat_lit 2)))))

/-- Inline Stage-1 `tCap = 26` word + cell check without dictionary allocation. -/
noncomputable def checkS1InlineLo (wd x0 y0 w sym : Nat) : Bool :=
  evalWordTcBoxFast (nat_lit 26) wd (fun _ bx =>
    checkDetBoxForced x0 y0 w (nat_lit 13456) (nat_lit 1000000000000) bx sym)

/-- Evaluate an inline Stage-1 `Lo` leaf given expanded `wd`, shifted `sNext`, and continuation `k`. -/
noncomputable def evalS1InlineStep (wd x0 y0 w sym sNext : Nat) (bc : BitChain) (nw : Nat)
    (k : Nat → BitChain → Nat → Bool) : Bool :=
  forceNatCBV wd (fun wdVal =>
    @Bool.rec (fun _ => Bool) false
      (forceNatCBV sNext (fun sVal => k sVal bc nw))
      (checkS1InlineLo wdVal x0 y0 w sym))

/-- Evaluate a `BitChain`-backed Stage-1 quadtree stream with inline `Lo` (`39b`/`55b`/`57b`) + dict leaves. -/
noncomputable def evalS1StreamV32K (dict : BTree (BTree (Bool × Box2DS))) :
    Nat → Nat → Nat → Nat → Nat → BitChain → Nat →
      (Nat → BitChain → Nat → Bool) → Bool :=
  @Nat.rec
    (fun _ => Nat → Nat → Nat → Nat → BitChain → Nat →
      (Nat → BitChain → Nat → Bool) → Bool)
    (fun _ _ _ _ _ _ _ => false)
    (fun _ ih x0 y0 w sIn bcIn nw k =>
      withStreamWord sIn bcIn (fun s bc =>
        let low := Nat.land s (nat_lit 0x1FFFFFFFFFFFFFFF)
        let tag := Nat.land low (nat_lit 3)
        @Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool)
            (@Bool.rec (fun _ => Bool)
              false
              (let sub := Nat.land (Nat.shiftRight low (nat_lit 2)) (nat_lit 7)
               @Bool.rec (fun _ => Bool)
                 (@Bool.rec (fun _ => Bool)
                   (@Bool.rec (fun _ => Bool)
                     (@Bool.rec (fun _ => Bool)
                       (@Bool.rec (fun _ => Bool)
                         (@Bool.rec (fun _ => Bool) false
                           (let e0 := Nat.land (Nat.shiftRight low (nat_lit 5)) (nat_lit 0x1FFF)
                            let e1 := Nat.land (Nat.shiftRight low (nat_lit 18)) (nat_lit 0x1FFF)
                            let inc := Nat.land (Nat.shiftRight low (nat_lit 31)) (nat_lit 3)
                            @Bool.rec (fun _ => Bool) false
                              (forceNatCBV (Nat.shiftRight s (nat_lit 33)) (fun sNext =>
                                k sNext bc (Nat.add nw inc)))
                              (checkS1Dual32 dict x0 y0 w e0 e1))
                           (Nat.beq sub (nat_lit 5)))
                         (let e0 := Nat.land (Nat.shiftRight low (nat_lit 5)) (nat_lit 0x1FFF)
                          @Bool.rec (fun _ => Bool) false
                            (forceNatCBV (Nat.shiftRight s (nat_lit 18)) (fun sNext => k sNext bc nw))
                            (checkS1Diag32 dict (Nat.shiftRight e0 (nat_lit 3)) x0 y0 w
                              (Nat.land e0 (nat_lit 7))))
                         (Nat.beq sub (nat_lit 4)))
                       (@Bool.rec (fun _ => Bool) false
                         (forceNatCBV (Nat.shiftRight s (nat_lit 8)) (fun sNext =>
                           k sNext bc (Nat.add nw (nat_lit 1))))
                         (checkS1Diag32 dict nw x0 y0 w
                           (Nat.land (Nat.shiftRight low (nat_lit 5)) (nat_lit 7))))
                       (Nat.beq sub (nat_lit 3)))
                     (evalS1InlineStep
                       (expandS1Split (nat_lit 8)
                         (Nat.land (Nat.shiftRight low (nat_lit 8)) (nat_lit 0x1FFFFFFFFFFFF)))
                       x0 y0 w (Nat.land (Nat.shiftRight low (nat_lit 5)) (nat_lit 7))
                       (Nat.shiftRight s (nat_lit 57)) bc nw k)
                     (Nat.beq sub (nat_lit 2)))
                   (evalS1InlineStep
                     (expandS1Split (nat_lit 10)
                       (Nat.land (Nat.shiftRight low (nat_lit 8)) (nat_lit 0x7FFFFFFFFFFF)))
                     x0 y0 w (Nat.land (Nat.shiftRight low (nat_lit 5)) (nat_lit 7))
                     (Nat.shiftRight s (nat_lit 55)) bc nw k)
                   (Nat.beq sub (nat_lit 1)))
                 (evalS1InlineStep
                   (expandS1Even25
                     (Nat.land (Nat.shiftRight low (nat_lit 8)) (nat_lit 0x7FFFFFFF)))
                   x0 y0 w (Nat.land (Nat.shiftRight low (nat_lit 5)) (nat_lit 7))
                   (Nat.shiftRight s (nat_lit 39)) bc nw k)
                 (Nat.beq sub (nat_lit 0)))
              (Nat.beq tag (nat_lit 3)))
            (@Bool.rec (fun _ => Bool) false
              (@Bool.rec (fun _ => Bool) false
                (forceNatCBV (Nat.shiftRight w (nat_lit 1)) (fun hw =>
                  forceNatCBV (Nat.add x0 hw) (fun xMid =>
                    forceNatCBV (Nat.add y0 hw) (fun yMid =>
                      forceNatCBV (Nat.shiftRight s (nat_lit 2)) (fun s0 =>
                        ih x0 y0 hw s0 bc nw (fun s1 bc1 nw1 =>
                          ih x0 yMid hw s1 bc1 nw1 (fun s2 bc2 nw2 =>
                            ih xMid y0 hw s2 bc2 nw2 (fun s3 bc3 nw3 =>
                              ih xMid yMid hw s3 bc3 nw3 k))))))))
                (Nat.ble (nat_lit 2) w))
              (Nat.beq (Nat.land w (nat_lit 1)) (nat_lit 0)))
            (Nat.beq tag (nat_lit 2)))
          (@Bool.rec (fun _ => Bool) false
            (forceNatCBV (Nat.shiftRight s (nat_lit 2)) (fun sNext => k sNext bc nw))
            (isOutsideDom (nat_lit 1) x0 y0 w (nat_lit 1020100) (nat_lit 100000000)))
          (Nat.beq tag (nat_lit 1))))

/-- Dyadic Stage-1 grid scale `7146825580544 * 2 ^ k`. -/
def w1 : Nat → Nat
  | 0 => 7146825580544
  | k + 1 => 2 * w1 k

/-- Dyadic Stage-1 cell coverage at scale `w1 k` and grid index `(ix, iy)`. -/
def D1 (k ix iy : Nat) : Prop :=
  Stage1SquareCov (ix * w1 k) (iy * w1 k) (w1 k)

theorem d1_o {k ix iy : Nat}
    (h : isOutsideDom 1 (ix * w1 k) (iy * w1 k) (w1 k) 1020100 100000000 = true := by decide) :
    D1 k ix iy := .out h

theorem d1_b {k ix iy : Nat}
    (c00 : D1 k (ix * 2) (iy * 2))
    (c01 : D1 k (ix * 2) (iy * 2 + 1))
    (c10 : D1 k (ix * 2 + 1) (iy * 2))
    (c11 : D1 k (ix * 2 + 1) (iy * 2 + 1)) :
    D1 (k + 1) ix iy := by
  dsimp only [D1, w1]
  have hw : 1 ≤ w1 k := Nat.rec (by decide) (fun _ ih => Nat.le_trans (by decide) (Nat.mul_le_mul_left 2 ih)) k
  have hd : Nat.div (2 * w1 k) 2 = w1 k := Nat.mul_div_right _ (by decide)
  have hm (u : Nat) : u * (2 * w1 k) = u * 2 * w1 k := (Nat.mul_assoc u 2 _).symm
  have ha (u : Nat) : Nat.add (u * (2 * w1 k)) (w1 k) = (u * 2 + 1) * w1 k :=
    (show Nat.add (u * (2 * w1 k)) (w1 k) = u * (2 * w1 k) + w1 k from rfl).trans
      (by rw [hm u, Nat.add_mul, Nat.one_mul])
  exact .branch (Nat.mul_mod_right 2 _) (Nat.mul_le_mul_left 2 hw)
    (by rwa [hd, hm ix, hm iy]) (by rwa [hd, hm ix, ha iy])
    (by rwa [hd, ha ix, hm iy]) (by rwa [hd, ha ix, ha iy])

theorem d1_root (h : D1 6 0 0) : Stage1SquareCov 0 0 457396837154816 := by
  rwa [D1, show 0 * w1 6 = 0 by decide, show w1 6 = 457396837154816 by decide] at h

/-- Conjunction of `D1` over all dyadic cells in a `CellList`. -/
def Stage1BatchCov : CellList → Prop
  | .one k ix iy => D1 k ix iy
  | .more k ix iy rest => D1 k ix iy ∧ Stage1BatchCov rest

/-- Evaluate a `CellList` of dyadic Stage-1 sub-cells over a shared `BitChain` stream. -/
noncomputable def evalS1BatchK (dict : BTree (BTree (Bool × Box2DS))) :
    CellList → Nat → BitChain → Nat → Bool :=
  @CellList.rec (fun _ => Nat → BitChain → Nat → Bool)
    (fun k ix iy s bc nw =>
      forceNatCBV (w1 k) (fun wc =>
        forceNatCBV (ix * wc) (fun x0 =>
          forceNatCBV (iy * wc) (fun y0 =>
            evalS1StreamV32K dict (nat_lit 128) x0 y0 wc s bc nw (fun s' _ _ =>
              Nat.beq s' (nat_lit 1))))))
    (fun k ix iy _ ihr s bc nw =>
      forceNatCBV (w1 k) (fun wc =>
        forceNatCBV (ix * wc) (fun x0 =>
          forceNatCBV (iy * wc) (fun y0 =>
            evalS1StreamV32K dict (nat_lit 128) x0 y0 wc s bc nw (fun s' bc' nw' =>
              ihr s' bc' nw')))))

/-- Decode a 53-bit `27`-word Stage-1 forest and evaluate a `CellList` + `BitChain`. -/
noncomputable def evalS1Batch (b : CellList) (w : BTree Nat) (bc : BitChain) : Bool :=
  decodeWForestKFast (nat_lit 27) (nat_lit 55) (nat_lit 0x1FFFFFFFFFFFFF) evalWordStage1Compact w
    (fun dict => evalS1BatchK dict b (nat_lit 1) bc (nat_lit 0))

theorem evalS1Batch_sound (b : CellList) (w : BTree Nat) (bc : BitChain)
    (h : evalS1Batch b w bc = true) : Stage1BatchCov b := by
  obtain ⟨dict, hdict, hb⟩ := decodeWForestKFast_sound
    (fun h => evalWordStage1Fast_sound (by rwa [evalWordStage1Compact, forceNatCBV_eq] at h)) h
  have hbr {f t c : Bool} : @Bool.rec (fun _ => Bool) f t c = true → t = true ∨ f = true :=
    match c with | false => Or.inr | true => Or.inl
  have hEnt {reqPar x0 y0 w e : Nat} (he : checkS1Entry32 reqPar dict x0 y0 w e = true) :
      ∃ wd bx s, ((isFuseOutWord wd = true ∧ (s / 2) % 2 = reqPar ∧
        checkWord2BitBox 28 wd bx = true) ∨ checkWord2BitBox 26 wd bx = true) ∧
        checkDetBox x0 y0 w 13456 1000000000000 bx s = true := by
    rw [checkS1Entry32] at he
    obtain ⟨⟨isLo, bx⟩, hv, hb0⟩ := forestKWithFast_sound hdict he
    dsimp only at hb0
    generalize Nat.land e (nat_lit 7) = s at hb0
    cases isLo
    · dsimp only at hb0 hv
      simp only [bool_rec_false_eq_and, Bool.and_eq_true, checkDetBoxForced_eq] at hb0
      rw [show Nat.shiftRight s (nat_lit 1) = s / 2 from Nat.shiftRight_eq_div_pow s 1,
        show Nat.land (s / 2) (nat_lit 1) = (s / 2) % 2 from
          Nat.and_two_pow_sub_one_eq_mod (s / 2) 1] at hb0
      exact hv.elim fun wd h => ⟨wd, bx, s, .inl ⟨h.1, Nat.beq_eq.mp hb0.1, h.2⟩, hb0.2⟩
    · exact hv.elim fun wd h => ⟨wd, bx, s, .inr h, by simpa only [checkDetBoxForced_eq] using hb0⟩
  have hInl {wd x0 y0 w sym sNext : Nat} {bc : BitChain} {nw : Nat}
      {k : Nat → BitChain → Nat → Bool}
      (hs : evalS1InlineStep wd x0 y0 w sym sNext bc nw k = true) :
      Stage1SquareCov x0 y0 w ∧ ∃ s' bc' nw', k s' bc' nw' = true := by
    simp only [evalS1InlineStep, checkS1InlineLo, forceNatCBV_eq,
      bool_rec_false_eq_and, Bool.and_eq_true] at hs
    obtain ⟨_, bx, h26, hchk, hdet⟩ := evalWordTcBoxFast_sound hs.1
    exact ⟨.leaf fun _ _ => ⟨wd, bx, sym, .inr (hchk 26 h26),
      by simpa only [checkDetBoxForced_eq] using hdet⟩, sNext, bc, nw, hs.2⟩
  have hStr (fuel : Nat) : ∀ {x0 y0 w s : Nat} {bc : BitChain} {nw : Nat}
      {k : Nat → BitChain → Nat → Bool},
      evalS1StreamV32K dict fuel x0 y0 w s bc nw k = true →
      Stage1SquareCov x0 y0 w ∧ ∃ s' bc' nw', k s' bc' nw' = true := by
    induction fuel with
    | zero => rintro _ _ _ _ _ _ _ ⟨⟩
    | succ _ ih =>
      intro x0 y0 w sIn bcIn nw k hs0
      dsimp only [evalS1StreamV32K] at hs0
      obtain ⟨s, bc, hs⟩ := withStreamWord_sound hs0
      have hdiag {wid sh nw' sym : Nat} (hc : @Bool.rec (fun _ => Bool) false
          (forceNatCBV (Nat.shiftRight s sh) (fun sNext => k sNext bc nw'))
          (checkS1Diag32 dict wid x0 y0 w sym) = true) :
          Stage1SquareCov x0 y0 w ∧ ∃ s' bc' nw'', k s' bc' nw'' = true := by
        simp only [bool_rec_false_eq_and, Bool.and_eq_true, forceNatCBV_eq, checkS1Diag32] at hc
        obtain ⟨⟨isLo, bx⟩, hv, hb0⟩ := forestKWithFast_sound hdict hc.1
        cases isLo
        · cases hb0
        · exact ⟨.leaf fun _ _ => hv.elim fun wd h => ⟨wd, bx, sym, .inr h,
            by simpa only [checkDetBoxForced_eq, Bool.true_and] using hb0⟩, _, bc, _, hc.2⟩
      refine (hbr hs).elim (fun hs => ?_) fun hs => (hbr hs).elim (fun hs => ?_) fun hs =>
        (hbr hs).elim (fun hs => (hbr hs).elim hInl fun hs => (hbr hs).elim hInl fun hs =>
          (hbr hs).elim hInl fun hs => (hbr hs).elim hdiag fun hs => (hbr hs).elim hdiag fun hs =>
            (hbr hs).elim (fun hs => ?_) fun hs => nomatch hs) fun hs => nomatch hs
      · simp only [bool_rec_false_eq_and, Bool.and_eq_true, forceNatCBV_eq] at hs
        exact ⟨.out hs.1, _, bc, nw, hs.2⟩
      · simp only [bool_rec_false_eq_and, Bool.and_eq_true, forceNatCBV_eq,
          show Nat.land w (nat_lit 1) = Nat.mod w 2 from Nat.and_two_pow_sub_one_eq_mod w 1,
          show Nat.shiftRight w (nat_lit 1) = Nat.div w 2 from Nat.shiftRight_eq_div_pow w 1] at hs
        obtain ⟨hp, hg, hs⟩ := hs
        obtain ⟨h00, _, _, _, s1⟩ := ih hs
        obtain ⟨h01, _, _, _, s2⟩ := ih s1
        obtain ⟨h10, _, _, _, s3⟩ := ih s2
        obtain ⟨h11, s', bc', nw', hs'⟩ := ih s3
        exact ⟨.branch (Nat.beq_eq.mp hp) (Nat.ble_eq.mp hg) h00 h01 h10 h11, s', bc', nw', hs'⟩
      · simp only [bool_rec_false_eq_and, Bool.and_eq_true, forceNatCBV_eq, checkS1Dual32] at hs
        exact ⟨.leaf (fun | 0, _ => hEnt hs.1.1 | 1, _ => hEnt hs.1.2), _, bc, _, hs.2⟩
  suffices ∀ {s bcIn nw}, evalS1BatchK dict b s bcIn nw = true → Stage1BatchCov b from this hb
  clear h hb
  unfold evalS1BatchK
  induction b with
  | one k ix iy => exact fun hc => (hStr (nat_lit 128) (by simpa only [forceNatCBV_eq] using hc)).1
  | more _ _ _ _ ihr =>
    intro _ _ _ hc
    dsimp only at hc
    rw [forceNatCBV_eq, forceNatCBV_eq, forceNatCBV_eq] at hc
    obtain ⟨hcov, _, _, _, hrest⟩ := hStr (nat_lit 128) hc
    exact ⟨hcov, ihr hrest⟩

end QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

end
