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

public import FQCExternal.Vendor.Core

@[expose] public section

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

set_option exponentiation.threshold 256
set_option autoImplicit false

/-! ### Pure-`Lit` Call-By-Value (`CBV`) Kernel Forcing Combinators -/

/--
Linear-continuation pure-`Lit` CBV `Nat` forcing via `@Nat.rec ... (Nat.add x (nat_lit 1))`:
definitionally `k x` (`k` occurs ONCE), while in the Lean kernel `reduce_nat` reduces
`Nat.add x 1` to `nat_lit (N + 1)` and `@Nat.rec` extracts pure `nat_lit N`.
-/
noncomputable def forceNatCBV (x : Nat) (k : Nat → Bool) : Bool :=
  @Nat.rec (fun _ => Bool) false (fun n _ => k n) (Nat.add x (nat_lit 1))

theorem bool_rec_false_true_iff {a b : Bool} : @Bool.rec (fun _ => Bool) false b a = true ↔ a =
    true ∧ b = true := by
  cases a <;> simp
theorem forceNatCBV_eq (x : Nat) (k : Nat → Bool) : forceNatCBV x k = k x := by cases x <;> rfl

/-- Single-`Nat.rec` pure-`Lit` CBV `SInt` forcing (`0` `Nat.add p 1` trees). -/
noncomputable def forceSIntCBV (x : SInt) (k : SInt → Bool) : Bool :=
  @SInt.rec (fun _ => Bool) (fun sn sm =>
    @Bool.rec (fun _ => Bool)
      (forceNatCBV sm (fun sm' => k (SInt.mk false sm')))
      (forceNatCBV sm (fun sm' => k (SInt.mk true sm')))
      sn) x

theorem forceSIntCBV_eq (x : SInt) (k : SInt → Bool) : forceSIntCBV x k = k x := by
  rcases x with ⟨_ | _, sm⟩
  · exact forceNatCBV_eq sm (fun sm' => k ⟨false, sm'⟩)
  · exact forceNatCBV_eq sm (fun sm' => k ⟨true, sm'⟩)

/-! ### Stage-1 Fuse-Out Predicate -/

/-- Whether a packed 2-bit `SU(2)` syllable word ends in a fuseable syllable `{2, 4, 6, 8}`. -/
def isFuseOutWord (w : Nat) : Bool :=
  let cl := Nat.mod (Nat.div w 16) 16
  (!Nat.beq w 0) && (Nat.beq cl 2 || Nat.beq cl 4 || Nat.beq cl 6 || Nat.beq cl 8)

/-- FastKernel `isFuseOutWord` using `@Bool.rec`, bitwise shifts/masks, and `nat_lit`. -/
noncomputable def isFuseOutWordFast (w : Nat) : Bool :=
  let cl := Nat.land (Nat.shiftRight w (nat_lit 4)) (nat_lit 15)
  @Bool.rec (fun _ => Bool) false
    (@Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          (Nat.beq cl (nat_lit 8))
          true
          (Nat.beq cl (nat_lit 6)))
        true
        (Nat.beq cl (nat_lit 4)))
      true
      (Nat.beq cl (nat_lit 2)))
    (!Nat.beq w (nat_lit 0))

theorem isFuseOutWordFast_eq (w : Nat) : isFuseOutWordFast w = isFuseOutWord w := by
  unfold isFuseOutWordFast isFuseOutWord
  dsimp only
  rw [show Nat.shiftRight w (nat_lit 4) = Nat.div w 16 from Nat.shiftRight_eq_div_pow w 4,
    show Nat.land (Nat.div w 16) (nat_lit 15) = Nat.mod (Nat.div w 16) 16 from
      Nat.and_two_pow_sub_one_eq_mod (Nat.div w 16) 4]
  simp only [bool_rec_false_eq_and, bool_rec_true_eq_or, Bool.or_assoc]

/-! ### Box-Free Analytic Interval Derivation -/

/-- Generic tight lower-bound `SInt` coordinate for `(num * bs) / den` given `0 < dLo`. -/
def sFloorRatScale (bs : Nat) (num : SInt) (dLo dHi : Nat) : SInt :=
  match num with
  | ⟨false, m⟩ => ⟨false, Nat.div (Nat.mul m bs) dHi⟩
  | ⟨true, m⟩ =>
      match Nat.beq m 0 with
      | true => ⟨false, 0⟩
      | false => ⟨true, Nat.div (Nat.sub (Nat.add (Nat.mul m bs) dLo) 1) dLo⟩

/-- Helper for negative-numerator `sCeilRat` normalized at `-0 -> +0`. -/
def sCeilNegSpec (q : Nat) : SInt :=
  match Nat.beq q 0 with
  | true => ⟨false, 0⟩
  | false => ⟨true, q⟩

/-- Generic tight upper-bound `SInt` coordinate for `(num * bs) / den` given `0 < dLo`. -/
def sCeilRatScale (bs : Nat) (num : SInt) (dLo dHi : Nat) : SInt :=
  match num with
  | ⟨false, m⟩ => ⟨false, Nat.div (Nat.sub (Nat.add (Nat.mul m bs) dLo) 1) dLo⟩
  | ⟨true, m⟩ => sCeilNegSpec (Nat.div (Nat.mul m bs) dHi)

/--
Tight lower-bound `SInt` coordinate for `(num * 2^52) / den` given `0 < dLo` and
`denHi = ⟨false, dHi⟩` .
-/
def sFloorRat (num : SInt) (dLo dHi : Nat) : SInt :=
  sFloorRatScale 4503599627370496 num dLo dHi

/--
Tight upper-bound `SInt` coordinate for `(num * 2^52) / den` given `0 < dLo` and
`denHi = ⟨false, dHi⟩` .
-/
def sCeilRat (num : SInt) (dLo dHi : Nat) : SInt :=
  sCeilRatScale 4503599627370496 num dLo dHi

/-- FastKernel generic `sFloorRatScale` using `@SInt.rec`, `@Bool.rec`, and `nat_lit`. -/
noncomputable def sFloorRatScaleFast (bs : Nat) (num : SInt) (dLo dHi : Nat) : SInt :=
  @SInt.rec (fun _ => SInt) (fun sn sm =>
    @Bool.rec (fun _ => SInt)
      (SInt.mk false (Nat.div (Nat.mul sm bs) dHi))
      (@Bool.rec (fun _ => SInt)
        (SInt.mk true (Nat.div (Nat.sub (Nat.add (Nat.mul sm bs) dLo) (nat_lit 1)) dLo))
        (SInt.mk false (nat_lit 0))
        (Nat.beq sm (nat_lit 0)))
      sn) num

/-- FastKernel `sFloorRat` using `@SInt.rec`, `@Bool.rec`, and `nat_lit`. -/
noncomputable def sFloorRatFast (num : SInt) (dLo dHi : Nat) : SInt :=
  sFloorRatScaleFast (nat_lit 4503599627370496) num dLo dHi

theorem sFloorRatScaleFast_eq (bs : Nat) (num : SInt) (dLo dHi : Nat) :
    sFloorRatScaleFast bs num dLo dHi = sFloorRatScale bs num dLo dHi := by
  rcases num with ⟨_ | _, sm⟩
  · rfl
  · unfold sFloorRatScaleFast sFloorRatScale
    dsimp only
    rw [show (nat_lit 0 : Nat) = 0 from rfl]
    cases Nat.beq sm 0 <;> rfl

theorem sFloorRatFast_eq (num : SInt) (dLo dHi : Nat) :
    sFloorRatFast num dLo dHi = sFloorRat num dLo dHi :=
  sFloorRatScaleFast_eq 4503599627370496 num dLo dHi

noncomputable def sCeilNegFast (q : Nat) : SInt :=
  @Bool.rec (fun _ => SInt) (SInt.mk true q) (SInt.mk false (nat_lit 0)) (Nat.beq q (nat_lit 0))

theorem sCeilNegFast_eq (q : Nat) : sCeilNegFast q = sCeilNegSpec q := by
  unfold sCeilNegFast sCeilNegSpec
  rw [show Nat.beq q (nat_lit 0) = Nat.beq q 0 from rfl]
  cases Nat.beq q 0 <;> rfl

/-- FastKernel generic `sCeilRatScale` using `@SInt.rec`, `@Bool.rec`, and `nat_lit`. -/
noncomputable def sCeilRatScaleFast (bs : Nat) (num : SInt) (dLo dHi : Nat) : SInt :=
  @SInt.rec (fun _ => SInt) (fun sn sm =>
    @Bool.rec (fun _ => SInt)
      (SInt.mk false (Nat.div (Nat.sub (Nat.add (Nat.mul sm bs) dLo) (nat_lit 1)) dLo))
      (sCeilNegFast (Nat.div (Nat.mul sm bs) dHi))
      sn) num

/-- FastKernel `sCeilRat` using `@SInt.rec`, `@Bool.rec`, and `nat_lit`. -/
noncomputable def sCeilRatFast (num : SInt) (dLo dHi : Nat) : SInt :=
  sCeilRatScaleFast (nat_lit 4503599627370496) num dLo dHi

theorem sCeilRatScaleFast_eq (bs : Nat) (num : SInt) (dLo dHi : Nat) :
    sCeilRatScaleFast bs num dLo dHi = sCeilRatScale bs num dLo dHi := by
  rcases num with ⟨_ | _, sm⟩
  · rfl
  · exact sCeilNegFast_eq (Nat.div (Nat.mul sm bs) dHi)

theorem sCeilRatFast_eq (num : SInt) (dLo dHi : Nat) :
    sCeilRatFast num dLo dHi = sCeilRat num dLo dHi :=
  sCeilRatScaleFast_eq 4503599627370496 num dLo dHi

theorem nat_le_ceil_div_mul {a d : Nat} (ha : 0 < a) (hd : 0 < d) :
    a ≤ Nat.mul (Nat.div (Nat.sub (Nat.add a d) 1) d) d := by
  have := Nat.div_add_mod (a + d - 1) d
  have := Nat.mod_lt (a + d - 1) hd
  change a ≤ ((a + d - 1) / d) * d
  rw [Nat.mul_comm]
  omega

theorem nat_ceil_div_pos {a d : Nat} (ha : 0 < a) (hd : 0 < d) :
    0 < Nat.div (Nat.sub (Nat.add a d) 1) d := by
  have hle := nat_le_ceil_div_mul ha hd
  rcases hq : Nat.div (Nat.sub (Nat.add a d) 1) d with _ | k
  · rw [hq, show Nat.mul 0 d = 0 from Nat.zero_mul d] at hle
    omega
  · exact Nat.succ_pos k

theorem nat_beq_zero_of_pos {q : Nat} (hq : 0 < q) : Nat.beq q 0 = false := by
  rcases q with _ | _ <;> (try cases hq) <;> rfl

theorem sLe_false_false {a b : Nat} (h : a ≤ b) : sLe ⟨false, a⟩ ⟨false, b⟩ = true := by
  unfold sLe sSub sAdd sNeg
  dsimp only
  rw [Nat.ble_eq.mpr h]
  rfl

theorem sLe_true_true {a b : Nat} (h : b ≤ a) : sLe ⟨true, a⟩ ⟨true, b⟩ = true := by
  unfold sLe sSub sAdd sNeg
  dsimp only
  cases Nat.ble a b
  · rfl
  · rw [show Nat.sub b a = 0 from Nat.sub_eq_zero_of_le h]
    rfl

theorem sFloorRatScale_sound {bs : Nat} {num : SInt} {dLo dHi : Nat}
    (hbs : 0 < bs) (hdLo : 0 < dLo) :
    let x0 := sFloorRatScale bs num dLo dHi
    sLe (match sNonneg x0 with | true => sMul x0 ⟨false, dHi⟩ | false => sMul x0 ⟨false, dLo⟩)
        (sMul num ⟨false, bs⟩) = true := by
  rcases num with ⟨_ | _, m⟩
  · exact sLe_false_false (Nat.div_mul_le_self (Nat.mul m bs) dHi)
  · rcases m with _ | m'
    · unfold sFloorRatScale sNonneg sMul sLe sSub sAdd sNeg
      dsimp only
      rw [show Nat.mul 0 bs = 0 from Nat.zero_mul bs, show Nat.mul 0 dHi = 0 from Nat.zero_mul dHi]
      rfl
    · have ha : 0 < Nat.mul (m' + 1) bs := Nat.mul_pos (Nat.succ_pos m') hbs
      dsimp only [sFloorRatScale]
      rw [show Nat.beq (m' + 1) 0 = false from rfl]
      dsimp only [sNonneg]
      rw [nat_beq_zero_of_pos (nat_ceil_div_pos ha hdLo)]
      exact sLe_true_true (nat_le_ceil_div_mul ha hdLo)

theorem sCeilNegSpec_sound {a q dLo dHi : Nat} (hle : Nat.mul q dHi ≤ a) :
    let x1 := sCeilNegSpec q
    sLe ⟨true, a⟩
        (match sNonneg x1 with | true => sMul x1 ⟨false, dLo⟩ | false => sMul x1 ⟨false, dHi⟩) =
        true := by
  unfold sCeilNegSpec
  cases hq : Nat.beq q 0
  · dsimp only [sNonneg]
    rw [hq]
    exact sLe_true_true hle
  · unfold sNonneg sMul sLe sSub sAdd sNeg
    dsimp only
    rw [show Nat.mul 0 dLo = 0 from Nat.zero_mul dLo]
    rfl

theorem sCeilRatScale_sound {bs : Nat} {num : SInt} {dLo dHi : Nat}
    (hbs : 0 < bs) (hdLo : 0 < dLo) :
    let x1 := sCeilRatScale bs num dLo dHi
    sLe (sMul num ⟨false, bs⟩)
        (match sNonneg x1 with | true => sMul x1 ⟨false, dLo⟩ | false => sMul x1 ⟨false, dHi⟩) =
            true := by
  rcases num with ⟨_ | _, m⟩
  · rcases m with _ | m'
    · dsimp only [sCeilRatScale, sNonneg, sMul]
      rw [show Nat.mul 0 bs = 0 from Nat.zero_mul bs]
      exact sLe_false_false (Nat.zero_le _)
    · exact sLe_false_false (nat_le_ceil_div_mul (Nat.mul_pos (Nat.succ_pos m') hbs) hdLo)
  · exact sCeilNegSpec_sound (Nat.div_mul_le_self (Nat.mul m bs) dHi)

theorem boxScale_pos : 0 < 4503599627370496 := by decide

theorem sFloorRat_sound {num : SInt} {dLo dHi : Nat} (hdLo : 0 < dLo) :
    let x0 := sFloorRat num dLo dHi
    sLe (match sNonneg x0 with | true => sMul x0 ⟨false, dHi⟩ | false => sMul x0 ⟨false, dLo⟩)
        (sMul num boxScaleS) = true :=
  sFloorRatScale_sound boxScale_pos hdLo

theorem sCeilRat_sound {num : SInt} {dLo dHi : Nat} (hdLo : 0 < dLo) :
    let x1 := sCeilRat num dLo dHi
    sLe (sMul num boxScaleS)
        (match sNonneg x1 with | true => sMul x1 ⟨false, dLo⟩ | false => sMul x1 ⟨false, dHi⟩) =
        true :=
  sCeilRatScale_sound boxScale_pos hdLo

/-- Analytic box derivation from `Z[ζ_8]` denominator `wden` and numerator `wnum`. -/
def boxOfWordZ8 (wden wnum : FastZ8) : Option Box2DS :=
  let denLo := fzReLo wden
  let denHi := fzReHi wden
  let nxLo := fzReLo wnum
  let nxHi := fzReHi wnum
  let nyLo := fzImLo wnum
  let nyHi := fzImHi wnum
  match denLo, denHi with
  | ⟨false, dLo⟩, ⟨false, dHi⟩ =>
      match Nat.beq dLo 0 with
      | true => none
      | false =>
          let x0 := sFloorRat nxLo dLo dHi
          let x1 := sCeilRat nxHi dLo dHi
          let y0 := sFloorRat nyLo dLo dHi
          let y1 := sCeilRat nyHi dLo dHi
          match sLe x0 x1 && sLe y0 y1 with
          | true => some ⟨x0, x1, y0, y1⟩
          | false => none
  | _, _ => none

/-- Analytic `(tc, Box2DS)` of packed 2-bit word `w` under T-count cap `tCap`. -/
def boxTcOfWordOpt (tCap w : Nat) : Option (Nat × Box2DS) :=
  let st := evalWord2Bit w
  match st with
  | ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ =>
      match ok && inRangeCol st && Nat.blt dm 8 && Nat.ble tc tCap with
      | false => none
      | true =>
          let u : FastZ8 := ⟨unbiasS ua, unbiasS ub, unbiasS uc, unbiasS ud⟩
          let v : FastZ8 := ⟨unbiasS va, unbiasS vb, unbiasS vc, unbiasS vd⟩
          match boxOfWordZ8 (fzMul u (fzConj u)) (fzNeg (fzMul (fzConj v) u)) with
          | none => none
          | some bx => some (tc, bx)

def boxOfWordOpt (tCap w : Nat) : Option Box2DS :=
  let st := evalWord2Bit w
  match st with
  | ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ =>
      match ok && inRangeCol st && Nat.blt dm 8 && Nat.ble tc tCap with
      | false => none
      | true =>
          let u : FastZ8 := ⟨unbiasS ua, unbiasS ub, unbiasS uc, unbiasS ud⟩
          let v : FastZ8 := ⟨unbiasS va, unbiasS vb, unbiasS vc, unbiasS vd⟩
          boxOfWordZ8 (fzMul u (fzConj u)) (fzNeg (fzMul (fzConj v) u))

theorem boxOfWordOpt_sound {tCap w : Nat} {bx : Box2DS}
    (h : boxOfWordOpt tCap w = some bx) :
    checkWord2BitBox tCap w bx = true := by
  unfold boxOfWordOpt at h
  unfold checkWord2BitBox
  rcases hst : evalWord2Bit w with ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
  rw [hst] at h
  dsimp only at h ⊢
  cases hpre : (ok && inRangeCol ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ &&
      Nat.blt dm 8 && Nat.ble tc tCap) <;> rw [hpre] at h <;> try cases h
  rw [Bool.true_and]
  dsimp only [boxOfWordZ8] at h
  generalize fzMul _ _ = wden at h ⊢
  generalize fzNeg _ = wnum at h ⊢
  rcases hdl : fzReLo wden with ⟨_ | _, dLo⟩ <;> rw [hdl] at h <;> try cases h
  rcases hdh : fzReHi wden with ⟨_ | _, dHi⟩ <;> rw [hdh] at h <;> try cases h
  dsimp only at h
  cases hd0 : Nat.beq dLo 0 <;> rw [hd0] at h <;> try cases h
  dsimp only at h
  cases hxy : (sLe (sFloorRat (fzReLo wnum) dLo dHi) (sCeilRat (fzReHi wnum) dLo dHi) &&
      sLe (sFloorRat (fzImLo wnum) dLo dHi) (sCeilRat (fzImHi wnum) dLo dHi)) <;>
    rw [hxy] at h <;> cases h
  have hdLo_pos : 0 < dLo := Nat.pos_of_ne_zero fun hz => by simp [hz] at hd0
  rcases Bool.and_eq_true_iff.mp hxy with ⟨hxle, hyle⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨congrArg Bool.not hd0, hxle⟩, hyle⟩, sFloorRat_sound hdLo_pos⟩,
    sCeilRat_sound hdLo_pos⟩, sFloorRat_sound hdLo_pos⟩, sCeilRat_sound hdLo_pos⟩

theorem boxTcOfWordOpt_sound {tCap w tc : Nat} {bx : Box2DS}
    (h : boxTcOfWordOpt tCap w = some (tc, bx)) :
    tc ≤ tCap ∧ ∀ c : Nat, tc ≤ c → checkWord2BitBox c w bx = true := by
  unfold boxTcOfWordOpt at h
  rcases hst : evalWord2Bit w with ⟨tc0, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
  rw [hst] at h
  dsimp only at h
  cases hpre : (ok && inRangeCol ⟨tc0, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ &&
      Nat.blt dm 8 && Nat.ble tc0 tCap) <;> rw [hpre] at h <;> try cases h
  dsimp only at h
  rcases Bool.and_eq_true_iff.mp hpre with ⟨hpre1, htc_ble⟩
  rcases hbz : boxOfWordZ8 _ _ with _ | bx' <;> rw [hbz] at h <;> cases h
  refine ⟨Nat.ble_eq.mp htc_ble, fun c hle => boxOfWordOpt_sound ?_⟩
  simp only [boxOfWordOpt, hst, hpre1, Nat.ble_eq.mpr hle, Bool.true_and, hbz]

/-- FastKernel CPS `boxOfWordZ8` forcing all 4 output `SInt` coordinates via `forceSIntK`. -/
noncomputable def evalWordBoxZ8Fast (wden wnum : FastZ8) (k : Box2DS → Bool) : Bool :=
  @FastZ8.rec (fun _ => Bool) (fun da db _ dd =>
    @FastZ8.rec (fun _ => Bool) (fun na nb nc nd =>
      forceSIntCBV (sSubFast db dd) (fun bdD =>
        forceSIntCBV (sAddFast (sMulFast (SInt.mk false (nat_lit 2000000000000000000)) da)
          (sMulFast bdD (SInt.mk false (nat_lit 1414213562373095048)))) (fun sumD =>
          forceSIntCBV (sSubFast sumD (sAbsFast bdD)) (fun denLo =>
            forceSIntCBV (sAddFast sumD (sAbsFast bdD)) (fun denHi =>
              @SInt.rec (fun _ => Bool) (fun dnLo dLo =>
                @SInt.rec (fun _ => Bool) (fun dnHi dHi =>
                  @Bool.rec (fun _ => Bool)
                    (@Bool.rec (fun _ => Bool)
                      (@Bool.rec (fun _ => Bool)
                        (forceSIntCBV (sSubFast nb nd) (fun bdN =>
                          forceSIntCBV (sAddFast (sMulFast (SInt.mk false
                              (nat_lit 2000000000000000000)) na)
                            (sMulFast bdN (SInt.mk false (nat_lit 1414213562373095048))))
                                (fun sumReN =>
                            forceSIntCBV (sAddFast nb nd) (fun bpN =>
                              forceSIntCBV (sAddFast (sMulFast (SInt.mk false
                                  (nat_lit 2000000000000000000)) nc)
                                (sMulFast bpN (SInt.mk false (nat_lit 1414213562373095048))))
                                    (fun sumImN =>
                                forceSIntCBV (sFloorRatFast (sSubFast sumReN (sAbsFast bdN)) dLo
                                    dHi) (fun x0 =>
                                  forceSIntCBV (sCeilRatFast (sAddFast sumReN (sAbsFast bdN)) dLo
                                      dHi) (fun x1 =>
                                    forceSIntCBV (sFloorRatFast (sSubFast sumImN (sAbsFast bpN)) dLo
                                        dHi) (fun y0 =>
                                      forceSIntCBV (sCeilRatFast (sAddFast sumImN (sAbsFast bpN))
                                          dLo dHi) (fun y1 =>
                                        @Bool.rec (fun _ => Bool) false
                                          (@Bool.rec (fun _ => Bool) false
                                            (k (Box2DS.mk x0 x1 y0 y1))
                                            (sLeFast y0 y1))
                                          (sLeFast x0 x1))))))))))
                        false
                        (Nat.beq dLo (nat_lit 0)))
                      false
                      dnHi)
                    false
                    dnLo) denHi) denLo))))) wnum) wden

theorem evalWordBoxZ8Fast_eq (wden wnum : FastZ8) (k : Box2DS → Bool) :
    evalWordBoxZ8Fast wden wnum k =
      (match boxOfWordZ8 wden wnum with | none => false | some bx => k bx) := by
  rcases wden with ⟨da, db, dc, dd⟩
  rcases wnum with ⟨na, nb, nc, nd⟩
  unfold evalWordBoxZ8Fast boxOfWordZ8 fzReLo fzReHi fzImLo fzImHi
  dsimp only
  simp only [forceSIntCBV_eq, show SInt.mk false (nat_lit 2000000000000000000) = twoD18S from rfl,
    show SInt.mk false (nat_lit 1414213562373095048) = s2MidS from rfl, sSubFast_eq, sAddFast_eq,
    sMulFast_eq, sAbsFast_eq, sFloorRatFast_eq, sCeilRatFast_eq, sLeFast_eq]
  rcases sSub (sAdd (sMul twoD18S da) _) _ with ⟨_ | _, dLo⟩ <;>
    rcases sAdd (sAdd (sMul twoD18S da) _) _ with ⟨_ | _, dHi⟩ <;> try rfl
  dsimp only
  rw [show Nat.beq dLo (nat_lit 0) = Nat.beq dLo 0 from rfl]
  cases Nat.beq dLo 0 <;> dsimp only <;> try rfl
  cases sLe (sFloorRat _ dLo dHi) (sCeilRat _ dLo dHi) <;>
    cases sLe (sFloorRat _ dLo dHi) (sCeilRat _ dLo dHi) <;> rfl

noncomputable def evalWordTcEndFast (tCap : Nat) (k : Nat → Box2DS → Bool) :
    Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd =>
    @Bool.rec (fun _ => Bool) false
      (@Bool.rec (fun _ => Bool) false
        (@Bool.rec (fun _ => Bool) false
          (@Bool.rec (fun _ => Bool) false
            (let u : FastZ8 := FastZ8.mk (unbiasSFast ua) (unbiasSFast ub) (unbiasSFast uc)
                (unbiasSFast ud)
             let v : FastZ8 :=
                 FastZ8.mk (unbiasSFast va) (unbiasSFast vb) (unbiasSFast vc) (unbiasSFast vd)
             evalWordBoxZ8Fast (fzMulFast u (fzConjFast u)) (fzNegFast (fzMulFast (fzConjFast v) u))
                 (k tc))
            (Nat.ble tc tCap))
          (Nat.blt dm (nat_lit 8)))
        (inRange8Fast ua ub uc ud va vb vc vd))
      ok

theorem evalWordTcEndFast_eq (tCap : Nat) (k : Nat → Box2DS → Bool) (st : FastCol) :
    appColK (evalWordTcEndFast tCap k) st =
      (match st with
       | ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ =>
           match ok && inRangeCol st && Nat.blt dm 8 && Nat.ble tc tCap with
           | false => false
           | true =>
               let u : FastZ8 := ⟨unbiasS ua, unbiasS ub, unbiasS uc, unbiasS ud⟩
               let v : FastZ8 := ⟨unbiasS va, unbiasS vb, unbiasS vc, unbiasS vd⟩
               match boxOfWordZ8 (fzMul u (fzConj u)) (fzNeg (fzMul (fzConj v) u)) with
               | none => false
               | some bx => k tc bx) := by
  rcases st with ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
  dsimp only [appColK, evalWordTcEndFast]
  rw [inRange8Fast_eq tc dm ok, show Nat.blt dm (nat_lit 8) = Nat.blt dm 8 from rfl]
  cases ok <;> cases inRangeCol ⟨tc, dm, _, ua, ub, uc, ud, va, vb, vc, vd⟩ <;>
    cases Nat.blt dm 8 <;> cases Nat.ble tc tCap <;> try rfl
  dsimp only
  simp only [unbiasSFast_eq, fzConjFast_eq, fzMulFast_eq, fzNegFast_eq]
  exact evalWordBoxZ8Fast_eq _ _ (k tc)

noncomputable def evalWordTcFinishK (tCap cLast : Nat) (k : Nat → Box2DS → Bool) (acc : Bool)
    (m4 tc4 dm4 : Nat) (ok4 : Bool) (ua4 ub4 uc4 ud4 va4 vb4 vc4 vd4 : Nat) : Bool :=
  let acc4 := acc && inRange8Fast ua4 ub4 uc4 ud4 va4 vb4 vc4 vd4 && Nat.beq m4 (nat_lit 1)
  stepSylK
    (forceColStateK (fun tc dm sfOk ua ub uc ud va vb vc vd =>
      evalWordTcEndFast tCap k tc dm (acc4 && sfOk) ua ub uc ud va vb vc vd))
    cLast tc4 dm4 ok4 ua4 ub4 uc4 ud4 va4 vb4 vc4 vd4

theorem appMidK_evalWordTcFinishK (tCap cLast : Nat) (k : Nat → Box2DS → Bool) (acc : Bool)
    (p4 : Nat × FastCol) :
    appMidK (evalWordTcFinishK tCap cLast k acc) p4 =
      appColK (evalWordTcEndFast tCap k)
        { stepSyl cLast p4.2 with
          ok := acc && inRangeCol p4.2 && Nat.beq p4.1 1 && (stepSyl cLast p4.2).ok } := by
  rcases p4 with ⟨m4, ⟨tc4, dm4, ok4, ua4, ub4, uc4, ud4, va4, vb4, vc4, vd4⟩⟩
  change appColK (stepSylK (forceColStateK _) cLast) ⟨tc4, dm4, ok4, ua4, ub4, uc4, ud4, va4, vb4,
      vc4, vd4⟩ = _
  rw [appColK_stepSylK, appColK_forceColStateK]
  rcases stepSyl cLast ⟨tc4, dm4, ok4, ua4, ub4, uc4, ud4, va4, vb4, vc4, vd4⟩ with ⟨_, _, _, _, _,
      _, _, _, _, _, _⟩
  dsimp only [appColK]
  rw [inRange8Fast_eq tc4 dm4 ok4, show Nat.beq m4 (nat_lit 1) = Nat.beq m4 1 from rfl]

theorem appMidK_fourStepsTcBox (tCap cLast : Nat) (k : Nat → Box2DS → Bool) (m0 : Nat)
    (s0 : FastCol) :
    appMidK
      (stepMid12CheckedK
        (stepMid12CheckedK
          (stepMid12CheckedK
            (stepMid12CheckedK
              (evalWordTcFinishK tCap cLast k)))) true) (m0, s0) =
    appColK (evalWordTcEndFast tCap k)
      (let p1 := stepMid12Raw (m0, s0)
       let p2 := stepMid12Raw p1
       let p3 := stepMid12Raw p2
       let p4 := stepMid12Raw p3
       let sf := stepSyl cLast p4.2
       { sf with ok := inRangeCol s0 && inRangeCol p1.2 && inRangeCol p2.2 &&
                       inRangeCol p3.2 && inRangeCol p4.2 && Nat.beq p4.1 1 && sf.ok }) := by
  dsimp only
  rw [appMidK_stepMid12CheckedK, appMidK_stepMid12CheckedK, appMidK_stepMid12CheckedK,
    appMidK_stepMid12CheckedK, appMidK_evalWordTcFinishK]
  simp only [Bool.true_and, Bool.and_assoc]

noncomputable def evalWordTcNonzeroFast (tCap w : Nat) (k : Nat → Box2DS → Bool) : Bool :=
  let cFirst := Nat.land w (nat_lit 15)
  let cLast := Nat.land (Nat.shiftRight w (nat_lit 4)) (nat_lit 15)
  let m0 := Nat.shiftRight w (nat_lit 8)
  stepSylK
    (forceColStateK (fun tc0 dm0 ok0 ua0 ub0 uc0 ud0 va0 vb0 vc0 vd0 =>
      stepMid12CheckedK
        (stepMid12CheckedK
          (stepMid12CheckedK
            (stepMid12CheckedK
              (evalWordTcFinishK tCap cLast k))))
        true m0 tc0 dm0 ok0 ua0 ub0 uc0 ud0 va0 vb0 vc0 vd0))
    cFirst
    (nat_lit 0) (nat_lit 0) true
    (nat_lit 70368744177665) (nat_lit 70368744177664) (nat_lit 70368744177664)
        (nat_lit 70368744177664)
    (nat_lit 70368744177664) (nat_lit 70368744177664) (nat_lit 70368744177664)
        (nat_lit 70368744177664)

theorem evalWordTcNonzeroFast_eq (tCap w : Nat) (k : Nat → Box2DS → Bool) :
    evalWordTcNonzeroFast tCap w k =
      appColK (evalWordTcEndFast tCap k)
        (let cFirst := Nat.mod w 16
         let cLast := Nat.mod (Nat.div w 16) 16
         let m0 := Nat.div w 256
         let s0 := stepSyl cFirst fastColInit
         let p1 := stepMid12Raw (m0, s0)
         let p2 := stepMid12Raw p1
         let p3 := stepMid12Raw p2
         let p4 := stepMid12Raw p3
         let sf := stepSyl cLast p4.2
         { sf with ok := inRangeCol s0 && inRangeCol p1.2 && inRangeCol p2.2 &&
                         inRangeCol p3.2 && inRangeCol p4.2 && Nat.beq p4.1 1 && sf.ok }) := by
  unfold evalWordTcNonzeroFast
  dsimp only
  rw [show Nat.land w (nat_lit 15) = Nat.mod w 16 from Nat.and_two_pow_sub_one_eq_mod w 4,
    show Nat.shiftRight w (nat_lit 4) = Nat.div w 16 from Nat.shiftRight_eq_div_pow w 4,
    show Nat.land (Nat.div w 16) (nat_lit 15) = Nat.mod (Nat.div w 16) 16 from
      Nat.and_two_pow_sub_one_eq_mod (Nat.div w 16) 4,
    show Nat.shiftRight w (nat_lit 8) = Nat.div w 256 from Nat.shiftRight_eq_div_pow w 8]
  change appColK (stepSylK (forceColStateK _) (Nat.mod w 16)) fastColInit = _
  rw [appColK_stepSylK, appColK_forceColStateK]
  generalize stepSyl (Nat.mod w 16) fastColInit = s0
  rcases s0 with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  exact appMidK_fourStepsTcBox tCap (Nat.mod (Nat.div w 16) 16) k (Nat.div w 256) _

/-- FastKernel CPS single-word evaluator producing `(tc, Box2DS)` without stored boxes. -/
noncomputable def evalWordTcBoxFast (tCap w : Nat) (k : Nat → Box2DS → Bool) : Bool :=
  @Bool.rec (fun _ => Bool)
    (evalWordTcNonzeroFast tCap w k)
    (evalWordTcEndFast tCap k
      (nat_lit 0) (nat_lit 0) true
      (nat_lit 70368744177665) (nat_lit 70368744177664) (nat_lit 70368744177664)
          (nat_lit 70368744177664)
      (nat_lit 70368744177664) (nat_lit 70368744177664) (nat_lit 70368744177664)
          (nat_lit 70368744177664))
    (Nat.beq w (nat_lit 0))

theorem evalWordTcBoxFast_eq (tCap w : Nat) (k : Nat → Box2DS → Bool) :
    evalWordTcBoxFast tCap w k =
      (match boxTcOfWordOpt tCap w with | none => false | some (tc, bx) => k tc bx) := by
  refine Eq.trans (b := appColK (evalWordTcEndFast tCap k) (evalWord2Bit w)) ?_ ?_
  · unfold evalWordTcBoxFast evalWord2Bit
    rw [show Nat.beq w (nat_lit 0) = Nat.beq w 0 from rfl]
    cases Nat.beq w 0
    · exact evalWordTcNonzeroFast_eq tCap w k
    · generalize evalWordTcEndFast tCap k = f
      rfl
  · unfold boxTcOfWordOpt
    rw [evalWordTcEndFast_eq tCap k (evalWord2Bit w)]
    rcases evalWord2Bit w with ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
    dsimp only
    cases (ok && inRangeCol ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ &&
      Nat.blt dm 8 && Nat.ble tc tCap) <;> try rfl
    cases boxOfWordZ8 _ _ <;> rfl

theorem evalWordTcBoxFast_sound {tCap w : Nat} {k : Nat → Box2DS → Bool}
    (h : evalWordTcBoxFast tCap w k = true) :
    ∃ tc : Nat, ∃ bx : Box2DS,
      tc ≤ tCap ∧ (∀ c : Nat, tc ≤ c → checkWord2BitBox c w bx = true) ∧ k tc bx = true := by
  rw [evalWordTcBoxFast_eq] at h
  rcases hopt : boxTcOfWordOpt tCap w with _ | ⟨tc, bx⟩ <;> rw [hopt] at h
  · cases h
  · exact ⟨tc, bx, (boxTcOfWordOpt_sound hopt).1, (boxTcOfWordOpt_sound hopt).2, h⟩

/-! ### Stage-Specific Certified Word Entries & Packed `wchunk100` Dictionary Forest -/

/--
Certified Stage-1 local dictionary entry: `true` for `Lo` (`tCap=26`), `false` for `Hi`
(`isFuseOutWord ∧ tCap=28`).
-/
def ValidStage1Entry (p : Bool × Box2DS) : Prop :=
  match p.1 with
  | true => ∃ wd : Nat, checkWord2BitBox 26 wd p.2 = true
  | false => ∃ wd : Nat, isFuseOutWord wd = true ∧ checkWord2BitBox 28 wd p.2 = true

noncomputable def evalWordStage1Fast (w : Nat) (k : (Bool × Box2DS) → Bool) : Bool :=
  evalWordTcBoxFast (nat_lit 28) w (fun tc bx =>
    @Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool) false (k (false, bx)) (isFuseOutWordFast w))
      (k (true, bx))
      (Nat.ble tc (nat_lit 26)))

theorem evalWordStage1Fast_sound {w : Nat} {k : (Bool × Box2DS) → Bool}
    (h : evalWordStage1Fast w k = true) :
    ∃ e : Bool × Box2DS, ValidStage1Entry e ∧ k e = true := by
  obtain ⟨tc, bx, hle28, hchk, hbody⟩ := evalWordTcBoxFast_sound h
  rw [show Nat.ble tc (nat_lit 26) = Nat.ble tc 26 from rfl] at hbody
  cases hble : Nat.ble tc 26 <;> simp only [hble, bool_rec_false_true_iff,
      isFuseOutWordFast_eq] at hbody
  · exact ⟨(false, bx), ⟨w, hbody.1, hchk 28 hle28⟩, hbody.2⟩
  · exact ⟨(true, bx), ⟨w, hchk 26 (Nat.ble_eq.mp hble)⟩, hbody⟩

/-- Certified Stage-2 local dictionary entry (`tCap = 45`). -/
def ValidStage2Box (bx : Box2DS) : Prop :=
  ∃ wd : Nat, checkWord2BitBox 45 wd bx = true

noncomputable def evalWordStage2Fast (w : Nat) (k : Box2DS → Bool) : Bool :=
  evalWordTcBoxFast (nat_lit 45) w (fun _ bx => k bx)

theorem evalWordStage2Fast_sound {w : Nat} {k : Box2DS → Bool}
    (h : evalWordStage2Fast w k = true) :
    ∃ bx : Box2DS, ValidStage2Box bx ∧ k bx = true := by
  obtain ⟨tc, bx, hle45, hchk, hk⟩ := evalWordTcBoxFast_sound h
  exact ⟨bx, ⟨w, hchk 45 hle45⟩, hk⟩

/-- Inductive validity invariant over a `BTree α`. -/
def ValidBoxTree {α : Type} (P : α → Prop) : BTree α → Prop
  | .empty => True
  | .node x l r => P x ∧ ValidBoxTree P l ∧ ValidBoxTree P r

theorem ValidBoxTree.get? {α : Type} {P : α → Prop} {t : BTree α}
    (ht : ValidBoxTree P t) {n : Nat} {v : α} (hg : BTree.get? t n = some v) : P v := by
  induction t generalizing n with
  | empty => cases hg
  | node x l r ihl ihr =>
    rcases n with _ | m
    · exact Option.some.inj hg ▸ ht.1
    · unfold BTree.get? at hg
      cases hm : Nat.beq (Nat.mod m 2) 0 <;> rw [hm] at hg
      · exact ihr ht.2.2 hg
      · exact ihl ht.2.1 hg

/-- Prepend into a Braun tree so sequential `0..m-1` slots map directly to `BTree.get? t i`. -/
noncomputable def consBraunFast {α : Type} (t : BTree α) (x : α) : BTree α :=
  @BTree.rec α (fun _ => α → BTree α)
    (fun y => BTree.node y BTree.empty BTree.empty)
    (fun v l _ _ ihr y => BTree.node y (ihr v) l)
    t x

theorem validBoxTree_consBraunFast {α : Type} {P : α → Prop} {t : BTree α}
    (ht : ValidBoxTree P t) {x : α} (hx : P x) :
    ValidBoxTree P (consBraunFast t x) := by
  induction t generalizing x with
  | empty => exact ⟨hx, trivial, trivial⟩
  | node v l r _ ihr => exact ⟨hx, ihr ht.2.2 ht.1, ht.2.1⟩

/-- CPS Braun-tree prepend forcing every internal `BTree.node` before invoking `k`. -/
noncomputable def consBraunK {α : Type} : BTree α → α → (BTree α → Bool) → Bool :=
  @BTree.rec α (fun _ => α → (BTree α → Bool) → Bool)
    (fun y k => k (BTree.node y BTree.empty BTree.empty))
    (fun v l _ _ ihr y k => ihr v (fun r' => k (BTree.node y r' l)))

theorem consBraunK_eq {α : Type} (t : BTree α) (x : α) (k : BTree α → Bool) :
    consBraunK t x k = k (consBraunFast t x) := by
  induction t generalizing x k with
  | empty => rfl
  | node v l _ _ ihr => exact ihr v (fun r' => k (BTree.node x r' l))

/--
Decode one `<= 16` -word `wchunk` (`slotShift`-bit `(w <<< 2) ||| 3` slots + top sentinel `1` ).
-/
noncomputable def decodeWChunkK {α : Type} (slotShift wordMask : Nat)
    (evalOne : Nat → (α → Bool) → Bool) :
    Nat → Nat → (BTree α → Bool) → Bool :=
  @Nat.rec (fun _ => Nat → (BTree α → Bool) → Bool)
    (fun s k => @Bool.rec (fun _ => Bool) false (k BTree.empty) (Nat.beq s (nat_lit 1)))
    (fun _ ih s k =>
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool) false
          (let w := Nat.land (Nat.shiftRight s (nat_lit 2)) wordMask
           forceNatCBV (Nat.shiftRight s slotShift) (fun sNext =>
             evalOne w (fun entry =>
               ih sNext (fun tail =>
                 consBraunK tail entry k))))
          (Nat.beq (Nat.land s (nat_lit 3)) (nat_lit 3)))
        (k BTree.empty)
        (Nat.beq s (nat_lit 1)))

theorem decodeWChunkK_sound {α : Type} {P : α → Prop} {slotShift wordMask : Nat}
    {evalOne : Nat → (α → Bool) → Bool}
    (heval : ∀ {w : Nat} {k : α → Bool}, evalOne w k = true → ∃ x : α, P x ∧ k x = true)
    (fuel : Nat) :
    ∀ {s : Nat} {k : BTree α → Bool},
      decodeWChunkK slotShift wordMask evalOne fuel s k = true →
      ∃ t : BTree α, ValidBoxTree P t ∧ k t = true := by
  induction fuel with
  | zero =>
    intro s k h
    dsimp only [decodeWChunkK] at h
    exact ⟨.empty, trivial, (bool_rec_false_true_iff.mp h).2⟩
  | succ fuel' ih =>
    intro s k h
    dsimp only [decodeWChunkK] at h
    cases h1 : Nat.beq s (nat_lit 1) <;>
      simp only [h1, bool_rec_false_true_iff, forceNatCBV_eq] at h
    · obtain ⟨entry, hentry, hrec⟩ := heval h.2
      obtain ⟨tail, htail, hk⟩ := ih hrec
      exact ⟨consBraunFast tail entry, validBoxTree_consBraunFast htail hentry,
        consBraunK_eq tail entry k ▸ hk⟩
    · exact ⟨.empty, trivial, h⟩

/--
Decode a `BTree Nat` of `wchunk` literals (`<= 32` chunks per local unit) into `BTree (BTree α)` .
-/
noncomputable def decodeWForestFast {α : Type} (slotShift wordMask : Nat)
    (evalOne : Nat → (α → Bool) → Bool) :
    BTree Nat → (BTree (BTree α) → Bool) → Bool :=
  @BTree.rec Nat (fun _ => (BTree (BTree α) → Bool) → Bool)
    (fun k => k BTree.empty)
    (fun s _ _ ihl ihr k =>
      decodeWChunkK slotShift wordMask evalOne (nat_lit 16) s (fun ch =>
        ihl (fun fl =>
          ihr (fun fr =>
            k (BTree.node ch fl fr)))))

theorem decodeWForestFast_sound {α : Type} {P : α → Prop} {slotShift wordMask : Nat}
    {evalOne : Nat → (α → Bool) → Bool}
    (heval : ∀ {w : Nat} {k : α → Bool}, evalOne w k = true → ∃ x : α, P x ∧ k x = true)
    {chunks : BTree Nat} {k : BTree (BTree α) → Bool}
    (h : decodeWForestFast slotShift wordMask evalOne chunks k = true) :
    ∃ dict : BTree (BTree α), ValidBoxTree (ValidBoxTree P) dict ∧ k dict = true := by
  unfold decodeWForestFast at h
  induction chunks generalizing k with
  | empty => exact ⟨.empty, trivial, h⟩
  | node s _ _ ihl ihr =>
    dsimp only at h
    obtain ⟨ch, hch, hl_in⟩ := decodeWChunkK_sound heval (nat_lit 16) h
    obtain ⟨fl, hfl, hr_in⟩ := ihl hl_in
    obtain ⟨fr, hfr, hk⟩ := ihr hr_in
    exact ⟨.node ch fl fr, ⟨hch, hfl, hfr⟩, hk⟩

/-- Lookup `wid` (`wid >>> 4` outer chunk, `wid &&& 15` inner slot) in a 16-word Braun forest. -/
noncomputable def forest16WithFast {α : Type} (f : BTree (BTree α)) (idx : Nat)
    (k : α → Bool) : Bool :=
  bTreeWithGetFast (fun sub => bTreeWithGetFast k sub (Nat.land idx (nat_lit 15)))
    f (Nat.shiftRight idx (nat_lit 4))

theorem forest16WithFast_sound {α : Type} {P : α → Prop} {f : BTree (BTree α)}
    (hf : ValidBoxTree (ValidBoxTree P) f) {idx : Nat} {k : α → Bool}
    (h : forest16WithFast f idx k = true) :
    ∃ v : α, P v ∧ k v = true := by
  unfold forest16WithFast at h
  rw [bTreeWithGetFast_eq] at h
  rcases hsub : BTree.get? f (Nat.shiftRight idx (nat_lit 4)) with _ | sub <;> rw [hsub] at h
  · cases h
  · dsimp only at h
    rw [bTreeWithGetFast_eq] at h
    rcases hv : BTree.get? sub (Nat.land idx (nat_lit 15)) with _ | v <;> rw [hv] at h
    · cases h
    · exact ⟨v, (hf.get? hsub).get? hv, h⟩

/-! ### Packed Quadtree Stream Chunks (`<= 1,900` Bits/Literal) -/

/-- Bounded-literal preorder quadtree stream chunk (`<= 1,900` bits per `.bits` literal). -/
inductive QStreamChunk where
  | bits (s : Nat) : QStreamChunk
  | quad (c00 c01 c10 c11 : QStreamChunk) : QStreamChunk

/-! ### Stage-1 Box-Free Stream Evaluator & Pure-`Init` `Stage1SquareCov` -/

/-- Pure-`Init` covering witness for a Stage-1 cell `[x0, x0+w] × [y0, y0+w]`. -/
def Stage1CellWitness (x0 y0 w : Nat) : Prop :=
  ∀ reqPar : Nat, reqPar < 2 →
    ∃ wd : Nat, ∃ bx : Box2DS, ∃ s : Nat,
      ((isFuseOutWord wd = true ∧ (s / 2) % 2 = reqPar ∧ checkWord2BitBox 28 wd bx = true) ∨
       checkWord2BitBox 26 wd bx = true) ∧
      checkDetBox x0 y0 w 13456 1000000000000 bx s = true

/--
Pure-`Init` quadtree coverage tree for Stage 1 (`rIn^2 = 1020100 / 10^8`, `rOut^2 = 13456 / 10^12`
).
-/
inductive Stage1SquareCov : Nat → Nat → Nat → Prop where
  | out {x0 y0 w : Nat} :
      isOutsideDom 1 x0 y0 w 1020100 100000000 = true →
      Stage1SquareCov x0 y0 w
  | leaf {x0 y0 w : Nat} :
      Stage1CellWitness x0 y0 w →
      Stage1SquareCov x0 y0 w
  | branch {x0 y0 w : Nat} :
      Nat.mod w 2 = 0 →
      2 ≤ w →
      Stage1SquareCov x0 y0 (Nat.div w 2) →
      Stage1SquareCov x0 (Nat.add y0 (Nat.div w 2)) (Nat.div w 2) →
      Stage1SquareCov (Nat.add x0 (Nat.div w 2)) y0 (Nat.div w 2) →
      Stage1SquareCov (Nat.add x0 (Nat.div w 2)) (Nat.add y0 (Nat.div w 2)) (Nat.div w 2) →
      Stage1SquareCov x0 y0 w

/--
Autonomous Stage-1 shard tree combining `.out` , local `(wChunks, stream)` units, and `.branch` .
-/
inductive Stage1Tree where
  | out : Stage1Tree
  | unit (wChunks : BTree Nat) (stream : QStreamChunk) : Stage1Tree
  | branch (t00 t01 t10 t11 : Stage1Tree) : Stage1Tree

/-- CPS WHNF-forcing combinator for `Box2DS` so `let`-bound vertices are never zeta-duplicated. -/
noncomputable def forceBox2DSK (b : Box2DS) (k : Box2DS → Bool) : Bool :=
  @Box2DS.rec (fun _ => Bool) (fun x0 x1 y0 y1 =>
    forceSIntCBV x0 (fun x0' =>
      forceSIntCBV x1 (fun x1' =>
        forceSIntCBV y0 (fun y0' =>
          forceSIntCBV y1 (fun y1' =>
            k (Box2DS.mk x0' x1' y0' y1')))))) b

theorem forceBox2DSK_eq (b : Box2DS) (k : Box2DS → Bool) :
    forceBox2DSK b k = k b := by
  cases b <;> simp only [forceBox2DSK, forceSIntCBV_eq]

/-- `SInt.sLe` on two non-negative `SInt`s reduces to `Nat.ble`. -/
theorem sLe_false_false_eq_ble (a b : Nat) :
    sLe (SInt.mk false a) (SInt.mk false b) = Nat.ble a b := by
  unfold sLe sSub sNeg sAdd
  dsimp only
  cases h : Nat.ble a b
  · have hnotle : ¬ a ≤ b := fun hle => Bool.noConfusion (h.symm.trans (Nat.ble_eq.mpr hle))
    have hne : a - b ≠ 0 := by omega
    exact Bool.eq_false_iff.mpr (fun hb => hne (Nat.beq_eq.mp hb))
  · rfl

/-- `sintMax` of two `sAbs` values is always non-negative (`SInt.mk false m`). -/
theorem sintMax_sAbs_eq_mk (a b : SInt) :
    ∃ m : Nat, sintMax (sAbs a) (sAbs b) = SInt.mk false m := by
  unfold sintMax sAbs
  cases sLe ⟨false, a.mag⟩ ⟨false, b.mag⟩
  · exact ⟨a.mag, rfl⟩
  · exact ⟨b.mag, rfl⟩

/-- `Nat.ble (a + 1) (b + 1) = Nat.ble a b` in pure `Init`. -/
theorem ble_add_one_eq (a b : Nat) :
    Nat.ble (Nat.add a 1) (Nat.add b 1) = Nat.ble a b := by
  change Nat.ble (a + 1) (b + 1) = Nat.ble a b
  rw [Bool.eq_iff_iff, Nat.ble_eq, Nat.ble_eq]
  omega

/-- `2^52` (`boxScaleS.mag`) kept opaque as a `def` during symbolic equivalence proofs. -/
def bsMag : Nat := nat_lit 4503599627370496

/-- `SInt.mk false 2^52` constant for `sMulFast` without materializing `2^104` in ASTs. -/
def bsSInt : SInt := SInt.mk false (nat_lit 4503599627370496)

/--
`2^104 - 1` (`low64 != 0`) kept opaque during symbolic equivalence proofs and GMP-reduced on closed
leaves.
-/
def two104Sub1 : Nat := nat_lit 20282409603651670423947251286015

/-- `10^18` constant kept opaque during symbolic equivalence proofs. -/
def ten18Nat : Nat := nat_lit 1000000000000000000

theorem two104Sub1_add_one :
    Nat.add two104Sub1 1 = Nat.mul bsMag bsMag := rfl

theorem sMul_boxScaleS :
    sMul boxScaleS boxScaleS = SInt.mk false (Nat.mul bsMag bsMag) := rfl

theorem ten18Nat_mul :
    Nat.mul 1000000000 1000000000 = ten18Nat := rfl

theorem mul_two104Sub1_add (p : Nat) :
    Nat.add (Nat.mul p two104Sub1) p = Nat.mul p (Nat.mul bsMag bsMag) := by
  change p * two104Sub1 + p = p * (bsMag * bsMag)
  rw [← Nat.mul_succ p two104Sub1]
  exact congrArg (Nat.mul p) two104Sub1_add_one

theorem sAdd_mk_false (a b : Nat) :
    sAdd (SInt.mk false a) (SInt.mk false b) = SInt.mk false (Nat.add a b) := rfl

theorem sMul_mk_false (a b : Nat) :
    sMul (SInt.mk false a) (SInt.mk false b) = SInt.mk false (Nat.mul a b) := rfl

theorem sPos_mk_false_eq (m : Nat) :
    sPos (SInt.mk false m) = !Nat.beq m 0 := rfl

theorem sPos_mk_true_eq (m : Nat) :
    sPos (SInt.mk true m) = false := rfl

/--
CPS-forced `checkDetBoxFast` avoiding both sub-DAG duplication and `2^104` (`low64 == 0`) WHNF
collisions.
-/
noncomputable def checkDetBoxForced (x0 y0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS)
    (sym : Nat) : Bool :=
  @Bool.rec (fun _ => Bool) false
    (forceNatCBV (Nat.add x0 w) (fun x1 =>
      forceNatCBV (Nat.add y0 w) (fun y1 =>
        forceBox2DSK (applyD8BoxFast rawBox sym) (fun wb =>
          @Box2DS.rec (fun _ => Bool) (fun wx0 wx1 wy0 wy1 =>
            let x0s := SInt.mk false x0
            let x1s := SInt.mk false x1
            let y0s := SInt.mk false y0
            let y1s := SInt.mk false y1
            let bsSq := sMulFast bsSInt bsSInt
            forceSIntCBV
              (sAddFast (sAddFast bsSq (sMin4Fast (sMulFast x0s wx0) (sMulFast x0s wx1)
                  (sMulFast x1s wx0) (sMulFast x1s wx1)))
                        (sMin4Fast (sMulFast y0s wy0) (sMulFast y0s wy1) (sMulFast y1s wy0)
                            (sMulFast y1s wy1)))
              (fun dotMin =>
                @Bool.rec (fun _ => Bool) false
                  (forceSIntCBV (sintMaxFast (sAbsFast (sSubFast x0s wx1))
                      (sAbsFast (sSubFast x1s wx0))) (fun dxMax =>
                    forceSIntCBV (sintMaxFast (sAbsFast (sSubFast y0s wy1))
                        (sAbsFast (sSubFast y1s wy0))) (fun dyMax =>
                      forceNatCBV (Nat.mul (Nat.add (Nat.mul dxMax.mag dxMax.mag)
                          (Nat.mul dyMax.mag dyMax.mag)) rScaleSq) (fun lhsPre =>
                        let lhsPlus1 :=
                            Nat.add (Nat.add (Nat.mul lhsPre two104Sub1) lhsPre) (nat_lit 1)
                        let rhsPlus1 :=
                            Nat.add (Nat.mul rNumSq (Nat.mul dotMin.mag dotMin.mag)) (nat_lit 1)
                        Nat.ble lhsPlus1 rhsPlus1))))
                  (sPosFast dotMin)))
            wb))))
    (Nat.blt sym (nat_lit 8))

theorem checkDetBoxForced_eq (x0 y0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS) (sym : Nat) :
    checkDetBoxForced x0 y0 w rNumSq rScaleSq rawBox sym =
        checkDetBox x0 y0 w rNumSq rScaleSq rawBox sym := by
  unfold checkDetBoxForced checkDetBox
  rw [show Nat.blt sym (nat_lit 8) = Nat.blt sym 8 from rfl]
  cases Nat.blt sym 8
  · rfl
  · simp only [Bool.true_and, forceNatCBV_eq, forceBox2DSK_eq, applyD8BoxFast_eq]
    rcases applyD8Box rawBox sym with ⟨wx0, wx1, wy0, wy1⟩
    simp only [forceSIntCBV_eq, show sMulFast bsSInt bsSInt =
        sMul boxScaleS boxScaleS from rfl,
      sAddFast_eq, sSubFast_eq, sMulFast_eq, sAbsFast_eq,
      sMin4Fast_eq, sintMaxFast_eq2, sPosFast_eq, bool_rec_false_eq_and]
    obtain ⟨_, hdx⟩ := sintMax_sAbs_eq_mk (sSub ⟨false, x0⟩ wx1) (sSub ⟨false, Nat.add x0 w⟩ wx0)
    obtain ⟨_, hdy⟩ := sintMax_sAbs_eq_mk (sSub ⟨false, y0⟩ wy1) (sSub ⟨false, Nat.add y0 w⟩ wy0)
    rw [hdx, hdy]
    rcases sAdd (sAdd (sMul boxScaleS boxScaleS) _) _ with ⟨_ | _, m_dm⟩
    · rw [sPos_mk_false_eq]
      cases Nat.beq m_dm 0 <;> simp only [Bool.not_false, Bool.not_true, Bool.true_and,
          Bool.false_and,
        sMul_boxScaleS, sMul_mk_false, sAdd_mk_false, sLe_false_false_eq_ble, ble_add_one_eq,
            mul_two104Sub1_add]
    · simp only [sPos_mk_true_eq, Bool.false_and]

/-! ### Stage-2 Box-Free Simplicial Stream Evaluator & Pure-`Init` `Stage2SquareCov` -/

/--
Pure-`Init` covering witness for a Stage-2 cell `[x0, x0+w] × [y0, y0+w]` parameterized by
`(epPair, rVert)` .
-/
def Stage2CellWitness (epPair _rVert x0 y0 w : Nat) : Prop :=
  1 ≤ w ∧
  ∃ wd0 wd1 wd2 : Nat, ∃ raw0 raw1 raw2 : Box2DS, ∃ s0 s1 s2 : Nat,
    checkWord2BitBox 45 wd0 raw0 = true ∧
    checkWord2BitBox 45 wd1 raw1 = true ∧
    checkWord2BitBox 45 wd2 raw2 = true ∧
    let v0 := applyD8Box raw0 s0
    let v1 := applyD8Box raw1 s1
    let v2 := applyD8Box raw2 s2
    checkLagrangeBox v0 v1 epPair 1000000000 = true ∧
    checkLagrangeBox v0 v2 epPair 1000000000 = true ∧
    checkLagrangeBox v1 v2 epPair 1000000000 = true ∧
    checkCornerEncl ⟨false, x0⟩ ⟨false, y0⟩ v0 v1 v2 = true ∧
    checkCornerEncl ⟨false, x0⟩ ⟨false, Nat.add y0 w⟩ v0 v1 v2 = true ∧
    checkCornerEncl ⟨false, Nat.add x0 w⟩ ⟨false, y0⟩ v0 v1 v2 = true ∧
    checkCornerEncl ⟨false, Nat.add x0 w⟩ ⟨false, Nat.add y0 w⟩ v0 v1 v2 = true

/-- Pure-`Init` quadtree coverage tree for Stage 2 (`rIn^2 = 13456 / 10^12`). -/
inductive Stage2SquareCov (epPair rVert : Nat) : Nat → Nat → Nat → Prop where
  | out {x0 y0 w : Nat} :
      isOutsideDom 2 x0 y0 w 13456 1000000000000 = true →
      Stage2SquareCov epPair rVert x0 y0 w
  | leaf {x0 y0 w : Nat} :
      Stage2CellWitness epPair rVert x0 y0 w →
      Stage2SquareCov epPair rVert x0 y0 w
  | branch {x0 y0 w : Nat} :
      Nat.mod w 2 = 0 →
      2 ≤ w →
      Stage2SquareCov epPair rVert x0 y0 (Nat.div w 2) →
      Stage2SquareCov epPair rVert x0 (Nat.add y0 (Nat.div w 2)) (Nat.div w 2) →
      Stage2SquareCov epPair rVert (Nat.add x0 (Nat.div w 2)) y0 (Nat.div w 2) →
      Stage2SquareCov epPair rVert (Nat.add x0 (Nat.div w 2)) (Nat.add y0 (Nat.div w 2))
          (Nat.div w 2) →
      Stage2SquareCov epPair rVert x0 y0 w

/--
Autonomous Stage-2 shard tree combining `.out` , local `(wChunks, stream)` units, and `.branch` .
-/
inductive Stage2Tree where
  | out : Stage2Tree
  | unit (wChunks : BTree Nat) (stream : QStreamChunk) : Stage2Tree
  | branch (t00 t01 t10 t11 : Stage2Tree) : Stage2Tree

/--
CPS-forced `checkLagrangeBox1e9Fast` avoiding `2^104` (`low64 == 0`) WHNF bucket-0 collisions.
-/
noncomputable def checkLagrangeBox1e9Forced (a b : Box2DS) (capNumSq : Nat) : Bool :=
  @Box2DS.rec (fun _ => Bool) (fun ax0 ax1 ay0 ay1 =>
    @Box2DS.rec (fun _ => Bool) (fun bx0 bx1 by0 by1 =>
      forceSIntCBV (sintMaxFast (sAbsFast ax0) (sAbsFast ax1)) (fun axAbs =>
        forceSIntCBV (sintMaxFast (sAbsFast ay0) (sAbsFast ay1)) (fun ayAbs =>
          forceSIntCBV (sintMaxFast (sAbsFast bx0) (sAbsFast bx1)) (fun bxAbs =>
            forceSIntCBV (sintMaxFast (sAbsFast by0) (sAbsFast by1)) (fun byAbs =>
              let bsSq := sMulFast bsSInt bsSInt
              forceSIntCBV (sSubFast (sSubFast bsSq (sMulFast axAbs bxAbs)) (sMulFast ayAbs byAbs))
                  (fun dotLo =>
                @Bool.rec (fun _ => Bool) false
                  (forceSIntCBV (sintMaxFast (sAbsFast (sSubFast ax0 bx1))
                      (sAbsFast (sSubFast ax1 bx0))) (fun dxMax =>
                    forceSIntCBV (sintMaxFast (sAbsFast (sSubFast ay0 by1))
                        (sAbsFast (sSubFast ay1 by0))) (fun dyMax =>
                      forceNatCBV (Nat.add (Nat.mul dxMax.mag dxMax.mag)
                          (Nat.mul dyMax.mag dyMax.mag)) (fun distSqMag =>
                        let imUbMag :=
                            Nat.add (Nat.mul ayAbs.mag bxAbs.mag) (Nat.mul axAbs.mag byAbs.mag)
                        let numMag := Nat.add
                          (Nat.add (Nat.mul distSqMag two104Sub1)
                                   (Nat.mul imUbMag imUbMag))
                          distSqMag
                        Nat.ble (Nat.mul numMag ten18Nat)
                                (Nat.mul capNumSq (Nat.mul dotLo.mag dotLo.mag))))))
                  (sPosFast dotLo)))))))
      b)
    a

/--
Algebraic identity for `checkLagrangeBox1e9Forced` numerator avoiding `d * 2^104` WHNF literals.
-/
theorem lagrange_num_id (d j : Nat) :
    Nat.add (Nat.add (Nat.mul d two104Sub1) j) d =
      Nat.add (Nat.mul d (Nat.mul bsMag bsMag)) j := by
  change d * two104Sub1 + j + d = d * (bsMag * bsMag) + j
  rw [Nat.add_right_comm, show d * two104Sub1 + d = d * (bsMag * bsMag) from mul_two104Sub1_add d]

theorem checkLagrangeBox1e9Forced_eq (a b : Box2DS) (capNum capNumSq : Nat)
    (hSq : capNumSq = Nat.mul capNum capNum) :
    checkLagrangeBox1e9Forced a b capNumSq = checkLagrangeBox a b capNum 1000000000 := by
  rcases a with ⟨ax0, ax1, ay0, ay1⟩
  rcases b with ⟨bx0, bx1, by0, by1⟩
  unfold checkLagrangeBox1e9Forced checkLagrangeBox
  simp only [forceSIntCBV_eq, forceNatCBV_eq, show sMulFast bsSInt bsSInt =
      sMul boxScaleS boxScaleS from rfl,
    sSubFast_eq, sMulFast_eq, sAbsFast_eq, sintMaxFast_eq2, sPosFast_eq,
        bool_rec_false_eq_and]
  rcases sintMax_sAbs_eq_mk ax0 ax1, sintMax_sAbs_eq_mk ay0 ay1,
      sintMax_sAbs_eq_mk bx0 bx1, sintMax_sAbs_eq_mk by0 by1,
      sintMax_sAbs_eq_mk (sSub ax0 bx1) (sSub ax1 bx0),
      sintMax_sAbs_eq_mk (sSub ay0 by1) (sSub ay1 by0) with
    ⟨⟨m_ax, hax⟩, ⟨m_ay, hay⟩, ⟨m_bx, hbx⟩, ⟨m_by, hby⟩, ⟨_, hdx⟩, ⟨_, hdy⟩⟩
  rw [hax, hay, hbx, hby, hdx, hdy]
  rcases sSub (sSub (sMul boxScaleS boxScaleS) (sMul ⟨false, m_ax⟩ ⟨false, m_bx⟩))
      (sMul ⟨false, m_ay⟩ ⟨false, m_by⟩) with ⟨_ | _, m_dl⟩
  · rw [sPos_mk_false_eq]
    cases Nat.beq m_dl 0 <;> simp only [Bool.not_false, Bool.not_true, Bool.true_and,
      Bool.false_and, ← hSq, ten18Nat_mul, sMul_boxScaleS, sMul_mk_false, sAdd_mk_false,
      sLe_false_false_eq_ble, lagrange_num_id]
  · simp only [sPos_mk_true_eq, Bool.false_and]

/--
Joint 4-corner triangle enclosure check sharing the 24 vertex-minus-corner `SInt` differences across
all 12 cross products.
-/
noncomputable def checkAllCornersEnclForced (x0s x1s y0s y1s : SInt) (v0 v1 v2 : Box2DS) : Bool :=
  @Bool.rec (fun _ => Bool) false
    (@Bool.rec (fun _ => Bool) false
      (@Bool.rec (fun _ => Bool) false
        (checkCornerEnclFast x1s y1s v0 v1 v2)
        (checkCornerEnclFast x1s y0s v0 v1 v2))
      (checkCornerEnclFast x0s y1s v0 v1 v2))
    (checkCornerEnclFast x0s y0s v0 v1 v2)

theorem checkAllCornersEnclForced_eq (x0s x1s y0s y1s : SInt) (v0 v1 v2 : Box2DS) :
    checkAllCornersEnclForced x0s x1s y0s y1s v0 v1 v2 =
      (checkCornerEncl x0s y0s v0 v1 v2 &&
       checkCornerEncl x0s y1s v0 v1 v2 &&
       checkCornerEncl x1s y0s v0 v1 v2 &&
       checkCornerEncl x1s y1s v0 v1 v2) := by
  simp only [checkAllCornersEnclForced, bool_rec_false_eq_and, Bool.and_assoc,
      checkCornerEnclFast_eq]

/-! ### Stage-1 Hadamard Lookup Tables & Certificates -/

def w0_stg1Had_0 : BTree Nat :=
  (f6 ~0x0 ~0x100b1 ~0x5341 ~0x4031 ~0x11521 ~0x11051 ~0x15521 ~0x7b1
      ~0x10541 ~0x121 ~0x44071 ~0x441 ~0x4021 ~0x0 ~0x0 ~0x0)

def b0_stg1Had_0 : BTree Nat :=
  (f6 ~0x800000000000080000000000000 ~0x766c0848b175ba4ab2deecbf885
      ~0x5f4c7575a43459327ef6e9d1485 ~0x3af186061d6576bc618187595d5
      ~0x5ac10db8eb0755ec8adebf55115 ~0x5d78c3030eb2b40de18d840ec85
      ~0x42a1dbc8fa5abc1baa078c0ed05 ~0x3504f333f9de6cafb0ccc062195
      ~0x2d92fd8127852a3f2c9ad778805 ~0x15f619980c43380000000000004
      ~0xa8ae49a20fb560105ac12a668f5 ~0x2aaaaaaaaaaaa07520888041665
      ~0xa0b38a8a5bcba6cd8109162eb75 ~0x800000000000080000000000000
      ~0x800000000000080000000000000 ~0x800000000000080000000000000)

def stageQTree0Stg1Had : QTree Nat :=
  (qb (qb (q4 ~0x0 ~0xe ~0x9 ~0x11) (qb qo qo (ql ~0xe) qo)
          (qb (ql ~0x9) (ql ~0x9) (q4 ~0x8 ~0x9 ~0x1b ~0x1b) (ql ~0x1b))
          (q4 ~0x23 ~0x2b ~0x2c ~0x31))
      (qb qo qo (qb qo qo (ql ~0x39) qo) qo)
      (qb (qb (ql ~0x1b) (ql ~0x46) (q4 ~0x4b ~0x46 ~0x4b ~0x4b) (ql ~0x46))
          (qb (ql ~0x46) (ql ~0x39) (ql ~0x46) (q4 ~0x46 ~0x39 ~0x46 ~0x39))
          (qb (ql ~0x4b) (q4 ~0x4b ~0x46 ~0x4b ~0x55) qo qo)
          (qb (qb (ql ~0x46) (ql ~0x46) (ql ~0x55) qo)
              (qb (ql ~0x46)
                  (qb (q4 ~0x39 ~0x39 ~0x46 ~0x39) (ql ~0x39)
                      (qb (ql ~0x46)
                          (qb (ql ~0x46) (ql ~0x39) (ql ~0x55)
                              (qb (qb (ql ~0x46) (q4 ~0x39 ~0x39 ~0x5c ~0x39) qo qo)
                                  (ql ~0x5c) qo qo))
                          qo qo)
                      (qb (qb (ql ~0x39) (ql ~0x39) (ql ~0x5c) qo) (ql ~0x39) qo qo))
                  qo qo)
              qo qo))
      (qb (q4 ~0x39 ~0x39 ~0x39 ~0x39) (qb qo qo (ql ~0x5b) qo)
          (qb (qb (qb (ql ~0x39) (ql ~0x39) (ql ~0x5c) qo) (ql ~0x39) qo qo) (ql ~0x5c) qo qo)
          qo))

def isFuseInWord (w : Nat) : Bool :=
  (!Nat.beq w 0) && Nat.beq (Nat.mod w 16) 1 && Nat.ble 4 (Nat.div w 256)

def checkWord0CapPacked (capFi capNoFi w pb : Nat) : Bool :=
  (isFuseInWord w && checkWord2BitPacked capFi 2251799813685248 4503599627370496 w pb) ||
  checkWord2BitPacked capNoFi 2251799813685248 4503599627370496 w pb

def stageWords0Stg1Had : BTree (BTree Nat) := lf w0_stg1Had_0
def stageBoxes0Stg1Had : BTree (BTree Nat) := lf b0_stg1Had_0

theorem stageWords0Stg1Had_ok :
    BTree.all2 (BTree.all2 (checkWord0CapPacked 5 3)) stageWords0Stg1Had stageBoxes0Stg1Had =
        true := by
  decide +kernel

theorem qt0_stg1Had_chunk_intro {boxes : BTree (BTree Nat)} {t : QTree Nat} {x0 y0 w : Nat}
    (h : checkDetQTreeFast 0 2251799813685248 52 4503599627370495 0 1 1020100 100000000 boxes t x0
        y0 w = true) :
    checkDetQTree 0 2251799813685248 4503599627370496 0 1 1020100 100000000 boxes t x0 y0 w =
        true := by
  rwa [checkDetQTreeFast_eq 0 2251799813685248 52 4503599627370495 4503599627370496 (by decide)
      (by decide)] at h

theorem stageQTree0Stg1Had_ok :
    checkDetQTree 0 2251799813685248 4503599627370496 0 1 1020100 100000000
      stageBoxes0Stg1Had stageQTree0Stg1Had 0 0 2251799813685248 = true :=
  qt0_stg1Had_chunk_intro (by decide +kernel)

/-! ### Direct 1D `c_top` Prefix (`tCap = 28`, `tTop = 73 T`) Stream Evaluator & Soundness -/

def checkDetBox1D (x0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS) (sym : Nat) : Bool :=
  Nat.blt sym 8 &&
  let wb := applyD8Box rawBox sym
  let x0s : SInt := ⟨false, x0⟩
  let x1s : SInt := ⟨false, Nat.add x0 w⟩
  let bsSq := sMul boxScaleS boxScaleS
  let dotMin :=
      sAdd bsSq (sMin4 (sMul x0s wb.x0) (sMul x0s wb.x1) (sMul x1s wb.x0) (sMul x1s wb.x1))
  sPos dotMin &&
  let dxMax := sintMax (sAbs (sSub x0s wb.x1)) (sAbs (sSub x1s wb.x0))
  let dyMax := sintMax (sAbs wb.y1) (sAbs wb.y0)
  sLe (sMul (sMul (sAdd (sMul dxMax dxMax) (sMul dyMax dyMax)) ⟨false, rScaleSq⟩) bsSq)
      (sMul ⟨false, rNumSq⟩ (sMul dotMin dotMin))

noncomputable def checkDetBox1DFast (x0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS)
    (sym : Nat) : Bool :=
  @Bool.rec (fun _ => Bool) false
    (@Box2DS.rec (fun _ => Bool) (fun wx0 wx1 wy0 wy1 =>
      forceSIntCBV (SInt.mk false (Nat.add x0 w)) (fun x1s =>
        let x0s := SInt.mk false x0
        let bs := SInt.mk false (nat_lit 4503599627370496)
        forceSIntCBV (sMulFast bs bs) (fun bsSq =>
          forceSIntCBV
            (sAddFast bsSq
              (sMin4Fast (sMulFast x0s wx0) (sMulFast x0s wx1) (sMulFast x1s wx0)
                  (sMulFast x1s wx1)))
            (fun dotMin =>
              @Bool.rec (fun _ => Bool) false
                (forceSIntCBV
                  (sintMaxFast (sAbsFast (sSubFast x0s wx1)) (sAbsFast (sSubFast x1s wx0)))
                  (fun dxMax =>
                    forceSIntCBV
                      (sintMaxFast (sAbsFast wy1) (sAbsFast wy0))
                      (fun dyMax =>
                        sLeFast (sMulFast (sMulFast (sAddFast (sMulFast dxMax dxMax)
                            (sMulFast dyMax dyMax))
                                                    (SInt.mk false rScaleSq)) bsSq)
                                (sMulFast (SInt.mk false rNumSq) (sMulFast dotMin dotMin)))))
                (sPosFast dotMin)))))
      (applyD8BoxFast rawBox sym))
    (Nat.blt sym (nat_lit 8))

theorem checkDetBox1DFast_eq (x0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS) (sym : Nat) :
    checkDetBox1DFast x0 w rNumSq rScaleSq rawBox sym =
      checkDetBox1D x0 w rNumSq rScaleSq rawBox sym := by
  unfold checkDetBox1DFast checkDetBox1D
  rw [applyD8BoxFast_eq]
  rcases applyD8Box rawBox sym with ⟨_, _, _, _⟩
  dsimp only
  rw [show Nat.blt sym (nat_lit 8) = Nat.blt sym 8 from rfl]
  simp only [forceSIntCBV_eq, show SInt.mk false (nat_lit 4503599627370496) = boxScaleS from rfl,
    bool_rec_false_eq_and, sAddFast_eq, sSubFast_eq, sMulFast_eq, sAbsFast_eq, sMin4Fast_eq,
        sintMaxFast_eq2, sPosFast_eq, sLeFast_eq]

/-- Certified 1D `c_top` prefix box (`tCap = 28 => tTop = 45 + 28 = 73 T`). -/
def ValidTop1DBox (bx : Box2DS) : Prop :=
  ∃ wd : Nat, checkWord2BitBox 28 wd bx = true

/--
Pure-`Init` covering witness for a 1D equator segment `[x0, x0+w]` into Stage-2 disk `13456 / 10^12`
.
-/
def Top1DCellWitness (x0 w : Nat) : Prop :=
  ∃ wd : Nat, ∃ bx : Box2DS, ∃ s : Nat,
    checkWord2BitBox 28 wd bx = true ∧
    checkDetBox1D x0 w 13456 1000000000000 bx s = true

/-- Pure-`Init` binary segment coverage tree for `[0, 1/2]` (`[0, 2251799813685248]`). -/
inductive Top1DSegCov : Nat → Nat → Prop where
  | leaf {x0 w : Nat} : Top1DCellWitness x0 w → Top1DSegCov x0 w
  | branch {x0 w : Nat} :
      Nat.mod w 2 = 0 →
      2 ≤ w →
      Top1DSegCov x0 (Nat.div w 2) →
      Top1DSegCov (Nat.add x0 (Nat.div w 2)) (Nat.div w 2) →
      Top1DSegCov x0 w

/--
Bounded-literal binary segment stream chunk (`<= 1,850` bits per `.bits` literal, `0` `low64 == 0`
shifts).
-/
inductive SegStreamChunk where
  | bits (s : Nat) : SegStreamChunk
  | split (l r : SegStreamChunk) : SegStreamChunk

abbrev ssb : Nat → SegStreamChunk := .bits
abbrev sss : SegStreamChunk → SegStreamChunk → SegStreamChunk := .split

/-- Autonomous 1D `c_top` tree combining local `(wChunks, stream)` units and `.branch`. -/
inductive Top1DTree where
  | unit (wChunks : BTree Nat) (stream : SegStreamChunk) : Top1DTree
  | branch (l r : Top1DTree) : Top1DTree

abbrev t1u : BTree Nat → SegStreamChunk → Top1DTree := .unit
abbrev t1b : Top1DTree → Top1DTree → Top1DTree := .branch

noncomputable def checkTop1DLeafFast (dict : BTree (BTree Box2DS)) (x0 w pay12 : Nat) : Bool :=
  let sym := Nat.land pay12 (nat_lit 7)
  let wid := Nat.shiftRight pay12 (nat_lit 3)
  forest16WithFast dict wid (fun bx =>
    checkDetBox1DFast x0 w (nat_lit 13456) (nat_lit 1000000000000) bx sym)

theorem checkTop1DLeafFast_sound {dict : BTree (BTree Box2DS)}
    (hdict : ValidBoxTree (ValidBoxTree ValidTop1DBox) dict)
    {x0 w pay12 : Nat} (h : checkTop1DLeafFast dict x0 w pay12 = true) :
    Top1DCellWitness x0 w := by
  obtain ⟨bx, ⟨wd, hwd⟩, hdet⟩ := forest16WithFast_sound hdict h
  rw [checkDetBox1DFast_eq] at hdet
  exact ⟨wd, bx, Nat.land pay12 (nat_lit 7), hwd, hdet⟩

/--
Preorder 1D segment `.bits` evaluator (`0b10` 2-bit branch, `0b11` + 12-bit `(wid <<< 3) ||| sym` =
14-bit leaf).
-/
noncomputable def evalTop1DStreamK (dict : BTree (BTree Box2DS)) :
    Nat → Nat → Nat → Nat → (Nat → Bool) → Bool :=
  @Nat.rec (fun _ => Nat → Nat → Nat → (Nat → Bool) → Bool)
    (fun _ _ _ _ => false)
    (fun _ ih x0 w s k =>
      let low := Nat.land s (nat_lit 0x3FFF)
      let tag := Nat.land low (nat_lit 3)
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          false
          (@Bool.rec (fun _ => Bool) false
            (k (Nat.shiftRight s (nat_lit 14)))
            (checkTop1DLeafFast dict x0 w (Nat.shiftRight low (nat_lit 2))))
          (Nat.beq tag (nat_lit 3)))
        (@Bool.rec (fun _ => Bool) false
          (@Bool.rec (fun _ => Bool) false
            (let hw := Nat.shiftRight w (nat_lit 1)
             ih x0 hw (Nat.shiftRight s (nat_lit 2)) (fun s1 =>
               ih (Nat.add x0 hw) hw s1 k))
            (Nat.ble (nat_lit 2) w))
          (Nat.beq (Nat.land w (nat_lit 1)) (nat_lit 0)))
        (Nat.beq tag (nat_lit 2)))

theorem segSplit2_sound {fl fr : Nat → Nat → Bool} {x0 w : Nat}
    (ihl : ∀ {x u}, fl x u = true → Top1DSegCov x u)
    (ihr : ∀ {x u}, fr x u = true → Top1DSegCov x u)
    (h : @Bool.rec (fun _ => Bool) false
      (@Bool.rec (fun _ => Bool) false
        (let hw := Nat.shiftRight w (nat_lit 1)
         @Bool.rec (fun _ => Bool) false (fr (Nat.add x0 hw) hw) (fl x0 hw))
        (Nat.ble (nat_lit 2) w))
      (Nat.beq (Nat.land w (nat_lit 1)) (nat_lit 0)) = true) :
    Top1DSegCov x0 w := by
  simp only [bool_rec_false_true_iff,
    show Nat.land w (nat_lit 1) = Nat.mod w 2 from Nat.and_two_pow_sub_one_eq_mod w 1,
    show Nat.shiftRight w (nat_lit 1) = Nat.div w 2 from Nat.shiftRight_eq_div_pow w 1] at h
  rcases h with ⟨hw_par, hw_ge, hl, hr⟩
  exact .branch (Nat.beq_eq.mp hw_par) (Nat.ble_eq.mp hw_ge) (ihl hl) (ihr hr)

theorem evalTop1DStreamK_sound {dict : BTree (BTree Box2DS)}
    (hdict : ValidBoxTree (ValidBoxTree ValidTop1DBox) dict) (fuel : Nat) :
    ∀ {x0 w s : Nat} {k : Nat → Bool},
      evalTop1DStreamK dict fuel x0 w s k = true →
      Top1DSegCov x0 w ∧ ∃ s' : Nat, k s' = true := by
  unfold evalTop1DStreamK
  induction fuel with
  | zero => rintro _ _ _ _ ⟨⟩
  | succ _ ih =>
    intro x0 w s k h
    dsimp only at h
    generalize Nat.land s (nat_lit 0x3FFF) = low at h
    generalize Nat.land low (nat_lit 3) = tag at h
    cases ht2 : Nat.beq tag (nat_lit 2) <;> simp only [ht2, bool_rec_false_true_iff] at h
    · exact ⟨.leaf (checkTop1DLeafFast_sound hdict h.2.1), _, h.2.2⟩
    · rw [show Nat.land w (nat_lit 1) = Nat.mod w 2 from Nat.and_two_pow_sub_one_eq_mod w 1,
        show Nat.shiftRight w (nat_lit 1) = Nat.div w 2 from Nat.shiftRight_eq_div_pow w 1] at h
      rcases h with ⟨hw_par, hw_ge, hrec⟩
      obtain ⟨hl, _, hs1⟩ := ih hrec
      obtain ⟨hr, s', hs'⟩ := ih hs1
      exact ⟨.branch (Nat.beq_eq.mp hw_par) (Nat.ble_eq.mp hw_ge) hl hr, s', hs'⟩

noncomputable def evalTop1DChunk (dict : BTree (BTree Box2DS)) :
    SegStreamChunk → Nat → Nat → Bool :=
  @SegStreamChunk.rec (fun _ => Nat → Nat → Bool)
    (fun s x0 w =>
      evalTop1DStreamK dict (nat_lit 512) x0 w s (fun rem => Nat.beq rem (nat_lit 1)))
    (fun _ _ ihl ihr x0 w =>
      @Bool.rec (fun _ => Bool) false
        (@Bool.rec (fun _ => Bool) false
          (let hw := Nat.shiftRight w (nat_lit 1)
           @Bool.rec (fun _ => Bool) false
             (ihr (Nat.add x0 hw) hw)
             (ihl x0 hw))
          (Nat.ble (nat_lit 2) w))
        (Nat.beq (Nat.land w (nat_lit 1)) (nat_lit 0)))

theorem evalTop1DChunk_sound {dict : BTree (BTree Box2DS)}
    (hdict : ValidBoxTree (ValidBoxTree ValidTop1DBox) dict)
    {chunk : SegStreamChunk} :
    ∀ {x0 w : Nat}, evalTop1DChunk dict chunk x0 w = true → Top1DSegCov x0 w := by
  unfold evalTop1DChunk
  induction chunk with
  | bits _ => exact fun {_ _} h => (evalTop1DStreamK_sound hdict (nat_lit 512) h).1
  | split _ _ ihl ihr => exact fun {_ _} h => segSplit2_sound ihl ihr h

noncomputable def evalWordTop1DFast (w : Nat) (k : Box2DS → Bool) : Bool :=
  evalWordTcBoxFast (nat_lit 28) w (fun _ bx => k bx)

theorem evalWordTop1DFast_sound {w : Nat} {k : Box2DS → Bool}
    (h : evalWordTop1DFast w k = true) :
    ∃ bx : Box2DS, ValidTop1DBox bx ∧ k bx = true := by
  obtain ⟨tc, bx, hle28, hchk, hk⟩ := evalWordTcBoxFast_sound h
  exact ⟨bx, ⟨w, hchk 28 hle28⟩, hk⟩

/-- Top-level pure-`Init` evaluator for a `Top1DTree`. -/
noncomputable def evalTop1DTree : Top1DTree → Nat → Nat → Bool :=
  @Top1DTree.rec (fun _ => Nat → Nat → Bool)
    (fun wChunks stream x0 w =>
      decodeWForestFast (nat_lit 68) (nat_lit 0x3FFFFFFFFFFFFFFFF) evalWordTop1DFast wChunks
        (fun dict => evalTop1DChunk dict stream x0 w))
    (fun _ _ ihl ihr x0 w =>
      @Bool.rec (fun _ => Bool) false
        (@Bool.rec (fun _ => Bool) false
          (let hw := Nat.shiftRight w (nat_lit 1)
           @Bool.rec (fun _ => Bool) false
             (ihr (Nat.add x0 hw) hw)
             (ihl x0 hw))
          (Nat.ble (nat_lit 2) w))
        (Nat.beq (Nat.land w (nat_lit 1)) (nat_lit 0)))

theorem evalTop1DTree_sound {t : Top1DTree} :
    ∀ {x0 w : Nat}, evalTop1DTree t x0 w = true → Top1DSegCov x0 w := by
  unfold evalTop1DTree
  induction t with
  | unit _ _ =>
    intro _ _ h
    obtain ⟨dict, hdict, hc⟩ := decodeWForestFast_sound evalWordTop1DFast_sound h
    exact evalTop1DChunk_sound hdict hc
  | branch _ _ ihl ihr => exact fun {_ _} h => segSplit2_sound ihl ihr h

end QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

end
