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

public import FQCExternal.Vendor.Stream

@[expose] public section

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

set_option exponentiation.threshold 256
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- 16-bit Morton bit-dilation (`< 2^16` to `< 2^32`, pure scalar bit operations). -/
noncomputable def spread16 (u : Nat) : Nat :=
  let x0 := Nat.land u (nat_lit 0xFFFF)
  let x1 := Nat.land (Nat.lor x0 (Nat.shiftLeft x0 (nat_lit 8))) (nat_lit 0x00FF00FF)
  let x2 := Nat.land (Nat.lor x1 (Nat.shiftLeft x1 (nat_lit 4))) (nat_lit 0x0F0F0F0F)
  let x3 := Nat.land (Nat.lor x2 (Nat.shiftLeft x2 (nat_lit 2))) (nat_lit 0x33333333)
  Nat.land (Nat.lor x3 (Nat.shiftLeft x3 (nat_lit 1))) (nat_lit 0x55555555)

/-- Decode a `BTree Nat` of `<= kChunk`-word chunks into `BTree (BTree α)`. -/
noncomputable def decodeWForestKFast {α : Type} (kChunk slotShift wordMask : Nat)
    (evalOne : Nat → (α → Bool) → Bool) :
    BTree Nat → (BTree (BTree α) → Bool) → Bool :=
  @BTree.rec Nat (fun _ => (BTree (BTree α) → Bool) → Bool)
    (fun k => k BTree.empty)
    (fun s _ _ ihl ihr k =>
      decodeWChunkK slotShift wordMask evalOne kChunk s (fun ch =>
        ihl (fun fl =>
          ihr (fun fr =>
            k (BTree.node ch fl fr)))))

theorem decodeWForestKFast_sound {α : Type} {P : α → Prop} {kChunk slotShift wordMask : Nat}
    {evalOne : Nat → (α → Bool) → Bool}
    (heval : ∀ {w : Nat} {k : α → Bool}, evalOne w k = true → ∃ x : α, P x ∧ k x = true)
    {chunks : BTree Nat} {k : BTree (BTree α) → Bool}
    (h : decodeWForestKFast kChunk slotShift wordMask evalOne chunks k = true) :
    ∃ dict : BTree (BTree α), ValidBoxTree (ValidBoxTree P) dict ∧ k dict = true := by
  induction chunks generalizing k with
  | empty => exact ⟨.empty, trivial, h⟩
  | node s _ _ ihl ihr =>
    dsimp only [decodeWForestKFast] at h
    obtain ⟨ch, hch, hl_in⟩ := decodeWChunkK_sound heval kChunk h
    obtain ⟨fl, hfl, hr_in⟩ := ihl hl_in
    obtain ⟨fr, hfr, hk⟩ := ihr hr_in
    exact ⟨.node ch fl fr, ⟨hch, hfl, hfr⟩, hk⟩

/-- Lookup `idx` (`idx / kChunk` outer chunk, `idx % kChunk` inner slot) in a `kChunk`-word Braun forest. -/
noncomputable def forestKWithFast {α : Type} (kChunk : Nat) (f : BTree (BTree α))
    (idx : Nat) (k : α → Bool) : Bool :=
  bTreeWithGetFast (fun sub => bTreeWithGetFast k sub (Nat.mod idx kChunk))
    f (Nat.div idx kChunk)

theorem forestKWithFast_sound {α : Type} {P : α → Prop} {kChunk : Nat} {f : BTree (BTree α)}
    (hf : ValidBoxTree (ValidBoxTree P) f) {idx : Nat} {k : α → Bool}
    (h : forestKWithFast kChunk f idx k = true) :
    ∃ v : α, P v ∧ k v = true := by
  rw [forestKWithFast, bTreeWithGetFast_eq] at h
  cases hsub : BTree.get? f (Nat.div idx kChunk) with
  | none => simp [hsub] at h
  | some sub =>
    simp only [hsub, bTreeWithGetFast_eq] at h
    cases hv : BTree.get? sub (Nat.mod idx kChunk) with
    | none => simp [hv] at h
    | some v => exact ⟨v, (hf.get? hsub).get? hv, by simpa [hv] using h⟩

/-- Chain of `< 2^1900` sentinel-terminated bit-stream words. -/
inductive BitChain where
  | empty : BitChain
  | more (w : Nat) (rest : BitChain) : BitChain

/-- Single-word `BitChain` constructor alias. -/
abbrev bc1 (w : Nat) : BitChain := .more w .empty

/-- Cons-word `BitChain` constructor alias. -/
abbrev bcm : Nat → BitChain → BitChain := .more

/-- Non-empty list of `(x0, y0, w)` sub-cell coordinates in a certificate batch. -/
inductive CellList where
  | one (x0 y0 w : Nat) : CellList
  | more (x0 y0 w : Nat) (rest : CellList) : CellList

/-- Single-cell `CellList` constructor alias. -/
abbrev cl1 : Nat → Nat → Nat → CellList := .one

/-- Cons-cell `CellList` constructor alias. -/
abbrev clm : Nat → Nat → Nat → CellList → CellList := .more

/-- Ensure current stream word `s` has at least one token (`s ≠ 1`), popping `bc` when `s = 1`. -/
noncomputable def withStreamWord (s : Nat) (bc : BitChain)
    (k : Nat → BitChain → Bool) : Bool :=
  @Bool.rec (fun _ => Bool)
    (k s bc)
    (@BitChain.rec (fun _ => Bool)
      false
      (fun wNew rest _ => k wNew rest)
      bc)
    (Nat.beq s (nat_lit 1))

theorem withStreamWord_sound {s : Nat} {bc : BitChain} {k : Nat → BitChain → Bool}
    (h : withStreamWord s bc k = true) : ∃ s1 bc', k s1 bc' = true := by
  unfold withStreamWord at h
  cases hb : Nat.beq s (nat_lit 1)
  · exact ⟨s, bc, by rwa [hb] at h⟩
  · cases bc with
    | empty => simp [hb] at h
    | more wNew rest => exact ⟨wNew, rest, by rwa [hb] at h⟩

/-- Expand a 47-bit compact Stage-2 word into its full `evalWordStage2Fast` word. -/
noncomputable def expandStage2Word (cw : Nat) : Nat :=
  let b0 := Nat.land cw (nat_lit 1)
  let lo8 := Nat.add (nat_lit 0x41) (Nat.mul b0 (nat_lit 0x50))
  let s0 := Nat.land (Nat.shiftRight cw (nat_lit 1)) (nat_lit 3)
  let lo10 := Nat.lor lo8 (Nat.shiftLeft s0 (nat_lit 8))
  let b44 := Nat.shiftRight cw (nat_lit 3)
  let c0 := spread16 b44
  let c1 := spread16 (Nat.shiftRight b44 (nat_lit 16))
  let c2 := spread16 (Nat.shiftRight b44 (nat_lit 32))
  let low42 := Nat.lor lo10 (Nat.shiftLeft c0 (nat_lit 10))
  let hi := Nat.lor c1 (Nat.shiftLeft c2 (nat_lit 32))
  Nat.add (Nat.add (Nat.mul hi (nat_lit 0x3FFFFFFFFFF)) low42) hi

/-- Evaluate a 47-bit compact Stage-2 word in CPS. -/
noncomputable def evalWordStage2Compact (cw : Nat) (k : Box2DS → Bool) : Bool :=
  forceNatCBV (expandStage2Word cw) (fun wd => evalWordStage2Fast wd k)

/-- Decode one variable-width (`5b`/`9b`/`11b`/`15b`) Stage-2 vertex reference from `s` (`kChunk = 30`). -/
noncomputable def decodeS2Vert (dict : BTree (BTree Box2DS)) (s nw : Nat)
    (k : Box2DS → Nat → Nat → Nat → Bool) : Bool :=
  let low := Nat.land s (nat_lit 0x7FFF)
  let m := Nat.land low (nat_lit 3)
  @Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool)
        (let wid := Nat.land (Nat.shiftRight low (nat_lit 2)) (nat_lit 1023)
         let sym := Nat.shiftRight low (nat_lit 12)
         forestKWithFast (nat_lit 30) dict wid (fun raw =>
           forceNatCBV (Nat.shiftRight s (nat_lit 15)) (fun s' => k raw sym s' nw)))
        (let d := Nat.land (Nat.shiftRight low (nat_lit 2)) (nat_lit 63)
         let sym := Nat.land (Nat.shiftRight low (nat_lit 8)) (nat_lit 7)
         forestKWithFast (nat_lit 30) dict (Nat.sub nw (Nat.add d (nat_lit 1))) (fun raw =>
           forceNatCBV (Nat.shiftRight s (nat_lit 11)) (fun s' => k raw sym s' nw)))
        (Nat.beq m (nat_lit 2)))
      (let d := Nat.land (Nat.shiftRight low (nat_lit 2)) (nat_lit 15)
       let sym := Nat.land (Nat.shiftRight low (nat_lit 6)) (nat_lit 7)
       forestKWithFast (nat_lit 30) dict (Nat.sub nw (Nat.add d (nat_lit 1))) (fun raw =>
         forceNatCBV (Nat.shiftRight s (nat_lit 9)) (fun s' => k raw sym s' nw)))
      (Nat.beq m (nat_lit 1)))
    (let sym := Nat.land (Nat.shiftRight low (nat_lit 2)) (nat_lit 7)
     forestKWithFast (nat_lit 30) dict nw (fun raw =>
       forceNatCBV (Nat.shiftRight s (nat_lit 5)) (fun s' =>
         k raw sym s' (Nat.add nw (nat_lit 1)))))
    (Nat.beq m (nat_lit 0))

/-- Check a Stage-2 simplex leaf decoded from `s` at preorder cursor `nw`. -/
noncomputable def checkS2LeafV32 (epPairSq : Nat) (dict : BTree (BTree Box2DS))
    (x0 y0 w s nw : Nat) (k : Nat → Nat → Bool) : Bool :=
  @Bool.rec (fun _ => Bool) false
    (decodeS2Vert dict s nw (fun raw0 s0 sa nwa =>
      decodeS2Vert dict sa nwa (fun raw1 s1 sb nwb =>
        decodeS2Vert dict sb nwb (fun raw2 s2 sc nwc =>
          forceNatCBV (Nat.add x0 w) (fun x1 =>
            forceNatCBV (Nat.add y0 w) (fun y1 =>
              forceBox2DSK (applyD8BoxFast raw0 s0) (fun v0 =>
                forceBox2DSK (applyD8BoxFast raw1 s1) (fun v1 =>
                  forceBox2DSK (applyD8BoxFast raw2 s2) (fun v2 =>
                    @Bool.rec (fun _ => Bool) false
                      (@Bool.rec (fun _ => Bool) false
                        (@Bool.rec (fun _ => Bool) false
                          (@Bool.rec (fun _ => Bool) false
                            (k sc nwc)
                            (checkAllCornersEnclForced (SInt.mk false x0) (SInt.mk false x1)
                                                       (SInt.mk false y0) (SInt.mk false y1) v0 v1 v2))
                          (checkLagrangeBox1e9Forced v1 v2 epPairSq))
                        (checkLagrangeBox1e9Forced v0 v2 epPairSq))
                      (checkLagrangeBox1e9Forced v0 v1 epPairSq))))))))))
    (Nat.ble (nat_lit 1) w)

/-- Evaluate a `BitChain`-backed Stage-2 quadtree stream with preorder cursor `nw`. -/
noncomputable def evalS2StreamV32K (epPairSq : Nat) (dict : BTree (BTree Box2DS)) :
    Nat → Nat → Nat → Nat → Nat → BitChain → Nat →
      (Nat → BitChain → Nat → Bool) → Bool :=
  @Nat.rec
    (fun _ => Nat → Nat → Nat → Nat → BitChain → Nat →
      (Nat → BitChain → Nat → Bool) → Bool)
    (fun _ _ _ _ _ _ _ => false)
    (fun _ ih x0 y0 w sIn bcIn nw k =>
      withStreamWord sIn bcIn (fun s bc =>
        let tag := Nat.land s (nat_lit 3)
        @Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool)
            (@Bool.rec (fun _ => Bool)
              false
              (forceNatCBV (Nat.shiftRight s (nat_lit 2)) (fun sBody =>
                checkS2LeafV32 epPairSq dict x0 y0 w sBody nw (fun sc nwc => k sc bc nwc)))
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
            (isOutsideDom (nat_lit 2) x0 y0 w (nat_lit 13456) (nat_lit 1000000000000)))
          (Nat.beq tag (nat_lit 1))))

/-- Dyadic Stage-2 grid scale `5368709120 * 2 ^ k`. -/
def w2 : Nat → Nat
  | 0 => 5368709120
  | k + 1 => 2 * w2 k

/-- Dyadic Stage-2 cell coverage at scale `w2 k` and grid index `(ix, iy)`. -/
def D2 (k ix iy : Nat) : Prop :=
  Stage2SquareCov 460 540 (ix * w2 k) (iy * w2 k) (w2 k)

theorem d2_o {k ix iy : Nat}
    (h : isOutsideDom 2 (ix * w2 k) (iy * w2 k) (w2 k) 13456 1000000000000 = true := by decide) :
    D2 k ix iy := .out h

theorem d2_b {k ix iy : Nat}
    (c00 : D2 k (ix * 2) (iy * 2))
    (c01 : D2 k (ix * 2) (iy * 2 + 1))
    (c10 : D2 k (ix * 2 + 1) (iy * 2))
    (c11 : D2 k (ix * 2 + 1) (iy * 2 + 1)) :
    D2 (k + 1) ix iy := by
  dsimp only [D2, w2]
  have hw : 1 ≤ w2 k := Nat.rec (by decide) (fun _ ih => Nat.le_trans (by decide) (Nat.mul_le_mul_left 2 ih)) k
  have hd : Nat.div (2 * w2 k) 2 = w2 k := Nat.mul_div_right _ (by decide)
  have hm (u : Nat) : u * (2 * w2 k) = u * 2 * w2 k := (Nat.mul_assoc u 2 _).symm
  have ha (u : Nat) : Nat.add (u * (2 * w2 k)) (w2 k) = (u * 2 + 1) * w2 k :=
    (show Nat.add (u * (2 * w2 k)) (w2 k) = u * (2 * w2 k) + w2 k from rfl).trans
      (by rw [hm u, Nat.add_mul, Nat.one_mul])
  exact .branch (Nat.mul_mod_right 2 _) (Nat.mul_le_mul_left 2 hw)
    (by rwa [hd, hm ix, hm iy]) (by rwa [hd, hm ix, ha iy])
    (by rwa [hd, ha ix, hm iy]) (by rwa [hd, ha ix, ha iy])

theorem d2_root (h : D2 7 0 0) : Stage2SquareCov 460 540 0 0 687194767360 := by
  rwa [D2, show 0 * w2 7 = 0 by decide, show w2 7 = 687194767360 by decide] at h

/-- Conjunction of `D2` over all dyadic cells in a `CellList`. -/
def Stage2BatchCov : CellList → Prop
  | .one k ix iy => D2 k ix iy
  | .more k ix iy rest => D2 k ix iy ∧ Stage2BatchCov rest

/-- Evaluate a `CellList` of dyadic Stage-2 sub-cells over a shared `BitChain` stream. -/
noncomputable def evalS2BatchK (epPairSq : Nat) (dict : BTree (BTree Box2DS)) :
    CellList → Nat → BitChain → Nat → Bool :=
  @CellList.rec (fun _ => Nat → BitChain → Nat → Bool)
    (fun k ix iy s bc nw =>
      forceNatCBV (w2 k) (fun wc =>
        forceNatCBV (ix * wc) (fun x0 =>
          forceNatCBV (iy * wc) (fun y0 =>
            evalS2StreamV32K epPairSq dict (nat_lit 128) x0 y0 wc s bc nw (fun s' _ _ =>
              Nat.beq s' (nat_lit 1))))))
    (fun k ix iy _ ihr s bc nw =>
      forceNatCBV (w2 k) (fun wc =>
        forceNatCBV (ix * wc) (fun x0 =>
          forceNatCBV (iy * wc) (fun y0 =>
            evalS2StreamV32K epPairSq dict (nat_lit 128) x0 y0 wc s bc nw (fun s' bc' nw' =>
              ihr s' bc' nw')))))

/-- Decode a 47-bit `30`-word Stage-2 forest and evaluate a `CellList` + `BitChain` at `epPair = 460`. -/
noncomputable def evalS2Batch460 (b : CellList) (w : BTree Nat) (bc : BitChain) : Bool :=
  decodeWForestKFast (nat_lit 30) (nat_lit 49) (nat_lit 0x7FFFFFFFFFFF) evalWordStage2Compact w
    (fun dict => evalS2BatchK (nat_lit 211600) dict b (nat_lit 1) bc (nat_lit 0))

theorem evalS2Batch460_sound (b : CellList) (w : BTree Nat) (bc : BitChain)
    (h : evalS2Batch460 b w bc = true) : Stage2BatchCov b := by
  obtain ⟨dict, hdict, hb⟩ := decodeWForestKFast_sound
    (fun h => evalWordStage2Fast_sound (by rwa [evalWordStage2Compact, forceNatCBV_eq] at h)) h
  have hbr {f t c : Bool} : @Bool.rec (fun _ => Bool) f t c = true → t = true ∨ f = true :=
    match c with | false => Or.inr | true => Or.inl
  have hdV {s nw : Nat} {k : Box2DS → Nat → Nat → Nat → Bool}
      (hd : decodeS2Vert dict s nw k = true) :
      ∃ raw sym s' nw', ValidStage2Box raw ∧ k raw sym s' nw' = true := by
    have hl {i sh nw' sym : Nat} (hc : forestKWithFast (nat_lit 30) dict i
        (fun raw => forceNatCBV (Nat.shiftRight s sh) (fun s' => k raw sym s' nw')) = true) :
        ∃ raw sym s' nw', ValidStage2Box raw ∧ k raw sym s' nw' = true :=
      let ⟨raw, hv, hk⟩ := forestKWithFast_sound hdict hc
      ⟨raw, sym, _, nw', hv, by rwa [forceNatCBV_eq] at hk⟩
    dsimp only [decodeS2Vert] at hd
    exact (hbr hd).elim hl fun hd => (hbr hd).elim hl fun hd => (hbr hd).elim hl hl
  have hStr (fuel : Nat) : ∀ {x0 y0 w s : Nat} {bc : BitChain} {nw : Nat}
      {k : Nat → BitChain → Nat → Bool},
      evalS2StreamV32K (nat_lit 211600) dict fuel x0 y0 w s bc nw k = true →
      Stage2SquareCov 460 540 x0 y0 w ∧ ∃ s' bc' nw', k s' bc' nw' = true := by
    induction fuel with
    | zero => rintro _ _ _ _ _ _ _ ⟨⟩
    | succ _ ih =>
      intro x0 y0 w sIn bcIn nw k hs0
      dsimp only [evalS2StreamV32K] at hs0
      obtain ⟨s, bc, hs⟩ := withStreamWord_sound hs0
      refine (hbr hs).elim (fun hs => ?_) fun hs => (hbr hs).elim (fun hs => ?_) fun hs =>
        (hbr hs).elim (fun hs => ?_) fun hs => nomatch hs
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
      · simp only [forceNatCBV_eq, checkS2LeafV32, bool_rec_false_eq_and, Bool.and_eq_true] at hs
        obtain ⟨hw1, hs⟩ := hs
        obtain ⟨r0, s0, sa, nwa, ⟨wd0, hc0⟩, h0⟩ := hdV hs
        obtain ⟨r1, s1, sb, nwb, ⟨wd1, hc1⟩, h1⟩ := hdV h0
        obtain ⟨r2, s2, sc, nwc, ⟨wd2, hc2⟩, h2⟩ := hdV h1
        simp only [forceBox2DSK_eq, applyD8BoxFast_eq, checkAllCornersEnclForced_eq, Bool.and_eq_true,
          fun a b => checkLagrangeBox1e9Forced_eq a b 460 (nat_lit 211600) rfl, and_assoc] at h2
        rcases h2 with ⟨l01, l02, l12, e00, e01, e10, e11, hkc⟩
        exact ⟨.leaf ⟨Nat.ble_eq.mp hw1, wd0, wd1, wd2, r0, r1, r2, s0, s1, s2,
          hc0, hc1, hc2, l01, l02, l12, e00, e01, e10, e11⟩, sc, bc, nwc, hkc⟩
  suffices ∀ {s : Nat} {bcIn : BitChain} {nw : Nat},
      evalS2BatchK (nat_lit 211600) dict b s bcIn nw = true → Stage2BatchCov b from this hb
  clear h hb
  unfold evalS2BatchK
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
