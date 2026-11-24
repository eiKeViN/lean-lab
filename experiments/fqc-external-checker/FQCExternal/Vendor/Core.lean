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

@[expose] public section
set_option Elab.async false
set_option exponentiation.threshold 256
set_option autoImplicit false


namespace QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth
inductive BTree (α : Type) where
  | empty : BTree α
  | node : α → BTree α → BTree α → BTree α

def BTree.all {α : Type} (p : α → Bool) : BTree α → Bool
  | .empty => true
  | .node v l r =>
      match p v with
      | false => false
      | true =>
          match BTree.all p l with
          | false => false
          | true => BTree.all p r

def BTree.all2 {α β : Type} (p : α → β → Bool) : BTree α → BTree β → Bool
  | .empty, .empty => true
  | .node a la ra, .node b lb rb =>
      match p a b with
      | false => false
      | true =>
          match BTree.all2 p la lb with
          | false => false
          | true => BTree.all2 p ra rb
  | _, _ => false
def BTree.get? {α : Type} : BTree α → Nat → Option α
  | .empty, _ => none
  | .node v _ _, 0 => some v
  | .node _ l r, n + 1 =>
      match Nat.beq (Nat.mod n 2) 0 with
      | true => BTree.get? l (Nat.div n 2)
      | false => BTree.get? r (Nat.div n 2)

def forest256GetOpt {α : Type} (f : BTree (BTree α)) (idx : Nat) : Option α :=
  match BTree.get? f (Nat.div idx 256) with
  | none => none
  | some sub => BTree.get? sub (Nat.mod idx 256)

structure SInt where
  isNeg : Bool
  mag : Nat

def sNeg (x : SInt) : SInt := ⟨!x.isNeg, x.mag⟩

def sAdd (x y : SInt) : SInt :=
  match x.isNeg, y.isNeg with
  | false, false => ⟨false, Nat.add x.mag y.mag⟩
  | true, true => ⟨true, Nat.add x.mag y.mag⟩
  | _, _ =>
      match Nat.ble y.mag x.mag with
      | true => ⟨x.isNeg, Nat.sub x.mag y.mag⟩
      | false => ⟨y.isNeg, Nat.sub y.mag x.mag⟩

def sSub (x y : SInt) : SInt := sAdd x (sNeg y)

def sMul (x y : SInt) : SInt :=
  let isNeg := match x.isNeg, y.isNeg with
    | false, b => b
    | true, b => !b
  ⟨isNeg, Nat.mul x.mag y.mag⟩

def sLe (x y : SInt) : Bool :=
  match sSub y x with
  | ⟨false, _⟩ => true
  | ⟨true, m⟩ => Nat.beq m 0

def sPos (x : SInt) : Bool :=
  match x with
  | ⟨false, m⟩ => !Nat.beq m 0
  | ⟨true, _⟩ => false

def sNonneg (x : SInt) : Bool :=
  match x with
  | ⟨false, _⟩ => true
  | ⟨true, m⟩ => Nat.beq m 0

def sAbs (x : SInt) : SInt := ⟨false, x.mag⟩

def sintMax (x y : SInt) : SInt :=
  match sLe x y with
  | true => y
  | false => x

def sMin (x y : SInt) : SInt :=
  match sLe x y with
  | true => x
  | false => y

def sMin4 (a b c d : SInt) : SInt := sMin (sMin a b) (sMin c d)
def sMax4 (a b c d : SInt) : SInt := sintMax (sintMax a b) (sintMax c d)

structure Box2DS where
  x0 : SInt
  x1 : SInt
  y0 : SInt
  y1 : SInt

structure FastZ8 where
  a : SInt
  b : SInt
  c : SInt
  d : SInt

def fzConj (x : FastZ8) : FastZ8 := ⟨x.a, sNeg x.d, sNeg x.c, sNeg x.b⟩

def fzNeg (x : FastZ8) : FastZ8 := ⟨sNeg x.a, sNeg x.b, sNeg x.c, sNeg x.d⟩
def fzMul (x y : FastZ8) : FastZ8 :=
    ⟨sSub (sSub (sSub (sMul x.a y.a) (sMul x.b y.d)) (sMul x.c y.c))
    (sMul x.d y.b), sSub (sSub (sAdd (sMul x.a y.b) (sMul x.b y.a)) (sMul x.c y.d))
    (sMul x.d y.c), sSub (sAdd (sAdd (sMul x.a y.c) (sMul x.b y.b)) (sMul x.c y.a))
    (sMul x.d y.d), sAdd (sAdd (sAdd (sMul x.a y.d) (sMul x.b y.c)) (sMul x.c y.b)) (sMul x.d y.a)⟩
def fzMulOmega (m : Nat) (x : FastZ8) : FastZ8 :=
  let m8 := Nat.mod m 8
  match Nat.ble m8 3 with
  | true =>
      match Nat.ble m8 1 with
      | true =>
          match Nat.beq m8 0 with
          | true => x
          | false => ⟨sNeg x.d, x.a, x.b, x.c⟩
      | false =>
          match Nat.beq m8 2 with
          | true => ⟨sNeg x.c, sNeg x.d, x.a, x.b⟩
          | false => ⟨sNeg x.b, sNeg x.c, sNeg x.d, x.a⟩
  | false =>
      match Nat.ble m8 5 with
      | true =>
          match Nat.beq m8 4 with
          | true => ⟨sNeg x.a, sNeg x.b, sNeg x.c, sNeg x.d⟩
          | false => ⟨x.d, sNeg x.a, sNeg x.b, sNeg x.c⟩
      | false =>
          match Nat.beq m8 6 with
          | true => ⟨x.c, x.d, sNeg x.a, sNeg x.b⟩
          | false => ⟨x.b, x.c, x.d, sNeg x.a⟩

def bias : Nat := 70368744177664
def biasLo : Nat := 70364449210368
def biasHi : Nat := 70373039144960
def bias2 : Nat := 140737488355328

def unbiasS (x : Nat) : SInt :=
  match Nat.ble bias x with
  | true => ⟨false, Nat.sub x bias⟩
  | false => ⟨true, Nat.sub bias x⟩

structure FastCol where
  tCount : Nat
  detM : Nat
  ok : Bool
  ua : Nat
  ub : Nat
  uc : Nat
  ud : Nat
  va : Nat
  vb : Nat
  vc : Nat
  vd : Nat

def fastColInit : FastCol := ⟨0, 0, true, Nat.add bias 1, bias, bias, bias, bias, bias, bias, bias⟩
def inRange1 (x : Nat) : Bool :=
  match Nat.ble biasLo x with
  | false => false
  | true => Nat.ble x biasHi

def inRangeCol (s : FastCol) : Bool :=
  match s with
  | ⟨_, _, _, ua, ub, uc, ud, va, vb, vc, vd⟩ =>
      inRange1 ua && inRange1 ub && inRange1 uc && inRange1 ud &&
      inRange1 va && inRange1 vb && inRange1 vc && inRange1 vd

def hadStep (tc dm : Nat) (ok : Bool) (ua ub uc ud wa wb wc wd : Nat) : FastCol :=
    ⟨tc, dm, ok, Nat.sub (Nat.add ua wa) bias, Nat.sub (Nat.add ub wb) bias,
    Nat.sub (Nat.add uc wc) bias, Nat.sub (Nat.add ud wd) bias, Nat.sub (Nat.add ua bias) wa,
    Nat.sub (Nat.add ub bias) wb, Nat.sub (Nat.add uc bias) wc, Nat.sub (Nat.add ud bias) wd⟩
def stepSyl (c : Nat) (s : FastCol) : FastCol :=
  match s with
  | ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ =>
      match Nat.ble c 7 with
      | true =>
          match Nat.ble c 3 with
          | true =>
              match Nat.ble c 1 with
              | true =>
                  match Nat.beq c 0 with
                  | true => s
                  | false => hadStep tc (Nat.mod (Nat.add dm 4) 8) ok ua ub uc ud va vb vc vd
              | false =>
                  match Nat.beq c 2 with
                  | true =>
                        hadStep (Nat.add tc 1)
                        (Nat.mod (Nat.add dm 5) 8) ok ua ub uc ud (Nat.sub bias2 vd) va vb vc
                  | false =>
                        hadStep tc (Nat.mod (Nat.add dm 6) 8) ok ua ub uc ud (Nat.sub bias2 vc)
                        (Nat.sub bias2 vd) va vb
          | false =>
              match Nat.ble c 5 with
              | true =>
                  match Nat.beq c 4 with
                  | true =>
                        hadStep (Nat.add tc 1)
                        (Nat.mod (Nat.add dm 7) 8) ok ua ub uc ud (Nat.sub bias2 vb)
                        (Nat.sub bias2 vc) (Nat.sub bias2 vd) va
                  | false =>
                        hadStep tc dm ok ua ub uc ud (Nat.sub bias2 va) (Nat.sub bias2 vb)
                        (Nat.sub bias2 vc) (Nat.sub bias2 vd)
              | false =>
                  match Nat.beq c 6 with
                  | true =>
                        hadStep (Nat.add tc 1)
                        (Nat.mod (Nat.add dm 1) 8) ok ua ub uc ud vd (Nat.sub bias2 va)
                        (Nat.sub bias2 vb) (Nat.sub bias2 vc)
                  | false =>
                        hadStep tc (Nat.mod (Nat.add dm 2) 8) ok ua ub uc ud vc vd (Nat.sub bias2
                        va) (Nat.sub bias2 vb)
      | false =>
          match Nat.ble c 11 with
          | true =>
              match Nat.ble c 9 with
              | true =>
                  match Nat.beq c 8 with
                  | true =>
                        hadStep (Nat.add tc 1)
                        (Nat.mod (Nat.add dm 3) 8) ok ua ub uc ud vb vc vd (Nat.sub bias2 va)
                  | false =>
                        ⟨Nat.add tc 1, Nat.mod (Nat.add dm 1) 8, ok, ua, ub, uc, ud,
                        Nat.sub bias2 vd, va, vb, vc⟩
              | false =>
                  match Nat.beq c 10 with
                  | true =>
                        ⟨tc, Nat.mod (Nat.add dm 2) 8, ok, ua, ub, uc, ud, Nat.sub bias2 vc,
                        Nat.sub bias2 vd, va, vb⟩
                  | false =>
                        ⟨Nat.add tc 1, Nat.mod (Nat.add dm 3) 8, ok, ua, ub, uc, ud,
                        Nat.sub bias2 vb, Nat.sub bias2 vc, Nat.sub bias2 vd, va⟩
          | false =>
              match Nat.ble c 14 with
              | true =>
                  match Nat.beq c 12 with
                  | true =>
                        ⟨tc, Nat.mod (Nat.add dm 4) 8, ok, ua, ub, uc, ud, Nat.sub bias2 va,
                        Nat.sub bias2 vb, Nat.sub bias2 vc, Nat.sub bias2 vd⟩
                  | false =>
                      match Nat.beq c 13 with
                      | true =>
                            ⟨Nat.add tc 1, Nat.mod (Nat.add dm 5) 8, ok, ua, ub, uc, ud, vd,
                            Nat.sub bias2 va, Nat.sub bias2 vb, Nat.sub bias2 vc⟩
                      | false =>
                            ⟨tc, Nat.mod (Nat.add dm 6) 8, ok, ua, ub, uc, ud, vc, vd,
                            Nat.sub bias2 va, Nat.sub bias2 vb⟩
              | false =>
                  match Nat.beq c 15 with
                  | true =>
                        ⟨Nat.add tc 1, Nat.mod (Nat.add dm 7) 8, ok, ua, ub, uc, ud, vb, vc, vd,
                        Nat.sub bias2 va⟩
                  | false =>
                      match Nat.beq c 16 with
                      | true => ⟨tc, Nat.mod (Nat.add dm 4) 8, ok, va, vb, vc, vd, ua, ub, uc, ud⟩
                      | false => ⟨tc, dm, false, ua, ub, uc, ud, va, vb, vc, vd⟩

def s2MidS : SInt := ⟨false, 1414213562373095048⟩
def twoD18S : SInt := ⟨false, 2000000000000000000⟩
def boxScaleS : SInt := ⟨false, 4503599627370496⟩

def fzReLo (z : FastZ8) : SInt :=
  let bd := sSub z.b z.d
  sSub (sAdd (sMul twoD18S z.a) (sMul bd s2MidS)) (sAbs bd)

def fzReHi (z : FastZ8) : SInt :=
  let bd := sSub z.b z.d
  sAdd (sAdd (sMul twoD18S z.a) (sMul bd s2MidS)) (sAbs bd)

def fzImLo (z : FastZ8) : SInt :=
  let bp := sAdd z.b z.d
  sSub (sAdd (sMul twoD18S z.c) (sMul bp s2MidS)) (sAbs bp)

def fzImHi (z : FastZ8) : SInt :=
  let bp := sAdd z.b z.d
  sAdd (sAdd (sMul twoD18S z.c) (sMul bp s2MidS)) (sAbs bp)

abbrev e0 {α : Type} : BTree α := .empty
abbrev bn {α : Type} : α → BTree α → BTree α → BTree α := .node
abbrev lf {α : Type} (x : α) : BTree α := .node x .empty .empty
abbrev sn (m : Nat) : SInt := ⟨true, m⟩
def applyD8Box (b : Box2DS) (sym : Nat) : Box2DS :=
  let y0 := match Nat.beq (Nat.mod sym 2) 1 with
    | true => sNeg b.y1
    | false => b.y0
  let y1 := match Nat.beq (Nat.mod sym 2) 1 with
    | true => sNeg b.y0
    | false => b.y1
  let r := Nat.mod (Nat.div sym 2) 4
  match Nat.ble r 1 with
  | true =>
      match Nat.beq r 0 with
      | true => ⟨b.x0, b.x1, y0, y1⟩
      | false => ⟨y0, y1, sNeg b.x1, sNeg b.x0⟩
  | false =>
      match Nat.beq r 2 with
      | true => ⟨sNeg b.x1, sNeg b.x0, sNeg y1, sNeg y0⟩
      | false => ⟨sNeg y1, sNeg y0, b.x0, b.x1⟩

def checkLagrangeBox (a b : Box2DS) (capNum capDen : Nat) : Bool :=
  let dxMax := sintMax (sAbs (sSub a.x0 b.x1)) (sAbs (sSub a.x1 b.x0));
  let dyMax := sintMax (sAbs (sSub a.y0 b.y1)) (sAbs (sSub a.y1 b.y0));
  let axAbs := sintMax (sAbs a.x0) (sAbs a.x1); let ayAbs := sintMax (sAbs a.y0) (sAbs a.y1);
  let bxAbs := sintMax (sAbs b.x0) (sAbs b.x1); let byAbs := sintMax (sAbs b.y0) (sAbs b.y1);
  let imUb := sAdd (sMul ayAbs bxAbs) (sMul axAbs byAbs); let bsSq := sMul boxScaleS boxScaleS;
  let dotLo := sSub (sSub bsSq (sMul axAbs bxAbs)) (sMul ayAbs byAbs);
  let distSq := sAdd (sMul dxMax dxMax) (sMul dyMax dyMax);
  let num := sAdd (sMul distSq bsSq) (sMul imUb imUb);
  let capDenSq : SInt := ⟨false, Nat.mul capDen capDen⟩;
  let capNumSq : SInt := ⟨false, Nat.mul capNum capNum⟩
  sPos dotLo &&
  sLe (sMul num capDenSq) (sMul capNumSq (sMul dotLo dotLo))

def crossLoCorner (px py : SInt) (a b : Box2DS) : SInt :=
  let du0 := sSub a.x0 px; let du1 := sSub a.x1 px; let dv0 := sSub a.y0 py;
  let dv1 := sSub a.y1 py; let eu0 := sSub b.x0 px; let eu1 := sSub b.x1 px;
  let ev0 := sSub b.y0 py; let ev1 := sSub b.y1 py
  sSub (sMin4 (sMul du0 ev0) (sMul du0 ev1) (sMul du1 ev0) (sMul du1 ev1))
       (sMax4 (sMul dv0 eu0) (sMul dv0 eu1) (sMul dv1 eu0) (sMul dv1 eu1))

def checkCornerEncl (px py : SInt) (v0 v1 v2 : Box2DS) : Bool :=
    sPos (crossLoCorner px py v1 v2) && sPos (crossLoCorner px py v2 v0) &&
    sPos (crossLoCorner px py v0 v1)
def stepMid1 (p : Nat × FastCol) : Nat × FastCol :=
  match Nat.ble p.1 1 with
  | true => p
  | false => (Nat.div p.1 4, stepSyl (Nat.add (Nat.mul 2 (Nat.mod p.1 4)) 2) p.2)

def stepMid4 (p : Nat × FastCol) : Nat × FastCol :=
  match Nat.ble p.1 1 with
  | true => p
  | false => stepMid1 (stepMid1 (stepMid1 (stepMid1 p)))

def stepMid12Raw (p : Nat × FastCol) : Nat × FastCol := stepMid4 (stepMid4 (stepMid4 p))
def evalWord2Bit (w : Nat) : FastCol :=
  match Nat.beq w 0 with
  | true => fastColInit
  | false =>
      let cFirst := Nat.mod w 16; let cLast := Nat.mod (Nat.div w 16) 16; let m0 := Nat.div w 256;
      let s0 := stepSyl cFirst fastColInit; let p1 := stepMid12Raw (m0, s0);
      let p2 := stepMid12Raw p1; let p3 := stepMid12Raw p2; let p4 := stepMid12Raw p3;
      let sf := stepSyl cLast p4.2;
      let allOk :=
          inRangeCol s0 && inRangeCol p1.2 && inRangeCol p2.2 && inRangeCol p3.2 &&
          inRangeCol p4.2 && Nat.beq p4.1 1 && sf.ok
      { sf with ok := allOk }

def unpackCoord (biasB u : Nat) : SInt :=
  match Nat.ble biasB u with
  | true => ⟨false, Nat.sub u biasB⟩
  | false => ⟨true, Nat.sub biasB u⟩

def unpackBox (biasB modB p : Nat) : Box2DS :=
  let dx := Nat.mod p 4; let p1 := Nat.div p 4; let dy := Nat.mod p1 4; let p2 := Nat.div p1 4;
  let ux := Nat.mod p2 modB; let uy := Nat.div p2 modB; let x0 := unpackCoord biasB ux;
  let y0 := unpackCoord biasB uy
  ⟨x0, sAdd x0 ⟨false, dx⟩, y0, sAdd y0 ⟨false, dy⟩⟩

def checkWord2BitBox (tCap w : Nat) (bx : Box2DS) : Bool :=
  let st := evalWord2Bit w
  match st with
  | ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ =>
      ok &&
      inRangeCol st &&
      Nat.blt dm 8 &&
      Nat.ble tc tCap &&
      let u : FastZ8 := ⟨unbiasS ua, unbiasS ub, unbiasS uc, unbiasS ud⟩;
      let v : FastZ8 := ⟨unbiasS va, unbiasS vb, unbiasS vc, unbiasS vd⟩;
      let wden := fzMul u (fzConj u); let wnum := fzNeg (fzMul (fzConj v) u);
      let denLo := fzReLo wden; let denHi := fzReHi wden; let nxLo := fzReLo wnum;
      let nxHi := fzReHi wnum; let nyLo := fzImLo wnum; let nyHi := fzImHi wnum
      sPos denLo &&
      sLe bx.x0 bx.x1 &&
      sLe bx.y0 bx.y1 &&
      sLe (match sNonneg bx.x0 with | true => sMul bx.x0 denHi | false => sMul bx.x0 denLo)
          (sMul nxLo boxScaleS) &&
      sLe (sMul nxHi boxScaleS)
          (match sNonneg bx.x1 with | true => sMul bx.x1 denLo | false => sMul bx.x1 denHi) &&
      sLe (match sNonneg bx.y0 with | true => sMul bx.y0 denHi | false => sMul bx.y0 denLo)
          (sMul nyLo boxScaleS) &&
      sLe (sMul nyHi boxScaleS)
          (match sNonneg bx.y1 with | true => sMul bx.y1 denLo | false => sMul bx.y1 denHi)

def checkWord2BitPacked (tCap biasB modB w pb : Nat) : Bool :=
    checkWord2BitBox tCap w (unpackBox biasB modB pb)
inductive QTree (α : Type) where
  | out : QTree α
  | leaf : α → QTree α
  | branch : QTree α → QTree α → QTree α → QTree α → QTree α

abbrev qo : QTree Nat := .out
abbrev ql (u : Nat) : QTree Nat := .leaf u
abbrev qb : QTree Nat → QTree Nat → QTree Nat → QTree Nat → QTree Nat := .branch

def isOutsideDom (stageKind x0 y0 w rInNumSq rInScaleSq : Nat) : Bool :=
  Nat.blt (Nat.add x0 w) y0 ||
  match Nat.beq stageKind 0 with
  | true =>
      let xp := Nat.add x0 4503599627370496
      Nat.blt 40564819207303340847894502572032 (Nat.add (Nat.mul xp xp) (Nat.mul y0 y0))
  | false =>
      Nat.blt (Nat.mul rInNumSq 20282409603651670423947251286016)
              (Nat.mul (Nat.add (Nat.mul x0 x0) (Nat.mul y0 y0)) rInScaleSq)

def checkDetBox (x0 y0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS) (sym : Nat) : Bool :=
  Nat.blt sym 8 &&
  let wb := applyD8Box rawBox sym; let x0s : SInt := ⟨false, x0⟩;
  let x1s : SInt := ⟨false, Nat.add x0 w⟩; let y0s : SInt := ⟨false, y0⟩;
  let y1s : SInt := ⟨false, Nat.add y0 w⟩;
  let dxMax := sintMax (sAbs (sSub x0s wb.x1)) (sAbs (sSub x1s wb.x0));
  let dyMax := sintMax (sAbs (sSub y0s wb.y1)) (sAbs (sSub y1s wb.y0));
  let bsSq := sMul boxScaleS boxScaleS;
  let dotMin :=
      sAdd (sAdd bsSq (sMin4 (sMul x0s wb.x0) (sMul x0s wb.x1) (sMul x1s wb.x0) (sMul x1s wb.x1)))
      (sMin4 (sMul y0s wb.y0) (sMul y0s wb.y1) (sMul y1s wb.y0) (sMul y1s wb.y1))
  sPos dotMin &&
  sLe (sMul (sMul (sAdd (sMul dxMax dxMax) (sMul dyMax dyMax)) ⟨false, rScaleSq⟩) bsSq)
      (sMul ⟨false, rNumSq⟩ (sMul dotMin dotMin))

def checkDetLeaf (biasB modB x0 y0 w rNumSq rScaleSq : Nat) (boxes : BTree (BTree Nat))
    (u : Nat) : Bool :=
  let wid := Nat.div u 8; let sym := Nat.mod u 8
  match forest256GetOpt boxes wid with
  | none => false
  | some pb => checkDetBox x0 y0 w rNumSq rScaleSq (unpackBox biasB modB pb) sym

def checkDetQTree (stageKind biasB modB rInNumSq rInScaleSq rOutNumSq rOutScaleSq : Nat)
    (boxes : BTree (BTree Nat)) (t : QTree Nat) (x0 y0 w : Nat) : Bool :=
  match t with
  | .out => isOutsideDom stageKind x0 y0 w rInNumSq rInScaleSq
  | .leaf u => checkDetLeaf biasB modB x0 y0 w rOutNumSq rOutScaleSq boxes u
  | .branch c00 c01 c10 c11 =>
      Nat.beq (Nat.mod w 2) 0 && Nat.ble 2 w &&
      let hw := Nat.div w 2
      checkDetQTree stageKind biasB modB rInNumSq rInScaleSq rOutNumSq rOutScaleSq boxes c00 x0 y0
          hw &&
      checkDetQTree stageKind biasB modB rInNumSq rInScaleSq rOutNumSq rOutScaleSq boxes c01 x0
          (Nat.add y0 hw) hw &&
      checkDetQTree stageKind biasB modB rInNumSq rInScaleSq rOutNumSq rOutScaleSq boxes c10
          (Nat.add x0 hw) y0 hw &&
      checkDetQTree stageKind biasB modB rInNumSq rInScaleSq rOutNumSq rOutScaleSq boxes c11
          (Nat.add x0 hw) (Nat.add y0 hw) hw
abbrev q4 (a b c d : Nat) : QTree Nat := .branch (.leaf a) (.leaf b) (.leaf c) (.leaf d)
/-! ### FastKernel Evaluator & Equivalence Bridges -/

scoped syntax:max "n#" noWs num : term
scoped macro_rules
  | `(n#$x:num) => `(nat_lit $x)

scoped syntax:max "~" noWs num : term
scoped macro_rules
  | `(~$x:num) => `(nat_lit $x)

abbrev bN : Nat → BTree Nat → BTree Nat → BTree Nat := @BTree.node Nat
abbrev lfN (x : Nat) : BTree Nat := @BTree.node Nat x (@BTree.empty Nat) (@BTree.empty Nat)
abbrev f6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Nat) : BTree Nat :=
    (@BTree.node Nat a0 (@BTree.node Nat a1 (@BTree.node Nat a3 (@BTree.node Nat a7 (@BTree.node Nat
    a15 (@BTree.empty Nat) (@BTree.empty Nat)) (@BTree.empty Nat))
    (@BTree.node Nat a11 (@BTree.empty Nat) (@BTree.empty Nat)))
    (@BTree.node Nat a5 (@BTree.node Nat a9 (@BTree.empty Nat) (@BTree.empty Nat))
    (@BTree.node Nat a13 (@BTree.empty Nat) (@BTree.empty Nat))))
    (@BTree.node Nat a2 (@BTree.node Nat a4 (@BTree.node Nat a8 (@BTree.empty Nat)
    (@BTree.empty Nat)) (@BTree.node Nat a12 (@BTree.empty Nat) (@BTree.empty Nat)))
    (@BTree.node Nat a6 (@BTree.node Nat a10 (@BTree.empty Nat) (@BTree.empty Nat))
    (@BTree.node Nat a14 (@BTree.empty Nat) (@BTree.empty Nat)))))
theorem bool_rec_false_eq_and (a b : Bool) : @Bool.rec (fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bool_rec_true_eq_or (a b : Bool) :
    @Bool.rec (fun _ => Bool) b true a = (a || b) := by cases a <;> rfl

noncomputable def bTreeWithGetFast {α : Type} (k : α → Bool) : BTree α → Nat → Bool :=
    @BTree.rec α (fun _ => Nat → Bool) (fun _ => false)
    (fun v _ _ ihl ihr n => @Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool)
    (ihr (Nat.shiftRight (Nat.sub n (nat_lit 1)) (nat_lit 1)))
    (ihl (Nat.shiftRight (Nat.sub n (nat_lit 1)) (nat_lit 1)))
    (Nat.beq (Nat.land (Nat.sub n (nat_lit 1)) (nat_lit 1)) (nat_lit 0))) (k v)
    (Nat.beq n (nat_lit 0)))
theorem nat_land_eq_mod (x k m d : Nat) (hm : m = 2 ^ k - 1) (hd : d = 2 ^ k) : Nat.land x m =
    Nat.mod x d := by
  subst hm hd
  exact Nat.and_two_pow_sub_one_eq_mod x k
theorem nat_shr_eq_div (x k d : Nat) (hd : d = 2 ^ k) : Nat.shiftRight x k = Nat.div x d := by
  subst hd
  exact Nat.shiftRight_eq_div_pow x k
theorem bTreeWithGetFast_eq {α : Type} (k : α → Bool) (t : BTree α) :
    ∀ n : Nat, bTreeWithGetFast k t n =
      (match BTree.get? t n with | none => false | some v => k v) := by
  unfold bTreeWithGetFast
  induction t with
  | empty => exact fun _ => rfl
  | node v l r ihl ihr =>
    rintro (_ | m)
    · rfl
    · dsimp only [BTree.get?]
      rw [show Nat.beq (m + 1) (nat_lit 0) = false from rfl,
        show Nat.sub (m + 1) (nat_lit 1) = m from Nat.add_sub_cancel m 1,
        nat_land_eq_mod m 1 _ _ rfl rfl, nat_shr_eq_div m 1 _ rfl]
      dsimp only
      rw [ihl, ihr]
      cases Nat.beq (Nat.mod m 2) 0 <;> rfl

noncomputable def forest256WithFast {α : Type} (f : BTree (BTree α)) (idx : Nat)
    (k : α → Bool) : Bool :=
    bTreeWithGetFast (fun sub =>
    bTreeWithGetFast k sub (Nat.land idx (nat_lit 255))) f (Nat.shiftRight idx (nat_lit 8))
theorem forest256WithFast_eq {α : Type} (f : BTree (BTree α)) (idx : Nat) (k : α → Bool) :
    forest256WithFast f idx k =
      (match forest256GetOpt f idx with | none => false | some v => k v) := by
  simp only [forest256WithFast, forest256GetOpt, nat_shr_eq_div idx 8 _ rfl,
    nat_land_eq_mod idx 8 _ _ rfl rfl, bTreeWithGetFast_eq]
  cases BTree.get? f (Nat.div idx 256) <;> rfl

noncomputable def sNegFast (x : SInt) : SInt :=
    @SInt.rec (fun _ => SInt) (fun xn xm => SInt.mk (!xn) xm) x
theorem sNegFast_eq (x : SInt) : sNegFast x = sNeg x := by cases x <;> rfl

noncomputable def sAddFast (x y : SInt) : SInt :=
    @SInt.rec (fun _ => SInt) (fun xn xm => @SInt.rec (fun _ => SInt)
    (fun yn ym => @Bool.rec (fun _ => SInt) (@Bool.rec (fun _ => SInt) (SInt.mk yn (Nat.sub ym xm))
    (SInt.mk xn (Nat.sub xm ym)) (Nat.ble ym xm)) (SInt.mk xn (Nat.add xm ym))
    (@Bool.rec (fun _ => Bool) (!yn) yn xn)) y) x
theorem sAddFast_eq (x y : SInt) : sAddFast x y = sAdd x y := by
  rcases x with ⟨_ | _, xm⟩ <;> rcases y with ⟨_ | _, ym⟩ <;> dsimp [sAddFast, sAdd] <;>
      cases Nat.ble ym xm <;> rfl

noncomputable def sSubFast (x y : SInt) : SInt := sAddFast x (sNegFast y)

theorem sSubFast_eq (x y : SInt) : sSubFast x y = sSub x y := by
  simp only [sSubFast, sSub, sAddFast_eq, sNegFast_eq]
noncomputable def sMulFast (x y : SInt) : SInt :=
    @SInt.rec (fun _ => SInt) (fun xn xm => @SInt.rec (fun _ => SInt)
    (fun yn ym => SInt.mk (@Bool.rec (fun _ => Bool) yn (!yn) xn) (Nat.mul xm ym)) y) x
theorem sMulFast_eq (x y : SInt) : sMulFast x y = sMul x y := by
  rcases x with ⟨_ | _, _⟩ <;> rcases y with ⟨_ | _, _⟩ <;> rfl

noncomputable def sLeFast (x y : SInt) : Bool :=
    @SInt.rec (fun _ => Bool)
    (fun sn sm => @Bool.rec (fun _ => Bool) true (Nat.beq sm (nat_lit 0)) sn) (sSubFast y x)
theorem sLeFast_eq (x y : SInt) : sLeFast x y = sLe x y := by
  simp only [sLeFast, sLe, sSubFast_eq]
  rcases sSub y x with ⟨_ | _, _⟩ <;> rfl

noncomputable def sPosFast (x : SInt) : Bool :=
    @SInt.rec (fun _ => Bool) (fun xn xm => @Bool.rec (fun _ => Bool)
    (!Nat.beq xm (nat_lit 0)) false xn) x
theorem sPosFast_eq (x : SInt) : sPosFast x = sPos x := by rcases x with ⟨_ | _, _⟩ <;> rfl

noncomputable def sAbsFast (x : SInt) : SInt :=
    @SInt.rec (fun _ => SInt) (fun _ xm => SInt.mk false xm) x
theorem sAbsFast_eq (x : SInt) : sAbsFast x = sAbs x := by cases x <;> rfl

noncomputable def sintMaxFast (x y : SInt) : SInt := @Bool.rec (fun _ => SInt) x y (sLeFast x y)
theorem sintMaxFast_eq2 (x y : SInt) : sintMaxFast x y = sintMax x y := by
  simp only [sintMaxFast, sintMax, sLeFast_eq]
  cases sLe x y <;> rfl

noncomputable def sMinFast (x y : SInt) : SInt := @Bool.rec (fun _ => SInt) y x (sLeFast x y)
theorem sMinFast_eq (x y : SInt) : sMinFast x y = sMin x y := by
  simp only [sMinFast, sMin, sLeFast_eq]
  cases sLe x y <;> rfl

noncomputable def sMin4Fast (a b c d : SInt) : SInt := sMinFast (sMinFast a b) (sMinFast c d)
noncomputable def sMax4Fast (a b c d : SInt) : SInt :=
    sintMaxFast (sintMaxFast a b) (sintMaxFast c d)

theorem sMin4Fast_eq (a b c d : SInt) : sMin4Fast a b c d = sMin4 a b c d := by
  simp only [sMin4Fast, sMin4, sMinFast_eq]
theorem sMax4Fast_eq (a b c d : SInt) : sMax4Fast a b c d = sMax4 a b c d := by
  simp only [sMax4Fast, sMax4, sintMaxFast_eq2]
noncomputable def unbiasSFast (x : Nat) : SInt :=
    @Bool.rec (fun _ => SInt) (SInt.mk true (Nat.sub (nat_lit 70368744177664) x))
    (SInt.mk false (Nat.sub x (nat_lit 70368744177664))) (Nat.ble (nat_lit 70368744177664) x)
theorem unbiasSFast_eq (x : Nat) : unbiasSFast x = unbiasS x := by
  unfold unbiasSFast unbiasS
  rw [show (nat_lit 70368744177664 : Nat) = bias from rfl]
  cases Nat.ble bias x <;> rfl

noncomputable def inRange1Fast (x : Nat) : Bool :=
    @Bool.rec (fun _ => Bool) false (Nat.ble x (nat_lit 70373039144960))
    (Nat.ble (nat_lit 70364449210368) x)
theorem inRange1Fast_eq (x : Nat) : inRange1Fast x = inRange1 x := by
  unfold inRange1Fast inRange1
  rw [show (nat_lit 70364449210368 : Nat) = biasLo from rfl, show (nat_lit 70373039144960 : Nat) =
      biasHi from rfl]
  cases Nat.ble biasLo x <;> rfl

noncomputable def inRange8Fast (ua ub uc ud va vb vc vd : Nat) : Bool :=
    @Bool.rec (fun _ => Bool) false (@Bool.rec (fun _ => Bool) false (@Bool.rec (fun _ =>
    Bool) false (@Bool.rec (fun _ => Bool) false (@Bool.rec (fun _ =>
    Bool) false (@Bool.rec (fun _ => Bool) false (@Bool.rec (fun _ => Bool) false (inRange1Fast vd)
    (inRange1Fast vc)) (inRange1Fast vb)) (inRange1Fast va)) (inRange1Fast ud)) (inRange1Fast uc))
    (inRange1Fast ub)) (inRange1Fast ua)
theorem inRange8Fast_eq (tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) :
    inRange8Fast ua ub uc ud va vb vc vd = inRangeCol ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
    := by
  unfold inRange8Fast inRangeCol; simp only [inRange1Fast_eq, bool_rec_false_eq_and, Bool.and_assoc]
-- O(1) CPS proof-only applicators (avoid zeta let-duplication across nested CPS steps)
noncomputable def appColK {R : Type} (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → R) (s : FastCol) : R :=
    k s.tCount s.detM s.ok s.ua s.ub s.uc s.ud s.va s.vb s.vc s.vd
noncomputable def appMidK {R : Type} (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → R) (p : Nat × FastCol) : R :=
    k p.1 p.2.tCount p.2.detM p.2.ok p.2.ua p.2.ub p.2.uc p.2.ud p.2.va p.2.vb p.2.vc p.2.vd
noncomputable def forceColStateK (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Bool) (tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) : Bool :=
    k tc dm ok ua ub uc ud va vb vc vd
theorem appColK_forceColStateK
    (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (s : FastCol) :
    appColK (forceColStateK k) s = appColK k s := rfl

noncomputable def hadStepK (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Bool) (tc dm : Nat) (ok : Bool) (ua ub uc ud wa wb wc wd : Nat) : Bool :=
    k tc dm ok (Nat.sub (Nat.add ua wa) (nat_lit 70368744177664)) (Nat.sub (Nat.add ub wb)
    (nat_lit 70368744177664)) (Nat.sub (Nat.add uc wc) (nat_lit 70368744177664))
    (Nat.sub (Nat.add ud wd) (nat_lit 70368744177664))
    (Nat.sub (Nat.add ua (nat_lit 70368744177664)) wa)
    (Nat.sub (Nat.add ub (nat_lit 70368744177664)) wb)
    (Nat.sub (Nat.add uc (nat_lit 70368744177664)) wc)
    (Nat.sub (Nat.add ud (nat_lit 70368744177664)) wd)
noncomputable def stepSylK (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Bool) (c tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) : Bool :=
    @Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool) (k tc dm false ua ub uc ud va vb vc vd)
    (k tc (Nat.land (Nat.add dm (nat_lit 4)) (nat_lit 7)) ok va vb vc vd ua ub uc ud)
    (Nat.beq c (nat_lit 16))) (k (Nat.add tc (nat_lit 1)) (Nat.land (Nat.add dm (nat_lit 7))
    (nat_lit 7)) ok ua ub uc ud vb vc vd (Nat.sub (nat_lit 140737488355328) va))
    (Nat.beq c (nat_lit 15))) (@Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool)
    (k tc (Nat.land (Nat.add dm (nat_lit 6))
    (nat_lit 7)) ok ua ub uc ud vc vd (Nat.sub (nat_lit 140737488355328) va)
    (Nat.sub (nat_lit 140737488355328) vb)) (k (Nat.add tc (nat_lit 1))
    (Nat.land (Nat.add dm (nat_lit 5))
    (nat_lit 7)) ok ua ub uc ud vd (Nat.sub (nat_lit 140737488355328) va)
    (Nat.sub (nat_lit 140737488355328) vb) (Nat.sub (nat_lit 140737488355328) vc))
    (Nat.beq c (nat_lit 13))) (k tc (Nat.land (Nat.add dm (nat_lit 4))
    (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) va)
    (Nat.sub (nat_lit 140737488355328) vb) (Nat.sub (nat_lit 140737488355328) vc)
    (Nat.sub (nat_lit 140737488355328) vd)) (Nat.beq c (nat_lit 12))) (Nat.ble c (nat_lit 14)))
    (@Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool) (k (Nat.add tc (nat_lit 1))
    (Nat.land (Nat.add dm (nat_lit 3))
    (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vb)
    (Nat.sub (nat_lit 140737488355328) vc) (Nat.sub (nat_lit 140737488355328) vd) va)
    (k tc (Nat.land (Nat.add dm (nat_lit 2))
    (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vc)
    (Nat.sub (nat_lit 140737488355328) vd) va vb) (Nat.beq c (nat_lit 10)))
    (@Bool.rec (fun _ => Bool) (k (Nat.add tc (nat_lit 1)) (Nat.land (Nat.add dm (nat_lit 1))
    (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vd) va vb vc)
    (hadStepK k (Nat.add tc (nat_lit 1)) (Nat.land (Nat.add dm (nat_lit 3))
    (nat_lit 7)) ok ua ub uc ud vb vc vd (Nat.sub (nat_lit 140737488355328) va))
    (Nat.beq c (nat_lit 8))) (Nat.ble c (nat_lit 9))) (Nat.ble c (nat_lit 11)))
    (@Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool)
    (hadStepK k tc (Nat.land (Nat.add dm (nat_lit 2))
    (nat_lit 7)) ok ua ub uc ud vc vd (Nat.sub (nat_lit 140737488355328) va) (Nat.sub
  (nat_lit 140737488355328) vb)) (hadStepK k (Nat.add tc (nat_lit 1))
      (Nat.land (Nat.add dm (nat_lit 1))
      (nat_lit 7)) ok ua ub uc ud vd (Nat.sub (nat_lit 140737488355328) va)
      (Nat.sub (nat_lit 140737488355328) vb) (Nat.sub (nat_lit 140737488355328) vc))
      (Nat.beq c (nat_lit 6))) (@Bool.rec (fun _ => Bool)
      (hadStepK k tc dm ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) va)
      (Nat.sub (nat_lit 140737488355328) vb) (Nat.sub (nat_lit 140737488355328) vc)
      (Nat.sub (nat_lit 140737488355328) vd)) (hadStepK k (Nat.add tc (nat_lit 1))
      (Nat.land (Nat.add dm (nat_lit 7))
      (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vb)
      (Nat.sub (nat_lit 140737488355328) vc) (Nat.sub (nat_lit 140737488355328) vd) va)
      (Nat.beq c (nat_lit 4))) (Nat.ble c (nat_lit 5))) (@Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool) (hadStepK k tc (Nat.land (Nat.add dm (nat_lit 6))
      (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vc)
      (Nat.sub (nat_lit 140737488355328) vd) va vb) (hadStepK k (Nat.add tc (nat_lit 1))
      (Nat.land (Nat.add dm (nat_lit 5))
      (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vd) va vb vc)
      (Nat.beq c (nat_lit 2))) (@Bool.rec (fun _ => Bool)
      (hadStepK k tc (Nat.land (Nat.add dm (nat_lit 4)) (nat_lit 7)) ok ua ub uc ud va vb vc vd)
      (k tc dm ok ua ub uc ud va vb vc vd) (Nat.beq c (nat_lit 0))) (Nat.ble c (nat_lit 1)))
      (Nat.ble c (nat_lit 3))) (Nat.ble c (nat_lit 7))
theorem nat_land_7_eq_mod_8 (x : Nat) : Nat.land x (nat_lit 7) = Nat.mod x 8 :=
    nat_land_eq_mod x 3 _ _ rfl rfl
theorem hadStepK_eq (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (tc dm : Nat) (ok : Bool) (ua ub uc ud wa wb wc wd : Nat) :
    hadStepK k tc dm ok ua ub uc ud wa wb wc wd =
        appColK k (hadStep tc dm ok ua ub uc ud wa wb wc wd) := by
  unfold hadStepK appColK hadStep
  dsimp only
  rw [show (nat_lit 70368744177664 : Nat) = bias from rfl]
  rfl
theorem stepSylK_eq (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (c tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) :
    stepSylK k c tc dm ok ua ub uc ud va vb vc vd = appColK k (stepSyl c ⟨tc, dm, ok, ua, ub, uc,
        ud, va, vb, vc, vd⟩) := by
  unfold stepSylK stepSyl
  simp only [nat_land_7_eq_mod_8,
      hadStepK_eq]
  cases Nat.ble c 7
  · cases Nat.ble c 11
    · cases Nat.ble c 14
      · cases Nat.beq c 15 <;> cases Nat.beq c 16 <;> rfl
      · cases Nat.beq c 12 <;> cases Nat.beq c 13 <;> rfl
    · cases Nat.ble c 9 <;> cases Nat.beq c 10 <;> cases Nat.beq c 8 <;> rfl
  · cases Nat.ble c 3
    · cases Nat.ble c 5 <;> cases Nat.beq c 6 <;> cases Nat.beq c 4 <;> rfl
    · cases Nat.ble c 1 <;> cases Nat.beq c 2 <;> cases Nat.beq c 0 <;> rfl

theorem appColK_stepSylK (k : Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Bool)
    (c : Nat) (s : FastCol) : appColK (stepSylK k c) s = appColK k (stepSyl c s) := by
  cases s <;> exact stepSylK_eq k c _ _ _ _ _ _ _ _ _ _ _

-- Direct 2-bit middle-syllable step (rem = m % 4 ∈ {0,1,2,3} => c = 2*rem + 2 ∈ {2,4,6,8})
noncomputable def stepMid1K (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Bool) (m tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) : Bool :=
  @Bool.rec (fun _ => Bool)
    (let m' := Nat.shiftRight m (nat_lit 2)
     let rem := Nat.land m (nat_lit 3); let tc' := Nat.add tc (nat_lit 1)
     @Bool.rec (fun _ => Bool)
       (@Bool.rec (fun _ => Bool)
         (hadStepK (k m') tc' (Nat.land (Nat.add dm (nat_lit 3))
             (nat_lit 7)) ok ua ub uc ud vb vc vd (Nat.sub (nat_lit 140737488355328) va))
         (hadStepK (k m') tc' (Nat.land (Nat.add dm (nat_lit 1))
             (nat_lit 7)) ok ua ub uc ud vd (Nat.sub (nat_lit 140737488355328) va)
             (Nat.sub (nat_lit 140737488355328) vb) (Nat.sub (nat_lit 140737488355328) vc))
         (Nat.beq rem (nat_lit 2)))
       (@Bool.rec (fun _ => Bool)
         (hadStepK (k m') tc' (Nat.land (Nat.add dm (nat_lit 7))
             (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vb)
             (Nat.sub (nat_lit 140737488355328) vc) (Nat.sub (nat_lit 140737488355328) vd) va)
         (hadStepK (k m') tc' (Nat.land (Nat.add dm (nat_lit 5))
             (nat_lit 7)) ok ua ub uc ud (Nat.sub (nat_lit 140737488355328) vd) va vb vc)
         (Nat.beq rem (nat_lit 0)))
       (Nat.ble rem (nat_lit 1)))
    (k m tc dm ok ua ub uc ud va vb vc vd)
    (Nat.ble m (nat_lit 1))

theorem stepMid1K_eq (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Bool)
    (m tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) :
    stepMid1K k m tc dm ok ua ub uc ud va vb vc vd =
        appMidK k (stepMid1 (m, ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩)) := by
  unfold stepMid1K stepMid1
  dsimp only
  rw [show Nat.ble m (nat_lit 1) = Nat.ble m 1 from rfl]
  cases Nat.ble m 1
  · dsimp only
    rw [nat_land_eq_mod m 2 _ _ rfl rfl, nat_shr_eq_div m 2 _ rfl]
    have hlt : Nat.mod m 4 < 4 := Nat.mod_lt m (by decide)
    rcases (by omega : Nat.mod m 4 = 0 ∨ Nat.mod m 4 = 1 ∨ Nat.mod m 4 = 2 ∨ Nat.mod m 4 = 3) with h
        | h | h | h <;>
      simp only [h, stepSyl, 
          nat_land_7_eq_mod_8, hadStepK_eq] <;> rfl
  · rfl

theorem appMidK_stepMid1K (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Bool)
    (p : Nat × FastCol) : appMidK (stepMid1K k) p = appMidK k (stepMid1 p) := by
  rcases p with ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _⟩⟩ <;>
      exact stepMid1K_eq k _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def stepMid4K (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Bool) (m tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) : Bool :=
    @Bool.rec (fun _ => Bool)
    (stepMid1K (stepMid1K (stepMid1K (stepMid1K k))) m tc dm ok ua ub uc ud va vb vc vd)
    (k m tc dm ok ua ub uc ud va vb vc vd) (Nat.ble m (nat_lit 1))
theorem stepMid4K_eq (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Bool)
    (m tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) :
    stepMid4K k m tc dm ok ua ub uc ud va vb vc vd =
        appMidK k (stepMid4 (m, ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩)) := by
  unfold stepMid4K stepMid4
  dsimp only
  rw [show Nat.ble m (nat_lit 1) = Nat.ble m 1 from rfl]
  cases Nat.ble m 1
  · exact (appMidK_stepMid1K _ (m, ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩)).trans
      ((appMidK_stepMid1K _ _).trans ((appMidK_stepMid1K _ _).trans (appMidK_stepMid1K _ _)))
  · rfl

theorem appMidK_stepMid4K (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Bool)
    (p : Nat × FastCol) : appMidK (stepMid4K k) p = appMidK k (stepMid4 p) := by
  rcases p with ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _⟩⟩ <;>
      exact stepMid4K_eq k _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def stepMid12RawK (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Bool) (m tc dm : Nat) (ok : Bool) (ua ub uc ud va vb vc vd : Nat) : Bool :=
    stepMid4K (stepMid4K (stepMid4K k)) m tc dm ok ua ub uc ud va vb vc vd
theorem appMidK_stepMid12RawK (k : Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Bool) (p : Nat × FastCol) : appMidK (stepMid12RawK k) p = appMidK k (stepMid12Raw p)
    := by
  change appMidK (stepMid4K (stepMid4K (stepMid4K k))) p =
      appMidK k (stepMid4 (stepMid4 (stepMid4 p))); rw [appMidK_stepMid4K, appMidK_stepMid4K,
      appMidK_stepMid4K]
noncomputable def fzMulFast (x y : FastZ8) : FastZ8 :=
    @FastZ8.rec (fun _ => FastZ8) (fun xa xb xc xd => @FastZ8.rec (fun _ => FastZ8)
    (fun ya yb yc yd => FastZ8.mk (sSubFast (sSubFast (sSubFast (sMulFast xa ya) (sMulFast xb yd))
    (sMulFast xc yc)) (sMulFast xd yb)) (sSubFast (sSubFast (sAddFast (sMulFast xa yb)
    (sMulFast xb ya)) (sMulFast xc yd)) (sMulFast xd yc))
    (sSubFast (sAddFast (sAddFast (sMulFast xa yc) (sMulFast xb yb)) (sMulFast xc ya))
    (sMulFast xd yd)) (sAddFast (sAddFast (sAddFast (sMulFast xa yd) (sMulFast xb yc))
    (sMulFast xc yb)) (sMulFast xd ya))) y) x
theorem fzMulFast_eq (x y : FastZ8) : fzMulFast x y = fzMul x y := by
  cases x <;> cases y <;> simp only [fzMulFast, fzMul, sSubFast_eq, sAddFast_eq, sMulFast_eq]

noncomputable def fzConjFast (x : FastZ8) : FastZ8 :=
    @FastZ8.rec (fun _ => FastZ8) (fun xa xb xc xd => FastZ8.mk xa (sNegFast xd) (sNegFast xc)
    (sNegFast xb)) x
theorem fzConjFast_eq (x : FastZ8) : fzConjFast x = fzConj x := by
  cases x <;> simp only [fzConjFast, fzConj, sNegFast_eq]

noncomputable def fzNegFast (x : FastZ8) : FastZ8 :=
    @FastZ8.rec (fun _ => FastZ8) (fun xa xb xc xd => FastZ8.mk (sNegFast xa) (sNegFast xb)
    (sNegFast xc) (sNegFast xd)) x
theorem fzNegFast_eq (x : FastZ8) : fzNegFast x = fzNeg x := by
  cases x <;> simp only [fzNegFast, fzNeg, sNegFast_eq]

noncomputable def unpackCoordFast (biasB u : Nat) : SInt :=
    @Bool.rec (fun _ => SInt) (SInt.mk true (Nat.sub biasB u)) (SInt.mk false (Nat.sub u biasB))
    (Nat.ble biasB u)
noncomputable def unpackBoxFast (biasB shiftB maskB p : Nat) : Box2DS :=
  let dx := Nat.land p (nat_lit 3); let p1 := Nat.shiftRight p (nat_lit 2);
  let dy := Nat.land p1 (nat_lit 3); let p2 := Nat.shiftRight p1 (nat_lit 2);
  let ux := Nat.land p2 maskB; let uy := Nat.shiftRight p2 shiftB;
  let x0 := unpackCoordFast biasB ux; let y0 := unpackCoordFast biasB uy
  Box2DS.mk x0 (sAddFast x0 (SInt.mk false dx)) y0 (sAddFast y0 (SInt.mk false dy))

theorem unpackBoxFast_eq (biasB shiftB maskB modB : Nat) (hMask : maskB = 2 ^ shiftB - 1)
    (hMod : modB = 2 ^ shiftB) (p : Nat) :
    unpackBoxFast biasB shiftB maskB p = unpackBox biasB modB p := by
  unfold unpackBoxFast unpackBox unpackCoordFast unpackCoord
  simp only [fun x => nat_land_eq_mod x 2 _ _ rfl rfl, fun x => nat_shr_eq_div x 2 _ rfl,
    fun x => nat_land_eq_mod x shiftB maskB modB hMask hMod, fun x =>
        nat_shr_eq_div x shiftB modB hMod, sAddFast_eq]
  cases Nat.ble biasB (Nat.mod (Nat.div (Nat.div p 4) 4) modB) <;>
    cases Nat.ble biasB (Nat.div (Nat.div (Nat.div p 4) 4) modB) <;> rfl

noncomputable def stepMid12CheckedK (k : Bool → Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Bool) (acc : Bool) (m tc dm : Nat) (ok : Bool)
    (ua ub uc ud va vb vc vd : Nat) : Bool :=
  let acc' := acc && inRange8Fast ua ub uc ud va vb vc vd
  stepMid12RawK (k acc') m tc dm ok ua ub uc ud va vb vc vd

theorem appMidK_stepMid12CheckedK (k : Bool → Nat → Nat → Nat → Bool → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Bool) (acc : Bool) (p : Nat × FastCol) : appMidK (stepMid12CheckedK k acc) p =
    appMidK (k (acc && inRangeCol p.2)) (stepMid12Raw p) := by
  rcases p with ⟨m, ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩⟩
  change stepMid12RawK (k (acc &&
      inRange8Fast ua ub uc ud va vb vc vd)) m tc dm ok ua ub uc ud va vb vc vd =
      appMidK (k (acc && inRangeCol ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩))
      (stepMid12Raw (m, ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc,
      vd⟩)); rw [inRange8Fast_eq tc dm ok]; exact appMidK_stepMid12RawK (k (acc && inRangeCol ⟨tc,
      dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩)) (m, ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩)
-- Specialized 1-arg word chunk bridges for Stage 0, Stage 1, Stage 2

-- FastKernel Quadtree Evaluators & Equivalence Bridges
noncomputable def applyD8BoxFast (b : Box2DS) (sym : Nat) : Box2DS :=
  @Box2DS.rec (fun _ => Box2DS) (fun bx0 bx1 by0 by1 =>
    let m2 := Nat.beq (Nat.land sym (nat_lit 1)) (nat_lit 1)
    let y0 := @Bool.rec (fun _ => SInt) by0 (sNegFast by1) m2
    let y1 := @Bool.rec (fun _ => SInt) by1 (sNegFast by0) m2
    let r := Nat.land (Nat.shiftRight sym (nat_lit 1)) (nat_lit 3)
    @Bool.rec (fun _ => Box2DS)
      (@Bool.rec (fun _ => Box2DS)
        (Box2DS.mk (sNegFast y1) (sNegFast y0) bx0 bx1)
        (Box2DS.mk (sNegFast bx1) (sNegFast bx0) (sNegFast y1) (sNegFast y0))
        (Nat.beq r (nat_lit 2)))
      (@Bool.rec (fun _ => Box2DS)
        (Box2DS.mk y0 y1 (sNegFast bx1) (sNegFast bx0))
        (Box2DS.mk bx0 bx1 y0 y1)
        (Nat.beq r (nat_lit 0)))
      (Nat.ble r (nat_lit 1)))
    b

theorem applyD8BoxFast_eq (b : Box2DS) (sym : Nat) : applyD8BoxFast b sym = applyD8Box b sym := by
  cases b
  unfold applyD8BoxFast applyD8Box
  dsimp only
  rw [nat_land_eq_mod sym 1 _ _ rfl rfl, nat_shr_eq_div sym 1 _ rfl,
      nat_land_eq_mod _ 2 _ _ rfl rfl]
  simp only [sNegFast_eq]
  cases Nat.beq (Nat.mod sym 2) 1 <;> cases Nat.ble (Nat.mod (Nat.div sym 2) 4) 1 <;>
    cases Nat.beq (Nat.mod (Nat.div sym 2) 4) 0 <;> cases Nat.beq (Nat.mod (Nat.div sym 2) 4) 2 <;>
        rfl

noncomputable def checkDetBoxFast (x0 y0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS)
    (sym : Nat) : Bool :=
  @Bool.rec (fun _ => Bool) false
    (@Box2DS.rec (fun _ => Bool) (fun wx0 wx1 wy0 wy1 =>
      let x0s := SInt.mk false x0; let x1s := SInt.mk false (Nat.add x0 w);
      let y0s := SInt.mk false y0; let y1s := SInt.mk false (Nat.add y0 w);
      let bsSq := SInt.mk false (nat_lit 20282409603651670423947251286016);
      let dotMin :=
          sAddFast (sAddFast bsSq (sMin4Fast (sMulFast x0s wx0) (sMulFast x0s wx1)
          (sMulFast x1s wx0) (sMulFast x1s wx1))) (sMin4Fast (sMulFast y0s wy0) (sMulFast y0s wy1)
          (sMulFast y1s wy0) (sMulFast y1s wy1))
      @Bool.rec (fun _ => Bool) false
        (let dxMax := sintMaxFast (sAbsFast (sSubFast x0s wx1)) (sAbsFast (sSubFast x1s wx0))
         let dyMax := sintMaxFast (sAbsFast (sSubFast y0s wy1)) (sAbsFast (sSubFast y1s wy0))
         sLeFast (sMulFast (sMulFast (sAddFast (sMulFast dxMax dxMax) (sMulFast dyMax dyMax))
                                     (SInt.mk false rScaleSq)) bsSq)
                 (sMulFast (SInt.mk false rNumSq) (sMulFast dotMin dotMin)))
        (sPosFast dotMin))
      (applyD8BoxFast rawBox sym))
    (Nat.blt sym (nat_lit 8))

theorem checkDetBoxFast_eq (x0 y0 w rNumSq rScaleSq : Nat) (rawBox : Box2DS)
    (sym : Nat) : checkDetBoxFast x0 y0 w rNumSq rScaleSq rawBox sym =
    checkDetBox x0 y0 w rNumSq rScaleSq rawBox sym := by
  unfold checkDetBoxFast checkDetBox; rw [applyD8BoxFast_eq]
  cases applyD8Box rawBox sym with | mk wx0 wx1 wy0 wy1 =>
  have h8 : Nat.blt sym (nat_lit 8) = Nat.blt sym 8 := rfl;
  have hbs : SInt.mk false (nat_lit 20282409603651670423947251286016) = sMul boxScaleS boxScaleS :=
      rfl; dsimp only; rw [h8]; simp only [hbs, bool_rec_false_eq_and, sintMaxFast_eq2, sAbsFast_eq,
      sSubFast_eq, sAddFast_eq, sMin4Fast_eq, sMulFast_eq, sPosFast_eq, sLeFast_eq]
noncomputable def checkDetLeafFast (biasB shiftB maskB x0 y0 w rNumSq rScaleSq : Nat)
    (boxes : BTree (BTree Nat)) (u : Nat) : Bool :=
    forest256WithFast boxes (Nat.shiftRight u (nat_lit 3))
    (fun pb => checkDetBoxFast x0 y0 w rNumSq rScaleSq (unpackBoxFast biasB shiftB maskB pb)
    (Nat.land u (nat_lit 7)))
theorem checkDetLeafFast_eq (biasB shiftB maskB modB : Nat) (hMask : maskB = 2 ^ shiftB - 1)
    (hMod : modB = 2 ^ shiftB)
    (x0 y0 w rNumSq rScaleSq : Nat) (boxes : BTree (BTree Nat)) (u : Nat) :
    checkDetLeafFast biasB shiftB maskB x0 y0 w rNumSq rScaleSq boxes u =
        checkDetLeaf biasB modB x0 y0 w rNumSq rScaleSq boxes u := by
  unfold checkDetLeafFast checkDetLeaf
  dsimp only
  rw [nat_shr_eq_div u 3 _ rfl, nat_land_7_eq_mod_8, forest256WithFast_eq]
  cases forest256GetOpt boxes (Nat.div u 8)
  · rfl
  · simp only [unpackBoxFast_eq biasB shiftB maskB modB hMask hMod, checkDetBoxFast_eq]
noncomputable def checkDetQTreeFast (stageKind biasB shiftB maskB rInNumSq rInScaleSq rOutNumSq
    rOutScaleSq : Nat) (boxes : BTree (BTree Nat)) : QTree Nat → Nat → Nat → Nat → Bool :=
  @QTree.rec Nat (fun _ => Nat → Nat → Nat → Bool)
    (fun x0 y0 w => isOutsideDom stageKind x0 y0 w rInNumSq rInScaleSq)
    (fun u x0 y0 w => checkDetLeafFast biasB shiftB maskB x0 y0 w rOutNumSq rOutScaleSq boxes u)
    (fun _ _ _ _ ih00 ih01 ih10 ih11 x0 y0 w =>
      @Bool.rec (fun _ => Bool) false
        (@Bool.rec (fun _ => Bool) false
          (let hw := Nat.shiftRight w (nat_lit 1)
           @Bool.rec (fun _ => Bool) false
             (@Bool.rec (fun _ => Bool) false
               (@Bool.rec (fun _ => Bool) false
                 (ih11 (Nat.add x0 hw) (Nat.add y0 hw) hw)
                 (ih10 (Nat.add x0 hw) y0 hw))
               (ih01 x0 (Nat.add y0 hw) hw))
             (ih00 x0 y0 hw))
          (Nat.ble (nat_lit 2) w))
        (Nat.beq (Nat.land w (nat_lit 1)) (nat_lit 0)))

theorem checkDetQTreeFast_eq (stageKind biasB shiftB maskB modB : Nat)
    (hMask : maskB = 2 ^ shiftB - 1) (hMod : modB = 2 ^ shiftB)
    (rInN rInS rOutN rOutS : Nat) (boxes : BTree (BTree Nat)) (t : QTree Nat) :
    ∀ x0 y0 w : Nat,
        checkDetQTreeFast stageKind biasB shiftB maskB rInN rInS rOutN rOutS boxes t x0 y0 w =
      checkDetQTree stageKind biasB modB rInN rInS rOutN rOutS boxes t x0 y0 w := by
  unfold checkDetQTreeFast
  induction t with
  | out => exact fun _ _ _ => rfl
  | leaf u => exact fun x0 y0 w =>
        checkDetLeafFast_eq biasB shiftB maskB modB hMask hMod x0 y0 w rOutN rOutS boxes u
  | branch c00 c01 c10 c11 ih00 ih01 ih10 ih11 =>
    intro x0 y0 w
    dsimp only [checkDetQTree]
    rw [nat_land_eq_mod w 1 _ _ rfl rfl, nat_shr_eq_div w 1 _ rfl,
      show Nat.beq (Nat.mod w 2) (nat_lit 0) = Nat.beq (Nat.mod w 2) 0 from rfl,
      show Nat.ble (nat_lit 2) w = Nat.ble 2 w from rfl, ih00, ih01, ih10, ih11]
    simp only [bool_rec_false_eq_and, Bool.and_assoc]
noncomputable def crossLoCornerFast (px py : SInt) (a b : Box2DS) : SInt :=
  @Box2DS.rec (fun _ => SInt) (fun ax0 ax1 ay0 ay1 =>
    @Box2DS.rec (fun _ => SInt) (fun bx0 bx1 by0 by1 =>
      let du0 := sSubFast ax0 px; let du1 := sSubFast ax1 px; let dv0 := sSubFast ay0 py;
      let dv1 := sSubFast ay1 py; let eu0 := sSubFast bx0 px; let eu1 := sSubFast bx1 px;
      let ev0 := sSubFast by0 py; let ev1 := sSubFast by1 py
      sSubFast (sMin4Fast (sMulFast du0 ev0) (sMulFast du0 ev1) (sMulFast du1 ev0)
          (sMulFast du1 ev1))
               (sMax4Fast (sMulFast dv0 eu0) (sMulFast dv0 eu1) (sMulFast dv1 eu0)
                   (sMulFast dv1 eu1)))
      b)
    a

theorem crossLoCornerFast_eq (px py : SInt) (a b : Box2DS) : crossLoCornerFast px py a b =
    crossLoCorner px py a b := by
  cases a <;> cases b <;> simp only [crossLoCornerFast, crossLoCorner, sSubFast_eq, sMin4Fast_eq,
      sMax4Fast_eq, sMulFast_eq]
noncomputable def checkCornerEnclFast (px py : SInt) (v0 v1 v2 : Box2DS) : Bool :=
    @Bool.rec (fun _ => Bool) false (@Bool.rec (fun _ =>
    Bool) false (sPosFast (crossLoCornerFast px py v0 v1))
    (sPosFast (crossLoCornerFast px py v2 v0))) (sPosFast (crossLoCornerFast px py v1 v2))
theorem checkCornerEnclFast_eq (px py : SInt) (v0 v1 v2 : Box2DS) :
    checkCornerEnclFast px py v0 v1 v2 = checkCornerEncl px py v0 v1 v2 := by
  unfold checkCornerEnclFast checkCornerEncl;
  simp only [bool_rec_false_eq_and, Bool.and_assoc, sPosFast_eq, crossLoCornerFast_eq]
-- Specialized 1-arg QTree chunk bridges for Stage 0, Stage 1, Stage 2

end QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

end
