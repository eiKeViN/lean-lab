import FQCExternal.Exec

/- Executable Stage-2 simplicial coverage decoder. Full decoder correspondence
remains an external assumption; arithmetic predicates reuse the pinned source. -/
open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

namespace FQCExternal.Stage2

abbrev Dictionary := BTree (BTree Box2DS)

def expandWord (cw : Nat) : Nat :=
  let lo8 := 0x41 + (cw &&& 1) * 0x50
  let lo10 := lo8 ||| (((cw >>> 1) &&& 3) <<< 8)
  let body := cw >>> 3
  let c0 := spread16Exec body
  let c1 := spread16Exec (body >>> 16)
  let c2 := spread16Exec (body >>> 32)
  let low42 := lo10 ||| (c0 <<< 10)
  let hi := c1 ||| (c2 <<< 32)
  (hi * 0x3FFFFFFFFFF + low42) + hi

theorem expandWord_eq (cw : Nat) : expandWord cw = expandStage2Word cw := rfl

def wordChunk : Nat → Nat → Option (BTree Box2DS)
  | 0, s => if s == 1 then some .empty else none
  | fuel + 1, s => do
    if s == 1 then return .empty
    if s &&& 3 != 3 then none else do
      let entry ← boxOfWordOpt 45 (expandWord ((s >>> 2) &&& 0x7FFFFFFFFFFF))
      let tail ← wordChunk fuel (s >>> 49)
      return braunCons tail entry

def dictionary : BTree Nat → Option Dictionary
  | .empty => some .empty
  | .node s l r => do
    let chunk ← wordChunk 30 s
    let left ← dictionary l
    let right ← dictionary r
    return .node chunk left right

def lookup (dict : Dictionary) (idx : Nat) : Option Box2DS := do
  let chunk ← BTree.get? dict (idx / 30)
  BTree.get? chunk (idx % 30)

def vertex (dict : Dictionary) (s nw : Nat) : Option (Box2DS × Nat × Nat × Nat) := do
  let low := s &&& 0x7FFF
  let mode := low &&& 3
  let (idx, sym, shift, nw') :=
    if mode == 0 then (nw, (low >>> 2) &&& 7, 5, nw + 1)
    else if mode == 1 then
      (nw - (((low >>> 2) &&& 15) + 1), (low >>> 6) &&& 7, 9, nw)
    else if mode == 2 then
      (nw - (((low >>> 2) &&& 63) + 1), (low >>> 8) &&& 7, 11, nw)
    else ((low >>> 2) &&& 1023, low >>> 12, 15, nw)
  let raw ← lookup dict idx
  return (raw, sym, s >>> shift, nw')

def lagrange (a b : Box2DS) : Bool := checkLagrangeBox a b 460 1000000000

theorem lagrange_eq (a b : Box2DS) :
    lagrange a b = checkLagrangeBox1e9Forced a b 211600 :=
  (checkLagrangeBox1e9Forced_eq a b 460 211600 (by decide)).symm

def leaf (dict : Dictionary) (x y w s nw : Nat) : Option (Nat × Nat) := do
  if w < 1 then none else do
    let (raw0, sym0, sa, nwa) ← vertex dict s nw
    let (raw1, sym1, sb, nwb) ← vertex dict sa nwa
    let (raw2, sym2, sc, nwc) ← vertex dict sb nwb
    let v0 := applyD8Box raw0 sym0
    let v1 := applyD8Box raw1 sym1
    let v2 := applyD8Box raw2 sym2
    let x0 : SInt := ⟨false, x⟩
    let x1 : SInt := ⟨false, x + w⟩
    let y0 : SInt := ⟨false, y⟩
    let y1 : SInt := ⟨false, y + w⟩
    if lagrange v0 v1 && lagrange v0 v2 && lagrange v1 v2 &&
        checkCornerEncl x0 y0 v0 v1 v2 && checkCornerEncl x0 y1 v0 v1 v2 &&
        checkCornerEncl x1 y0 v0 v1 v2 && checkCornerEncl x1 y1 v0 v1 v2 then
      return (sc, nwc)
    else none

def square : Nat → Dictionary → Nat → Nat → Nat → StreamState → Option StreamState
  | 0, _, _, _, _, _ => none
  | fuel + 1, dict, x, y, w, (sIn, bcIn, nw) => do
    let (s, bc) ← popWord sIn bcIn
    let tag := s &&& 3
    if tag == 1 then
      if isOutsideDom 2 x y w 13456 1000000000000 then return (s >>> 2, bc, nw)
      else none
    else if tag == 2 then
      if w % 2 != 0 || w < 2 then none else do
        let hw := w >>> 1
        let a ← square fuel dict x y hw (s >>> 2, bc, nw)
        let b ← square fuel dict x (y + hw) hw a
        let c ← square fuel dict (x + hw) y hw b
        square fuel dict (x + hw) (y + hw) hw c
    else if tag == 3 then
      let (sc, nwc) ← leaf dict x y w (s >>> 2) nw
      return (sc, bc, nwc)
    else none

def cellsExec (dict : Dictionary) : CellList → StreamState → Option StreamState
  | .one k ix iy, state => square 128 dict (ix * w2 k) (iy * w2 k) (w2 k) state
  | .more k ix iy rest, state => do
    let next ← square 128 dict (ix * w2 k) (iy * w2 k) (w2 k) state
    cellsExec dict rest next

def checkBatch (b : CellList) (words : BTree Nat) (stream : BitChain) : Bool :=
  match dictionary words with
  | none => false
  | some dict =>
    match cellsExec dict b (1, stream, 0) with
    | none => false
    | some (s, _, _) => s == 1

end FQCExternal.Stage2
