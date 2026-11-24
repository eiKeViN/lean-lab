import FQCExternal.Vendor.Stage1
import FQCExternal.Entry

/-!
Executable port of the Stage-1 dictionary and quadtree decoder. Arithmetic and
word-to-box construction reuse upstream computable definitions. Entry.lean proves
one correspondence theorem; correspondence of this entire decoder is currently
tested against the kernel reference, NOT proved. It is part of the explicit
external trust boundary.
-/

open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

namespace FQCExternal

abbrev Entry := Bool × Box2DS
abbrev Dictionary := BTree (BTree Entry)
abbrev StreamState := Nat × BitChain × Nat

def spread16Exec (u : Nat) : Nat :=
  let x0 := u &&& 0xFFFF
  let x1 := (x0 ||| (x0 <<< 8)) &&& 0x00FF00FF
  let x2 := (x1 ||| (x1 <<< 4)) &&& 0x0F0F0F0F
  let x3 := (x2 ||| (x2 <<< 2)) &&& 0x33333333
  (x3 ||| (x3 <<< 1)) &&& 0x55555555

theorem spread16Exec_eq (u : Nat) : spread16Exec u = spread16 u := rfl

def expandWord (cw : Nat) : Nat :=
  let clast := cw &&& 15
  let lo8 := (clast <<< 4) ||| 1
  let s0 := (cw >>> 4) &&& 3
  let s14 := spread16Exec ((cw >>> 6) &&& 15)
  let lo18 := lo8 ||| ((s0 <<< 8) ||| (s14 <<< 10))
  let ku := ((cw >>> 10) &&& 7) * 3
  let body := cw >>> 13
  let mid := body &&& ((1 <<< ku) - 1)
  let smid := spread16Exec mid ||| (spread16Exec (mid >>> 16) <<< 32)
  lo18 ||| ((smid ||| ((body >>> ku) <<< (ku * 2))) <<< 18)

theorem expandWord_eq (cw : Nat) : expandWord cw = expandStage1Word cw := rfl

def entry? (word : Nat) : Option Entry :=
  match boxTcOfWordOpt 28 word with
  | none => none
  | some (tc, bx) =>
    match Nat.ble tc 26 with
    | true => some (true, bx)
    | false =>
      match isFuseOutWord word with
      | true => some (false, bx)
      | false => none

/-- The dictionary decoder actually uses this executable entry function. -/
theorem entryOption_eq (w : Nat) (k : Entry → Bool) :
    (match entry? w with | none => false | some e => k e) = entryExec w k := by
  unfold entry? entryExec
  cases h : boxTcOfWordOpt 28 w with
  | none => rfl
  | some p =>
    rcases p with ⟨tc, bx⟩
    dsimp only
    cases Nat.ble tc 26 <;> cases isFuseOutWord w <;> rfl

def braunCons {α : Type} : BTree α → α → BTree α
  | .empty, x => .node x .empty .empty
  | .node v l r, x => .node x (braunCons r v) l

theorem braunCons_eq {α : Type} (t : BTree α) (x : α) :
    braunCons t x = consBraunFast t x := by
  induction t generalizing x with
  | empty => rfl
  | node v l r _ ihr =>
    change BTree.node x (braunCons r v) l = BTree.node x (consBraunFast r v) l
    rw [ihr]

def wordChunk : Nat → Nat → Option (BTree Entry)
  | 0, s => if s == 1 then some .empty else none
  | fuel + 1, s => do
    if s == 1 then return .empty
    if s &&& 3 != 3 then none else do
      let e ← entry? (expandWord ((s >>> 2) &&& 0x1FFFFFFFFFFFFF))
      let tail ← wordChunk fuel (s >>> 55)
      return braunCons tail e

def dictionary : BTree Nat → Option Dictionary
  | .empty => some .empty
  | .node s l r => do
    let chunk ← wordChunk 27 s
    let left ← dictionary l
    let right ← dictionary r
    return .node chunk left right

def lookup (dict : Dictionary) (idx : Nat) : Option Entry := do
  let chunk ← BTree.get? dict (idx / 27)
  BTree.get? chunk (idx % 27)

def cellCheck (x y w : Nat) (bx : Box2DS) (sym : Nat) : Bool :=
  checkDetBox x y w 13456 1000000000000 bx sym

theorem cellCheck_eq (x y w : Nat) (bx : Box2DS) (sym : Nat) :
    cellCheck x y w bx sym = checkDetBoxForced x y w 13456 1000000000000 bx sym :=
  (checkDetBoxForced_eq x y w 13456 1000000000000 bx sym).symm

def diagonal (dict : Dictionary) (idx x y w sym : Nat) : Bool :=
  match lookup dict idx with
  | none => false
  | some (isLo, bx) => isLo && cellCheck x y w bx sym

def parityEntry (dict : Dictionary) (par x y w e : Nat) : Bool :=
  match lookup dict (e >>> 3) with
  | none => false
  | some (isLo, bx) =>
    (isLo || ((e &&& 7) / 2) % 2 == par) && cellCheck x y w bx (e &&& 7)

def even25 (pay : Nat) : Nat :=
  let lo10 := (((pay &&& 15) <<< 4) ||| 1) ||| (((pay >>> 4) &&& 3) <<< 8)
  let ev := pay >>> 6
  lo10 ||| ((spread16Exec (ev &&& 0xFFFF) <<< 10) ||| (spread16Exec (ev >>> 16) <<< 42))

def splitWord (kEven pay : Nat) : Nat :=
  let body := pay >>> 6
  let lo10 := (((pay &&& 15) <<< 4) ||| 1) ||| (((pay >>> 4) &&& 3) <<< 8)
  lo10 ||| ((spread16Exec (body &&& ((1 <<< kEven) - 1)) <<< 10) |||
    ((body >>> kEven) <<< (10 + kEven * 2)))

theorem even25_eq (p : Nat) : even25 p = expandS1Even25 p := rfl
theorem splitWord_eq (k p : Nat) : splitWord k p = expandS1Split k p := rfl

def inlineCheck (word x y w sym : Nat) : Bool :=
  match boxTcOfWordOpt 26 word with
  | none => false
  | some (_, bx) => cellCheck x y w bx sym

def popWord (s : Nat) (bc : BitChain) : Option (Nat × BitChain) :=
  if s != 1 then some (s, bc) else
    match bc with
    | .empty => none
    | .more next rest => some (next, rest)

/-- Fuel bounds depth, as in the upstream continuation-based evaluator. -/
def square : Nat → Dictionary → Nat → Nat → Nat → StreamState → Option StreamState
  | 0, _, _, _, _, _ => none
  | fuel + 1, dict, x, y, w, (sIn, bcIn, nw) => do
    let (s, bc) ← popWord sIn bcIn
    let low := s &&& 0x1FFFFFFFFFFFFFFF
    let tag := low &&& 3
    if tag == 1 then
      if isOutsideDom 1 x y w 1020100 100000000 then return (s >>> 2, bc, nw)
      else none
    else if tag == 2 then
      if w % 2 != 0 || w < 2 then none else do
        let hw := w >>> 1
        let a ← square fuel dict x y hw (s >>> 2, bc, nw)
        let b ← square fuel dict x (y + hw) hw a
        let c ← square fuel dict (x + hw) y hw b
        square fuel dict (x + hw) (y + hw) hw c
    else if tag == 3 then
      let sub := (low >>> 2) &&& 7
      let sym := (low >>> 5) &&& 7
      if sub ≤ 2 then
        let (word, shift) :=
          if sub == 0 then (even25 ((low >>> 8) &&& 0x7FFFFFFF), 39)
          else if sub == 1 then (splitWord 10 ((low >>> 8) &&& 0x7FFFFFFFFFFF), 55)
          else (splitWord 8 ((low >>> 8) &&& 0x1FFFFFFFFFFFF), 57)
        if inlineCheck word x y w sym then return (s >>> shift, bc, nw) else none
      else if sub == 3 then
        if diagonal dict nw x y w sym then return (s >>> 8, bc, nw + 1) else none
      else if sub == 4 then
        let e := (low >>> 5) &&& 0x1FFF
        if diagonal dict (e >>> 3) x y w (e &&& 7) then return (s >>> 18, bc, nw) else none
      else if sub == 5 then
        let e0 := (low >>> 5) &&& 0x1FFF
        let e1 := (low >>> 18) &&& 0x1FFF
        if parityEntry dict 0 x y w e0 && parityEntry dict 1 x y w e1 then
          return (s >>> 33, bc, nw + ((low >>> 31) &&& 3))
        else none
      else none
    else none

def cellsExec (dict : Dictionary) : CellList → StreamState → Option StreamState
  | .one k ix iy, state => square 128 dict (ix * w1 k) (iy * w1 k) (w1 k) state
  | .more k ix iy rest, state => do
    let next ← square 128 dict (ix * w1 k) (iy * w1 k) (w1 k) state
    cellsExec dict rest next

def checkBatch (b : CellList) (words : BTree Nat) (stream : BitChain) : Bool :=
  match dictionary words with
  | none => false
  | some dict =>
    match cellsExec dict b (1, stream, 0) with
    | none => false
    | some (s, _, _) => s == 1

end FQCExternal
