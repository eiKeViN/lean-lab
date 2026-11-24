import Lean
import FQCExternal.Exec2

open Lean QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

namespace FQCExternal.Input

def hexNat (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let cs := s.toList
  match cs with
  | '0' :: 'x' :: digits =>
    if digits.isEmpty then throw "empty hexadecimal integer"
    digits.foldlM (fun n c => do
      let k := c.toNat
      let digit ←
        if '0'.toNat ≤ k && k ≤ '9'.toNat then pure (k - '0'.toNat)
        else if 'a'.toNat ≤ k && k ≤ 'f'.toNat then pure (k - 'a'.toNat + 10)
        else throw "noncanonical hexadecimal digit"
      pure (n * 16 + digit)) 0
  | _ => throw "expected 0x-prefixed hexadecimal string"

def tree : Nat → Json → Except String (BTree Nat)
  | 0, _ => throw "dictionary nesting limit"
  | n + 1, j =>
    if j == Json.null then pure .empty else do
      let a ← j.getArr?
      if a.size != 3 then throw "dictionary node must have three fields"
      let x ← hexNat a[0]!
      let l ← tree n a[1]!
      let r ← tree n a[2]!
      pure (.node x l r)

def triple (j : Json) : Except String (Nat × Nat × Nat) := do
  let a ← j.getArr?
  if a.size != 3 then throw "cell must have three coordinates"
  let k ← a[0]!.getNat?
  let x ← a[1]!.getNat?
  let y ← a[2]!.getNat?
  if k > 64 then throw "unsupported dyadic scale"
  pure (k, x, y)

def cells (j : Json) : Except String CellList := do
  let a ← j.getArr?
  if a.size > 256 then throw "batch cell limit"
  let ts ← a.toList.mapM triple
  match ts.reverse with
  | [] => throw "empty cell list"
  | (k, x, y) :: rest =>
    pure (rest.foldl (fun b (k, x, y) => CellList.more k x y b) (.one k x y))

def stream (j : Json) : Except String BitChain := do
  let a ← j.getArr?
  if a.size > 100000 then throw "stream length limit"
  let ws ← a.toList.mapM hexNat
  pure (ws.foldr BitChain.more .empty)

def parse (j : Json) : Except String (Nat × Nat × CellList × BTree Nat × BitChain × Json) := do
  let schema ← (← j.getObjVal? "schema").getStr?
  let stage ←
    if schema == "fqc-stage1-batch-v1" then pure 1
    else if schema == "fqc-stage2-batch-v1" then pure 2
    else throw "unsupported certificate schema"
  let batch ← (← j.getObjVal? "batch").getNat?
  let rawCells ← j.getObjVal? "cells"
  let b ← cells rawCells
  let w ← tree 256 (← j.getObjVal? "words")
  let s ← stream (← j.getObjVal? "stream")
  pure (stage, batch, b, w, s, rawCells)

end FQCExternal.Input

def checkFile (path : String) : IO UInt32 := do
    try
      let text ← IO.FS.readFile path
      if text.length > 2000000 then throw (IO.userError "certificate file limit")
      match Json.parse text >>= FQCExternal.Input.parse with
      | .error err => IO.eprintln err; return 2
      | .ok (stage, batch, cells, words, stream, rawCells) =>
        let accepted := if stage == 1 then FQCExternal.checkBatch cells words stream
                        else FQCExternal.Stage2.checkBatch cells words stream
        IO.println (Json.mkObj [
          ("schema", toJson s!"fqc-stage{stage}-result-v1"),
          ("batch", toJson batch), ("cells", rawCells),
          ("accepted", toJson accepted)]).compress
        return if accepted then 0 else 1
    catch err => IO.eprintln err.toString; return 2

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: fqc_checker CERTIFICATE.json ..."; return 2
  let mut status := 0
  for path in args do
    status := max status (← checkFile path)
  return status
