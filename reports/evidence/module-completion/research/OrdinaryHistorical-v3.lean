module
import ForMathlib
import ForMathlib.Algebra.Module.Localization.FiniteCharacters
import ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion
import ForMathlib.GroupTheory.Coxeter.Bruhat.DiamondClosure
import ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds
import ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds
import ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport
import ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem
import ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords
import ForMathlib.GroupTheory.Coxeter.Roots.Basic
import ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder
import ForMathlib.GroupTheory.Coxeter.Roots.LaterCount
import ForMathlib.GroupTheory.Coxeter.Roots.Order
import ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis
import ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength
import ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup
import ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport
import ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder
import ForMathlib.GroupTheory.Coxeter.Roots.ReflectionLabels
import ForMathlib.GroupTheory.Coxeter.Roots.Splines
import ForMathlib.LinearAlgebra.Avoidance
import ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted
import ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates
import Lean


open Lean
namespace BoundaryCodec
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => toJson (#[nameJson p, toJson s])
  | .num p n => toJson (#[nameJson p, toJson n, Json.null])
partial def levelJson : Level → Json
  | .zero => toJson (#[toJson "zero"])
  | .succ u => toJson (#[toJson "succ", levelJson u])
  | .max u v => toJson (#[toJson "max", levelJson u, levelJson v])
  | .imax u v => toJson (#[toJson "imax", levelJson u, levelJson v])
  | .param n => toJson (#[toJson "param", nameJson n])
  | .mvar _ => panic! "unclosed level"
structure Dump where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def encode (e : Expr) : StateM Dump Nat := do
  if let .mdata _ b := e then return ← encode b
  if let some i := (← get).ids[ExprStructEq.mk e]? then return i
  let node : Array Json ← match e with
    | .bvar n => pure #[toJson "bvar", toJson n]
    | .sort u => pure #[toJson "sort", levelJson u]
    | .const n us => pure #[toJson "const", nameJson n, toJson (us.map levelJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi | .forallE n t b bi => do
      let tag := if e.isLambda then "lam" else "forall"
      let bi := match bi with | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
      pure #[toJson tag, nameJson n, toJson (← encode t), toJson (← encode b), toJson bi]
    | .letE n t v b nondep => do pure #[toJson "let", nameJson n, toJson (← encode t), toJson (← encode v), toJson (← encode b), toJson nondep]
    | .lit (.natVal n) => pure #[toJson "nat", toJson n]
    | .lit (.strVal s) => pure #[toJson "str", toJson s]
    | .proj n i b => do pure #[toJson "proj", nameJson n, toJson i, toJson (← encode b)]
    | _ => panic! "unclosed expression"
  let s ← get
  set ({ids := s.ids.insert (ExprStructEq.mk e) s.nodes.size, nodes := s.nodes.push (toJson node)} : Dump)
  return s.nodes.size
partial def readName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size == 2 then return .str (← readName a[0]!) (← a[1]!.getStr?)
  if a.size == 3 then return .num (← readName a[0]!) (← fromJson? a[1]!)
  throw "bad name"
partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => do pure (.zero)
  | "succ" => do pure (.succ (← readLevel a[1]!))
  | "max" => do pure (.max (← readLevel a[1]!) (← readLevel a[2]!))
  | "imax" => do pure (.imax (← readLevel a[1]!) (← readLevel a[2]!))
  | "param" => do pure (.param (← readName a[1]!))
  | _ => throw "bad level"
def decode (nodes : Array Json) : Except String (Array Expr) := do
  let mut es := #[]
  for j in nodes do
    let a ← j.getArr?
    let child := fun (i : Nat) => (show Except String Expr from do
      let n : Nat ← fromJson? a[i]!
      if n < es.size then return es[n]! else throw "non-topological DAG")
    let e : Expr ← match ← a[0]!.getStr? with
      | "bvar" => do pure (.bvar (← fromJson? a[1]!))
      | "sort" => do pure (.sort (← readLevel a[1]!))
      | "const" => do pure (.const (← readName a[1]!) (← (← a[2]!.getArr?).toList.mapM readLevel))
      | "app" => do pure (.app (← child 1) (← child 2))
      | "lam" | "forall" => do
        let bi : Nat ← fromJson? a[4]!
        let bi ← match bi with | 0 => pure BinderInfo.default | 1 => pure .implicit | 2 => pure .strictImplicit | 3 => pure .instImplicit | _ => throw "bad binder"
        if (← a[0]!.getStr?) == "lam" then pure (.lam (← readName a[1]!) (← child 2) (← child 3) bi)
        else pure (.forallE (← readName a[1]!) (← child 2) (← child 3) bi)
      | "let" => do pure (.letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← fromJson? a[5]!))
      | "nat" => do pure (.lit (.natVal (← fromJson? a[1]!)))
      | "str" => do pure (.lit (.strVal (← fromJson? a[1]!)))
      | "proj" => do pure (.proj (← readName a[1]!) (← fromJson? a[2]!) (← child 3))
      | _ => throw "bad expression"
    es := es.push e
  return es
end BoundaryCodec

open Lean Meta Elab Command BoundaryCodec
run_elab do
  let all ← ofExcept (Json.parse (← IO.FS.readFile "../../results/matcher-compat/ordinary-old-batch.json"))
  let oldGroups ← ofExcept (← ofExcept (all.getObjVal? "groups")).getObj?
  let helperGroups ← ofExcept (← ofExcept (all.getObjVal? "helpers")).getObj?
  let order ← ofExcept (all.getObjValAs? (Array Json) "order")
  let mut helperNames : Array Name := #[]
  for row in order do
    let row ← ofExcept row.getArr?
    let group ← ofExcept row[0]!.getStr?
    let i : Nat ← ofExcept (fromJson? row[1]!)
    let d := helperGroups[group]!
    let a ← ofExcept (← ofExcept (d.getObjValAs? (Array Json) "aux"))[i]!.getArr?
    helperNames := helperNames.push (← ofExcept (readName a[0]!))
  let rename := fun (e : Expr) => e.replace fun e => match e with
    | .const n us => if helperNames.contains n then some (.const (`AllOld ++ n) us) else none
    | _ => none
  for row in order do
    let row ← ofExcept row.getArr?
    let group ← ofExcept row[0]!.getStr?
    let i : Nat ← ofExcept (fromJson? row[1]!)
    let d := helperGroups[group]!
    let es ← ofExcept (decode (← ofExcept (d.getObjValAs? (Array Json) "nodes")))
    let a ← ofExcept (← ofExcept (d.getObjValAs? (Array Json) "aux"))[i]!.getArr?
    let n ← ofExcept (readName a[0]!)
    let us ← (← ofExcept a[1]!.getArr?).toList.mapM fun x => ofExcept (readName x)
    let ti : Nat ← ofExcept (fromJson? a[2]!)
    let vi : Nat ← ofExcept (fromJson? a[3]!)
    let kind ← ofExcept a[4]!.getStr?
    if kind == "theorem" then addDecl <| .thmDecl {
      name := `AllOld ++ n
      levelParams := us
      type := rename es[ti]!
      value := rename es[vi]!
    }
    else addDecl (forceExpose := true) <| .defnDecl {
      name := `AllOld ++ n
      levelParams := us
      type := rename es[ti]!
      value := rename es[vi]!
      hints := .opaque
      safety := .safe }
  let mut checked := 0
  let mut current : Array Json := #[]
  for (_, old) in oldGroups.toArray do
    let es ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))
    let records ← ofExcept (old.getObjValAs? (Array Json) "records")
    for r in records do
      let a ← ofExcept r.getArr?
      let user ← ofExcept (readName a[0]!)
      let n ← realizeGlobalConstNoOverload (mkIdent user)
      let ci ← getConstInfo n
      unless toJson (ci.levelParams.map nameJson) == a[1]! do throwError "changed universe parameters {user}"
      let (_, dump) := (BoundaryCodec.encode ci.type).run {}
      current := current.push (Json.mkObj [("name",toJson user.toString),("nodes",toJson dump.nodes)])
      let i : Nat ← ofExcept (fromJson? a[2]!)
      let oldType := rename es[i]!
      check oldType
      check ci.type
      unless ← isDefEq oldType ci.type do throwError "not defeq: {user}"
      let historical := `AllHistoricalUse ++ user
      if ← isProp oldType then addDecl <| .thmDecl {
        name := historical
        levelParams := ci.levelParams
        type := oldType
        value := .const n (ci.levelParams.map .param)
      }
      else addDecl (forceExpose := true) <| .defnDecl {
        name := historical
        levelParams := ci.levelParams
        type := oldType
        value := .const n (ci.levelParams.map .param)
        hints := .opaque
        safety := .safe }
      checked := checked+1
      let axioms ← collectAxioms historical
      unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
        throwError "unexpected axiom: {user} {axioms}"
      logInfo m!"PASS actual historical type/kernel/defeq/axioms: {user}; actual={n}"
  for n in helperNames do
    let axioms ← collectAxioms (`AllOld ++ n)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected helper axiom {n}"
  logInfo m!"Kernel checked {helperNames.size} actual old helper type/value pairs under fresh names"

  unless checked == 115 do throwError "incomplete historical ordinary checks"
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative defeq control failed"
  IO.FS.writeFile "../../results/matcher-compat/ordinary-current-expressions.json" ((toJson current).compress)
  logInfo m!"Checked {checked} actual historical types in ordinary modern imports."
