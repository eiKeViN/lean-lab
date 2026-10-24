import Lean
import Mathlib
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion. Source spans: GradedSheaves:15.
See migration.json and MIGRATION.md for exact provenance.
Removing a vertex and splitting graph coordinates into the remaining graph and incident edges. GraphEquiv is currently supplied by the existing graded reindex source unit. -/

namespace OAI

section
namespace KLInvariance.MomentGraph
universe um
variable {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

 def removeGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    OrderedGraph {y : V // y ≠ x} {e : E // G.source e ≠ x} where
  source e := ⟨G.source e.val,e.property⟩
  target e := ⟨G.target e.val,ht e.val⟩
  increasing e := G.increasing e.val

 def removeTarget (x : V) (ht : ∀ e, G.target e ≠ x) :
    {e : E // G.source e = x} → {y : V // y ≠ x} := fun e => ⟨G.target e.val,ht e.val⟩

noncomputable def splitVertex (x : V) : V ≃ WithBot {y : V // y ≠ x} := by
  classical
  exact
    { toFun := fun y => if h : y=x then ⊥ else (⟨y,h⟩ : {y : V // y ≠ x})
      invFun := WithBot.recBotCoe x Subtype.val
      left_inv := by intro y; by_cases h : y=x <;> simp [h]
      right_inv := by
        intro y
        induction y using WithBot.recBotCoe with
        | bot => simp
        | coe y => simp [y.property] }

noncomputable def splitEdge (x : V) : E ≃ {e : E // G.source e ≠ x} ⊕ {e : E // G.source e = x} := by
  classical
  exact
    { toFun := fun e => if h : G.source e=x then Sum.inr ⟨e,h⟩ else Sum.inl ⟨e,h⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := by intro e; by_cases h : G.source e=x <;> simp [h]
      right_inv := by
        intro e
        cases e with
        | inl e => simp [e.property]
        | inr e => simp [e.property] }

omit [PartialOrder V] in
@[simp] theorem splitVertex_self (x : V) : splitVertex x x = ⊥ := by
  classical
  simp [splitVertex]

omit [PartialOrder V] in
 theorem splitVertex_ne (x y : V) (hy : y ≠ x) :
    splitVertex x y = (⟨y,hy⟩ : {y : V // y ≠ x}) := by
  classical
  simp [splitVertex,hy]

noncomputable def splitGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    GraphEquiv G (bottomGraph (removeGraph G x ht) (removeTarget G x ht)) where
  vertex := splitVertex x
  edge := splitEdge G x
  source := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,bottomGraph]
    · simp [splitEdge,splitVertex,h,bottomGraph,removeGraph]
  target := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeTarget]
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeGraph]

 theorem splitEdge_labels {A : Type*} (α : E → A) (x : V) :
    (Sum.elim (fun e : {e : E // G.source e ≠ x} => α e.val)
      (fun e : {e : E // G.source e = x} => α e.val)) ∘ (splitEdge G x) = α := by
  classical
  funext e
  by_cases h : G.source e=x <;> simp [splitEdge,h]

end KLInvariance.MomentGraph
end

end OAI

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
  let names : Array Name := #[`OAI.KLInvariance.MomentGraph.splitEdge.eq_1, `OAI.KLInvariance.MomentGraph.splitVertex.eq_1]
  let env := (← Lean.getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending : Array Name := names
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
