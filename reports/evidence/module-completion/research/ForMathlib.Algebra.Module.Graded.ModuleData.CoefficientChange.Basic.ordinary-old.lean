import Lean
import Mathlib
import ForMathlib.Algebra.Module.CoefficientChange.Basic
import ForMathlib.Algebra.Module.Graded.ModuleData.Basic

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic. Source spans: BottSamelson:28.
See migration.json and MIGRATION.md for exact provenance.
Changing coefficients of graded module data and their homomorphisms through a grading-preserving algebra equivalence. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 def changePiece (M : ModuleData.{uk,ua,um} 𝓐) : ℤ → Submodule k (CoefficientChange e M) :=
  fun n => (M.piece n).map (CoefficientChange.kEquiv e M).toLinearMap

 theorem mem_changePiece (M : ModuleData.{uk,ua,um} 𝓐) (n : ℤ) (m : CoefficientChange e M) :
    m ∈ changePiece e M n ↔ m.val ∈ M.piece n := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    change CoefficientChange.mk x=m at hxm
    exact (congrArg CoefficientChange.val hxm) ▸ hx
  · intro hm
    exact ⟨m.val,hm,rfl⟩

 def change (M : ModuleData.{uk,ua,um} 𝓐) : ModuleData.{uk,ua,um} 𝓑 where
  obj := ModuleCat.of B (CoefficientChange e M)
  kModule := inferInstance
  tower := inferInstance
  piece := changePiece e M
  decomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    apply image_isInternal M.piece (CoefficientChange.kEquiv e M).toLinearMap
      (CoefficientChange.kEquiv e M).surjective
    intro n m hm
    have hz : m=0 := congrArg CoefficientChange.val hm
    subst m
    simp only [map_zero]
  graded := by
    constructor
    intro i j b m hb hm
    apply (mem_changePiece e M (i+j) _).mpr
    change e.symm b • m.val ∈ M.piece (i+j)
    have ha : e.symm b ∈ 𝓐 i := (he i _).mpr (by simpa using hb)
    exact SetLike.GradedSMul.smul_mem ha ((mem_changePiece e M j m).mp hm)
  nonneg n hn := by simp only [changePiece,M.nonneg n hn,Submodule.map_bot]
  finite := inferInstance

 def changeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) :
    Hom (change e he M) (change e he N) where
  map := CoefficientChange.map e f.map
  graded n m hm := (mem_changePiece e N n _).mpr
    (f.graded n m.val ((mem_changePiece e M n m).mp hm))

 theorem change_free (M : ModuleData.{uk,ua,um} 𝓐) [Module.Free A M] :
    Module.Free B (change e he M) := inferInstanceAs (Module.Free B (CoefficientChange e M))

end
end KLInvariance.Graded.ModuleData
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
  let names : Array Name := #[`OAI.KLInvariance.Graded.ModuleData.changePiece.eq_1]
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
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."

open Lean

structure TypeDumpState where
  ids : ExprStructMap Nat := {}
  proofIds : ExprStructMap Nat := {}
  next : Nat := 0
  privateOwners : Std.HashMap Name Name := {}
  proofAliases : NameHashSet := {}
  unrenamed : NameHashSet := {}

-- Alpha equivalence ignores binder display names. Only compiler-private OAI
-- owner prefixes are erased from constant names; their user names stay exact.
-- There are no duplicate private user names in the pinned source.
private def canonicalConstant (n : Name) : Name :=
  if n.toString.startsWith "_private.OAI." then
    (privateToUserName? n).getD n
  else n

-- Keep every mathematical expression constructor, universe, binder info,
-- constant, application and de Bruijn index. Metadata and binder display names
-- have no effect on the mathematical type. A local compiler theorem auxiliary
-- is represented by its full proposition, using kernel proof irrelevance.
-- No proof body, general definition, data instance or user theorem is unfolded.
partial def dumpType (env : Environment) (out : IO.FS.Handle) (e : Expr)
    (proofContext := false) : StateT TypeDumpState IO Nat := do
  let cached : TypeDumpState ← get
  let cache := if proofContext then cached.proofIds else cached.ids
  if let some id := cache[ExprStructEq.mk e]? then return id
  if let .mdata _ body := e then return ← dumpType env out body proofContext
  let fields ← match e with
    | .bvar i => pure ["bvar", toString i]
    | .sort u => pure ["sort", reprStr u]
    | .const n us =>
      let proofName := match n with
        | .str _ s => s.startsWith "_proof_"
        | _ => false
      if n.isInternal && n.toString.startsWith "OAI." && proofName then
        if let some (.thmInfo info) := env.find? n then
          -- Kernel theorem declarations prove propositions. Their full
          -- proposition, including parameters, is retained; only its binder
          -- display/implicitness metadata is irrelevant to the proof value.
          let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
          modify fun st => { st with proofAliases := st.proofAliases.insert n }
          pure ["proof", toString proposition]
        else pure ["const", reprStr n, reprStr us]
      else
        let canonical := canonicalConstant n
        if canonical != n then
          if env.contains canonical then
            throw <| IO.userError "Private canonical name collides with an unrenamed global constant"
          if let some previous := (← get).privateOwners[canonical]? then
            if previous != n then throw <| IO.userError "Ambiguous private type constant"
          modify fun st => { st with privateOwners := st.privateOwners.insert canonical n }
        pure ["const", reprStr canonical, reprStr us]
    | .app f a => do
      let f ← dumpType env out f proofContext; let a ← dumpType env out a proofContext
      pure ["app", toString f, toString a]
    | .lam _ t b bi | .forallE _ t b bi => do
      let t ← dumpType env out t proofContext; let b ← dumpType env out b proofContext
      pure [if e.isLambda then "lam" else "forall", "_", if proofContext then "kernel" else reprStr bi, toString t, toString b]
    | .letE _ t v b nondep => do
      let t ← dumpType env out t proofContext; let v ← dumpType env out v proofContext; let b ← dumpType env out b proofContext
      pure ["let", "_", toString t, toString v, toString b, toString nondep]
    | .lit v => pure ["lit", reprStr v]
    | .proj n i b => do
      let b ← dumpType env out b proofContext
      pure ["proj", reprStr n, toString i, toString b]
    | .fvar _ | .mvar _ => throw <| IO.userError "Non-closed declaration type"
    | .mdata _ _ => unreachable!
  match e with
  | .const n _ =>
    if fields.head! == "const" && canonicalConstant n == n then
      modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | .proj n _ _ => modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | _ => pure ()
  let state : TypeDumpState ← get
  if proofContext then
    set { state with proofIds := state.proofIds.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  else
    set { state with ids := state.ids.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  out.putStrLn s!"NODE\t{state.next}\t{(toJson fields).compress}"
  return state.next

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

-- This experiment accepts duplicate serialized theorem records only.
-- Other ConstantInfo variants fail closed; their safety/hints are not omitted
-- from a purported full-record comparison. ExprStructEq retains binder names
-- and annotations, unlike BEq Expr (Expr.eqv).
private def sameSerializedTheorem (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams &&
      ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
      ExprStructEq.mk a.value == ExprStructEq.mk b.value && a.all == b.all
  | _, _ => false


run_elab do
  let env := (← Lean.getEnv).setExporting false
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.Graded.ModuleData.changePiece.eq_1] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t1\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
