module
import OAI.Architecture
import ForMathlib.Algebra.BigOperators.FiniteCharacterCancellation
import ForMathlib.Algebra.BigOperators.SingleCoordinate
import ForMathlib.Algebra.Module.Cover.Product
import ForMathlib.Algebra.Module.Flat.Kernel
import ForMathlib.Algebra.Module.Free.ScalarDivisibility
import ForMathlib.Algebra.Module.Graded.Adjoint
import ForMathlib.Algebra.Module.Graded.AlgebraMap
import ForMathlib.Algebra.Module.Graded.Basis
import ForMathlib.Algebra.Module.Graded.Components
import ForMathlib.Algebra.Module.Graded.FinitePieces
import ForMathlib.Algebra.Module.Graded.Generators
import ForMathlib.Algebra.Module.Graded.Hilbert.Basic
import ForMathlib.Algebra.Module.Graded.Hilbert.Images
import ForMathlib.Algebra.Module.Graded.Hilbert.Increment
import ForMathlib.Algebra.Module.Graded.Hilbert.Numerator
import ForMathlib.Algebra.Module.Graded.Hilbert.RationalFunction
import ForMathlib.Algebra.Module.Graded.Hilbert.Series
import ForMathlib.Algebra.Module.Graded.HomogeneousDual
import ForMathlib.Algebra.Module.Graded.HomogeneousEquiv
import ForMathlib.Algebra.Module.Graded.HomogeneousMul
import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
import ForMathlib.Algebra.Module.Graded.ModuleData.Character
import ForMathlib.Algebra.Module.Graded.ModuleData.CharacterDual
import ForMathlib.Algebra.Module.Graded.ModuleData.CoverUniqueness
import ForMathlib.Algebra.Module.Graded.ModuleData.Duality
import ForMathlib.Algebra.Module.Graded.ModuleData.Equality
import ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection
import ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom
import ForMathlib.Algebra.Module.Graded.ModuleData.Range
import ForMathlib.Algebra.Module.Graded.ModuleData.Transport
import ForMathlib.Algebra.Module.Graded.NonnegativeBasis
import ForMathlib.Algebra.Module.Graded.PolynomialMap
import ForMathlib.Algebra.Module.Graded.RegularScalar
import ForMathlib.Algebra.Module.Localization.Lattice
import ForMathlib.Algebra.Module.Localization.Membership
import ForMathlib.Algebra.Module.Localization.Products
import ForMathlib.Algebra.Module.Localization.ProjectiveLattice
import ForMathlib.Algebra.Module.Projective.Range
import ForMathlib.Algebra.Module.Projective.ReverseFiltration
import ForMathlib.Algebra.Module.Projective.ScalarKernel
import ForMathlib.Algebra.Module.Projective.ScalarQuotient
import ForMathlib.Algebra.Module.Quotient.KernelReduction
import ForMathlib.Algebra.Module.Quotient.ScalarImage
import ForMathlib.Algebra.Module.Submodule.PiIdeal
import ForMathlib.Algebra.Module.Submodule.ProductScaling
import ForMathlib.Algebra.Module.Submodule.ScaledImage
import ForMathlib.Algebra.Order.Field.RealScaling
import ForMathlib.Algebra.Polynomial.LowPart
import ForMathlib.Algebra.Polynomial.Reciprocal
import ForMathlib.Algebra.Polynomial.ScaledEvaluation
import ForMathlib.Algebra.Polynomial.ScaledReciprocity
import ForMathlib.Algebra.Polynomial.TransferEvaluation
import ForMathlib.Combinatorics.Dihedral.SignedCount
import ForMathlib.Combinatorics.DirectedPaths.Basic
import ForMathlib.Combinatorics.DirectedPaths.Monotone
import ForMathlib.Combinatorics.DirectedPaths.PositiveTransfer
import ForMathlib.Combinatorics.DirectedPaths.ScalarMap
import ForMathlib.Combinatorics.DirectedPaths.SortedSchedule
import ForMathlib.Combinatorics.DirectedPaths.Subpaths
import ForMathlib.Combinatorics.DirectedPaths.Suffix
import ForMathlib.Combinatorics.DirectedPaths.Transfer
import ForMathlib.GroupTheory.Coxeter.Bruhat.Basic
import ForMathlib.GroupTheory.Coxeter.Bruhat.Defs
import ForMathlib.GroupTheory.Coxeter.Bruhat.Descent
import ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset
import ForMathlib.GroupTheory.Coxeter.Bruhat.Transport
import ForMathlib.GroupTheory.Coxeter.Dihedral.Words
import ForMathlib.GroupTheory.Coxeter.Exchange
import ForMathlib.GroupTheory.Coxeter.Parabolic.InversionList
import ForMathlib.GroupTheory.Coxeter.Parabolic.Standard
import ForMathlib.GroupTheory.Coxeter.Parabolic.Support
import ForMathlib.GroupTheory.Coxeter.Realization.Cotangent
import ForMathlib.GroupTheory.Coxeter.Realization.Faithful
import ForMathlib.GroupTheory.Coxeter.Realization.Geometric
import ForMathlib.GroupTheory.Coxeter.Realization.Positivity
import ForMathlib.GroupTheory.Coxeter.Realization.Tits
import ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension
import ForMathlib.LinearAlgebra.ConjugateRange
import ForMathlib.LinearAlgebra.CoordinateProjection
import ForMathlib.LinearAlgebra.Dual.Adjoint
import ForMathlib.LinearAlgebra.Dual.BalancedCut
import ForMathlib.LinearAlgebra.Dual.IntegralSupport
import ForMathlib.LinearAlgebra.Dual.Summand
import ForMathlib.LinearAlgebra.Dual.TransportPairing
import ForMathlib.LinearAlgebra.KernelTransport
import ForMathlib.LinearAlgebra.PairProjection
import ForMathlib.LinearAlgebra.PlaneReduction
import ForMathlib.LinearAlgebra.Quotient.Transport
import ForMathlib.LinearAlgebra.Reflection.Bilinear
import ForMathlib.LinearAlgebra.Reflection.Classification
import ForMathlib.LinearAlgebra.Reflection.Forms
import ForMathlib.LinearAlgebra.Reflection.Plane
import ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient
import ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal
import ForMathlib.LinearAlgebra.TensorProduct.Coordinates
import ForMathlib.Order.Interval.Diamonds
import ForMathlib.RepresentationTheory.Hecke.Coefficients
import ForMathlib.RepresentationTheory.Hecke.DualR
import ForMathlib.RepresentationTheory.Hecke.Inverse
import ForMathlib.RepresentationTheory.Hecke.Operators
import ForMathlib.RepresentationTheory.Hecke.OrdinaryR
import ForMathlib.RepresentationTheory.Hecke.PositiveWord
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Dihedral
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.FiniteRankReduction
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.IntervalTransport
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Unique
import ForMathlib.RingTheory.Localization.RelativePrime
import OAI.KL.Compatibility.KernelTransport
import OAI.LinearAlgebra.KernelTransport
import OAI.RepresentationTheory.KazhdanLusztig.Bruhat
import OAI.RepresentationTheory.KazhdanLusztig.CanonicalKL
import OAI.RepresentationTheory.KazhdanLusztig.Comparison
import OAI.RepresentationTheory.KazhdanLusztig.Coxeter
import OAI.RepresentationTheory.KazhdanLusztig.Dihedral
import OAI.RepresentationTheory.KazhdanLusztig.Hecke
import OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat
import OAI.RepresentationTheory.KazhdanLusztig.Model
import OAI.RepresentationTheory.KazhdanLusztig.OrdinaryR
import OAI.RepresentationTheory.KazhdanLusztig.ReflectionPlane
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

open Lean Meta in
partial def proofLocations (a b : Expr) : MetaM (Nat × Array String) := do
  let a := a.consumeMData; let b := b.consumeMData
  if ExprStructEq.mk a == ExprStructEq.mk b then return (0, #[])
  if (← isProof a) && (← isProof b) then
    if ← isDefEq (← inferType a) (← inferType b) then return (1, #[])
  let combine := fun x y => (x.1+y.1, x.2++y.2)
  match a,b with
  | .app f x, .app g y => return combine (← proofLocations f g) (← proofLocations x y)
  | .lam n t v bi, .lam _ s w bj
  | .forallE n t v bi, .forallE _ s w bj =>
    if bi != bj then return (0, #["binder annotation"])
    let types ← proofLocations t s
    withLocalDecl n bi t fun x => do
      return combine types (← proofLocations (v.instantiate1 x) (w.instantiate1 x))
  | .proj n i x, .proj m j y =>
    if n != m || i != j then return (0, #["projection"])
    proofLocations x y
  | _,_ => return (0, #[s!"{a} => {b}"])

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
    | .const n us => if helperNames.contains n && n != `OAI.KLInvariance.TitsSpace.bottDegree.match_1 then some (.const (`AllOld ++ n) us) else none
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
      hints := .abbrev
      safety := .safe }
  let mut checked := 0
  let mut current : Array Json := #[]
  let retained ← getConstInfo `OAI.KLInvariance.TitsSpace.bottDegree.match_1
  let fresh ← getConstInfo `AllOld.OAI.KLInvariance.TitsSpace.bottDegree.match_1
  unless ← isDefEq (retained.value?.get!) (fresh.value?.get!) do throwError "retained matcher value changed"
  for (_, old) in oldGroups.toArray do
    let es ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))
    let records ← ofExcept (old.getObjValAs? (Array Json) "records")
    for r in records do
      let a ← ofExcept r.getArr?
      let user ← ofExcept (readName a[0]!)
      let n ← realizeGlobalConstNoOverload (mkIdent user)
      let ci ← getConstInfo n
      if a.size == 5 then
        let env ← getEnv
        unless defeqAttr.hasTag env n == (← ofExcept (fromJson? a[3]!)) &&
            backwardDefeqAttr.hasTag env n == (← ofExcept (fromJson? a[4]!)) do
          throwError "Changed original equation attributes: {user}"
      if user == `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend.eq_1 then
        let attrs ← ofExcept (Json.parse (← IO.FS.readFile "../../results/matcher-compat/onhom-old-attribute-values.json"))
        let env ← getEnv
        unless defeqAttr.hasTag env n == (← ofExcept (attrs.getObjValAs? Bool "defeq")) &&
            backwardDefeqAttr.hasTag env n == (← ofExcept (attrs.getObjValAs? Bool "backward_defeq")) do
          throwError "Changed OnHom equation attributes"
      unless toJson (ci.levelParams.map nameJson) == a[1]! do throwError "changed universe parameters {user}"
      let (_, dump) := (BoundaryCodec.encode ci.type).run {}
      current := current.push (Json.mkObj [("name",toJson user.toString),("nodes",toJson dump.nodes)])
      let i : Nat ← ofExcept (fromJson? a[2]!)
      let oldType := rename es[i]!
      check oldType
      check ci.type
      unless ← isDefEq oldType ci.type do throwError "not defeq: {user}"
      if (#[`OAI.KLInvariance.TitsSpace.bottHeadPairCoordinates.eq_1, `OAI.KLInvariance.TitsSpace.coefficientAction_reflection, `OAI.KLInvariance.TitsSpace.embedLinear.eq_1] : Array Name).contains user then
        let (proofs, data) ← proofLocations oldType ci.type
        logInfo m!"PROOF_LOCATIONS {user}: proof subexpressions={proofs}, nonproof differences={data}"

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
        hints := .abbrev
        safety := .safe }
      checked := checked+1
      let axioms ← collectAxioms historical
      unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
        throwError "unexpected axiom: {user} {axioms}"
      if (#[`OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.mapAssignment.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient.eq_1, `OAI.KLInvariance.MomentGraph.Sheaf.castStalkIso.eq_1, `OAI.KLInvariance.TitsSpace.bottCanonicalAdjointIso_vertex, `OAI.KLInvariance.TitsSpace.bottHeadPairCoordinates.eq_1, `OAI.KLInvariance.TitsSpace.bottImageSectionWordEquiv_coordinates, `OAI.KLInvariance.TitsSpace.bottSplitLeftWord_coordinates, `OAI.KLInvariance.TitsSpace.coefficientAction_reflection, `OAI.KLInvariance.TitsSpace.embedLinear.eq_1] : Array Name).contains user then
        forallTelescope ci.type fun xs body => do
          let some (_, lhs, rhs) := body.eq? | throwError "not equation: {user}"
          let proof := mkAppN (.const n (ci.levelParams.map .param)) xs
          let goal ← mkFreshExprSyntheticOpaqueMVar body
          let rewritten ← goal.mvarId!.rewrite lhs proof
          unless ← isDefEq rewritten.eNew rhs do throwError "rw changed target {user}"
          check rewritten.eqProof
          let thms ← ({} : SimpTheorems).add (.decl n) ci.levelParams.toArray proof
          let ctx ← Simp.mkContext (simpTheorems := #[thms])
          let (simplified, stats) ← simp lhs ctx
          unless stats.usedTheorems.contains (.decl n) do throwError "simp did not use actual equation: {user}"
          unless ← isDefEq simplified.expr rhs do throwError "simp changed target {user}"
          if let some p := simplified.proof? then check p
        logInfo m!"PASS actual equation directed rw/simp: {user}"
      logInfo m!"PASS actual historical type/kernel/defeq/axioms: {user}; actual={n}"
  for n in helperNames do
    let axioms ← collectAxioms (`AllOld ++ n)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected helper axiom {n}"
  logInfo m!"Kernel checked {helperNames.size} actual old helper type/value pairs under fresh names"

  unless checked == 120 do throwError "incomplete historical ordinary checks"
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative defeq control failed"
  pure ()
  logInfo m!"Checked {checked} actual historical types in ordinary modern imports."
