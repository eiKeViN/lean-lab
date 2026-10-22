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
import ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality
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
import OAI.RepresentationTheory.KazhdanLusztig.Sheaves
import Lean

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
  let ty := Expr.forallE `p (.sort .zero)
    (.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let value := Expr.lam `p (.sort .zero)
    (.lam `h (.bvar 0) (.bvar 0) .default) .default
  let base : TheoremVal := { name := `SerializationProbe, levelParams := [], type := ty, value := value }
  let renamedTy := Expr.forallE `q (.sort .zero)
    (.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let renamedValue := Expr.lam `q (.sort .zero)
    (.lam `h (.bvar 0) (.bvar 0) .default) .default
  unless ty == renamedTy && value == renamedValue do
    throwError "Expected alpha-equivalent controls for the previous BEq Expr guard"
  unless sameSerializedTheorem (.thmInfo base) (.thmInfo base) do
    throwError "Identical theorem record rejected"
  let cases : Array ConstantInfo := #[
    .thmInfo { base with type := renamedTy },
    .thmInfo { base with value := renamedValue },
    .thmInfo { base with type := .mdata {} ty },
    .thmInfo { base with value := .mdata {} value },
    .thmInfo { base with name := `Other },
    .thmInfo { base with levelParams := [`u] },
    .thmInfo { base with all := [`Other] },
    .thmInfo { base with type := (.forallE `p (.sort .zero)
      (.forallE `h (.bvar 0) (.bvar 1) .default) .implicit) }]
  for candidate in cases do
    if sameSerializedTheorem (.thmInfo base) candidate then
      throwError "Changed serialized theorem record accepted"
  let safeDef : DefinitionVal := {
    name := base.name
    levelParams := []
    type := ty
    value := value
    hints := .opaque
    safety := .safe }
  let unsafeDef := { safeDef with safety := DefinitionSafety.«unsafe» }
  let abbrevDef := { safeDef with hints := ReducibilityHints.abbrev }
  for candidate in #[safeDef, unsafeDef, abbrevDef] do
    if sameSerializedTheorem (.defnInfo safeDef) (.defnInfo candidate) then
      throwError "Unsupported definition duplicate accepted"
  IO.println "Serialization guard: identical record and alpha controls accepted; 8 theorem mutations and 3 unsupported definition cases rejected."

run_elab do
  let env ← getEnv
  let some path ← IO.getEnv "LEAN_TYPES_OUT" | throwError "Set LEAN_TYPES_OUT"
  let out ← IO.FS.Handle.mk (System.FilePath.mk path) .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    let mut seen : Std.HashMap Name ConstantInfo := {}
    let mut duplicates := 0
    for idx in [:env.header.moduleData.size] do
      let moduleName := env.header.moduleNames[idx]!
      if moduleName.toString.startsWith "OAI." || moduleName.toString.startsWith "ForMathlib." then
        for info in env.header.moduleData[idx]!.constants do
          if !isPrivateName info.name && !info.name.isInternal then
            if let some previous := seen[info.name]? then
              -- Only complete, structurally identical theorem records are accepted.
              unless sameSerializedTheorem info previous do
                throw <| IO.userError s!"Conflicting serialized declaration: {info.name}"
              duplicates := duplicates + 1
              out.putStrLn s!"SERIALIZED_COPY\t{info.name}\t{moduleName}"
              continue
            seen := seen.insert info.name info
            let some actual := env.find? info.name | throw <| IO.userError "Missing global declaration"
            let some owner := env.getModuleIdxFor? info.name | throw <| IO.userError "Missing global owner"
            out.putStrLn s!"MODULE\t{env.header.moduleNames[owner.toNat]!}"
            let id ← dumpType env out actual.type
            out.putStrLn s!"TYPE\t{actual.name}\t{(toJson (reprStr actual.levelParams)).compress}\t{id}\t{declarationKind actual}"
    for n in (← get).proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    let state ← get
    for (canonical, original) in state.privateOwners.toList do
      if state.unrenamed.contains canonical || env.contains canonical then
        throw <| IO.userError "Private/public canonical-name collision"
      out.putStrLn s!"PRIVATE_CANONICAL\t{original}\t{canonical}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{state.privateOwners.size}\t{state.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t{seen.size}\t{duplicates}\t{state.proofAliases.size}"
  discard <| action.run {}
  out.flush
  IO.println "Unique global public types exported with checked serialization copies and compiler-proof propositions."
