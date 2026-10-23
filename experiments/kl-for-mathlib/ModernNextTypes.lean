module
import ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex
import Lean

open Lean

private def rolloutProofAliases : Array Name := #[`OAI.KLInvariance.AdaptedDyer.rotateEdge._proof_1, `OAI.KLInvariance.BruhatGraph.edgeFactorMap._proof_1, `OAI.KLInvariance.BruhatGraph.edgeFactorMap._proof_2, `OAI.KLInvariance.BruhatGraph.lowerCharacter._proof_1, `OAI.KLInvariance.BruhatGraph.lowerCharacter._proof_2, `OAI.KLInvariance.BruhatGraph.lowerCharacter._proof_3, `OAI.KLInvariance.BruhatGraph.normalizedKernel._proof_1, `OAI.KLInvariance.BruhatGraph.normalizedKernel._proof_2, `OAI.KLInvariance.BruhatGraph.polynomialLabel._proof_1, `OAI.KLInvariance.BruhatGraph.polynomialLabel._proof_2, `OAI.KLInvariance.BruhatGraph.polynomialLabel._proof_3, `OAI.KLInvariance.BruhatGraph.polynomialRoot._proof_1, `OAI.KLInvariance.BruhatGraph.polynomialRoot._proof_2, `OAI.KLInvariance.BruhatGraph.polynomialRoot._proof_3, `OAI.KLInvariance.Cotangent.root._proof_1, `OAI.KLInvariance.Dihedral.inducedLabel._proof_1, `OAI.KLInvariance.Dihedral.pairMatrix._proof_1, `OAI.KLInvariance.Dihedral.pairMatrix._proof_2, `OAI.KLInvariance.Dihedral.pairMatrix._proof_3, `OAI.KLInvariance.EdgeAlgebra.rootIdeal._proof_1, `OAI.KLInvariance.EdgeAlgebra.symQuotientMap._proof_3, `OAI.KLInvariance.EmbeddedModule.scaled._proof_1, `OAI.KLInvariance.EmbeddedModule.scaled._proof_2, `OAI.KLInvariance.FiniteCharacterLocalization.diagonal._proof_1, `OAI.KLInvariance.FiniteCharacterLocalization.diagonal._proof_2, `OAI.KLInvariance.Graded.ModuleData.changePiece._proof_1, `OAI.KLInvariance.Graded.ModuleData.changePiece._proof_2, `OAI.KLInvariance.Graded.ModuleData.char._proof_1, `OAI.KLInvariance.Graded.ModuleData.char._proof_2, `OAI.KLInvariance.Graded.ModuleData.char._proof_3, `OAI.KLInvariance.Graded.ModuleData.char._proof_4, `OAI.KLInvariance.Graded.ModuleData.range._proof_1, `OAI.KLInvariance.Graded.quotientPiece._proof_1, `OAI.KLInvariance.Graded.quotientPiece._proof_2, `OAI.KLInvariance.Hecke.leftInv._proof_1, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.boundary._proof_1, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_1, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_10, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_11, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_12, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_13, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_14, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_15, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_16, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_17, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_18, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_2, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_3, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_4, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_5, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_6, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_7, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_8, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend._proof_9, `OAI.KLInvariance.MomentGraph.GradedSheaf.kernelHilbert._proof_1, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.symm._proof_1, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient._proof_1, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient._proof_2, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient._proof_3, `OAI.KLInvariance.MomentGraph.Sheaf.outgoingLabelProduct._proof_1, `OAI.KLInvariance.MomentGraph.Sheaf.stalkMap._proof_1, `OAI.KLInvariance.MomentGraph.Sheaf.stalkMap._proof_2, `OAI.KLInvariance.MomentGraph.Sheaf.stalkMap._proof_3, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf._proof_1, `OAI.KLInvariance.MomentGraph.Sheaf.structureVertexIso._proof_1, `OAI.KLInvariance.MomentGraph.bottomGraph._proof_1, `OAI.KLInvariance.MomentGraph.removeGraph._proof_1, `OAI.KLInvariance.MomentGraph.removeGraph._proof_2, `OAI.KLInvariance.MomentGraph.removeGraph._proof_3, `OAI.KLInvariance.MomentGraph.removeTarget._proof_1, `OAI.KLInvariance.MomentGraph.splitEdge._proof_1, `OAI.KLInvariance.MomentGraph.splitEdge._proof_2, `OAI.KLInvariance.MomentGraph.splitVertex._proof_1, `OAI.KLInvariance.MomentGraph.splitVertex._proof_2, `OAI.KLInvariance.QuotientEdge.descend._proof_1, `OAI.KLInvariance.QuotientEdge.iso._proof_1, `OAI.KLInvariance.QuotientEdge.iso._proof_2, `OAI.KLInvariance.QuotientEdge.iso._proof_3, `OAI.KLInvariance.Realization.Extension._proof_1, `OAI.KLInvariance.Realization.geometricSimple._proof_1, `OAI.KLInvariance.Realization.geometricSimple._proof_2, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_1, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_2, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_3, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_4, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_5, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_6, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_7, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_8, `OAI.KLInvariance.ReflectionFrobenius.crossPair._proof_9, `OAI.KLInvariance.ReflectionFrobenius.polynomialAction._proof_1, `OAI.KLInvariance.ReflectionFrobenius.polynomialLinear._proof_1, `OAI.KLInvariance.ReflectionFrobenius.reflectionAction._proof_1, `OAI.KLInvariance.ReflectionFrobenius.symmetricMap._proof_1, `OAI.KLInvariance.ReflectionFrobenius.symmetricMap._proof_2, `OAI.KLInvariance.ReflectionFrobenius.symmetricMap._proof_3, `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate._proof_1, `OAI.KLInvariance.ReflectionSchedules.momentFunctional._proof_1, `OAI.KLInvariance.ReflectionSchedules.momentFunctional._proof_2, `OAI.KLInvariance.ScalarQuotient.coordinateReduction._proof_1, `OAI.KLInvariance.ScalarQuotient.coordinateReduction._proof_2, `OAI.KLInvariance.ScalarQuotient.coordinateReduction._proof_3, `OAI.KLInvariance.SchedulePaths.blockValues._proof_1, `OAI.KLInvariance.SchedulePaths.blockValues._proof_2, `OAI.KLInvariance.SymmetricPlaneIdeal.ideal._proof_1, `OAI.KLInvariance.SymmetricPlaneIdeal.quotientMap._proof_3, `OAI.KLInvariance.TitsSpace.EdgeCoefficient._proof_1, `OAI.KLInvariance.TitsSpace.PlaneBasis.negPrefixRoot._proof_1, `OAI.KLInvariance.TitsSpace.PlaneBasis.prefixRoot._proof_1, `OAI.KLInvariance.TitsSpace.SymmetricCoefficient._proof_1, `OAI.KLInvariance.TitsSpace.bottFullIndex._proof_1, `OAI.KLInvariance.TitsSpace.bottHeadPairCoordinates._proof_1, `OAI.KLInvariance.TitsSpace.bottHeadPairCoordinates._proof_2, `OAI.KLInvariance.TitsSpace.bottSetSecond._proof_1, `OAI.KLInvariance.TitsSpace.bottSetSecond._proof_2, `OAI.KLInvariance.TitsSpace.bottTopHom._proof_1, `OAI.KLInvariance.TitsSpace.bottTopHom._proof_2, `OAI.KLInvariance.TitsSpace.bottUnit._proof_1, `OAI.KLInvariance.TitsSpace.bottUnit._proof_2, `OAI.KLInvariance.TitsSpace.bottWeight._proof_1, `OAI.KLInvariance.TitsSpace.dominant._proof_1, `OAI.KLInvariance.TitsSpace.embedLinear._proof_1, `OAI.KLInvariance.TitsSpace.embedLinear._proof_2, `OAI.KLInvariance.TitsSpace.embedLinear._proof_3, `OAI.KLInvariance.TitsSpace.form._proof_1, `OAI.KLInvariance.TitsSpace.form._proof_2, `OAI.KLInvariance.TitsSpace.gram._proof_1, `OAI.KLInvariance.TitsSpace.height._proof_1, `OAI.KLInvariance.TitsSpace.height._proof_2, `OAI.KLInvariance.TitsSpace.linearPolynomial._proof_1, `OAI.KLInvariance.TitsSpace.linearPolynomial._proof_2, `OAI.KLInvariance.TitsSpace.linearPolynomial._proof_3, `OAI.KLInvariance.TitsSpace.normal._proof_1, `OAI.KLInvariance.TitsSpace.pencil._proof_1, `OAI.KLInvariance.TitsSpace.planePrime._proof_1, `OAI.KLInvariance.TitsSpace.reducedPlaneRoot._proof_1, `OAI.KLInvariance.TitsSpace.reducedPlaneRoot._proof_2, `OAI.KLInvariance.TitsSpace.rootCoeff._proof_1, `OAI.KLInvariance.TitsSpace.simpleFixed._proof_1, `OAI.KLInvariance.TitsSpace.simplePositive._proof_1, `OAI.KLInvariance.TitsSpace.symmetricGrading._proof_1, `OAI.KLInvariance.TitsSpace.symmetricGrading._proof_2, `OAI.KLInvariance.intervalBottom._proof_1, `OAI.LinearDescent.descend._proof_1, `OAI.LinearDescent.descend._proof_2, `OAI.LinearDescent.descend._proof_3, `OAI.PerfectAdjoint.adjoint._proof_1, `OAI.PerfectAdjoint.adjoint._proof_2, `OAI.PerfectAdjoint.adjoint._proof_3, `OAI.PerfectAdjoint.adjoint._proof_4]
private def rolloutOwners : Array Name := #[`ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex]
private def rolloutOriginalKind : ConstantKind → String
  | .defn => "def" | .thm => "theorem" | .«axiom» => "axiom"
  | .«opaque» => "opaque" | .quot => "quotient" | .induct => "inductive"
  | .ctor => "constructor" | .recursor => "recursor"

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
        else if let some (.axiomInfo info) := env.find? n then
          let owned := (env.getModuleIdxFor? n).any fun i => rolloutOwners.contains env.header.moduleNames[i.toNat]!
          if owned && rolloutProofAliases.contains n && getOriginalConstKind? env n == some .thm then
            let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
            modify fun st => { st with proofAliases := st.proofAliases.insert n }
            pure ["proof", toString proposition]
          else pure ["const", reprStr n, reprStr us]
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
  let policy ← IO.ofExcept <| Json.parse (← IO.FS.readFile "module-next-types.json")
  let entries := (← IO.ofExcept policy.getObj?).toList
  unless entries.length == 61 do throwError "Unexpected rollout coverage"
  let some path ← IO.getEnv "LEAN_TYPES_OUT" | throwError "Set LEAN_TYPES_OUT"
  let out ← IO.FS.Handle.mk (System.FilePath.mk path) .write
  let mut closures : Std.HashMap Name (Array Name) := {}
  for (str, _) in entries do
    let n := str.toName
    let axioms ← Lean.collectAxioms n
    unless axioms.all (fun a => #[`propext, `Quot.sound, `Classical.choice].contains a) do
      throwError "Unexpected axiom closure: {n}: {axioms}"
    closures := closures.insert n axioms
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for (str, record) in entries do
      let n := str.toName
      let want ← IO.ofExcept <| record.getObjValAs? String "kind"
      let some ci := env.find? n | throw <| IO.userError s!"Missing rollout public name: {n}"
      unless (getOriginalConstKind? env n).map rolloutOriginalKind == some want do
        throw <| IO.userError s!"Wrong original kind: {n}"
      let visible := declarationKind ci
      unless visible == want || (want == "theorem" && visible == "axiom") do
        throw <| IO.userError s!"Unexpected public representation: {n}: {visible}, wanted {want}"
      let some owner := env.getModuleIdxFor? n | throw <| IO.userError "Missing owner"
      unless rolloutOwners.contains env.header.moduleNames[owner.toNat]! do
        throw <| IO.userError s!"Wrong rollout owner: {n}"
      out.putStrLn s!"MODULE\t{env.header.moduleNames[owner.toNat]!}"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{want}"
      IO.println s!"PUBLIC {n}: visible={visible}; original={want}; axioms={closures[n]!}"
    let st ← get
    unless st.privateOwners.isEmpty do throw <| IO.userError "Private rewriting is not allowed"
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t0\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t61\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
