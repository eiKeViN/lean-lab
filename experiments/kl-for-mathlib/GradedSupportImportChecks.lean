import ForMathlib.Algebra.Module.Graded.HomogeneousEquiv
import ForMathlib.Algebra.Module.Graded.FinitePieces
import Lean

run_elab do
  let env ← Lean.getEnv
  for n in env.header.moduleNames do
    let s := n.toString
    if s.startsWith "OAI." || s.startsWith "ForMathlib.Algebra.Module.Graded.ModuleData." ||
       s.startsWith "ForMathlib.Algebra.Module.ReflectionPair." ||
       s.startsWith "ForMathlib.Algebra.Module.CoefficientChange." ||
       s.startsWith "ForMathlib.Combinatorics.MomentGraph." then
      throwError "Homogeneous equivalences/finiteness import unrelated constructions: {n}"
  for n in #[`OAI.KLInvariance.Graded.homogeneousPieceEquiv,
      `OAI.KLInvariance.Graded.perfectPairing_inverse_homogeneous,
      `OAI.KLInvariance.Graded.piPiece_finite] do
    unless env.contains n do throwError "Missing graded support declaration: {n}"
