import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
import ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient
import ForMathlib.LinearAlgebra.Reflection.Plane
import ForMathlib.Combinatorics.DirectedPaths.Basic
import ForMathlib.Combinatorics.Dihedral.SignedCount
import Lean

-- These general objects must remain independently importable, without the
-- Coxeter realizations, concrete sheaves, Bott words or final KL theorem.
run_elab do
  let env ← Lean.getEnv
  for n in env.header.moduleNames do
    let s := n.toString
    if s.startsWith "ForMathlib.RepresentationTheory." ||
       s.startsWith "ForMathlib.GroupTheory.Coxeter." ||
       s.startsWith "ForMathlib.Combinatorics.MomentGraph." then
      throwError "Unexpected domain dependency in foundational import: {n}"
  for n in #[`OAI.KLInvariance.Graded.ModuleData,
      `OAI.KLInvariance.SymmetricPlaneIdeal.quotientEquiv,
      `OAI.KLInvariance.SignedDihedral.arrowAfter_pair] do
    unless env.contains n do throwError "Missing original public declaration: {n}"
