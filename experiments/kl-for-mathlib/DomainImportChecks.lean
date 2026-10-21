import ForMathlib.GroupTheory.Coxeter.Bruhat.Basic
import ForMathlib.GroupTheory.Coxeter.Parabolic.Standard
import ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness
import Lean

-- Independently import the object layers without Hecke, Bott or the KL result.
run_elab do
  let env ← Lean.getEnv
  for n in env.header.moduleNames do
    if n.toString.startsWith "ForMathlib.RepresentationTheory." then
      throwError "Object layer imported a representation application: {n}"
  for n in #[`OAI.KLInvariance.bruhat_iff_reduced_subword,
      `OAI.KLInvariance.StandardParabolic.bruhat_inclusion_iff,
      `OAI.KLInvariance.TitsSpace.normalizedRoot_affine,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.edge_bijective_of_vertex] do
    unless env.contains n do throwError "Missing original object API: {n}"
