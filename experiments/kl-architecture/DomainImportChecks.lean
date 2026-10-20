import OAI.GroupTheory.Coxeter.Bruhat.Basic
import OAI.GroupTheory.Coxeter.Parabolic.Standard
import OAI.GroupTheory.Coxeter.Roots.ReflectionOrder
import OAI.Combinatorics.MomentGraph.GradedSheaf.Uniqueness
import Lean

-- Independently import the object layers without Hecke, Bott or the KL result.
run_elab do
  let env ← Lean.getEnv
  for n in env.header.moduleNames do
    if n.toString.startsWith "OAI.RepresentationTheory." then
      throwError "Object layer imported a representation application: {n}"
  for n in #[`OAI.KLInvariance.bruhat_iff_reduced_subword,
      `OAI.KLInvariance.StandardParabolic.bruhat_inclusion_iff,
      `OAI.KLInvariance.TitsSpace.normalizedRoot_affine,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.edge_bijective_of_vertex] do
    unless env.contains n do throwError "Missing original object API: {n}"
