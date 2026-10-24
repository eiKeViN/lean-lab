module
import ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic
import ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis
import ForMathlib.Algebra.Module.CoefficientChange.Basic
import ForMathlib.Algebra.Module.CoefficientChange.Dual
import ForMathlib.Algebra.Module.Cover.Local
import ForMathlib.Algebra.Module.Graded.DualAndShift
import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange
import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic
import ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover
import ForMathlib.Algebra.Module.Localization.FiniteCharacters
import ForMathlib.Algebra.Module.Projective.Transport
import ForMathlib.Algebra.Module.ReflectionPair.TensorDescent
import ForMathlib.Algebra.Module.ReflectionPair.TensorKernel
import ForMathlib.Algebra.Module.ReflectionPair.Twist
import ForMathlib.Combinatorics.MomentGraph.Boundary.Basic
import ForMathlib.Combinatorics.MomentGraph.Boundary.Extension
import ForMathlib.Combinatorics.MomentGraph.Boundary.Hom
import ForMathlib.Combinatorics.MomentGraph.Boundary.Models
import ForMathlib.Combinatorics.MomentGraph.Boundary.Summand
import ForMathlib.Combinatorics.MomentGraph.Boundary.Uniqueness
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Basic
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hilbert
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.StalkMaps
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness
import ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion
import ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Hom
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Isomorphism
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Models
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Products
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Uniqueness
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Zero
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
import ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder
import ForMathlib.GroupTheory.Coxeter.Roots.Splines
import ForMathlib.LinearAlgebra.Avoidance
import ForMathlib.LinearAlgebra.Dual.Frobenius
import ForMathlib.LinearAlgebra.KernelCoordinates
import ForMathlib.RepresentationTheory.BottSamelson.TitsWords
import ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted
import ForMathlib.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder
import ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates
import ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall
import Lean
open Lean
run_elab do
  let names : Array Name := #[`OAI.KLInvariance.CoefficientChange.ext.match_1, `OAI.KLInvariance.LocalCover.splitEquiv.match_3, `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_1, `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_3, `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate_injective.match_1_2, `OAI.KLInvariance.ReflectionFrobenius.wallMatrix_mulVec.match_1_1, `OAI.KLInvariance.ReflectionPairTranslation.Twist.ext.match_1, `OAI.KLInvariance.TitsSpace.exists_common_transverse.match_1_1, `OAI.KLInvariance.LocalCover.splitEquiv.match_6]
  for n in names do
    try
      let actual ← realizeGlobalConstNoOverload (mkIdent n)
      logInfo m!"RESOLVED {n} => {actual}"
    catch _ => logInfo m!"UNAVAILABLE {n}"
