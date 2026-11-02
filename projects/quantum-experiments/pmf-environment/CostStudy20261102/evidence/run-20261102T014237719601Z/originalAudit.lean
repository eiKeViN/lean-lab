import PMFComparison.Finite
import PMFComparison.Transport
import Lean
open Lean Elab Command

private partial def canonicalType (e : Expr) : Expr :=
  match e with
  | .mdata _ a => canonicalType a
  | .forallE _ t b bi => .forallE Name.anonymous (canonicalType t) (canonicalType b) bi
  | .lam _ t b bi => .lam Name.anonymous (canonicalType t) (canonicalType b) bi
  | .letE _ t v b nd => .letE Name.anonymous (canonicalType t) (canonicalType v) (canonicalType b) nd
  | .app f a => .app (canonicalType f) (canonicalType a)
  | .proj s i a => .proj s i (canonicalType a)
  | e => e

run_cmd do
  let env ← getEnv
  for n in [`QuantumExperiments.PMFComparison.Finite.mean, `QuantumExperiments.PMFComparison.Finite.variance, `QuantumExperiments.PMFComparison.Finite.productMean, `QuantumExperiments.PMFComparison.Finite.mean_center, `QuantumExperiments.PMFComparison.Finite.productMean_prod, `QuantumExperiments.PMFComparison.Finite.productMean_coordinate, `QuantumExperiments.PMFComparison.Finite.productMean_pair, `QuantumExperiments.PMFComparison.Finite.productMean_sum, `QuantumExperiments.PMFComparison.Finite.productMean_sum_coordinate, `QuantumExperiments.PMFComparison.Finite.productMean_centered_sum_sq, `QuantumExperiments.PMFComparison.Finite.variance_on_fin, `QuantumExperiments.PMFBridgeDraft.Bridge.toPMF, `QuantumExperiments.PMFBridgeDraft.Bridge.toPMF_apply, `QuantumExperiments.PMFBridgeDraft.Bridge.toPMF_toReal, `QuantumExperiments.PMFBridgeDraft.ChannelProduct.law, `QuantumExperiments.PMFBridgeDraft.ChannelProduct.law_probability, `QuantumExperiments.PMFBridgeDraft.ChannelProduct.law_singleton, `QuantumExperiments.PMFBridgeDraft.ChannelProduct.on_fin_real_apply, `QuantumExperiments.PMFBridgeDraft.ChannelProduct.law_on_fin_eq_pi, `QuantumExperiments.PMFBridgeDraft.ChannelStatistics.integral_real, `QuantumExperiments.PMFBridgeDraft.ChannelStatistics.score_memLp_two, `QuantumExperiments.PMFComparison.Transport.integral_eq_mean, `QuantumExperiments.PMFComparison.Transport.variance_eq_finite, `QuantumExperiments.PMFBridgeDraft.ChannelStatistics.totalScore, `QuantumExperiments.PMFBridgeDraft.ChannelStatistics.variance_totalScore_of_memLp, `QuantumExperiments.PMFBridgeDraft.ChannelStatistics.variance_totalScore, `QuantumExperiments.PMFComparison.Transport.variance_on_fin] do
    let some ci := env.find? n | throwError "missing declaration {n}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"u{i}")
    let t := canonicalType (ci.type.instantiateLevelParams ci.levelParams levels)
    liftIO <| IO.println ("TYPEJSON " ++ (Json.mkObj [("name", toJson n.toString),
      ("type", toJson (reprStr t))]).compress)

#print axioms QuantumExperiments.PMFComparison.Finite.mean
#print axioms QuantumExperiments.PMFComparison.Finite.variance
#print axioms QuantumExperiments.PMFComparison.Finite.productMean
#print axioms QuantumExperiments.PMFComparison.Finite.mean_center
#print axioms QuantumExperiments.PMFComparison.Finite.productMean_prod
#print axioms QuantumExperiments.PMFComparison.Finite.productMean_coordinate
#print axioms QuantumExperiments.PMFComparison.Finite.productMean_pair
#print axioms QuantumExperiments.PMFComparison.Finite.productMean_sum
#print axioms QuantumExperiments.PMFComparison.Finite.productMean_sum_coordinate
#print axioms QuantumExperiments.PMFComparison.Finite.productMean_centered_sum_sq
#print axioms QuantumExperiments.PMFComparison.Finite.variance_on_fin
#print axioms QuantumExperiments.PMFBridgeDraft.Bridge.toPMF
#print axioms QuantumExperiments.PMFBridgeDraft.Bridge.toPMF_apply
#print axioms QuantumExperiments.PMFBridgeDraft.Bridge.toPMF_toReal
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelProduct.law
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelProduct.law_probability
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelProduct.law_singleton
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelProduct.on_fin_real_apply
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelProduct.law_on_fin_eq_pi
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelStatistics.integral_real
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelStatistics.score_memLp_two
#print axioms QuantumExperiments.PMFComparison.Transport.integral_eq_mean
#print axioms QuantumExperiments.PMFComparison.Transport.variance_eq_finite
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelStatistics.totalScore
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelStatistics.variance_totalScore_of_memLp
#print axioms QuantumExperiments.PMFBridgeDraft.ChannelStatistics.variance_totalScore
#print axioms QuantumExperiments.PMFComparison.Transport.variance_on_fin
