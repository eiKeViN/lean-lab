import FiniteProbability
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for root in [``QuantumExperiments.FiniteProbability.productMean_prod,
      ``QuantumExperiments.FiniteProbability.productMean_coordinate,
      ``QuantumExperiments.FiniteProbability.productMean_pair,
      ``QuantumExperiments.FiniteProbability.productMean_sum_coordinate,
      ``QuantumExperiments.FiniteProbability.weighted_variance,
      ``QuantumExperiments.FiniteProbability.covariance_on_fin,
      ``QuantumExperiments.FiniteProbability.coordinates_independent] do
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut external : NameSet := {}
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      unless visited.contains n do
        visited := visited.insert n
        if let some info := env.find? n then
          for dep in info.getUsedConstantsAsSet.toList do
            if dep.toString.startsWith "QuantumExperiments." then
              pending := pending.push dep
            else if dep.toString.startsWith "ProbabilityTheory." ||
                dep.toString.startsWith "MeasureTheory.integral" then
              external := external.insert dep
    logInfo m!"SLICE {root}: {visited.toList}"
    logInfo m!"UPSTREAM {root}: {external.toList}"
