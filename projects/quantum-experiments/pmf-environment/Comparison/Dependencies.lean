import PMFComparison
import Lean

open Lean Elab Command

/- Diagnostic only: collect local constants in elaborated types and values. -/
run_cmd do
  let env ← getEnv
  for root in [``QuantumExperiments.PMFComparison.Finite.variance_on_fin,
      ``QuantumExperiments.PMFComparison.Transport.variance_on_fin,
      ``QuantumExperiments.PMFComparison.Finite.covariance_on_fin,
      ``QuantumExperiments.PMFComparison.Transport.covariance_on_fin] do
    let mut pending := #[root]
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      unless visited.contains n do
        visited := visited.insert n
        if let some info := env.find? n then
          for dep in info.getUsedConstantsAsSet.toList do
            if dep.toString.startsWith "QuantumExperiments." then
              pending := pending.push dep
    logInfo m!"SLICE {root}: {visited.toList}"
