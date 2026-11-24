import FQCExternal.ExternalFacts

open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

namespace FQCExternal
theorem c1_0_external : ((D1 1 0 0 ∧ D1 1 0 1) ∧ D1 1 1 0) ∧ ((D1 1 1 1 ∧ D1 2 0 1) ∧ D1 1 2 0) :=
  ⟨⟨External.batch0,
   External.batch1⟩,
   ⟨External.batch2,
   External.batch3⟩⟩


#print axioms c1_0_external
end FQCExternal
