import FQCExternal.Vendor.Stage1

open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

/- Generated only after successful external execution and exact source/input binding.
These axioms are external assumptions, not kernel-checked computations.
Upstream commit: a88de8ff65d78af564b2373088ca369dc95f6547
Checker sources SHA256: b7d720ebaa5864b1fcfbde548007329041411c23017c64ed3d798c771b8de8a1
Admission scripts SHA256: 21c97bbc8b90ae046c060e9de71e73e2c4b99b4efe364bdfe1f36ee4fbbc9870
Runtime observations and executable hashes: results/acceptance.json (not in Git).
-/

namespace FQCExternal.External

/-- External checker acceptance of `data/c1_0/batch0.json`.
Input SHA256: 049cecc361e43d6b98887286a172a0421d2ba77c9c301c2bd2d30ebe8a0a0a4d
Source: TopHadStage1Tab1Shard0.lean, theorem c1_0. -/
axiom batch0 : Stage1BatchCov (clm 1 0 0 (cl1 1 0 1))

/-- External checker acceptance of `data/c1_0/batch1.json`.
Input SHA256: 8bfd0ef5536d19bd26e96412443b378acf8c67783b7ec35300843cac4f50b766
Source: TopHadStage1Tab1Shard0.lean, theorem c1_0. -/
axiom batch1 : Stage1BatchCov (cl1 1 1 0)

/-- External checker acceptance of `data/c1_0/batch2.json`.
Input SHA256: b16b61b5872d40955bbe5c82740c8c360a4c90892deb4efacbb6973266f96fda
Source: TopHadStage1Tab1Shard0.lean, theorem c1_0. -/
axiom batch2 : Stage1BatchCov (clm 1 1 1 (cl1 2 0 1))

/-- External checker acceptance of `data/c1_0/batch3.json`.
Input SHA256: e93bfcc6e29495fbdf25beeb48f8c5bc4faf2186c1b90cb6982521f755e68743
Source: TopHadStage1Tab1Shard0.lean, theorem c1_0. -/
axiom batch3 : Stage1BatchCov (cl1 1 2 0)

end FQCExternal.External
