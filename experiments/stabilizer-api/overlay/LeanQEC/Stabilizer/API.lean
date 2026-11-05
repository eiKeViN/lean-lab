import LeanQEC.Stabilizer.CSS
import LeanQEC.Stabilizer.Reindex

/-!
# Downstream stabilizer-code API

Import this module for construction, typed stabilizers, generating presentations,
the binary linear bridge, CSS entry points, and qubit permutations.

* Use `C.Stabilizer` for generic commutative algebra.
* Use `C.mul_comm` with ambient Pauli elements and membership proofs.
* Use `C.Presentation ι` to retain a particular choice of generators.
* Use `C.binaryLinearEquiv` to reuse binary linear algebra.
* Use `C.reindex` and `P.reindexQubits` to relabel qubits.
-/
