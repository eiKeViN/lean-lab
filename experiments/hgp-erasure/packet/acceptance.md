# Acceptance

Deliver a Lean 4 project building offline against the supplied versions.
Export the results A–E of source.md and supply a short TARGETS.md mapping each
letter to a module and its declaration names, with instructions for the build.
A grader will import the results downstream and inspect their types, transitive
axioms and connection to the definitions. Equivalent encodings and theorem
splits are accepted. Only propext, Classical.choice and Quot.sound may occur
as transitive axioms. Every claimed target requires its complete proof. Keep
a record of any incomplete targets in the mapping. Supply actual check
operators, quotient/image semantics (or a proved equivalent), the two
sectors, and the concrete call sites. No rank hypothesis, positivity assumption,
hidden target assumption or tautological replacement for the mathematical
meaning is permitted. The two numerical identities in D must hold universally.
