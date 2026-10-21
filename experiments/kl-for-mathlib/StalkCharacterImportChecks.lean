import OAI.KL.BottSamelson.StalkCharacter
import Lean

-- Character recurrences do not depend on upper-section projectivity or sheaf gluing.
run_elab do
  let env ← Lean.getEnv
  for n in #[`OAI.KL.BottSamelson.UpperSections, `OAI.KL.BottSamelson.Flabby,
      `OAI.KL.BottSamelson.Pairings, `OAI.KL.BottSamelson.AdjointSheaf] do
    if env.header.moduleNames.contains n then
      throwError "Stalk character imports an unrelated section/gluing module: {n}"
  unless env.contains `OAI.KLInvariance.TitsSpace.bottStalkCharacter_eq_heckeWord do
    throwError "Missing preserved stalk-character theorem"
  if env.contains `OAI.KLInvariance.TitsSpace.BottProjectiveUpper then
    throwError "Upper-section projectivity leaked into the stalk-character entrypoint"
