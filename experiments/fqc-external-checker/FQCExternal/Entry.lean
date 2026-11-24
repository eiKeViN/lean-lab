import FQCExternal.Vendor.Stream

open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth

namespace FQCExternal

def entryExec (w : Nat) (k : Bool × Box2DS → Bool) : Bool :=
  match boxTcOfWordOpt 28 w with
  | none => false
  | some (tc, bx) =>
    match Nat.ble tc 26 with
    | true => k (true, bx)
    | false => isFuseOutWord w && k (false, bx)

theorem entryExec_eq (w : Nat) (k : Bool × Box2DS → Bool) :
    entryExec w k = evalWordStage1Fast w k := by
  rw [evalWordStage1Fast, evalWordTcBoxFast_eq]
  cases hbox : boxTcOfWordOpt 28 w with
  | none => simp only [entryExec, hbox]
  | some p =>
    rcases p with ⟨tc, bx⟩
    simp only [entryExec, hbox]
    rw [isFuseOutWordFast_eq]
    cases Nat.ble tc 26 <;> cases isFuseOutWord w <;> rfl

theorem acceptedEntry_sound {w : Nat} (h : entryExec w (fun _ => true) = true) :
    ∃ e : Bool × Box2DS, ValidStage1Entry e := by
  have hfast : evalWordStage1Fast w (fun _ => true) = true := by
    rwa [← entryExec_eq]
  obtain ⟨e, he, _⟩ := evalWordStage1Fast_sound hfast
  exact ⟨e, he⟩

#print axioms entryExec_eq
#print axioms acceptedEntry_sound

end FQCExternal
