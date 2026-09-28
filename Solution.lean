module

public import Zeta2Lean.Z7.Main

@[expose] public section

/-!
# Proof of the statement in `Challenge.lean`

`Zeta2.Z7.zeta2_7_irrational` (`Zeta2Lean/Z7/Main.lean`) is the main theorem of this repository,
and its type is the statement of `Challenge.lean`. That statement uses the definitions of
`Zeta2Lean/Defs.lean`, of which `Challenge.lean` contains verbatim copies, so this module does not
restate them. Comparator checks that the two statements, and every definition they use, are
identical, and that the proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

/-- **ζ₂(7) is irrational** (the statement of `Challenge.lean`). -/
theorem zeta2_7_irrational_palomar :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧ ¬ ∃ q : ℚ, zeta2 7 = q :=
  zeta2_7_irrational

end Zeta2.Z7

end
