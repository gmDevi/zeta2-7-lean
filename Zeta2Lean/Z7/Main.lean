module

public import Zeta2Lean.Z7.Assembly
public import Zeta2Lean.Proofs.JConvergence
public import Zeta2Lean.Proofs.Translation
public import Zeta2Lean.Proofs.Criterion
public import Zeta2Lean.Proofs.DeltaCalculus
public import Zeta2Lean.Proofs.DeltaFunctions
public import Zeta2Lean.Cited.PNT
public import Zeta2Lean.Z7.Proofs.TranslationNeg
public import Zeta2Lean.Z7.Proofs.GenLinearFormZ
public import Zeta2Lean.Z7.Proofs.PartialFractions7
public import Zeta2Lean.Z7.Proofs.CoeffVanish7
public import Zeta2Lean.Z7.Proofs.LinearForm7
public import Zeta2Lean.Z7.Proofs.IntegrandTaylor7
public import Zeta2Lean.Z7.Proofs.Valuation7
public import Zeta2Lean.Z7.Proofs.AuxPrime7
public import Zeta2Lean.Z7.Proofs.NonvanishingLS7
public import Zeta2Lean.Z7.Proofs.MaxU7
public import Zeta2Lean.Z7.Proofs.ResidueBound7
public import Zeta2Lean.Z7.Proofs.Growth7
public import Zeta2Lean.Z7.Proofs.BigPrimes7
public import Zeta2Lean.Z7.Proofs.SmallPrimes7
public import Zeta2Lean.Z7.Proofs.Emin7
public import Zeta2Lean.Z7.Proofs.ClassLemma7
public import Zeta2Lean.Z7.Proofs.KernelIdentity7
public import Zeta2Lean.Z7.Proofs.FarPart7
public import Zeta2Lean.Z7.Proofs.PerPole7
public import Zeta2Lean.Z7.Proofs.ThmK7
public import Zeta2Lean.Z7.Proofs.HeadCert7
public import Zeta2Lean.Z7.Proofs.ResCert7
public import Zeta2Lean.Z7.Proofs.ExpBounds7
public import Zeta2Lean.Z7.Proofs.Denominators7

@[expose] public section

set_option linter.style.header false

/-!
# Zeta2Lean.Z7.Main — `ζ₂(7)` is irrational

Wires the proofs of all statements of `Zeta2Lean/Z7/Statements.lean` into `main7_of_stmts`
(`Z7/Assembly.lean`, complete), with the prime number theorem `Zeta2.PNT_proof`
(`Cited/PNT.lean`) and the shared proofs `JConv_proof`, `Translation_proof`, `Criterion_proof`,
`Delta_proof`, `DeltaFun_proof` (`Zeta2Lean/Proofs/*.lean`).

* `zeta2_7_irrational_of_gaps` — any rates `g + δ < 6.8 log 2`, with the three top-level gap
  statements (`Stmt_Growth7 g`, `Stmt_Denominators7 δ`, `Stmt_Nonvanishing7`) as hypotheses;
* `zeta2_7_irrational` — everything plugged in (rates `g7 = 0.71`, `delta7 = 3.99`).

`#print axioms` at the end of this file gives `[propext, Classical.choice, Quot.sound]` for both
`main7_of_stmts` and `zeta2_7_irrational`.  Dependency graph: `BLUEPRINT_Z7.md`.
-/

namespace Zeta2.Z7

/-- `Stmt_CoeffVanish7`. -/
theorem CoeffVanish7_full : Stmt_CoeffVanish7 :=
  CoeffVanish7_proof PF7_proof

/-- `Stmt_L7` (Lemma L). -/
theorem L7_full : Stmt_L7 :=
  L7_proof (GenLinearFormZ_proof JConv_proof Translation_proof TranslationNeg_proof)
    CoeffVanish7_full

/-- `Stmt_Valuation7` (Theorem V). -/
theorem Valuation7_full : Stmt_Valuation7 :=
  Valuation7_proof (IntegrandTaylor7_proof PF7_proof) Delta_proof (DeltaFun_proof Delta_proof)

/-- `Stmt_Growth7 g7` (Theorem G). -/
theorem Growth7_full : Stmt_Growth7 g7 :=
  Growth7_proof MaxU7_proof (ResidueBound7_proof PF7_proof)

/-- `Stmt_ThmK7` (Theorem K). -/
theorem ThmK7_full : Stmt_ThmK7 :=
  ThmK7_proof (ClassLemma7_proof PF7_proof) (KernelIdentity7_proof CoeffVanish7_full)
    (FarPart7_proof PF7_proof) (PerPole7_proof PF7_proof) Emin7_proof

/-- `Stmt_ExpBounds7` (the five ranges of primes). -/
theorem ExpBounds7_full : Stmt_ExpBounds7 :=
  ExpBounds7_proof ThmK7_full HeadCert7_proof ResCert7_proof Emin7_proof SmallPrimes7_proof
    BigPrimes7_proof

/-- `Stmt_Denominators7 delta7` (Theorem A). -/
theorem Denominators7_full : Stmt_Denominators7 delta7 :=
  Denominators7_proof ExpBounds7_full

/-- `Stmt_Nonvanishing7` (Theorem N + Lai–Sprang). -/
theorem Nonvanishing7_full : Stmt_Nonvanishing7 :=
  Nonvanishing7_proof L7_full (AuxPrime7_proof PF7_proof CoeffVanish7_full)

/-- **Main theorem, general form.**  For any rates with `g + δ < 6.8 log 2`: given the three
top-level gap statements, the Riemann sums defining every `J s` converge and `ζ₂(7)` is
irrational. -/
theorem zeta2_7_irrational_of_gaps (g δ : ℝ) (hmargin : g + δ < 34 / 5 * Real.log 2)
    (hGrowth : Stmt_Growth7 g) (hDen : Stmt_Denominators7 δ) (hNV : Stmt_Nonvanishing7) :
    SevenStatement :=
  main7_of_stmts g δ hmargin JConv_proof L7_full Valuation7_full Criterion_proof hGrowth hDen hNV
    PNT_proof

/-- **Main theorem.**  The Riemann sums defining every `J s` converge (the Volkenborn integrals
exist), and the 2-adic zeta value `ζ₂(7) = J 6 / 768` is irrational. -/
theorem zeta2_7_irrational :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧ ¬ ∃ q : ℚ, zeta2 7 = q :=
  zeta2_7_irrational_of_gaps g7 delta7 margin7 Growth7_full Denominators7_full Nonvanishing7_full

end Zeta2.Z7

#print axioms Zeta2.Z7.main7_of_stmts
#print axioms Zeta2.Z7.zeta2_7_irrational
