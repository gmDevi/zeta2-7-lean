module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Lemma L for cand3: only `ζ₂(7)` survives (proof §3)

gap: '' (routine).  **Proved** (architect).

**Task.** Prove `Stmt_L7` from `Stmt_GenLinearFormZ` and `Stmt_CoeffVanish7`: the Riemann sums of
`integrand u` converge to `ρ + 60 c₃ J₆`.

**Proof.** By definition `integrand u = genIntegrandZ 4 (40u) (20u) (rcoef u)`,
`rho u = genRhoZ 4 (40u) (20u) (rcoef u)` and `csum u i = genCsum (40u) (rcoef u) i` (all `rfl`).
`Stmt_GenLinearFormZ 4 (40u) (20u) (rcoef u)` gives the limit `ρ + ∑_{i=1}^{4} (i)₃ c_i J_{i+3}`;
`c₁ = c₂ = c₄ = 0` (`Stmt_CoeffVanish7`) leaves `(3·4·5) c₃ J₆ = 60 c₃ J₆`.  (No `J_odd = 0` is
needed.)

**Numerical check.** `python/z7_mirror.py`, section "TranslationNeg / GenLinearFormZ / L7".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

/-- The limit value of `Stmt_GenLinearFormZ` at `a = 4`, `r = rcoef u` is `ρ + 60 c₃ J₆`. -/
private theorem L7_limit_eq (hV : Stmt_CoeffVanish7) (u : ℕ) :
    (genRhoZ 4 (40 * u) (20 * u) (rcoef u) : ℚ_[2]) +
        ∑ i ∈ Icc (1 : ℕ) 4, ((i : ℚ_[2]) * (i + 1) * (i + 2)) *
          (genCsum (40 * u) (rcoef u) i : ℚ_[2]) * J (i + 3) =
      (rho u : ℚ_[2]) + 60 * (csum u 3 : ℚ_[2]) * J 6 := by
  have hIcc : (Icc (1 : ℕ) 4) = {1, 2, 3, 4} := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h1 : genCsum (40 * u) (rcoef u) 1 = 0 := hV.c1 u
  have h2 : genCsum (40 * u) (rcoef u) 2 = 0 := hV.ceven u 2 ⟨1, rfl⟩
  have h4 : genCsum (40 * u) (rcoef u) 4 = 0 := hV.ceven u 4 ⟨2, rfl⟩
  simp only [h1, h2, h4, rho, csum]
  push_cast
  ring

theorem L7_proof (hG : Stmt_GenLinearFormZ) (hV : Stmt_CoeffVanish7) : Stmt_L7 := by
  intro u
  have key := hG 4 (40 * u) (20 * u) (rcoef u)
  rw [L7_limit_eq hV u] at key
  exact key

end Zeta2.Z7

end
