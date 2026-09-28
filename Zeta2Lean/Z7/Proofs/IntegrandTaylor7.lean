module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Product form of the centred integrand

gap: '' (routine, adapted).  **Proved** (architect, 2026-09-26).

**Task.** Prove `Stmt_IntegrandTaylor7` from `Stmt_PF7`: for all `u, x`,
`integrand u x = -6 [ε³] R_n(y + ε)` with `y = x - 20u + 1/2` (i.e. `-R_n'''(x + 1/2 - n/2)`).
This is the bridge to the product form used by Theorem V (`Stmt_Valuation7`).

**Proof** (as `Zeta2Lean/Pair/Proofs/IntegrandTaylor.lean`).  `y` is a half-integer, so
`y + j ≠ 0` for all `j` and `Stmt_PF7.series` gives
`Rser u y = ∑_{k ≤ n} ∑_{i=1}^{4} C r_{i,k} ((C (y+k) + X)^i)⁻¹`.  For `c ≠ 0`, `i ≥ 1`,
`[X³] ((c + X)^i)⁻¹ = -(i (i+1) (i+2)/6) c^{-(i+3)}` (`it_coeff_three`), and
`y + k = ((x + k - 20u : ℤ) : ℚ) + 1/2`.  So `-6 [ε³] Rser u y = ∑_{i,k} (i)₃ r_{i,k}
(x + k - 20u + 1/2)^{-(i+3)} = integrand u x` (`genIntegrandZ` with `a = 4`, sums swapped).

**Numerical check.** `python/z7_mirror.py`, section "IntegrandTaylor7".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

/-- Closed form of the inverse power: for `c ≠ 0`,
`((c + X)^{d+1})⁻¹ = c^{-(d+1)} · ∑_n C(d+n, d) (-X/c)^n` (copied from the pair). -/
private theorem it_inv_C_add_X_pow_succ (c : ℚ) (hc : c ≠ 0) (d : ℕ) :
    ((C c + X : PowerSeries ℚ) ^ (d + 1))⁻¹ =
      C (c⁻¹ ^ (d + 1)) * rescale (-c⁻¹) (mk fun n => ((d + n).choose d : ℚ)) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · have h1 : (C c + X : PowerSeries ℚ) = C c * rescale (-c⁻¹) (1 - X) := by
      rw [map_sub, map_one, rescale_X, mul_sub, mul_one, ← mul_assoc, ← map_mul, mul_neg,
        mul_inv_cancel₀ hc, map_neg, map_one, neg_one_mul, sub_neg_eq_add]
    rw [h1, mul_pow, ← map_pow C, ← map_pow (rescale (-c⁻¹))]
    calc C (c⁻¹ ^ (d + 1)) * rescale (-c⁻¹) (mk fun n => ((d + n).choose d : ℚ)) *
          (C (c ^ (d + 1)) * rescale (-c⁻¹) ((1 - X) ^ (d + 1)))
        = C (c⁻¹ ^ (d + 1) * c ^ (d + 1)) *
            rescale (-c⁻¹) ((mk fun n => ((d + n).choose d : ℚ)) * (1 - X) ^ (d + 1)) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by
          rw [mk_add_choose_mul_one_sub_pow_eq_one, ← mul_pow, inv_mul_cancel₀ hc, one_pow,
            map_one, map_one, one_mul]
  · simp [hc]

/-- `[X³] ((c + X)^i)⁻¹ = -(i (i+1) (i+2) / 6) c^{-(i+3)}` for `c ≠ 0`, `i ≥ 1`. -/
private theorem it_coeff_three (c : ℚ) (hc : c ≠ 0) (i : ℕ) (hi : 1 ≤ i) :
    coeff 3 ((C c + X : PowerSeries ℚ) ^ i)⁻¹ =
      -((i : ℚ) * (i + 1) * (i + 2) / 6) * c⁻¹ ^ (i + 3) := by
  obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
  rw [it_inv_C_add_X_pow_succ c hc d, coeff_C_mul, coeff_rescale, coeff_mk]
  have hch : (((d + 3).choose d : ℕ) : ℚ) = ((d : ℚ) + 1) * (d + 2) * (d + 3) / 6 := by
    rw [Nat.cast_choose ℚ (by omega : d ≤ d + 3), Nat.add_sub_cancel_left]
    simp [Nat.factorial]
    field_simp
    ring
  rw [hch]
  push_cast
  ring

/-- A half-integer is non-zero. -/
private theorem it_half_ne_zero (z : ℤ) : (z : ℚ) + 1 / 2 ≠ 0 := by
  intro hz
  have h1 : ((2 * z + 1 : ℤ) : ℚ) = 0 := by
    push_cast
    linear_combination 2 * hz
  have h2 : (2 * z + 1 : ℤ) = 0 := by exact_mod_cast h1
  omega

theorem IntegrandTaylor7_proof (hPF : Stmt_PF7) : Stmt_IntegrandTaylor7 := by
  intro u x
  -- the base points `y + k` are the half-integers `(x + k - 20u) + 1/2`
  have hbase : ∀ k : ℕ, (x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2 + (k : ℚ) =
      ((((x : ℤ) + k - (20 * u : ℕ) : ℤ) : ℚ) + 1 / 2) := by
    intro k
    push_cast
    ring
  have hy : ∀ j ≤ 40 * u, ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2) + (j : ℚ) ≠ 0 := by
    intro j _
    rw [hbase j]
    exact it_half_ne_zero _
  rw [hPF.series u _ hy]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold integrand genIntegrandZ
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k _ => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hc : (x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2 + (k : ℚ) ≠ 0 := by
    rw [hbase k]
    exact it_half_ne_zero _
  rw [coeff_C_mul, it_coeff_three _ hc i hi1, hbase k]
  ring

end Zeta2.Z7

end
