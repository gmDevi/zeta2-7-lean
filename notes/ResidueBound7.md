# ResidueBound7 (Lemmas G1–G6, `Stmt_ResidueBound7`) — DONE (round 4)

`Zeta2Lean/Z7/Proofs/ResidueBound7.lean`: `ResidueBound7_proof : Stmt_PF7 → Stmt_ResidueBound7`
is sorry-free; `#print axioms` = `propext, Classical.choice, Quot.sound`. Elaborates in ~6 s
(`bash scripts/check.sh ...`), `bash scripts/build.sh Zeta2Lean.Z7.Proofs.ResidueBound7` green.
No new files; helpers are in namespace `Zeta2.Z7.RB7` inside the proof file. `hPF` is unused
(linter warning only; the statement was not touched).

Constants: `C = 8 e^20 40^21`, `B = 21`, i.e. `log|r_{i,k}| ≤ n U(k/n) + 21 log(n+1) + 20 + log 8`
(weaker than proof §5's `log(n+1) + 14 log n + 37.44`, irrelevant for `Growth7`, which only needs
polynomial `(u+1)^B`).

## Route (no integrals, no complex analysis)
* **G1+G2** `tnorm F = ∑_{l<4} |coeff l F| 2^{-l}` (in ℝ, for `PowerSeries ℚ`):
  `tnorm_mul` (explicit 4×4 coefficient expansion + `nlinarith`), `tnorm_prod`, `tnorm_pow`,
  `tnorm_C_add_X = |b| + 1/2`, `tnorm_lin = |b| + 1`, `tnorm_inv ≤ (|b| - 1/2)⁻¹` for `|b| ≥ 1`
  (explicit inverse `inv_C_add_X`: coefficients `(-1)^l b^{-(l+1)}`), `coeff_le_tnorm`
  (`|coeff l F| ≤ 8 tnorm F`, `l < 4`). `inv_prod_pow` uses `PowerSeries.mul_inv_rev`,
  `PowerSeries.inv_pow` (hypothesis-free in this Mathlib). Result `tnorm_Gser_le`:
  `tnorm (Gser u k) ≤ P_k := (|40u - 2k| + 1) ∏_m ∏_{c∈C_m} (|c-k+1/2|+1/2) ∏_{j≠k} (|j-k|-1/2)^{-a_j}`.
* **G3** telescoping with `F = Fx`: basic facts `Fx_sub_le` (`F b - F a ≤ (b-a) log b`),
  `le_Fx_sub` (`(b-a) log a ≤ F b - F a`, `a > 0`), `Fx_sub_ge` (`F(b-a) ≤ F b - F a`),
  `neg_one_le_Fx`, `pole_cell`. Potentials `Phi k c` (numerator), `Psi k j` (poles) with one-step
  inequalities `num_step`, `pole_step`, sums `num_sum`, `pole_sum`, endpoint errors `phi_err`,
  `psi_err_lo/hi` (≤ `log(|x-k|+1) + 2`). Blocks: `num_block_n`, `pole_block_n` (error
  `2 log(n+1) + 2` each).
* **G4–G5** `Upot_scaled`: `40u·U(k/(40u)) = ∑_t w_t F(u p_t - k)` (via `Fx_scale`, the log-n
  terms vanish because `∑ w_t = ∑ w_t p_t = 0`); `blocks_poles_eq` identifies it with
  `∑_m [F(B_m - k) - F(A_m - k)] - ∑_{l<4} [F(40u-2lu-k) - F(2lu-k)]`
  (`apole_eq_sum`: `a_j = ∑_{l<4} [2lu ≤ j ≤ 40u-2lu]`, `pole_sum_decomp`).
* **G6** `P_bound`: `P_k ≤ e^20 (40u+1)^21 e^{nU(k/n)}`; `coeff_Gser_bound` then the main theorem
  (`rcoef = 0` outside `1 ≤ i ≤ a_k`).

## Pitfalls met (this Mathlib, Lean v4.35.0-rc2)
* `if_pos/if_neg/if_true` are deprecated: use `ite_eq_left/ite_eq_right/ite_true`.
* `Finset.prod_le_prod` is the ordered-monoid version; for nonneg reals use `Finset.prod_le_prod₀`.
* `Rat.cast_abs` takes the rational explicitly (`Rat.cast_abs b`).
* `Finset.sum_erase` needs `(a := k)` when used with `←` (else the erased point is a metavariable).
* After `push_cast`, `↑(eta m * u)` becomes `↑(eta m) * ↑u`: push_cast every hypothesis that
  `linarith` must match (including the identity `hid`).
