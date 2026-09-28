# PerPole7 (Lemma 4.7) — prover notes (round 4)

## Status: PROVED (sorry-free, kernel-checked)

* `Zeta2Lean/Z7/Proofs/PerPole7.lean`: `PerPole7_proof : Stmt_PF7 → Stmt_PerPole7` (the hypothesis
  is unused and named `_hPF`; the statement is unchanged, `Main` applies it positionally).
* `#print axioms Zeta2.Z7.PerPole7_proof`: `[propext, Classical.choice, Quot.sound]`.
  `leanchecker Zeta2Lean.Z7.Proofs.PerPole7`: exit 0.  `bash scripts/build.sh
  Zeta2Lean.Z7.Proofs.PerPole7`: green, no warnings (style linters included).
  `lake env lean Zeta2Lean/Z7/Main.lean` (against the current oleans): exit 0.
  `scripts/audit.sh`: file no longer listed.
* No new files besides this note; the import is now `Zeta2Lean.Z7.Proofs.LocalExpansion7`
  (read-only use of `LE7`).  Defs/Statements/Assembly/Main/DenTable untouched.

## Proof (about 40 lines, namespace `Zeta2.Z7.PP7`)

`PP7.perPole` proves the bound at `k = k₀ + J q` (`hJ : k₀ + J q ≤ 40u`); `PerPole7_proof`
rewrites `k = k % q + (k / q) q` (`Nat.mod_add_div`).

1. `unfold rcoef`; outside `1 ≤ i ≤ a_k` the value is `0` (`LE7.valGe_zero`).
2. `rw [LE7.Gser_factor, coeff_C_mul, coeff_X_pow_mul']`: `r_{i,k} = q^{E+ord} ·
   (if ctr ≤ a_k - i then [ε^{a_k-i-ctr}] (Û · rescale q⁻¹ τ_k) else 0)`; the `else` branch is
   `r_{4,n/2} = 0` at the centre.
3. `LE7.coeff_mul_rescale_inv`, `coeff_mul`, `Finset.mul_sum` (twice), `LE7.valGe_sum`: each term is
   `q^{E+ord} · (q^N)⁻¹ · (q^m [ε^m]Û · τ_l)` with `m + l = N = a_k - i - ctr`.
4. `τ_l = 0`: trivial.  Otherwise `PoleLevAt` (unfolded) gives `l ≤ E - netE w - T`, using
   `l + 1 ≤ -netE w` (from `l ≤ N`, `i ≥ 1`, `LE7.ord_pole : ord + ctr = a_k`,
   `LE7.netE_pole : netE w = -a_k + ctr`).  The valuation bound is `LE7.valGe_mul` chained with
   `LE7.valGe_qzpow`, `PP7.valGe_inv_qpow`, `PP7.valGe_qpow`, `LE7.PSV_Uhat` (`[ε^m]Û` integral)
   and `LE7.PSV_taylorAt_model` (Lemma 4.2, `τ_l` integral, needs `80u + 2q < q²`); `omega` closes
   `T ≤ E + ord - N + m` after `unfold LE7.ord`.

## Pitfalls met

* `Finset.mem_antidiagonal` does not match the `HasAntidiagonal` antidiagonal produced by
  `coeff_mul`; use `Finset.HasAntidiagonal.mem_antidiagonal`.
* `push_neg` is deprecated in this Mathlib (warning); use `push Not`.

## Math remarks (no error found)

* Lemma 4.7 needs only `q ≠ 2` and `80u + 2q < q²` (for Lemma 4.2); `q ≥ 5` is used as `q ≠ 2`.
  `Stmt_PF7` is not needed: `Gser_factor` comes straight from the definition of `Gser`.
