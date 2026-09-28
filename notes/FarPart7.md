# FarPart7 (Lemma 4.5) — prover notes (round 4)

## Status: PROVED (no sorry, kernel-checked)

* `Zeta2Lean/Z7/Proofs/FarPart7.lean`: `FarPart7_proof : Stmt_PF7 → Stmt_FarPart7` (statement
  unchanged). Helpers in namespace `Zeta2.Z7.FP7`, same file; no new files. Imports only
  `Proofs/LocalExpansion7` (not edited).
* `#print axioms FarPart7_proof`: `[propext, Classical.choice, Quot.sound]`. `leanchecker` replay of
  the module: exit 0. `bash scripts/build.sh Zeta2Lean.Z7.Proofs.FarPart7`: green, no warnings
  (also with `weak.linter.mathlibStandardSet`). Elaboration takes about 4 s.
* The hypothesis `Stmt_PF7` is unused (binder renamed `_hPF`). `g_{j,ξ}` has no pole in the disc,
  so only the class poles contribute.

## Proof route (see the file header)

1. `farRes_eq`: `farRes = q^{E+1} ResF τ Φ`, where `Φ_w = rescale q ((Û g)(-k₀ + q w/2 + ε))`. It
   is proved per pole (`farPole_eq`) from `LE7.coeff_Gser_mul_eq_sum`, `LE7.coeff_lin_neg` and
   `LE7.coeff_Gser_mul`, with `S = rescale q g`.
2. `trunc_far`: one `LE7.trunc_general` per `i'` (`A = Onum`, `B = Oden·(X + i')^j`), combined
   with `choose` and summed. The existential `F` of `trunc_general` hides `F_m = [ε^m](A/B)`, so
   `J = 0` is used to get it back: `F_m ≡ [ε^m] (Û g)(-k₀+ε) (mod q^{M-m})`.
3. Power sums (`powsum_val`): Fermat reduces `(i'-k₀)^{-s}` to `(i'-k₀)^{q-1-s}` mod `q`, then
   `FiniteField.sum_pow_lt_card_sub_one` on `ZMod q`. The reindexing uses `sum_range_zmod` and
   `Equiv.subRight`.
4. `farRes_val` with `M = (-E).toNat`. A polynomial term is non-zero only if `m = -E-1`, and then
   `m ≤ q-2-j` by the hypothesis `j + 1 ≤ q + E`. The remainder has valuation `≥ M`
   (`LE7.PSV_taylorAt_model`).

## Pitfalls

* `rw [map_mul]` inside `coeff n (A * B)` tries `coeff` (a linear map) first and fails with a
  `MulHomClass` error. Write `map_mul (rescale (q : ℚ))`.
* `Fintype.sum_equiv e f g h` needs `f` given explicitly. Otherwise `f` is inferred as `g ∘ e`
  and `rw` finds no match.
* Do not write the word "sorry" in docstrings: `scripts/audit.sh` counts it.

## Math remarks (no error found)

The informal proof matches the Lean proof, with the exact truncation in place of the infinite
q-adic series (as in ClassLemma7). `q ≥ 5` is used only as `q ≠ 2`. `q > 2x + 2` is used only for
Lemma 4.2 (q-integrality of `taylorAt` at the class poles).
