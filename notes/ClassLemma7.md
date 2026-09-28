# ClassLemma7 (Lemma 4.3) — prover notes (round 3)

## Status: PROVED (sorry-free, kernel-checked)

* `Zeta2Lean/Z7/Proofs/ClassLemma7.lean`: `ClassLemma7_proof : Stmt_PF7 → Stmt_ClassLemma7`.
* New shared helper `Zeta2Lean/Z7/Proofs/LocalExpansion7.lean` (namespace `Zeta2.Z7.LE7`), fully
  proved; imported by `ClassLemma7.lean` (so `Main` gets it transitively; `Main.lean` unchanged).
* `#print axioms ClassLemma7_proof` (and `LE7.Gser_factor`, `Rser_factor`, `grt_local`,
  `trunc_exists`): `[propext, Classical.choice, Quot.sound]`.  `leanchecker` replay of both modules:
  exit 0.  `bash scripts/build.sh Zeta2Lean.Z7.Main`: green.  No warnings in either file (also
  with the Mathlib style linters of `lake build`).  `scripts/audit.sh`: neither file listed.
* No statement changed; Defs/Statements/Assembly/Main/DenTable untouched.
* Obsolete dev copies `Zeta2Lean/Scratch/CL7_*.lean` (git-ignored) can be ignored/removed.

## Proof route (finite algebra; no q-adic analysis)

Notation: `n = 40u`, class `k % q = k₀`, `τ = localModel u q k₀`, `E = τ.E`, class pole
`k = k₀ + J q ≤ n` at the doubled local position `w = -2J`, `ord w = -netE w` (`= a_k`, or `a_k - 1`
at the centre when the δ-zero is in the disc: `ctr J = 1`).

1. Outer factor `Û = Onum/Oden` (the constant 2, the δ-factor if `q ∤ 2k₀ - n`, numerator factors
   `t + 1/2 + c` with `q ∤ 2c+1-2k₀`, poles `j % q ≠ k₀`); `Uhat y` = its Taylor series at `t = y`.
2. **Per-pole factorisation** `LE7.Gser_factor` (Lemma 4.1 at `-k`):
   `Gser u k = C(q^(E+ord)) * (X^ctr * (Uhat(-k) * rescale q⁻¹ (taylorAt τ w)))`;
   `LE7.Rser_factor`: `Rser u (-k₀) = C(q^E) * (Uhat(-k₀) * rescale q⁻¹ (taylorAt τ 0))` if `k₀ > n`.
3. Residue functionals (`ClassLemma7.lean`, namespace `CL7`): `PairF`, `LE7.ResF`, `Psi =
   PairF τ - c0 ResF τ - c ResF (kerType τ j)`; main identity `CL7.LHS_eq`:
   `classBad - 24 q^-5 kerRes = 24 q^(E-4) Ψ(Ufam)`; pieces `Xk_eq`, `rcoef_one_eq`, `kerPole_eq`,
   `KP_eq` (residue at the kernel pole `-k₀`: partial fractions at `-k₀` = `Gser_pf_pole` from
   `Stmt_PF7.poly` if `k₀ ≤ n`, `Stmt_PF7.series` if `k₀ > n`), reindexing `classBad_eq`,
   `r1_eq`, `cpart_eq`, `kerRes_eq`.
4. `CL7.Psi_poly`: `Ψ((C(w/2)+X)^m) = coeffD τ c0 j c (E+m+1)` by the residue theorem at infinity
   `LE7.grt_local` (for `τ` and `kerType τ j`) and the binomial identity `pair_poly_term` (ASer).
5. Truncation `LE7.trunc_exists` (`M = (P-E-1).toNat`), `Ψ(T̃) = 0` by `LevGe`,
   `v_q(Ψ(Ũ - T̃)) ≥ M` by `CL7.Psi_val` + Lemma 4.2 (`PSV_taylorAt_model`, `PSV_taylorAt_ker`,
   `PSV_gSer_model`).  Hence `v_q(LHS) ≥ E - 4 + M ≥ P - 5`.

## Reuse guide for the next round

### PerPole7 (`Stmt_PerPole7`)
With `k₀ = k % q`, `J = k / q` (`k = k₀ + J q`, `Nat.mod_add_div`):
* `rcoef u i k = coeff (a_k - i) (Gser u k)` for `1 ≤ i ≤ a_k` (else `0`, `valGe_zero`).
* `LE7.Gser_factor`, then `coeff_C_mul`, `PowerSeries.coeff_X_pow_mul'` (index `a_k - i - ctr =
  ord - i`, using `LE7.ord_pole : ord + ctr = a_k`; if `i > ord` the coefficient is `0` — the centre
  `r_{4,n/2} = 0`), and `LE7.coeff_mul_rescale_inv`:
  `r_{i,k} = q^(E+ord) q^-(ord-i) ∑_{m+l=ord-i} [ε^m](rescale q Û) · τ_l`, i.e. each term is
  `q^(E + ord - l) · (q-integral) · τ_l`.
* `q`-integrality: `LE7.PSV_Uhat hq2 hk₀ J` (then `PSV.resc`), `LE7.PSV_taylorAt_model` (Lemma 4.2,
  needs `80u + 2q < q²`).  `PoleLevAt T` kills the `τ_l` with `l > E + ord - T` (note `PoleLevAt`
  is stated with `-netE`, and `LE7.netE_pole`/`ord_pole` give `-netE w = ord w` as integers).

### FarPart7 (`Stmt_FarPart7`)
* `farRes = ∑_{k ∈ class} ∑_i r_{i,k} ∑_{i'≠k₀} negChoose j (i-1) ((i'-k)⁻¹)^(i+j-1)`
  `= ∑_{k} coeff (a_k - 1) (Gser u k * g_k)` with `g_k = ∑_{i'≠k₀} lin (i' - k) (-j)`
  (`LE7.coeff_Gser_mul_eq_sum`, `LE7.coeff_lin_neg`).
* Write `Û·g = A/B` with polynomials (`A = Onum · (numerator of g)`, `B = Oden · ∏_{i'≠k₀}(t+i')^j`);
  `B` is a unit on the disc.  `LE7.trunc_general A B M` gives the truncation of `rescale q (A/B)` at
  every `w = -2J` with centre coefficients `H_m = [ε^m](A/B)(-k₀+ε)`.
* The analogue of `CL7.r1_eq`/`LE7.coeff_Gser_mul` with `Û` replaced by `A/B` (same proof: the
  per-pole factorisation times the analytic factor `g`), then `LE7.ResF_sum` + `LE7.grt_local`
  give `∑_{m<M} H_m q^m coeffZ (rSer τ) (E+m+1)`; the power sums (`FiniteField.sum_pow_units`) give
  `q ∣ H_m` for `m ≤ q-2-j`.  `LE7.sum_cls`, `LE7.poleSet_eq` reindex class sums.

## Main lemma index of `LocalExpansion7.lean` (see its header for all 12 sections)

`grt` (generic residue theorem at infinity), `grt_local`, `taylorAt_eq_prod`, `rSer_eq_prod`,
`kerType_*`, `items_eq` (`PLf`/`ZLl`/`DLl`), `clsJ`, `mem_clsJ`, `sum_cls`, `prod_cls`,
`netE_pole`, `ord_pole`, `ord_pole_pos`, `poleSet_eq`, `netE_zero_nonpos`, `netE_zero_of_gt`,
`pairs_sum`, `pairs_mem`, `sum_oddBetween_dvd`, `items_sep`, `PSV_taylorAt_model`,
`PSV_taylorAt_ker`, `PSV_gSer_model`, `PSV_Uhat`, `PSV_Oden_inv`, `trunc_general`, `trunc_exists`,
`Gser_split`, `in_part`, `Gser_factor`, `Rser_factor`, `ResF`, `Ufam`, `coeff_Gser_mul`,
`coeff_Gser_mul_eq_sum`, `coeff_mul_rescale_inv`, `gchoose_neg`, `coeff_lin_neg`, `coeff_inv_pow`.

## Pitfalls met

* In `localModel` the zero index `t` and the pair index `t` are INTEGERS ranging over
  `bind (List.range N) (fun a => pure ↑a)` (= `(List.range N).map Nat.cast`, `bind_range_cast`).
* `coeff (a - 1)` with `a = 0` is junk: every pole position has `ord ≥ 1` (`ord_pole_pos`; the
  centre has `a_k = 4`, net 3).
* `(C β + X)^e` for `e : ℤ` is `lin β e = C (β^e) * bser β⁻¹ e` (`lin_add` needs `β ≠ 0`).
* `omega` atomises products only when they are syntactically identical (`↑J * ↑q` vs
  `-2 * ↑J * ↑q` differ); `linarith`/`nlinarith` or `generalize` otherwise.

## Math remarks (no error found)

* The informal (4.1) sums an infinite `q`-adic series `∑_m F_m q^m [y^{m+E+1}] D`; the Lean proof
  replaces it by the exact truncation `Û = T + q^M Z` (`trunc_exists`), so only finitely many
  coefficients `coeffD` are used.  The hypothesis `q ≥ 5` is only used for `q ≠ 2`; `24` need only
  be `q`-integral.  Lemma 4.2 is used in the form: every item position differs from a pole position
  (or `0`) by an integer `z ≠ 0` with `q|z| ≤ 2 max(n, q-1) < q²`.
