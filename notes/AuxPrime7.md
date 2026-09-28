# AuxPrime7 (Theorem N, `Stmt_AuxPrime7`) -- prover notes

Target: `Zeta2Lean/Z7/Proofs/AuxPrime7.lean`, `AuxPrime7_proof (hPF) (hV) : Stmt_AuxPrime7`.
Only `hV.symm` (Stmt_CoeffVanish7) is used; `hPF` is part of the fixed signature.

## Route (as formalised, namespace `Zeta2.Z7.AP7`, all names prefixed `ap_`)

Imports `Zeta2Lean.Pair.Proofs.Nonvanishing` and reuses its generic `q`-integral machinery
(`NVq.Zq`, `HasRes`, `IsU`, `ZqPS`, `inv_mem` (opened as `zinv_mem`), `rescale_*`, `not_dvd_*`,
`half_mem`, `linG_mem`, `pv_*`, `zmod_ne_zero_of_lt`).  Everything with `q = 38u - 1`, hypothesis
`hqu : q + 1 = 38 * u`, `[Fact q.Prime]`; the final theorem takes `U = 10` (so `q > 300`, all
small constants are units).

1. Middle poles `2u+2 <= k <= q-1`: `Gser u k` is `q`-integral (`ap_Gser_mem_mid`).
2. End poles `k <= 2u+1`: `Gser u k = Qser7 q a' * Gam7 u q k`, `a' = apole u (k+q)`
   (= 2 for k <= 1, 1 otherwise), `Qser7 q a = (C(q/2)+X)^6 ((C q + X)^a)^{-1}`; `Gam7` integral,
   `Gam7 u q 0` has unit constant term.  Rescaling by `q` gives `r_{i,k}` integral.
3. Mirror poles by `hV.symm`.  So every `rcoef` is integral (`ap_rcoef_mem`), hence `Zc`.
4. `AhalfZ (k - 20u) s = A + [k<=u](-(-2/q)^s) + [39u<=k](2/q)^s` (`ap_AhalfZ_split`).
5. `q * rho = -sum_k Fk k`; `Fk k == 0` for `2 <= k <= n-2`, `== 12 g_k` for `k in {0,1}` and
   for the mirrors `n-k`, `g_k = res(coeff 0 (Gam7 u q k))`.  So `q rho == -24 (g0 + g1)`.
6. Ratio: `r_{1,1} * A0 = r_{1,0} * B0` (telescoped blocks `ap_block_tel`, poles `ap_pole_tel`
   via the exponent identity `a_j + [j in {2u-1,4u-1,6u-1}] = a_{j+1} + [j in {34u,36u,38u}]`),
   hence `Gam_1(0) A0 = Gam_0(0) B0`; mod q with `38U = 1`: `224 B0 = -81 A0`, `A0 != 0`
   (theta0 = -81/224, 1 + theta0 = 143/224).
7. `-24 (g0 + g1) != 0`, so `v_q(rho) = -1`.

## Status (2026-09-28, round 4)

**Proved**, 0 sorry.  `bash scripts/build.sh Zeta2Lean.Z7.Proofs.AuxPrime7` green (about 8 s),
no warnings; `#print axioms Zeta2.Z7.AuxPrime7_proof` = `[propext, Classical.choice, Quot.sound]`
(checked on a scratch copy with the `#print` appended; the repository file has no `#print`).

Files touched: `Zeta2Lean/Z7/Proofs/AuxPrime7.lean` (new import
`Zeta2Lean.Pair.Proofs.Nonvanishing`, precedent: `MaxU7` imports a Pair file) and this note.

## Pitfalls met

* `open Zeta2.Pair.NVq` clashes with root `inv_mem`: opened `hiding inv_mem` plus
  `renaming inv_mem -> zinv_mem`.  Do not `open Zeta2.Pair` (its `Gser`, `rcoef`, `rho` clash with
  `Zeta2.Z7`).  All lemma names carry the prefix `ap_` (defs: `Nprime7`, `Pprime7`, `Gam7`, `Qser7`,
  `Qhat7`, `Tt`, `Fk`, `A0R`, `B0R`, all in `Zeta2.Z7.AP7`) to avoid clashes with NVq names.
* `if_pos`/`if_neg` are deprecated in this toolchain: use `ite_eq_left`/`ite_eq_right`.
* `field_simp` leaves `q^5 * q⁻¹^5`; close with `linear_combination c * (q * q⁻¹ = 1)`.
* In `ap_T1_bad` calls pass `(k := ...)` explicitly (else `omega` sees a metavariable).
* `ring` on `(1 - 38u)⁻¹ = -(38u - 1)⁻¹` fails: rewrite with `inv_neg`, `inv_div`, `neg_div`.
