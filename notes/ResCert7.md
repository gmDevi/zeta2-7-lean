# ResCert7 — prover notes (round 3)

Target: `Zeta2Lean/Z7/Proofs/ResCert7.lean`, `theorem ResCert7_proof : Stmt_ResCert7`.

## Status: PROVED

`#print axioms Zeta2.Z7.ResCert7_proof` = `[propext, Classical.choice, Quot.sound]`.
No statement, `Defs`, `Statements`, `DenTable`, `Assembly` or `Main` change.

| file | content | build |
|---|---|---|
| `Z7/Proofs/ResCert7Floor.lean` | generic sweep certificates (`LineSys7`, `ECert7`, `ECert7.ok_sound`), the 20-line system `sysE7`, periodicity, the floor-sum formula `localModel_E_eq_sysE7`, realizability `sysE7_real_disc`, `ECert7.E_ge`, vacuity lemmas `RC7.LevGe_of_E`, `RC7.PoleLevGe_of_E` | 7 s |
| `Z7/Proofs/ResCert7Data.lean` | generated: 980 certificates `resECerts7_0 … _9`, `resECerts7_ok` (10 × `decide +kernel`), `resRows7_keys`, `resRows7_cert` | 30 s |
| `Z7/Proofs/ResCert7.lean` | `ResCert7_proof` (15 lines) | 3 s |
| `Z7/Proofs/ResCert7Head.lean` | generated, **for `HeadCert7`, not imported by anything yet**: 469 head-row certificates with the exact `E_min`, `headECerts7_ok`, `headRows7_keys`, `headRows7_E` | 15 s |
| `Z7/Proofs/ResCert7_gen.py` | generator of the two data files (`--check`, `--selftest`) | – |

`ResCert7.lean` imports `ResCert7Data` (which imports `ResCert7Floor`); `Main.lean` already
imports `ResCert7`, so the helpers are built by `lake build Zeta2Lean.Z7.Main`.
`ResCert7Head` is built only when imported (`bash scripts/build.sh Zeta2Lean.Z7.Proofs.ResCert7Head`
builds it by hand; it was built and checked on 2026-09-28).

## The proof

1. **Floor-sum form of `E`** (`localModel_E_eq_sysE7`, proof Lemma 4.12): for odd `q` and `k₀ < q`,
   with `x = 40u/q`, `y = k₀/q`,
   `E_ξ = sysE7.val x y + [q ∣ 2k₀ - 40u]`, where
   `sysE7.val x y = ∑_m (⌊(1-η_m)x - y - 1/2⌋ - ⌊η_m x - y - 1/2⌋) - ∑_{ℓ=0}^{3} (⌊(1-ℓ/20)x - y⌋ - ⌈(ℓ/20)x - y⌉ + 1)`.
   Proof: the three item lists of `localModel` are summed (`RC7.sum_snd_filterMap`); `a_k` is
   `1 + [2u ≤ k ≤ 38u] + [4u ≤ k ≤ 36u] + [6u ≤ k ≤ 34u]` (`RC7.apole_ind`), `μ(c)` is a sum of six
   block indicators (`RC7.mu_ind`); every indicator is a difference of two `[j q ≤ s]`, and
   `∑_{j<M} [j q ≤ s] = ⌊s/q⌋ + 1` (`RC7.cnt_le`).  On the `sysE7` side `⌊M/q - 1/2⌋ = RC7.zc q M - 1`,
   `⌊M/q⌋ = M / q`, `⌈M/q⌉ = (M-1)/q + 1` (`RC7.floor_half`, `RC7.ceil_div`).  Valid for **every odd
   `q`** (no size condition), `u = 0` included.
2. **Periodicity** (`sysE7_val_add_40`): `A_j` even and `∑ W_j A_j/2 = 0` (both by `decide`).
3. **Realizability** (`sysE7_real_disc`, needs `q > 40` prime and `q ∤ u`): no floor line and no
   ceiling line are integral at the same discrete point.  Numerator lines never are (`q` odd);
   a pole upper line (`A/2 ∈ {40,38,36,34}`) and a pole lower line (`A/2 ∈ {0,2,4,6}`) together
   force `q ∣ d u` with `28 ≤ d ≤ 40`.
4. **Certificates** (`ECert7.ok_sound`): see the encoding below.  `ResCert7_proof` = `resRows7_cert`
   + `ECert7.E_ge` with `t` = the shift (`ECert7.E_ge` needs only `q > 40`; the statement's
   `q² > 2n + 3q` is not used).

## The E-certificate encoding (reusable by `HeadCert7`)

* `LineSys7 = ⟨n, A, B, W, C, K⟩`: lines `ℓ_j(x) = (A_j x + B_j)/80`, weights `W_j`, `C_j = true`
  for ceiling lines; `val x y = ∑_j W_j F_j(ℓ_j(x) - y) + K`.
* `sysE7` (index: `A`, `B`, `W`, floor/ceil):
  `j = 0..5`: `70 66 66 62 58 54`, `-40`, `+1`, floor (numerator upper ends, `2(40 - 40η_m)`);
  `j = 6..11`: `10 14 14 18 22 26`, `-40`, `-1`, floor (numerator lower ends, `2·40η_m`);
  `j = 12..15`: `80 76 72 68`, `0`, `-1`, floor (pole levels `(1 - ℓ/20)x`);
  `j = 16..19`: `0 4 8 12`, `0`, `+1`, ceiling (pole levels `(ℓ/20)x`); `K = -4`.
* `ECert7 = ⟨pa, qa, pb, qb, sig, ord⟩` for `[pa/qa, pb/qb)`; `ord` = permutation of `0..n-1`.
  `ECert7.ok S c` (Bool, kernel-reducible) checks: `qa, qb > 0`, `a < b`; `ord ~ range n`
  (`List.isPerm`); for each line `0 ≤ sa ≤ 80 qa`, `0 ≤ sb ≤ 80 qb` and `sa < 80 qa` for floor
  lines, where `sa = 80 qa (ℓ_j(a) - N_j)`, `sb = 80 qb (ℓ_j(b) - N_j)`, `N_j` = integer part at
  the midpoint (`Nm`, recomputed); `ord` weakly increasing in `(sa, sb)` (`chainOK`); every
  prefix sum `V₀ - ∑_{i<p} W_{ord i} ≥ sig` (`ECert7.prefOK`), `V₀ = ∑_j W_j (N_j + [C_j]) + K`.
* Soundness `ECert7.ok_sound`: `c.ok S → a ≤ x < b → 0 ≤ y < 1 → S.Real x y → c.sig ≤ S.val x y`.
  (Floor line drops when `β < y`, ceiling line when `β ≤ y`; realizability makes the dropped set
  a prefix of `ord`.)
* `ECert7.E_ge c hc t u q …`: for `sysE7`, prime `q > 40`, `q ∤ u`,
  `a + 40t ≤ 40u/q < b + 40t`, every `k₀ < q` has `c.sig ≤ (localModel u q k₀).E`.
* Generator: sort the lines by `(sa, sb)`; `sig` = min of the prefix sums.  On a candidate interval
  of `⋃_{d≤40}(20/d)ℤ` the lines never cross (so the chain check passes), and the prefix-sum
  minimum is the exact continuum `E_min` (identical lines 1/2 and 7/8 have equal weights, so
  their "half-dropped" prefix never lowers the minimum).

### For `HeadCert7`

* `import Zeta2Lean.Z7.Proofs.ResCert7Head` gives `headRows7_E : ∀ row ∈ headRows7, ∃ c ∈ headECerts7,
  (interval of row) ∧ ∀ u q, q.Prime → 40 < q → ¬ q ∣ u → row.a ≤ n/q → n/q < row.b →
  ∀ k₀ < q, c.sig ≤ (localModel u q k₀).E`, with `c.sig` the exact `E_min` of the row
  (`∈ [-4, -1]`).
* 216 of the 469 head rows have `E_min ≥ 4 - f`; there `RC7.LevGe_of_E` (`5 - f ≤ E + 1`) and
  `RC7.PoleLevGe_of_E` (`-f ≤ E + 1`) make both certificate conditions vacuous.
  (The audit counts 222 rows "without series check"; the 6 extra rows presumably have low-`E`
  types whose `ASer` vanishes — not checked here.)
* For the other rows one needs the types in the low-`E` gaps: extend `sysE7` by weight-0 lines
  (bad-pair lines `x/2 - y - j`, pole existence `x - y`, cells `b x/40 - y`, …) and reuse
  `ECert7.ok_sound`'s proof, which shows that the dropped set is exactly a prefix of `ord`
  (every floor/ceiling value is `N_j + [C_j] - [j dropped]`, see `hfl` in the proof).  Note that
  realizability is a hypothesis of the generic theorem; for new lines prove the analogue of
  `sysE7_real_disc`.

## Kernel time

All 980 residue certificates: ~35 s in one `decide +kernel`; split into 10 chunks of 98 (the file
builds in 30 s).  Head: 469 certificates in 5 chunks, 15 s.  `resRows7_keys` (compares
`resRows7.map RC7.rowKey` with the certificates' keys): negligible.  Per certificate: 20 lines,
`List.isPerm` (≤ 400 `Nat` comparisons), integer arithmetic only.

## Math remarks (no issue found)

* The floor-sum formula of Lemma 4.12 is exactly right for the Lean `localModel`, for every odd
  `q` and `k₀ < q` (3000 random tests with `q ∈ [3, 131]` in `ResCert7_gen.py --selftest`, and the
  Lean proof).  The pole count uses a ceiling at the lower ends `ℓ n/20` (closed cells).
* `f = max(0, 4 - E_min)` is exact on all 980 residue rows (`sig = 4 - f` checked), and
  `E_min ∈ [-6, -1]`, i.e. `f ∈ [5, 10]` (audit: TRUE).
* `q ∤ u` (with `q > 40` prime) is used only for realizability: it excludes simultaneous
  integrality of a pole upper and a pole lower line (a floor/ceiling tie that would break the
  sweep order).  The hypothesis `80u + 3q < q²` of the statement is not used.

## Pitfalls met

* In `localModel` the zero list runs over `((List.range N : List ℕ) : List ℤ)` (the variable `t`
  is an integer); `RC7.sum_map_coe_range` turns it into a `Finset` sum.
* Deprecated here: `if_pos/if_neg` (use `ite_eq_left/ite_eq_right`), `push_neg` (use `push Not`).
  Names: `Int.emod_add_mul_ediv`, `Int.le_ediv_iff_mul_le`, `Int.ediv_lt_iff_lt_mul`,
  `Rat.floor_intCast_div_natCast`, `Int.natCast_dvd_natCast`.
* `scripts/check.sh` counts the word "sorry" also in comments: keep it out of docstrings.

## Reproduce / re-check

```
python3 Zeta2Lean/Z7/Proofs/ResCert7_gen.py --check      # data files = generator output
python3 Zeta2Lean/Z7/Proofs/ResCert7_gen.py --selftest   # + floor-sum formula vs literal localModel
bash scripts/build.sh Zeta2Lean.Z7.Proofs.ResCert7 Zeta2Lean.Z7.Proofs.ResCert7Head
bash scripts/kernels.sh Zeta2Lean.Z7.Proofs.ResCert7     # leanchecker replay: 8 modules, fail=0 (2026-09-28)
```
