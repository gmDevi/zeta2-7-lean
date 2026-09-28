# Status: ζ₂(7) is irrational (the Z7 programme)

Updated 2026-09-28 (architect round; adversarial audit; integrator rounds 1–4, see below). Plan, statement
map and design: `BLUEPRINT_Z7.md`.

## Headline

* The Lean skeleton is complete and **builds green**: `bash scripts/build.sh Zeta2Lean.Z7.Main`
  (also part of the default target via `Zeta2Lean.lean`).
* The assembly is **sorry-free**: `#print axioms Zeta2.Z7.main7_of_stmts` gives
  `[propext, Classical.choice, Quot.sound]`.
* **COMPLETE (2026-09-28, round 4).** All 24 proof files are proved. `#print axioms
  Zeta2.Z7.zeta2_7_irrational` gives `[propext, Classical.choice, Quot.sound]`: the theorem
  `(∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧ ¬ ∃ q : ℚ, zeta2 7 = q` (ζ₂(7) is irrational) holds
  with the trusted definitions of `Zeta2Lean/Defs.lean` and no `sorry`. `scripts/audit.sh`: no `sorry`,
  no forbidden construct in any file.
* `python3 python/z7_mirror.py`: every definition and statement checked against the research
  engines, 0 failures (`python/z7_mirror_full.log`).

## Per-file census (`Zeta2Lean/Z7/`)

| file | theorem : Stmt | difficulty | status |
|---|---|---|---|
| `Defs` | definitions | – | done |
| `DenTable` | `headRows7`, `resRows7`, `denTable7` (generated) | – | done |
| `Statements` | 24 statements + `SevenStatement` | – | done |
| `Assembly` | `main7_of_stmts`, `margin7`, `bound_core7`, `linear_form_zeta7` | – | **done** |
| `Main` | `zeta2_7_irrational` (+ `_of_gaps`) | – | done (wiring) |
| `Proofs/TranslationNeg` | `TranslationNeg_proof` | 2 | **proved** |
| `Proofs/GenLinearFormZ` | `GenLinearFormZ_proof` | 2 | **proved** |
| `Proofs/PartialFractions7` | `PF7_proof` | 3 | **proved** |
| `Proofs/CoeffVanish7` | `CoeffVanish7_proof` | 3 | **proved** |
| `Proofs/LinearForm7` | `L7_proof` | 1 | **proved** |
| `Proofs/IntegrandTaylor7` | `IntegrandTaylor7_proof` | 2 | **proved** |
| `Proofs/Valuation7` | `Valuation7_proof` (Theorem V) | 3 | **proved** |
| `Proofs/AuxPrime7` | `AuxPrime7_proof` (Theorem N) | 4 | **proved** (r4) |
| `Proofs/NonvanishingLS7` | `Nonvanishing7_proof` (+ Dirichlet mod 38) | 2 | **proved** |
| `Proofs/MaxU7` | `MaxU7_proof` (Lemma G7, certificate) | 3 | **proved** (r3) |
| `Proofs/ResidueBound7` | `ResidueBound7_proof` (G1–G6) | 5 | **proved** (r4) |
| `Proofs/Growth7` | `Growth7_proof` (Theorem G) | 3 | **proved** (r3) |
| `Proofs/BigPrimes7` | `BigPrimes7_proof` (Theorem C) | 3 | **proved** (r3) |
| `Proofs/SmallPrimes7` | `SmallPrimes7_proof` (Lemma 4.9) | 4 | **proved** (r4) |
| `Proofs/Emin7` | `Emin7_proof` (Lemma 4.8(1)) | 3 | **proved** (r3) |
| `Proofs/ClassLemma7` | `ClassLemma7_proof` (Lemma 4.3; helper `LocalExpansion7`) | 5 | **proved** (r3) |
| `Proofs/KernelIdentity7` | `KernelIdentity7_proof` (Lemma 4.4) | 2 | **proved** |
| `Proofs/FarPart7` | `FarPart7_proof` (Lemma 4.5) | 4 | **proved** (r4) |
| `Proofs/PerPole7` | `PerPole7_proof` (Lemma 4.7) | 4 | **proved** (r4) |
| `Proofs/ThmK7` | `ThmK7_proof` (Theorem K) | 3 | **proved** (r3) |
| `Proofs/HeadCert7` | `HeadCert7_proof` (continuum + certificates on `[1,20)`) | 5 | **proved** (r4) |
| `Proofs/ResCert7` | `ResCert7_proof` (residue certificates + periodicity; helpers `ResCert7{Floor,Data,Head}`) | 4 | **proved** (r3) |
| `Proofs/ExpBounds7` | `ExpBounds7_proof` (five prime ranges) | 2 | **proved** |
| `Proofs/Denominators7` | `Denominators7_proof` (Theorem A, PNT) | 4 | **proved** (r4) |

Shared (proved, unchanged from the pair): `Zeta2Lean/Defs.lean`, `Statements.lean`,
`Proofs/{JConvergence, Translation, Criterion, DeltaCalculus, DeltaFunctions}.lean`,
`Cited/PNT.lean` + `Cited/Vendor/PNT/*`. Of the pair development (`Zeta2Lean/Pair/`) only the six
files in the import closure of `Z7.Main` are kept (see "Publication preparation" below);
`Zeta2Lean.lean` imports `Z7.Main`.

## Constants

| quantity | value | where |
|---|---|---|
| growth rate `g7` | `0.71` (true max `U = 0.7067022242`) | `Defs.g7`, `Stmt_MaxU7` |
| denominator rate `delta7` | `3.99` (table integral `3.9240891610`) | `Defs.delta7`, `DenTable` |
| 2-adic gain | `6.8 log 2 = 4.7134008` (`v₂(S_n) ≥ 272u - O(log u)`) | `Stmt_Valuation7` |
| margin | `g7 + delta7 = 4.70 < 4.7134008` | `Assembly.margin7` |

## Python files

| file | role |
|---|---|
| `python/z7_mirror.py` | mirror of `Z7/Defs.lean`, checks of every `Stmt` (`--quick` / full) |
| `python/z7_mirror_full.log` | full-run log |
| `python/z7_den_table.py` | generator of `Z7/DenTable.lean` (`--check` compares) |
| `python/z7_audit.py` | independent adversarial audit, no code shared with the mirror (`--jobs N`; `VERIF_DIR` for the truth section) |
| `python/z7_audit_full.log` | full-run log of the audit |
| `python/z7_ref/*.py` | verbatim copies of the research engines (below) |
| `python/z7_ref/data/*.json` | the certified interval data of the denominators-theory track |

SHA-256 of the reference engines (copied verbatim, LF endings):
```
98c914b96601f95a3f5ae64548ae3755387a627c86b09e0d23aab5e7d879e7c6  vc_common.py   (verify-candidate)
41abcbebbe96501bf0f1b8893bcab4dccfab852d215dd4641fb8adcc6a8f9ce3  vc_engine.py   (verify-candidate)
6f827ba833df89de1083e51a82c993b7d325a671d28f760ab37f4b99982f58fe  kernel.py      (denominators-theory)
8b9e0b4cb6a8a92af8def1730b70522f2e04efece5a0783aba82f27382450717  levels.py      (denominators-theory)
d12bf79397eb2ec2e84a6a18dccd88d909c9acad3af20677b7e5ee315a71418e  cont.py        (denominators-theory)
f70f6620e9c41d5a7798ba961a110c61332eddc0f7bcc021c95b28ebab64272c  qeng.py        (denominators-theory)
cb1ab91a89c68da301c64ae7f523a9f2943ffaa2cf2442591d5e403a8542f77f  cand.py        (growth-nonvanishing)
```

## Adversarial audit (2026-09-26)

**Verdict: no gap.** The skeleton is sound. Each of the 24 statements (and `SevenStatement`) is
faithful to the informal proof, up to the documented Lean-friendly choices: `n = 40u`, rates
`0.71`/`3.99`, `q > 1000` in the certificate statements, residue level on `[20, 140)`, tail
`10/140`. Every statement tested true: 700,181 checks, 0 failures. No Lean statement had to change.

*Lean soundness.*
* `lake build Zeta2Lean.Z7.Main` green; `scripts/audit.sh`: 18 stubs (one `sorry` each), no
  forbidden construct.
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `main7_of_stmts`,
  `margin7`, `denTable7_sane`, `denTable7_integral_fixed` and the six proved files
  (`TranslationNeg_proof`, `GenLinearFormZ_proof`, `L7_proof`, `IntegrandTaylor7_proof`,
  `Nonvanishing7_proof`, `KernelIdentity7_proof`).
* The main theorem is literally the trusted statement (`zeta2 7 = J 6 / 768` from
  `Zeta2Lean/Defs.lean`); nothing in `Z7/` shadows a trusted name.
* Casts, checked by `#print` with `pp.coercions`: `5 - row.f` and `4 - row.f` are computed in `ℤ`;
  `n/q` is `((40u : ℕ) : ℚ) / q`; `localModel`'s zero and pair indices are integers.
* Junk values are harmless: `rcoef = 0` outside `1 ≤ i ≤ a_k`, so the `Icc 1 4` sums and
  `rcoef u 4 (20u) = 0` are consistent; `38u - 1` truncates to `0` at `u = 0`; `eq7` is only used
  at odd primes; `u = 0` (where `R = 2/t³`) satisfies every `∀ u` statement.
* No vacuity: every hypothesis of a proof file is the conclusion of another statement on the same
  domain.
* The dependency hypotheses suffice. The splitting `rho = -(∑ classBad + goodPart)`, the
  `q`-integrality of the row kernels (denominators divide `41!^256`), the tiling of `[1,20)` and
  `[20,60)` by the rows, and `f ≤ 10` on the residue rows are all elementary or decidable.

*Truth: `python/z7_audit.py`.* This is an independent script: it shares no code with the mirror, has
its own transcription of every `Defs` function and its own exact engine for `r_{i,k}`. Its
transcription agrees with the mirror on 8482 random local types. Full log:
`python/z7_audit_full.log`: the main run (30 jobs, 27 min) plus two supplementary runs,
`exact --exact-u 1,3,4,6` and `bigj`.

| check | scope | result |
|---|---|---|
| table | independent parse of `DenTable.lean`: rows chain `[1,20)`, `[20,60)`; endpoints = the candidate set `⋃_{d≤40}(20/d)ℤ`; `max f⁰ = 10`; exact integral `3.9240891610`; Lean fixed-point bound | ok |
| `HeadCert7`, continuum, all `u` | every row, 3 rational `x` per row. All types of `T(x)` (the type in every gap of a superset of the event points `frac(bx/40 + e)`, plus the type at every `e = 0` point where discrete classes can sit) satisfy the row certificate. `T(x)` is the same at the 3 points (Lemma 4.10) | 0 failures |
| `ResCert7`, continuum | 980 rows × 3 `x` × shifts `t = 0..3`: `E ≥ 4 - f`, `f = max(0, 4 - E_min)` exactly, `E_min` 40-periodic | 0 failures |
| discrete, statement domain | 1918 `(u, q)` with `q ∈ (1000, 9000)` prime, `q ∤ u`, 2 per head row and 1 per residue row, all `q` classes. Literal `localModel` = continuum model at `(n/q, k₀/q)`, and it lies in `T(x_mid)` of its row (Lemma 4.11) and satisfies the certificate | 0 failures |
| `ClassLemma7` | `n = 40, 80, 120, 160, 200, 240, 280, 400`, every admissible prime. Kernels `0`, `1`, `1 - (5/4)y²` and 3 random `q`-integral kernels with `j ≤ 4`, checked at the largest `P` allowed by `LevGe`. Also `j ∈ {5, 6, 8, 11}` at `n = 80, 200` | 0 failures |
| `FarPart7` (`j = 1..6`), `PerPole7` (direct: largest `T` with `PoleLevAt`, then `v_q(r_{i,k}) ≥ T`; the bound is attained), `ThmK7` (best `T` for 3 kernels ⇒ true `e_q ≤ -T`) | the same 8 values of `n` | 0 failures |
| `Emin7` | all primes `5 ≤ q ≤ 2n + 50`, all classes, `u ≤ 60` | 0 failures; `min E = -6` |
| `BigPrimes7`, `SmallPrimes7`, `ExpBounds7.crude`/`tail`, `CoeffVanish7`, `ResidueBound7` and `Growth7` (the per-`n` forms), `AuxPrime7` | exact, `n = 40 … 800` | 0 failures |
| `ExpBounds7.rows`/`tail`/`crude` against TRUE exponents | 11,662 `(n, q)` of the research verifier (`q`-adic truth, `n ≤ 200000`) | 0 violations; `e = f` at 10,880 of the 10,972 head cases |
| far-part fallback | the six `[2, 20/9)` rows certify `f + 1` with `κ = 1` (then `E = 3.9741 < 3.99`) | ok |

*For the certificate team (`HeadCert7`).* Most of the certificate is vacuous. Only 76 distinct
`(type, kernel, P)` `LevGe` checks on 63 types, and 9 `PoleLevGe` checks on 4 types, are
non-vacuous. They need series coefficients of index `≤ 4`. 222 of the 469 rows need no series
check at all, only an `E` lower bound. Details are in the docstring of `Proofs/HeadCert7.lean`.
Exact `ℚ` arithmetic under `decide +kernel` is fragile: closed equalities such as
`1/3 + 1/6 = 1/2` reduce, but a `List.map`/`sum` over `ℚ` got stuck. Use integer-scaled data, as
`denTable7_integral_fixed` does.

*Fixed:* a line of `BLUEPRINT_Z7.md` (mirror section) that a shell escape had mangled.
*Not a gap, for later:* `Challenge.lean`, `Solution.lean` and `comparator.json` are still the
pair's. A `ζ₂(7)` Palomar statement must be added when the stubs are closed (done 2026-09-28).

## Integrator, round 1 (2026-09-26)

* Four prover reports: `LinearForm7`, `TranslationNeg`, `GenLinearFormZ`, and a statement/math
  review of `Defs`/`DenTable`/`Statements`/`Assembly`/`Main`. The three proof files were already
  proved and committed (HEAD `d056c9b`); the working tree was clean, so there was nothing new to
  merge.
* `bash scripts/build.sh Zeta2Lean.Z7.Main`: green (8969 jobs, exit 0). `#print axioms`:
  `main7_of_stmts` gives `[propext, Classical.choice, Quot.sound]`; `zeta2_7_irrational` also
  lists `sorryAx` (the 18 stubs). `scripts/audit.sh`: 18 files with one `sorry` each, no
  forbidden construct.
* Frozen files: `git diff 793c0f1 HEAD` is empty on `Zeta2Lean/Defs.lean`, `Pair/`, `Cited/`,
  `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`. `git diff d5b05ca HEAD` is empty on
  `Z7/{Defs,Statements,Assembly,Main}.lean`.
* Rulings (no statement changed):
  - The reviewer found a small gap in the informal proof. Lemma 4.9 writes
    `G_k(ε) = G_k(0)·∏(1+ε/β)^e`, but at the centre `k = n/2` the linear factor is `2ε`, so
    `G_k(0) = 0`. The fix is to use `H = G_k/(2ε)`, as the proof of Theorem C does. The bound is
    unchanged, because `H_{n/2}` is empty and `r_{3,n/2} = 2H(0)` has the same count. This
    affects the proof of `SmallPrimes7` only, not the statement. `SmallPrimes7` passes the audit
    exactly for `n ≤ 800`. The provers of `SmallPrimes7` and `BigPrimes7` must treat
    `k = 20u` separately.
  - `Stmt_PerPole7` assumes `5 ≤ q`. Lemma 4.7 needs `q ≥ 11` only for the good-part remark; the
    per-pole bound itself holds for `q ≥ 5`. The statement is correct as written (audit: exact,
    8 values of `n`, 0 failures).

## Integrator, round 2 (2026-09-26)

* Four prover reports, all complete, 0 `sorry`: `PartialFractions7` (`PF7_proof`),
  `CoeffVanish7` (`CoeffVanish7_proof`), `Valuation7` (`Valuation7_proof`, Theorem V) and
  `ExpBounds7` (`ExpBounds7_proof`). No new files; only these four proof files changed.
* `bash scripts/build.sh Zeta2Lean.Z7.Main`: green (8969 jobs, exit 0), no compile fix needed.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `PF7_proof`,
  `CoeffVanish7_proof`, `Valuation7_proof`, `ExpBounds7_proof` and `main7_of_stmts`;
  `zeta2_7_irrational` still lists `sorryAx`. `scripts/audit.sh`: 14 files with one `sorry`
  each, no forbidden construct.
* Frozen files: `git diff 793c0f1` is empty on `Zeta2Lean/Defs.lean`, `Statements.lean`,
  `Proofs/`, `Pair/`, `Cited/`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`.
  `git diff d5b05ca` is empty on `Z7/{Defs,Statements,Assembly,Main}.lean`; `DenTable.lean` only
  has the committed kernel-checked facts of `1bf4700`.
* Rulings: no statement issue was raised; no statement changed. Remarks recorded:
  - `ExpBounds7`: the exposure hypothesis `x > 3` of Lemma 4.8(2) is not needed for
    `e_q ≤ max(0, 4 - E_min)` (non-exposed classes only help). In Lean the trivial-kernel bound
    holds for every `q ≥ 29` with `q² > 2n + 3q`.
  - `Valuation7`: before the crude Legendre step the Lean proof gives
    `v₂ ≥ 272u + 4 - σ - 4L`, one more than §6's `272u + 7 - σ - 4(L+1)` (§6 loses a bit in its
    bookkeeping). Examples: `n = 480`: 3215 (§6 3214, true 3237); `n = 960`: 6475 (6474, 6499);
    `n = 2000`: 13535 (13534, 13560). The statement's `272u + 7 - 10(L+1)` is implied.
  - `PF7`/`CoeffVanish7`: Lemma 0(a)–(d) confirmed for all `u`: block lengths
    `30,26,26,22,18,14` (× `u`), `N = 136u`, `∑ a_k = 136u + 4`, `deg R_n = -3`,
    `G_{n-k}(ε) = -(-1)^{a_k} G_k(-ε)`, `R_n(-n-t) = -R_n(t)`.

## Integrator, round 3 (2026-09-28)

* Seven prover reports, all complete, 0 `sorry`: `Growth7`, `MaxU7`, `BigPrimes7`, `Emin7`,
  `ThmK7`, `ResCert7`, `ClassLemma7`. New helper files: `Proofs/LocalExpansion7.lean`
  (namespace `LE7`: `Gser_factor`, `Rser_factor`, `grt_local`, `trunc_exists`; reusable for
  `PerPole7`/`FarPart7`), `Proofs/ResCert7{Floor,Data,Head}.lean` (`ResCert7Head` holds the 469
  head-row `E_min` certificates for `HeadCert7` and is not imported yet), generators
  `Proofs/MaxU7_gen.py`, `Proofs/ResCert7_gen.py`; handoff notes in `notes/*.md`.
* `bash scripts/build.sh Zeta2Lean.Z7.Main`: green (8973 jobs, exit 0), no compile fix needed
  (`MaxU7` elaborates in about 5.5 min). `#print axioms` gives `[propext, Classical.choice,
  Quot.sound]` for all seven new `*_proof`; `zeta2_7_irrational` still lists `sorryAx`.
  `scripts/audit.sh`: 7 files with one `sorry` each, no forbidden construct.
* Frozen files: `git diff ebe6816` is empty on `Zeta2Lean/Defs.lean`, `Statements.lean`,
  `Proofs/`, `Pair/`, `Cited/`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and
  `Z7/{Defs,Statements,Assembly,Main,DenTable}.lean`. Prover work committed as `545d74a`.
* Rulings: no statement issue raised; no statement changed. Remarks recorded:
  - `BigPrimes7` (Theorem C) needs no absorption argument (Lemma D2): numerator factors have
    `q`-integral coefficients, pole differences `j - k` are `q`-units, and the centred A-sums only
    involve `q`-units (`|2h| < q`).
  - `ResCert7`: the floor-sum formula of Lemma 4.12 (ceiling at closed lower cell ends) is exact
    for `localModel`; `f = max(0, 4 - E_min)` is exact on all 980 residue rows, `E_min ∈ [-6,-1]`.
  - `ClassLemma7`: the infinite `q`-adic series of (4.1) is replaced by an exact finite
    truncation `Û = T + q^M Z`; `q ≥ 5` is only used as `q ≠ 2`.
  - `MaxU7`: chord/tangent bounds on 42 boxes, worst box bound 0.708146 (margin 0.00185 to 0.71).

## Integration, round 4 (2026-09-28): COMPLETE

* Seven prover reports, all complete with 0 `sorry`: `PerPole7`, `FarPart7`, `AuxPrime7`, `SmallPrimes7`,
  `Denominators7`, `HeadCert7` (with the generated modules `HeadCert7{Dict,Series,Row,Tab,Rows,Pole}`,
  `HeadCert7Lev0..7`, `HeadCert7Data0..7` and the generator `HeadCert7_gen.py`) and `ResidueBound7`.
* The round's integrator agent did not integrate. Integration was done by hand:
  - prover work committed as b00f241;
  - `git diff ebe6816` is empty on the frozen files (`Defs.lean`, `Statements.lean`, `Proofs/`, `Pair/`,
    `Cited/`, the Lake files, `Z7/{Defs,Statements,Assembly,Main,DenTable}.lean`);
  - `scripts/audit.sh`: no `sorry`, no forbidden construct;
  - `bash scripts/build.sh Zeta2Lean.Z7.Main`: exit 0;
  - `#print axioms`: `main7_of_stmts` and `zeta2_7_irrational` both `[propext, Classical.choice, Quot.sound]`.
* Prover remarks (no statement changed, no math issue):
  - `SmallPrimes7`: the statement's 19λ₁ holds with 18λ₁.
  - `HeadCert7`: the hypotheses `q > 1000` and `80u + 3q < q²` are unused.
  - `PerPole7`, `FarPart7`: `q ≥ 5` is only used as `q ≠ 2`; exact finite truncation replaces the q-adic series.
  - `AuxPrime7`: θ₀ = −81/224 confirmed; the N1(b) product form degenerates at the centre, but only integrality
    is needed there.
  - `ResidueBound7`: exact telescoping replaces the sum/integral comparisons G3–G5 (weaker, sufficient constants).
* Then pending (done on 2026-09-28, see below): kernel replay of all 70 modules, a `ζ₂(7)`
  Challenge/Solution, the module-system port Palomar now requires, and the metadata.

## Publication preparation (2026-09-28)

* **Kernel replay** of the 70 modules of `Zeta2Lean.Z7.Main` with `leanchecker`, one at a time
  (`scripts/kernels.sh Zeta2Lean.Z7.Main`, master build): `fail=0`.
* **Cleanup** (branch `palomar-prep`): removed the pair development outside the import closure of
  `Zeta2Lean.Z7.Main` (`Pair/{Assembly,Main,Unconditional}`, 8 `Pair/Proofs` files, 3 landscape files and
  their generators), the unused generated `Z7/Proofs/ResCert7Head.lean`, `BLUEPRINT_PAIR.md`,
  `STATUS_PAIR.md` and the pair's Python mirrors. Kept from the pair: `Pair/{Defs,Statements}` and
  `Pair/Proofs/{Denominators,Nonvanishing,NonvanishingLS,Landscape/Numerics}` (in the closure; the proof uses
  their lemmas in namespaces `Pair.Den`, `Pair.NVq`, `Pair.Landscape`). `Zeta2Lean.lean` imports `Z7.Main`
  only; `Challenge.lean`, `Solution.lean` (`Zeta2.Z7.zeta2_7_irrational_palomar`), `comparator.json`,
  `formalization.yaml`, `README.md` and `docs/proof.md` (the informal proof) are new.
  Declaration-level comparison with master (type and value hashes of every constant of the project
  modules): all 4592 remaining constants unchanged; the 930 removed ones are exactly those of the 14
  removed modules.
* **Comments only** (checked: the code outside comments is unchanged): a provenance paragraph in each kept
  pair file, the module docstrings of `Defs.lean`, `Statements.lean`, `Cited/PNT.lean` and the porting
  notes of the vendored files, research-session references in `Z7/{Defs,Statements,Main}.lean` and four
  proof files.
* **Module system** (Palomar's source requirements of 2026-09-28): every Lean file starts with `module`,
  uses `public import` and opens `@[expose] public section` after the imports (vendored files: `module`
  after the copyright header). The generators `python/z7_den_table.py`, `HeadCert7_gen.py` and
  `ResCert7_gen.py` emit the same headers (`ResCert7_gen.py` no longer writes the unused
  `ResCert7Head.lean`), and all generated files are reproduced byte for byte (`--check`; `MaxU7_gen.py`
  keeps the header of its input). Palomar's `source_requirements.py` (PalomarSubmission 65f0154) on the
  tracked files: 73 `.lean` files, no issue; largest file 3382 lines; `Challenge.lean` 99 lines.
* **Memory of the build**: built in parallel, the 16 certificate modules `HeadCert7Lev*`/`HeadCert7Data*`
  (about 10 GB each) exhausted 54 GB. The generator now chains them (each part imports the previous one);
  the full build then peaked at about 22 GB (`MaxU7` up to 15 GB) and took about 20 minutes on 32 threads.
* **Checks after the port**: `bash scripts/build.sh` (default targets) green; `scripts/audit.sh` clean;
  `#print axioms` of `zeta2_7_irrational`, `main7_of_stmts` and `zeta2_7_irrational_palomar`:
  `[propext, Classical.choice, Quot.sound]`. Declaration-level comparison with master: all 2618 user-level
  constants have the same kind and type hash; 536 of the 538 definitions the same value hash, and the other
  two (`Pair.configE`, `Pair.NVq.Zq`) differ only inside proof terms (`configE`: an auxiliary proof renamed;
  `Zq`: identical when printed with proofs elided, master rebuilt outside Lake); 333 theorems differ in their
  proofs, through auxiliary constants that the module system names differently (`_private` prefixes,
  `_proof_*`, `_simp_*`, matchers).
* **Local Palomar-style comparator run** (`lake comparator` as Palomar runs it, unsandboxed): the statement
  comparison accepted `Solution.lean`; two altered copies of `Challenge.lean` (`zeta2 9` for `zeta2 7`;
  `∃ q : ℤ` for `∃ q : ℚ`) were rejected ("statement do not match"). The kernel replays of the accepting
  run did not finish: con-ron (default 16 workers) reached 55 GB resident and was killed by the Linux OOM
  killer. **Open before submission:** Palomar's execution profile (16 vCPU, 32 GB) runs con-ron with the
  same default, so its mechanical check would probably fail the same way. Next step: run
  `con-ron --jobs=1 --progress` on the Solution export under a memory cap to find the declarations that
  need the memory (presumably the `decide +kernel` certificates), then split them or ask the Palomar
  maintainers. (Resolved: see "Kernel memory" below.)

## Kernel memory (2026-09-28)

* **Problem.** Palomar's runner (16 vCPUs, 32 GB) runs `lake comparator`: con-ron with its default 16
  workers, then NanoDa (4 threads), then Lean's kernel. The 16 certificate theorems `levJobs*_ok` and
  `hrows7_*_ok` were one `decide +kernel` each over a whole `HeadCert7Lev*` or `HeadCert7Data*` part
  (33-134 s and 5-15 GB each in con-ron with one worker; con-ron keeps a declaration's intermediate terms
  until that declaration is checked). They are adjacent in the export, so con-ron's 16 workers checked them
  together: killed after 62 s under a 32 GB cap (55 GB resident before the Linux OOM kill above). NanoDa
  (17 GB) and Lean's kernel (8 GB) passed.
* **Fix** (certificate internals only; no statement changed). `HeadCert7Series` evaluates `levChk` by pole
  groups, computing each pole's Taylor series once for all its bad pairs (`HC7.grp`, `HC7.grpC`,
  `HC7.ASerC_eq_grp`), and in pieces (`HC7.grpR`/`HC7.grpT`, combined by `HC7.LevJob.ok_of_vals1..4`).
  `HeadCert7_gen.py` cuts the 76 `LevGe` jobs into 237 pieces and the 469 rows into 243 chunks by a
  cost estimate; each is one `have … := by decide +kernel` inside `levJob*_*_ok` / `hrows7_*_ok` (at most
  about 2 s in con-ron with one worker). `HeadCert7_gen.py --check` reproduces the generated files byte for
  byte. Details: `notes/HeadCert7.md`.
* **Checks.** `lake build` green (`lake build Solution` rebuilt the 24 modules that depend on the change in
  4.5 min on 16 CPUs, peak 5.6 GiB); `#print axioms` of `zeta2_7_irrational_palomar`, `zeta2_7_irrational`
  and `main7_of_stmts`: `[propext, Classical.choice, Quot.sound]`; `scripts/audit.sh` clean; Palomar's
  `source_requirements.py` (65f0154) on the tracked files: no issue (73 Lean files, largest 3382
  lines). Declaration-level comparison with b77c555 (kind, type hash and value hash of every constant of
  the project modules): the 4414 constants outside `HeadCert7Series` and the generated parts are all
  identical, among them every `Stmt_*`, `*_proof` and main theorem; inside, the statements are unchanged:
  `levJobs0..7`, `hrows7_0..7` and their `_ok` theorems have new values, the auxiliary lemmas
  `levJobs*_ok._proof_1_1` are gone, the names `hrows7_*_ok._proof_1_1` now denote the check of a part's
  first chunk, and 1003 constants are new.
* **Local Palomar-style comparator run** (Palomar's steps and command lines, unsandboxed, the whole run in
  a 32 GB memory cgroup): accepted, with all three kernel replays. Peak resident memory: con-ron (16
  workers) 13.1 GiB (96 s), NanoDa 1.9 GiB (101 s), Lean's kernel 1.3 GiB (570 s); the run's
  anonymous memory peaked at 14.2 GiB (23.9 GiB with the page cache of the `.olean` and export files).
  While con-ron checks the generated parts it stays at 5-6 GiB; its peak comes from the 10
  `resECerts7_*_ok` checks of `ResCert7Data` (unchanged), which it finishes together at the end. The two
  altered copies of `Challenge.lean` (`zeta2 9`; `∃ q : ℤ`) were rejected ("statement do not match").

## Pre-publication audit (2026-09-28)

An auditor agent, independent of the preparer, re-checked branch `palomar-prep` at b77c555, and a
verifier agent, independent of both, re-checked the final version 1ce8200 (after "Kernel memory").
* **Build and axioms**: at b77c555 `lake build --no-build` reported all 9006 jobs up to date. At 1ce8200 a
  clean build of the project modules in a fresh clone (`lake build Solution`, 71 modules, 16 CPUs, in a
  30.5 GiB memory cgroup) succeeded in 411 s; its largest process was `MaxU7` (15.3 GB). `#print axioms` of
  `zeta2_7_irrational_palomar`, `zeta2_7_irrational` and `main7_of_stmts` gives
  `[propext, Classical.choice, Quot.sound]`; `scripts/audit.sh` is clean. The statement of
  `zeta2_7_irrational_palomar` elaborates with `Rat.cast : ℚ → ℚ_[2]`, and `zeta2 7 = J 6 / 768` holds
  by `norm_num`.
* **Trusted definitions**: the six definitions are byte-identical in `Challenge.lean`,
  `Zeta2Lean/Defs.lean` (this branch and master) and the registered pair repository (`Challenge.lean`
  and `Defs.lean`).
* **Removal and port, source level**: the 15 removed Lean files lie outside the import closure of
  `Zeta2Lean.Z7.Main` at master (70 modules). With comments stripped and the module-system header
  normalised, the 70 files of that closure are unchanged apart from the imports that chain the
  `HeadCert7Lev*`/`HeadCert7Data*` parts.
* **Kernel-memory change**: an independent declaration-level comparison of 1ce8200 with b77c555 found
  the 4414 constants outside the certificate modules identical (type and value hashes), and no public
  type changed inside them; each old `hrows7_*` and `levJobs*` list equals the concatenation of its new
  chunks, so the certificate data is unchanged.
* **Generated files**: `python/z7_den_table.py --check`, `HeadCert7_gen.py` (19 files regenerated from
  scratch; `--audit`: 0 mirror failures), `ResCert7_gen.py --check` and `MaxU7_gen.py` (42 boxes, worst
  box bound 0.708146) reproduce the committed files byte for byte at 1ce8200.
* **Kernel replays**: `scripts/kernels.sh Solution` (Lean's `leanchecker`, one module at a time) passes
  all 71 modules at 1ce8200 (largest `maxrss` 6.8 GB: `Pair.Proofs.Denominators`, `ResCert7Data`,
  `HeadCert7Data7`). A local Palomar-style comparator run (Palomar's steps and command lines,
  unsandboxed, in a cgroup with Palomar's limits: 30.5 GiB, high mark 29.6 GiB, no swap) accepted the
  proof with all three kernel replays: con-ron (default 16 workers) 13.1 GiB, NanoDa 2.1 GiB, Lean's
  kernel 1.3 GiB; no out-of-memory kill. The verifier's own altered copies of `Challenge.lean` were
  rejected: `halfPow` changed from `2⁻¹` to `3⁻¹` ("Const does not match ... Zeta2.halfPow", so the
  definitions are compared, not only the statement) and the first conjunct (`HasVolkenborn`) dropped
  ("theorem statement do not match").
* **Palomar**: `scripts/source_requirements.py` of PalomarSubmission 65f0154 (identical to its current
  main) on the tracked files finds no issue in the 73 Lean files (on master it flags all 88);
  `formalization.yaml` passes the upstream v0.4 JSON schema and Palomar's `load_formalization_metadata`
  (65f0154), with result origin `original`; `LICENSE` is byte-identical to PalomarTemplate's.
* **Tracked files**: no e-mail addresses, local paths or model version names.
