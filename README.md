# The 2-adic zeta value ζ₂(7) is irrational

A Lean 4 + Mathlib proof of the following theorem. The mathematics and the Lean code were produced by AI agents
under human direction and have not been refereed (see *Status and caveats*).

> **Theorem.** The 2-adic zeta value ζ₂(7) is irrational.

ζ₂(3) is irrational (F. Calegari, 2005; F. Beukers, 2008), and so is ζ₂(5) (F. Calegari, V. Dimitrov and Y. Tang;
L. Lai, J. Sprang and W. Zudilin, IMRN 2026). L. Lai, *On the irrationality of certain 2-adic zeta values*, Int. J.
Number Theory 21 (2025), 207–235 (arXiv:2304.00816), Theorem 1.1 with s = 3, proves that at least one of ζ₂(7),
ζ₂(9), ζ₂(11), ζ₂(13) is irrational. Two earlier formalisations by the same maintainer, registered in the Palomar
registry, prove that at least one of ζ₂(7), ζ₂(9), ζ₂(11) is irrational
([gmDevi/zeta2-7-9-11-lean](https://github.com/gmDevi/zeta2-7-9-11-lean), PALOMAR-2026-09-25-000023) and that at
least one of ζ₂(7), ζ₂(9) is irrational ([gmDevi/zeta2-7-9-lean](https://github.com/gmDevi/zeta2-7-9-lean),
PALOMAR-2026-09-25-000026). The theorem here implies all three.

An unrefereed draft by C. D. Long ([octonion/p-adic-zeta-irrationality](https://github.com/octonion/p-adic-zeta-irrationality),
August 2026) claims, by a different method (hybrid arithmetic holonomy), that ζ₂(s) is irrational for every odd s
with 3 ≤ s ≤ 29, which includes ζ₂(7). It is not used here. We were unable to verify it: an internal AI-assisted review ([docs/long_review.md](docs/long_review.md);
not a refereed report; the author has not been contacted) found that its large-prime estimate (the torsor decomposition
and Prop. "Torsor Cartier strictness") does not appear to hold for the Eisenstein–Eichler leaf, and that without it the
method's margin for ζ₂(7) is negative; the draft's other ingredients and all 22 of its printed margins were
reproduced. No refereed proof that ζ₂(7) is irrational is known to us.

## What exactly is proved in Lean

```lean
-- Zeta2Lean/Z7/Main.lean
theorem Zeta2.Z7.zeta2_7_irrational :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧ ¬ ∃ q : ℚ, zeta2 7 = q
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`, and the theorem has no hypotheses. There is no
`sorry` (apart from the intended one in the Palomar statement file `Challenge.lean`), no `axiom` declaration and no
`native_decide`; the certificates of the growth and denominator bounds are checked by `norm_num` and by
`decide +kernel`, i.e. by kernel reduction. The first conjunct says that the Riemann sums defining every `J s`
converge, so no unspecified value of Mathlib's `limUnder` enters the statement. "Rational" means "in the image of
ℚ → ℚ₂".

**Trusted definitions.** These are the only project definitions that occur in the statement
(`Zeta2Lean/Defs.lean`, identical to those of the two registered repositories above):
* `volkenbornSum f N = (2^N)⁻¹ * ∑_{x < 2^N} f x`, the Riemann sums of the Volkenborn integral on ℤ₂;
* `HasVolkenborn f I`, meaning `Filter.Tendsto (volkenbornSum f) atTop (𝓝 I)` in `ℚ_[2]`;
* `halfPow s x = (x + 1/2)^(-s)`;
* `J s = limUnder …` (the first conjunct of the theorem proves that this limit exists);
* `zeta2 s = J (s-1) / ((s-1) * 2^s)`, so `zeta2 7 = J 6 / 768`.

**One cited identification, not formalised.** `zeta2 s` is defined through the Volkenborn integral. By
Lai–Sprang–Zudilin (IMRN 2026, rnag180; arXiv:2505.05005, Lemma 2.8), J(s−1) = (s−1)·2^s·ζ₂(s) for every integer
s ≥ 2, where ζ₂(s) = L₂(s, ω^{1−s}) is the Kubota–Leopoldt value; so `zeta2 s` = ζ₂(s). This identification is
cited, not formalised. It only involves the non-zero rational factor (s−1)·2^s, which does not affect
irrationality; other normalisations of ζ₂(s) (for example with the Euler factor (1 − 2^{−s})⁻¹) also differ by a
non-zero rational factor.

## The mathematics

The informal proof is `docs/proof.md`. For n ∈ 40ℤ, let η = (5, 7, 7, 9, 11, 13)/40, let C_m be the integer
interval [η_m n, (1 − η_m) n − 1], and let the pole orders a_k ∈ {1, 2, 3, 4} ramp up from both ends (a_k = 1, 2, 3
for min(k, n − k) < n/20, n/10, 3n/20, and a_k = 4 otherwise). With

R_n(t) = (2t + n) ∏_{m=1}^{6} ∏_{c ∈ C_m} (t + ½ + c) / ∏_{k=0}^{n} (t + k)^{a_k},  S_n = ∫_{ℤ₂} R_n'''(t + ½ − n/2) dt,

the Volkenborn integral at the *centred* point t + ½ − n/2 gives a linear form in 1 and ζ₂(7) only:
* **linear form** (Lemma L): S_n = ρ_n + Z_n ζ₂(7) with Z_n = −46080 c₃ and ρ_n ∈ ℚ explicit. deg R_n = −3 removes
  ζ₂(5), the symmetry R_n(−n−t) = −R_n(t) removes the even values, and a_k ≤ 4 removes ζ₂(9) and beyond;
* **2-adic size** (Theorem V): v₂(S_n) ≥ 6.8n − O(log n), by the Δ-calculus of Lai and Sprang;
* **growth** (Theorem G): max(|ρ_n|, |Z_n|) ≤ e^{U* n + O(log n)} with U* = 0.70670…, the maximum of an explicit
  potential U on [0, 1] (residue-level Cauchy bounds and a certified maximum);
* **denominators** (Theorems C, K, A): the odd part of a common denominator of ρ_n and Z_n is at most
  e^{E n + o(n)}, with E = 3.8808… in the informal proof. No prime above n divides it (Theorem C). For the other
  primes q, the partial-fraction data are grouped by residue classes modulo q: a *class lemma* (a residue identity
  for the bad pairs of each class), a kernel identity for the sum over all classes and per-pole bounds give a
  bound e_q(n) ≤ f(n/q) (Theorem K), where f is computed from local models of the classes; f is piecewise constant
  on finitely many candidate intervals, which are certified; the prime number theorem sums the bounds;
* **nonvanishing** (Theorem N): if ℓ = 19n/20 − 1 is prime, then v_ℓ(ρ_n) = −1 and v_ℓ(Z_n) ≥ 0 (the auxiliary-prime
  condition of Lai–Sprang, arXiv:2306.10393, Lemma 2.2), and Dirichlet's theorem gives infinitely many such n;
* **Lai's criterion** (Lai, Lemma 2.1) along these n: the margin is U* + E − 6.8 log 2 = −0.126 per n.

## The proof in Lean

`Zeta2Lean/Z7/Defs.lean` defines the construction, indexed by u with n = 40u: the partial-fraction coefficients
r_{i,k} as Taylor coefficients in `PowerSeries ℚ`, ρ (`rho`) and Z (`Zc`), the local models of residue classes and
the class sums of the denominator argument, the potential U (`Upot`) and the rates `g7 = 0.71` and `delta7 = 3.99`.
`Zeta2Lean/Z7/DenTable.lean` (generated) holds the certified exponent table. `Zeta2Lean/Z7/Statements.lean` has
one statement per lemma, `Zeta2Lean/Z7/Assembly.lean` (`main7_of_stmts`) derives the theorem, for any rates g, δ
with g + δ < 6.8 log 2, from the linear form, the 2-adic bound, Lai's criterion and the three top-level statements,
and `margin7` checks 0.71 + 3.99 = 4.70 < 6.8 log 2 = 4.7134. `Zeta2Lean/Z7/Main.lean` plugs in the proofs:
* **Linear form** (`TranslationNeg`, `GenLinearFormZ`, `PartialFractions7`, `CoeffVanish7`, `LinearForm7`): the
  Riemann sums of the centred integrand converge to ρ + 60 c₃ J₆, with c₁ = c₂ = c₄ = 0.
* **2-adic size** (`IntegrandTaylor7`, `Valuation7`): ‖S‖₂ · 2^{272u} ≤ c (u + 1)^A (with c = 4 · 30¹⁰, A = 10),
  i.e. v₂(S_n) ≥ 6.8n − O(log n), by the Δ-calculus.
* **Growth** (`MaxU7`, `ResidueBound7`, `Growth7`): U ≤ 0.71 on [0, 1], certified on 42 boxes with rational
  enclosures of `log` (worst box 0.7081); |r_{i,k}| ≤ C (u+1)^B e^{n U(k/n)}; hence |ρ|, |Z| ≤ e^{(0.71 + ε) n}.
* **Denominators** (`BigPrimes7`, `SmallPrimes7`, `Emin7`, `ClassLemma7` with `LocalExpansion7`, `KernelIdentity7`,
  `FarPart7`, `PerPole7`, `ThmK7`, `HeadCert7`, `ResCert7`, `ExpBounds7`, `Denominators7`): Theorems C and K and
  Lemmas 4.3–4.12 of `docs/proof.md`, and Theorem A with the prime number theorem. `HeadCert7` certifies the
  kernel-level bound on the 469 candidate intervals of [1, 20) and `ResCert7` the residue level on one period
  [20, 60) (with its 40-periodicity); their data (`HeadCert7Lev*`, `HeadCert7Data*`, `ResCert7Data`, generated by
  the scripts next to them) are checked by `decide +kernel`. The exponent integral of the table on [1, 140), plus
  the tail 10/140, is 3.9241 ≤ 3.99 (checked in fixed-point arithmetic by the kernel).
* **Nonvanishing** (`AuxPrime7`, `NonvanishingLS7`): Theorem N for ℓ = 38u − 1 and the Lai–Sprang argument, with
  Mathlib's Dirichlet theorem (`Nat.frequently_atTop_prime_and_modEq`) for primes ≡ −1 (mod 38).
* **Shared infrastructure**, from the registered repositories: the six trusted definitions, the convergence of
  `J s`, the translation formula, Lai's criterion and the Δ-calculus (`Zeta2Lean/Defs.lean`,
  `Zeta2Lean/Statements.lean`, `Zeta2Lean/Proofs/`), the prime number theorem (`Zeta2Lean/Cited/`, with the
  vendored Wiener–Ikehara theorem), and four files of the pair repository whose lemmas are reused: prime sums
  (`Pair/Proofs/Denominators.lean`), a `q`-integral residue calculus (`Pair/Proofs/Nonvanishing.lean`, with
  `NonvanishingLS.lean`) and certified enclosures of `log` (`Pair/Proofs/Landscape/Numerics.lean`), together with the
  pair's `Defs.lean` and `Statements.lean`, which they import.

**Differences from `docs/proof.md`.** The Lean proof follows the "Lean-friendly" variant of docs/proof.md (§0.2
and §10):
* weaker constants: growth rate 0.71 instead of U* = 0.70670; denominator exponent 3.99 ≥ 3.9241, from the kernel
  level on [1, 20), the residue level on [20, 140) (by periodicity) and the bound 10 beyond 140, instead of
  E* = 3.8808 (kernel level on [1, 60] and the exact residue-level tail). The margin 4.70 < 4.7134 still holds;
* its own certificates: the maximum of U on 42 boxes (chord and tangent bounds) instead of the interval-arithmetic
  certificate of docs/proof.md Lemma G7, and sweep certificates of the event lines of Lemmas 4.10–4.12, checked by
  the kernel, instead of the exact Python computation of f;
* the certificate statements assume q > 1000 (docs/proof.md: q > 40), q ∤ n/40 and q² > 2n + 3q; the other primes
  are covered by the crude bounds (Lemmas 4.8 and 4.9), so the asymptotics are unchanged;
* exact finite truncations in place of infinite q-adic series (class lemma, far part, per-pole bounds), and exact
  telescoping in place of the sum–integral comparisons of Lemmas G3–G5 (weaker, sufficient constants);
* Theorem N is used for all large n (docs/proof.md: every n ∈ 40ℤ with ℓ prime);
* the sign convention S_n = −∫ R_n'''(t + ½ − n/2) dt, which changes the signs of ρ_n and Z_n.

## Status and caveats

* **Unrefereed, produced by AI agents.** The mathematics (the construction and the informal proof) and this
  formalisation were produced by AI agents (Anthropic Claude models) under the direction of the maintainer, and have
  not been reviewed by a human expert (`formalization.yaml` describes the process). The Lean kernel checks the
  formal statement displayed above. Whether that statement matches the mathematics is a matter of the trusted
  definitions and the cited identification listed here.
* **Literature.** No refereed proof that ζ₂(7) is irrational is known to us. The literature search of 2026-09-26
  (arXiv listings and the author pages of Lai, Sprang and Zudilin, OpenAlex, GitHub, Lai's homepage, blogs and a web
  search) found no refereed paper and no arXiv preprint proving it; the only public claim is C. D. Long's
  unrefereed draft above. Google Scholar, MathSciNet, zbMATH full text and Lai's thesis were not searched.
* **Relation to the registered repositories.** This repository started as a copy of the pair repository
  (gmDevi/zeta2-7-9-lean), which started as a copy of the {7, 9, 11} repository. The three proofs share the
  Volkenborn integral, the Δ-calculus, Lai's criterion and the prime number theorem, but not the construction or the
  denominator and nonvanishing arguments. The files reused from them are unchanged apart from the module-system
  header and, in the pair files and in `Defs.lean`, `Statements.lean`, `Cited/PNT.lean` and the vendored files,
  comments on their role here; references in their docstrings to documents that are not included here are to those
  repositories.
* **Scope.** The theorem says that ζ₂(7) is irrational. It gives no irrationality measure.

## Layout

* `Zeta2Lean/Defs.lean`, `Zeta2Lean/Statements.lean`, `Zeta2Lean/Proofs/`: the shared definitions (among them the
  six trusted ones), statements and proofs.
* `Zeta2Lean/Cited/PNT.lean`, `Zeta2Lean/Cited/Vendor/PNT/`: the prime number theorem and the vendored
  Wiener–Ikehara code (mathlib4 pull requests #43046, #43233 and #43238; Apache-2.0).
* `Zeta2Lean/Pair/`: the six files of the pair repository that the proof reuses (see above).
* `Zeta2Lean/Z7/Defs.lean`, `DenTable.lean`, `Statements.lean`, `Assembly.lean`, `Main.lean`: the construction, the
  exponent table, one statement per lemma, the assembly and the wiring (with `#print axioms`).
* `Zeta2Lean/Z7/Proofs/*.lean`: one proof per statement, helper files, the generated certificate files and their
  generators (`HeadCert7_gen.py`, `ResCert7_gen.py`, `MaxU7_gen.py`).
* `BLUEPRINT_Z7.md` (statement map, dependency graph, design), `STATUS_Z7.md` (per-file census and the checks of
  each round), `notes/` (the provers' notes).
* `docs/proof.md`: the informal proof.
* `python/`: `z7_mirror.py` (an exact-arithmetic mirror of the definitions with numerical checks of every
  statement), `z7_audit.py` (an independent audit), `z7_den_table.py` (generator of `DenTable.lean`), logs of full
  runs, `z7_ref/` (verbatim copies of the research engines and the certified interval data), `pair_den_certs.py`
  (generator of the certificates in `Pair/Proofs/Denominators.lean`) and `zeta2_K17000.json` (2-adic values of the
  J_s used by the mirror).
* `scripts/`: `check.sh` (elaborate one file), `build.sh`, `audit.sh` (sorry and forbidden-construct census),
  `kernels.sh` (`leanchecker`, one module at a time).
* `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the statement, proof and metadata for
  [Comparator](https://github.com/leanprover/comparator) and the Palomar registry (next section).

Every Lean file uses Lean's module system (a `module` header, `public import` and an `@[expose] public section`), as
the Palomar registry requires; the generators emit the same header.

## Challenge and Solution

`Challenge.lean` imports only Mathlib. It contains verbatim copies of the six trusted definitions of
`Zeta2Lean/Defs.lean` and states the theorem as `Zeta2.Z7.zeta2_7_irrational_palomar`, with `sorry`. `Solution.lean`
proves the same statement from `Zeta2.Z7.zeta2_7_irrational`. `comparator.json` asks Comparator to check that the two
statements, and every definition they use, are identical, and that the proof uses only `propext`, `Quot.sound` and
`Classical.choice`. On 2026-09-28, after the port to Lean's module system, a local reproduction of Palomar's
mechanical check (`Challenge.lean` compiled outside Lake against Mathlib only, both modules exported with
`leanexport`, the toolchain's `lake comparator`; unsandboxed, because bubblewrap is not installed on that machine)
found the statement of `Solution.lean` identical to that of `Challenge.lean`, and rejected two altered copies of
`Challenge.lean`: one with `zeta2 9` in place of `zeta2 7`, and one with `∃ q : ℤ` in place of `∃ q : ℚ`. The kernel
replays of that first run did not finish: the con-ron checker, which Palomar runs besides Lean's kernel and NanoDa,
ran out of memory on the generated certificates. After these were cut into small kernel checks (no statement
changed; `STATUS_Z7.md`, "Kernel memory"), the same reproduction in a 32 GB memory cgroup, the memory of Palomar's
runner, completed the kernel replays of con-ron (default 16 workers, peak 13.1 GiB), NanoDa (1.9 GiB) and Lean's
kernel (1.3 GiB) and accepted the proof. All 70 modules of the proof had also been replayed with Lean's
`leanchecker` before the port, which changed no statement or definition, and all 71 modules of `Solution` were
replayed again on the final version. `formalization.yaml` records the sources,
the production process and the review status.

## Building

```bash
lake exe cache get
lake build                                    # also builds Challenge and Solution
lake env lean Zeta2Lean/Z7/Main.lean          # prints the axioms of the main theorems
lake comparator                               # judges Solution against Challenge (needs bwrap)
bash scripts/audit.sh                         # sorry / forbidden-construct census
bash scripts/kernels.sh                       # leanchecker on every module, one at a time
```

A full build (after `lake exe cache get`) took about 20 minutes on a 32-thread machine, with a peak memory use of
at most about 22 GB: `MaxU7` needs up to 15 GB; the 16 generated certificate modules `HeadCert7Lev*` and
`HeadCert7Data*` consist of small kernel checks (at most about 4 GB each, mostly the imported environment) and
import each other in a chain, so a parallel build checks them one at a time. `scripts/kernels.sh` replays one module
at a time (each run loads Mathlib, about 6-7 GB); the CI workflow does the same, which may exceed the memory of a
standard GitHub runner.

## Licence

Apache-2.0 (`LICENSE`). The vendored files under `Zeta2Lean/Cited/Vendor/PNT/` keep their upstream Apache-2.0
headers and authors.
