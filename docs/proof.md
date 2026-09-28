# The 2-adic zeta value ζ₂(7) is irrational — assembled informal proof (configuration cand3)

This proof was assembled on 2026-09-26 from the research tracks listed in §11 by an assembler agent, who also acted
as the final referee. It uses only results that were proved in a track **and** confirmed by an independent verifier
who wrote their own code and re-derived the arguments by hand.

> **Editorial note (2026-09-28, for this repository).** This is the assembled proof with the local file paths of the
> research session removed and the status lines of §0 updated. Script and data names (such as `vc_engine.py`,
> `levels.py` or `constants.py`) refer to the research computations, which are not part of this repository, except
> the verbatim copies of the reference engines in `python/z7_ref/`. §10 is the plan that the Lean formalisation in
> this repository followed, and `README.md` lists where the Lean proof differs from this text (it uses the
> "Lean-friendly" constants of §0.2). Neither this proof nor the formalisation has been refereed by a human expert.

Labels:
- **PROVED**: the complete argument is given here, modulo the cited tools (P1)–(P9) of §1.
- **PROVED (computer-assisted)**: the complete argument is given here, and one finite step is an exact rational or
  interval-arithmetic computation by a named script. Each such step was redone by an independent implementation.
- **NUMERICAL**: evidence only. Nothing labelled NUMERICAL is used in the proof.

---------------------------------------------------------------------------------------------------

## 0. Statement, status and margin

**Main Theorem.** ζ₂(7) ∉ ℚ.

Here ζ₂(7) := J₆/768, where J₆ := ∫_{ℤ₂}(t+½)^{−6}dt is a Volkenborn integral. By [LSZ, Lemma 2.8] this is the
Kubota–Leopoldt 2-adic zeta value ζ₂(7). It is the normalisation used by LSZ and by the project's Lean repositories
(`zeta2 7 = J 6 / 768`). Irrationality does not depend on nonzero rational normalising factors.

**Status.**
- The proof is complete and computer-assisted.
- Every ingredient was proved in a track and then confirmed by an independent verifier.
- It has not been refereed outside the research workflow that produced it. It is formalised in Lean in this repository
  (§10 is the plan that the formalisation followed).
- Previously known: ζ₂(3) (Calegari; Beukers) and ζ₂(5) (Lai–Sprang–Zudilin; Calegari–Dimitrov–Tang). No refereed
  proof that ζ₂(7) is irrational is known to us. An unrefereed draft by C. D. Long (GitHub, August 2026) claims the
  irrationality of ζ₂(s) for every odd s with 3 ≤ s ≤ 29, including ζ₂(7), by a different method; it is not used
  here. We were unable to verify it: an internal AI-assisted review (`docs/long_review.md`) found that its large-prime
  estimate does not appear to hold for the Eisenstein–Eichler leaf, and that without it that method gives a negative
  margin for ζ₂(7).

**Idea.** Take the Volkenborn integral of the third derivative of an explicit rational function R_n, evaluated at the
**centred** point t + ½ − n/2. R_n has:
- degree −3;
- antisymmetry R_n(−n−t) = −R_n(t);
- pole orders ≤ 4 that ramp up 1, 2, 3, 4 from the two ends;
- six nested well-poised numerator blocks.

The integral is S_n = ρ_n + Z_nζ₂(7), and no other zeta value occurs. Lai's 2-adic criterion then needs three bounds:
- the odd denominators, bounded through a new **residue-class (collective) cancellation**: the class lemma together
  with a global residue identity;
- the growth, bounded at residue level;
- the 2-adic size, bounded with the Δ-calculus.

Nonvanishing comes from an auxiliary prime ℓ = 19n/20 − 1.

### 0.1 The ingredients

| # | ingredient | statement (short) | status | proved in / confirmed by |
|---|---|---|---|---|
| 0 | construction (§2) | deg R_n = −3, R_n(−n−t) = −R_n(t), a_k ≤ 4 | PROVED | notes §5; all verifiers |
| L | linear form (§3) | S_n = ρ_n + Z_nζ₂(7), Z_n = −46080·c₃, ρ_n explicit (3.1) | PROVED | growth-nonvanishing §1.3; verify-candidate, verify-growth-nonvanishing |
| C | primes above n (§4.7) | no prime q > n divides D_n | PROVED | notes Thm C(ii); here |
| K | per-prime bound (§4.6) | e_q(n) ≤ f_n(q) for q ≥ 29 with q² > 2n+3q | PROVED | denominators-theory; verify-denominators-theory |
| A | denominators (§4.9) | (1/n)·log D_n ≤ E* + o(1), E* = 3.8808431 | PROVED (computer-assisted) | denominators-theory; verify-denominators-theory. Second proof: denominators-search (E = 3.8801844), verify-denominators-search |
| G | growth (§5) | log max(\|ρ_n\|,\|Z_n\|) ≤ U*·n + 14 log n + 2 log(n+1) + 47.5, with U* = 0.70670223 | PROVED (computer-assisted) | growth-nonvanishing §2; verify-growth-nonvanishing |
| V | 2-adic size (§6) | v₂(S_n) ≥ 6.8n + 7 − 10(⌊log₂(3n/4)⌋ + 1) | PROVED | growth-nonvanishing §3; verify-growth-nonvanishing |
| N | nonvanishing (§7) | if ℓ = 19n/20 − 1 is prime: v_ℓ(ρ_n) = −1 and v_ℓ(Z_n) ≥ 0 | PROVED | growth-nonvanishing §4; verify-growth-nonvanishing |
| — | criterion (§8) | Liouville / Lai, along I = {40m : 38m − 1 prime} | PROVED | growth-nonvanishing §5; here |

### 0.2 Margin table

The criterion needs growth + (denominator exponent) − gain < 0, where the gain is 6.8·log 2 = 4.7134008 (from V).
Recomputed by the assembler's `constants.py`.

| growth exponent | denominator exponent | margin per n | status |
|---|---|---|---|
| U* = 0.70670223 (G) | **E\* = 3.88084310** (A: kernel head on [1,60] + residue-level tail) | **−0.1258555** | **PROVED** |
| U* | 3.88018442 (the search track's version of Theorem K, head [1,40]) | −0.1265142 | PROVED (second proof) |
| U* | 3.9240892 (kernel head [1,20], residue level on [20,140] by periodicity, 10/140 beyond) | −0.0826094 | PROVED; the Lean-friendly variant (§10) |
| U* | 3.9308 (without the far-part Lemma 4.5) | −0.0759 | PROVED (robustness) |
| U* | 3.9843 (class lemma and the κ = 1 identity only) | −0.0224 | PROVED (robustness) |
| true g ≈ 0.684 | true E∞ ≈ 3.87 ± 0.02 | ≈ −0.16 ± 0.02 | NUMERICAL (verify-candidate) |
| true sizes at finite n | true D_n | −0.2296 (n = 480) … −0.1768 (n = 6000) | NUMERICAL (exact data) |

Break-even thresholds:
- The break-even denominator exponent is 6.8 log 2 − U* = **4.0066986**. E* is below it by 0.126.
- Conversely, E* closes the criterion for any growth exponent below 6.8 log 2 − E* = 0.8325577.

### 0.3 What is cited, and what is computed

**Cited (published, used as black boxes).**
- (P1) The Volkenborn integral and its translation formula [Robert GTM 198 §5.3; LSZ Lemma 2.4; Lai Lemma 2.2].
- (P2) J_s = s·2^{s+1}ζ₂(s+1) and ζ₂(even) = 0 [LSZ Lemma 2.8].
- (P3) The 2-adic Δ-calculus of Lai [Lai Def. 2.3, Lemmas 2.4–2.5] and LSZ [Lemmas 2.5–2.6]. Items (D1)–(D5) are
  re-proved in §6.
- (P5) The prime number theorem, and Chebyshev's bound θ(x) ≤ 1.02x.
- (P6) Dirichlet's theorem, for primes ≡ −1 (mod 38).
- (P7) Cauchy's estimate for power-series coefficients.

**Computer-assisted steps.** Each was done in exact or outward-rounded arithmetic and redone independently.
1. **max U ≤ U\*** (Lemma G7). 152 boxes, certified twice: mpmath.iv with outward rounding, and exact rationals with
   the script's own log enclosures. The verifier certified it a third time by a different method (chord/tangent
   convexity bounds, 109 boxes). A negative control at 0.70670222 fails, as it must.
2. **The value of E\*** (Theorem A).
   - The function f of Theorem K is computed in exact rational arithmetic (Python `fractions`) on the 1449 candidate
     intervals of [1,60] (`cont.py`, `levels.py`, `integrate.py` of the denominators-theory track).
   - The residue-level function f⁰ is computed on one period [20,60], which has 980 intervals (`tail.py`). The tail
     beyond 60 is then an explicit digamma sum.
   - The verifier's independent implementation reproduces all 1449 interval values exactly
     (`vlevels.py`, `vinteg.py`). It computes residue moments mod 2^127 − 1 per pole, with
     its own event set.
   - The assembler re-summed the three head files exactly: 51/20, 2989163/2882880 and
     5263504492683945763/27401381122591476000 (`constants.py`).
3. The constants of Theorem N, such as θ₀ = −81/224, are hand computations. They were checked exactly by `nv_theta.py`
   and again by the assembler's `constants.py`.

### 0.4 Referee's summary (details in §9)

**Standard parts.** L, G, V and N are standard in method:
- V is the pair's Lean-formalised Theorem G4 with one factorisation lemma changed.
- N is the pair's auxiliary-prime argument, simpler here because the leading poles have order 1.
- G is a residue-level estimate plus a 1-D certified maximum.

**The new part.** The new mathematics is the denominator theorem (K + A). Its evidence:
1. The per-prime bound was compared with the **true** exponent (exact odd denominators) at about 30,000 pairs (n, q),
   with n up to 200,000, by two independent implementations.
   - There were no violations.
   - The bound equals the truth at 99% of the pairs, and on intervals carrying 97.3% of the head integral.
2. The class lemma was tested as an exact identity, valuation and leading digit, on 19,827 class instances.
3. The margin survives the removal of the most intricate step, the far-part lemma (margin −0.076), and even of the
   whole kernel step (margin −0.022).

I found no gap. The items that deserve an external referee's attention are listed in §9.

---------------------------------------------------------------------------------------------------

## 1. Notation and cited tools

**Notation.**
- (x)_k is the rising factorial and C(x,k) = x(x−1)⋯(x−k+1)/k! the binomial coefficient.
- s₂(N) is the binary digit sum.
- [ε^λ]F is a Taylor coefficient at ε = 0, and [y^p] a coefficient of a (Laurent) series in y.
- v_q is the q-adic valuation (on ℚ, and on ℚ₂ for q = 2), and ℤ_(q) = {x ∈ ℚ : v_q(x) ≥ 0}.
- θ(x) = Σ_{p≤x} log p.
- For k ≥ 1, k₋ is k with its leading binary digit deleted.

**Cited tools.**
- **(P1) Volkenborn integral** [Robert, *A Course in p-adic Analysis*, GTM 198, Ch. 5; LSZ §2.2].
  - Definition: ∫_{ℤ₂}f(t)dt := lim_M 2^{−M}Σ_{x<2^M}f(x).
  - It exists for strictly differentiable f, in particular for every rational function without poles in ℤ₂, and it is
    ℚ₂-linear.
  - Translation: for d ≥ 1, ∫f(t+d)dt = ∫f + Σ_{l=0}^{d−1}f′(l). Hence, for d ≤ −1,
    ∫f(t+d)dt = ∫f − Σ_{l=d}^{−1}f′(l) (apply the first formula to t ↦ f(t+d)).
- **(P2) 2-adic zeta values** [LSZ Lemma 2.8]. J_s := ∫_{ℤ₂}(t+½)^{−s}dt = s·2^{s+1}ζ₂(s+1), and ζ₂(2k) = 0. So J_s = 0
  for odd s, and J₆ = 768·ζ₂(7).
- **(P3) Δ-calculus** [Lai, IJNT 21 (2025), Def. 2.3, Lemmas 2.4–2.5; LSZ Lemmas 2.5–2.6]. Re-proved in §6.2.
- **(P4) Elementary number theory.**
  - Legendre: v_q(m!) = Σ_e⌊m/q^e⌋, and v₂(L!) = L − s₂(L).
  - Kummer: v_q C(N,K) ≤ ⌊log_q N⌋.
  - Among L consecutive odd integers, at least ⌊L/q^e⌋ are divisible by q^e (q odd).
  - If q is an odd prime, then Σ_{u=1}^{q−1}u^{−s} ≡ 0 (mod q) unless (q−1) | s.
- **(P5) Prime number theorem**: θ(x) = x + o(x). Chebyshev: θ(x) ≤ 1.02x.
- **(P6) Dirichlet**: there are infinitely many primes ≡ −1 (mod 38).
- **(P7) Cauchy's estimate** for the Taylor coefficients of a function holomorphic on a disc.
- **(P8) Rigorous computation**: exact rationals (Python `fractions`); mpmath.iv with outward rounding.
- **(P9) Digamma**: ψ(z) − ψ(w) = Σ_{j≥0}(1/(j+w) − 1/(j+z)).

**Lemma D2** (from the pair, proof_pair.md §4.1). Let Π(ε) = ∏_β(1+ε/β)^{e_β} with v_q(β) ≥ 0 and e_β ∈ ℤ. Then
v_q([ε^λ]Π) ≥ −Top_λ, where Top_λ := max{Σ_β j_βv_q(β) : Σj_β = λ, j_β ≥ 0, j_β ≤ e_β whenever e_β ≥ 0}.

In particular:
- Top_λ ≤ λ·max v_q(β);
- if every β with v_q(β) > 0 has v_q(β) = 1 and e_β ≥ 0, and s is the number of such factors counted with
  multiplicity, then Top_λ ≤ min(λ, s).

*Proof.* [ε^λ]Π = Σ_{Σj_β=λ}∏_βC(e_β,j_β)β^{−j_β}, with C(e,j) ∈ ℤ, and C(e,j) = 0 for 0 ≤ e < j. ∎

References:
- [Lai] L. Lai, *On the irrationality of certain 2-adic zeta values*, IJNT 21 (2025) 207–235, arXiv:2304.00816.
- [LS] L. Lai, J. Sprang, *Many p-adic odd zeta values are irrational*, arXiv:2306.10393.
- [LSZ] L. Lai, J. Sprang, W. Zudilin, *A note on the irrationality of ζ₂(5)*, arXiv:2505.05005.
- [Robert] A. M. Robert, *A Course in p-adic Analysis*, GTM 198.

---------------------------------------------------------------------------------------------------

## 2. The construction (cand3) and Lemma 0

Fix n ∈ 40ℤ_{>0}.

**Numerator blocks.** Let η = (5, 7, 7, 9, 11, 13)/40. For m = 1, …, 6 put
C_m := [η_m n, (1−η_m)n − 1] ∩ ℤ. Its length is L_m = (1−2η_m)n, so the lengths are
3n/4, 13n/20, 13n/20, 11n/20, 9n/20, 7n/20. Their total is N := ΣL_m = 3.4n. Write μ(c) := #{m : c ∈ C_m}. Each C_m
is invariant under c ↦ n−1−c, and every block contains [13n/40, 27n/40 − 1].

**Pole orders.** For 0 ≤ k ≤ n put κ_k := min(k, n−k)/n and
a_k := 1, 2, 3 for κ_k ∈ [0, 1/20), [1/20, 1/10), [1/10, 3/20) respectively, and a_k := 4 for κ_k ≥ 3/20.
Explicitly:
- a = 1 on [0, n/20−1] ∪ [19n/20+1, n];
- a = 2 on [n/20, n/10−1] ∪ [9n/10+1, 19n/20];
- a = 3 on [n/10, 3n/20−1] ∪ [17n/20+1, 9n/10];
- a = 4 on [3n/20, 17n/20].

The profile is symmetric (a_{n−k} = a_k), and Σ_k a_k = N + 4 = 3.4n + 4.

**The form.**

  R_n(t) := (2t+n)·∏_{m=1}^{6}∏_{c∈C_m}(t+½+c) / ∏_{k=0}^{n}(t+k)^{a_k},    S_n := ∫_{ℤ₂} R_n'''(t+½−n/2) dt.

Equivalently, with nested well-poised blocks:

  R_n = (2t+n)(t+½+n/8)_{3n/4}(t+½+7n/40)²_{13n/20}(t+½+9n/40)_{11n/20}(t+½+11n/40)_{9n/20}(t+½+13n/40)_{7n/20}
        / [(t)_{n+1}(t+n/20)_{9n/10+1}(t+n/10)_{4n/5+1}(t+3n/20)_{7n/10+1}].

This is "cand3" of the research notes (§5 there), found by a genetic search over pole-order ramps and nested blocks.

**Lemma 0 (basic properties). PROVED.**

(a) Every numerator zero is a half-integer −½ − c, except the zero −n/2 of 2t+n, which lowers the pole order at −n/2
from 4 to 3. The partial-fraction expansion is R_n(t) = Σ_{k=0}^{n}PP_k(t), where PP_k(t) = Σ_{i=1}^{a_k}r_{i,k}(t+k)^{−i}.
Put G_k(ε) := ε^{a_k}R_n(−k+ε). It is holomorphic for |ε| < 1, and r_{i,k} = [ε^{a_k−i}]G_k.

(b) deg R_n = 1 + N − Σa_k = −3. Hence c₁ := Σ_k r_{1,k} = lim_{t→∞} tR_n(t) = 0.

(c) R_n(−n−t) = (−1)^{1+N+Σa_k}R_n(t) = −R_n(t), because N + Σa_k = 6.8n + 4 is even. Consequently:
- r_{i,n−k} = (−1)^{i+1}r_{i,k};
- PP_{n−k}(t) = −PP_k(−n−t);
- c_i := Σ_k r_{i,k} = 0 for even i.

(d) a_k ≤ 4, so c_i = 0 for i ≥ 5. The only possibly nonzero c_i is c₃.

*Proof.* (a) and (d) are read off the definitions. For (b), the degrees add up. For (c): t ↦ −n−t maps each factor
set to itself up to sign. There are 1 + N + Σa_k factors in all, counting the δ-factor and the zeros and poles with
multiplicity. Comparing principal parts at −k and −(n−k) gives the rest. ∎

(`verify_cand.py`, `vc_engine.py` and `vexact.py`, three independent engines, find c₁ = c₂ = c₄ = 0 and c₃ ≠ 0 at every
n computed.)

---------------------------------------------------------------------------------------------------

## 3. Lemma L (the centred linear form) — PROVED

Put d_k := k − n/2. Let H_k be the set of half-integers strictly between 0 and d_k (so H_{n/2} = ∅), and
X(k,h) := Σ_i(i)₄r_{i,k}h^{−i−4}. Then

  S_n = ρ_n + Z_n·ζ₂(7),   Z_n = −46080·c₃,   ρ_n = Σ_{k=0}^{n} sgn(d_k)·Σ_{h∈H_k} X(k,h)   (∈ ℚ).      (3.1)

Two further forms:
- By Lemma 0(c), ρ_n = −2Σ_{k<n/2}Σ_{h∈H_k}X(k,h).
- X(k,h) = 24·Res_{t=−k}R_n(t)(t_e − t)^{−5}, with t_e := −k + h.   (3.2)

*Proof.*
1. **Setup.** The poles of R_n(t+½−n/2) are half-integers, which have |·|₂ = 2. So the integrand is analytic on ℤ₂
   and S_n exists (P1). Moreover R_n''' = −Σ_{i,k}(i)₃r_{i,k}(t+k)^{−i−3}.
2. **One term.** Apply (P1) to g(t) := (t+½)^{−s}, whose derivative is g′(l) = −s(l+½)^{−s−1}, with the shift d_k.
   - For d_k ≥ 1 this gives ∫(t+½+d_k)^{−s}dt = J_s − sΣ_{l=0}^{d_k−1}(l+½)^{−s−1}.
   - For d_k ≤ −1 it gives J_s + sΣ_{l=d_k}^{−1}(l+½)^{−s−1}.
   - In both cases the correction is −sgn(d_k)·s·Σ_{h∈H_k}h^{−s−1}.
3. **Summation.** Take s = i+3 and sum −(i)₃r_{i,k}·(…). This gives
   S_n = −Σ_i(i)₃c_iJ_{i+3} + Σ_k sgn(d_k)Σ_{h∈H_k}Σ_i(i)₄r_{i,k}h^{−i−4}.
4. **The ζ-part.** By (P2), −(i)₃c_iJ_{i+3} = −(i)₄2^{i+4}c_iζ₂(i+4). The terms i = 1, 2, 4 vanish by Lemma 0, and
   ζ₂(6) = ζ₂(8) = 0 as well. The term i = 3 is −360·128·c₃ζ₂(7) = −46080c₃ζ₂(7).
5. **Symmetric form.** Put T_k := H_k − k, the half-integers strictly between −k and −n/2. Then
   Σ_{h∈H_k}X(k,h) = Σ_{t∈T_k}PP_k⁗(t).
   - PP_{n−k}⁗(t) = −PP_k⁗(−n−t).
   - t ↦ −n−t maps T_{n−k} onto T_k.
   - sgn(d_{n−k}) = −sgn(d_k).

   So the terms for k and n−k are equal.
6. **(3.2).** Write 24(h−u)^{−5} = Σ_{i≥1}(i)₄h^{−i−4}u^{i−1} with u = t+k. The rest of R_n is analytic at −k, and
   so is (t_e − t)^{−5}. ∎

**Checks** (NUMERICAL; the formula is proved).
- Five independent engines implement (3.1), and they agree with each other: genpole (through A-sums), vc_engine, and
  nv_ladic, vtruth and trueq (which use (3.1) directly).
- A zeta-free evaluation of S_n agrees with ρ_n − 60c₃J₆ modulo 2^{v₂(S_n)+64}. It works from Mahler series or from
  the Taylor coefficients of the product form, and was run for n ≤ 1600.
- J₆ was computed three independent ways: by Bernoulli numbers, by a Mahler series, and from the project's
  `zeta2_K17000.json`. The three agree to 17000–27992 bits.

---------------------------------------------------------------------------------------------------

## 4. The odd denominator (Theorems C, K, A)

Source: the denominators-theory track, confirmed in full by its verifier (verify-denominators-theory). Notation and
lemma numbers are adapted.

### 4.1 Set-up

Let D_n be the least odd positive integer with D_nρ_n, D_nZ_n ∈ ℤ[½]. For an odd prime q put

  e_q(n) := v_q(D_n) = max(0, −v_q(ρ_n), −v_q(Z_n)).

For q ≥ 7 we have v_q(Z_n) = v_q(c₃), since 46080 = 2¹⁰·3²·5. For q = 3, 5, v_q(Z_n) ≥ v_q(c₃). So in all cases
e_q(n) ≤ max(0, −v_q(ρ_n), −v_q(c₃)).

Fix an odd prime q and put x := n/q. A pair (k,h) with h ∈ H_k is **bad** if q | 2h (2h is an odd integer) and
**good** otherwise. Write ρ_n = G + B for the sums over the good and the bad pairs in (3.1).

### 4.2 Residue discs and local models

All zeros and poles of R_n lie in ½ℤ ⊂ ℤ_q.

**Discs.** For k₀ ∈ {0, …, q−1} let ξ = ξ(k₀) be the class of −k₀, with **disc** D_ξ := −k₀ + qℤ_q and centre
ξ̂ := −k₀. For a rational function F whose poles lie in ½ℤ, put ∮_{D_ξ}F := Σ_{poles w∈D_ξ}Res_wF.

Every pole −k lies in exactly one disc. The evaluation point t_e = −k+h of a pair lies in the disc of −k iff the pair
is bad. Hence B = Σ_ξβ_ξ, where β_ξ := Σ_{bad pairs with k≡k₀ (mod q)} sgn(d_k)X(k,h).

**Items.** Write R_n(t) = 2∏_w(t−w)^{e_w}. The **items** w are:
- the poles −k, with e = −a_k;
- the zeros −½−c, with e = μ(c);
- the point −n/2 of the factor 2t+n, with e = +1. It is kept separate from the pole at −n/2.

**Local coordinate.** Put v := (t−ξ̂)/q. An item w ∈ D_ξ has local point v_w := (w−ξ̂)/q ∈ ½ℤ. Define

  RR_ξ(v) := ∏_{w∈D_ξ}(v−v_w)^{e_w},   E_ξ := Σ_{w∈D_ξ}e_w,   Û_ξ(t) := 2∏_{w∉D_ξ}(t−w)^{e_w}.

Then R_n(t) = q^{E_ξ}·Û_ξ(t)·RR_ξ(v) on D_ξ.

**The local model of ξ** is the following list:
- poles v = −j for k = k₀ + jq ≤ n, of order a_k;
- zeros v = −s/2, for s odd with c = k₀ + (sq−1)/2 ∈ [0, n), of multiplicity μ(c);
- the δ-zero at v = (2k₀−n)/(2q), present when q | n − 2k₀. It sits on the pole −n/2, whose net order becomes 3;
- the bad pairs: a pole v_k = −j with d_k ≠ 0, and an evaluation point v_e = v_k + sgn(d_k)σ/2 with σ odd and
  σq < 2|d_k|. Equivalently, v_e is a half-integer strictly between v_k and v_c := (2k₀−n)/(2q).

**Lemma 4.1 (outside factor). PROVED.** Û_ξ(ξ̂+qv) = Σ_{m≥0}F_mq^mv^m with F_m ∈ ℤ_q and F₀ ∈ ℤ_q^×. The series
converges for |v|_q ≤ 1 and equals the rational function there.

*Proof.* For w ∉ D_ξ, u_w := ξ̂ − w is a q-unit, because q ∤ 2(w−ξ̂). Then
(ξ̂−w+qv)^{e} = u_w^{e}Σ_r C(e,r)(qv/u_w)^r, with C(e,r) ∈ ℤ for every e ∈ ℤ. A finite product of such series has the
stated form. Û_ξ has no pole on |v|_q ≤ 1. ∎

**Lemma 4.2 (sizes; q-integrality). PROVED.** Every local point (pole, zero, δ-point, evaluation point) lies in
[−x−½, ½]. Every rational number built below from a local model has a denominator composed of 2, of integers
2|v−v′| ≤ 2x+2, and of odd σ < 2x. This covers:
- the Taylor and Laurent coefficients of RR_ξ, of (v_e−v)^{−5} and of ∏(1−v_wy)^{e_w};
- polynomial combinations of these;
- the kernel constants c of Theorem 4.6.

Hence all these rationals are q-integral once q > 2x+2, and in particular once q² > 2n + 3q.

*Proof.*
- Poles: v = −j ∈ [−x, 0].
- Zeros: c ≥ 0 and k₀ ≤ q−1 force s ≥ −1, and c < n forces s < 2x + 1/q.
- Evaluation points lie between a pole and v_c ≤ ½.

Expanding RR(v)(v_e−v)^{−5} around v_k only divides by the differences v_k − v_w and v_e − v_k. ∎

(The track's text says [−x−½, 1]. The verifier's sharper [−x−½, ½] gives the same bound 2x+2.)

### 4.3 The class lemma

For a class ξ put (s is the local variable and y := 1/s):

  A_ξ(s) := Σ_{bad pairs (k,e) of ξ} sgn(d_k)·PP_{v_k}[RR_ξ(v)(v_e−v)^{−5}](s)   (PP = principal part at v_k),
  r_ξ(y) := ∏_{w∈D_ξ}(1−v_wy)^{e_w} = y^{E_ξ}RR_ξ(1/y) ∈ ℚ[[y]],   r_ξ(0) = 1.

For a **kernel polynomial** κ(y) = c₀ + Σ_{j≥1}c_jy^j ∈ ℚ[y], put K(v) := κ(1/v) = c₀ + Σ_jc_jv^{−j} and

  D_{ξ,κ}(y) := y^{E_ξ}A_ξ(1/y) − r_ξ(y)κ(y).

**Lemma 4.3 (class lemma). PROVED.** Let q ≥ 5, q > 2x+2, and let the c_j be q-integral. Then

  β_ξ − 24q^{−5}∮_{D_ξ}R_n(t)·K((t−ξ̂)/q)dt = 24q^{E_ξ−4}·Σ_{m≥0}F_mq^m·[y^{m+E_ξ+1}]D_{ξ,κ}(y).      (4.1)

Consequently v_q(LHS) ≥ Lev_κ(ξ) := −5 + min{p ≥ E_ξ+1 : [y^p]D_{ξ,κ} ≠ 0} (= +∞ if there is none). Always
Lev_κ(ξ) ≥ E_ξ − 4.

*Proof.*
(i) **The bad part.** By (3.2), a bad pair has X(k,h) = 24·Res_{t=−k}R_n(t)(t_e−t)^{−5}. Substitute t = ξ̂+qv, so that
dt = q·dv and t_e − t = q(v_e−v). This gives
X = 24q^{E−4}·Res_{v=v_k}[Û(ξ̂+qv)RR(v)(v_e−v)^{−5}].
- Insert Lemma 4.1. The re-expansion at v_k converges in ℚ_q because |v_k|_q ≤ 1.
- The residue at v_k only sees the principal part P_{k,e} of RR(v)(v_e−v)^{−5}.
- P_{k,e} is rational, has its only pole at v_k, and vanishes at ∞. Hence
  Res_{v_k}[v^mP_{k,e}] = −Res_∞[v^mP_{k,e}] = [y^{m+1}]P_{k,e}(1/y).

Summing with signs: β_ξ = 24q^{E−4}Σ_mF_mq^m[y^{m+1}]A_ξ(1/y) = 24q^{E−4}Σ_mF_mq^m[y^{m+E+1}](y^EA_ξ(1/y)).

(ii) **The subtracted part.**
- The poles of R_n(t)K(v) in D_ξ are the local poles, plus v = 0 if some c_j ≠ 0. These are all the finite poles of
  the rational function v^mRR(v)K(v).
- Hence ∮_{D_ξ}R_nK dt = q^{E+1}Σ_mF_mq^m·(sum of the finite residues of v^mRRK) = q^{E+1}Σ_mF_mq^m·[v^{−1}]_∞(v^mRRK).
- Since v^mRR(v)K(v) = Σ_p[y^p](r_ξκ)·v^{m+E−p}, this coefficient is [y^{m+E+1}](r_ξκ).

Multiply by 24q^{−5} and subtract. All coefficients are q-integral (Lemma 4.2, F_m ∈ ℤ_q), and the m-th term has
valuation ≥ E − 4 + m. ∎

Three kernels are used:
- **κ = 0** gives L_a-levels Lev₀(ξ). A class with no bad pairs has β_ξ = 0.
- **κ = 1** gives Lev₁(ξ).
- **κ = 1 + c·y^j** (j ≥ 0) gives Lev_κ(ξ).

Implementation: the levels are computed in exact rationals with series truncation M = 12. The coefficients are exact
below the truncation index, and if no nonzero coefficient is found there, the truncation index is used. That is
still a lower bound.

### 4.4 The kernel identity, the far part, and the collective bound

**Lemma 4.4 (kernel identity). PROVED.** Let Ψ(t) := c₀ + Σ_{j=1}^{J}c_jq^jΣ_{i=0}^{q−1}(t+i)^{−j}. Then
Σ_ξ∮_{D_ξ}R_nΨ dt = 0.

*Proof.* R_nΨ is rational, and its finite poles are integers, each lying in exactly one disc. So the left side is the
sum of all finite residues. It equals −Res_∞(R_nΨ) = 0, because deg(R_nΨ) ≤ deg R_n = −3 ≤ −2. ∎

On D_ξ, the summand i = k₀ is c_jq^j(t−ξ̂)^{−j} = c_jv^{−j}. Hence Ψ = K(v) + Σ_{j≥1}c_jq^jg_{j,ξ}(t), with
g_{j,ξ}(t) := Σ_{i≠k₀}(t+i)^{−j}. Each g_{j,ξ} is analytic on D_ξ, since 0 < |i−k₀| < q.

**Lemma 4.5 (far part). PROVED.** Suppose q > 2x+2, c_j is q-integral, and q ≥ j + 1 − E_ξ (j ≥ 1). Then
v_q(24q^{−5}·c_jq^j∮_{D_ξ}R_ng_{j,ξ}dt) ≥ j − 4.

*Proof.*
- **Expansion.** g_{j,ξ}(ξ̂+qv) = Σ_{r≥0}C(−j,r)q^rv^rP_{j+r}, where P_s := Σ_{i≠k₀}(i−k₀)^{−s}.
- **Power sums.** The numbers i − k₀ (i ≠ k₀) form a complete system of nonzero residues mod q. So P_s ≡ 0 (mod q)
  unless (q−1) | s (P4).
- **Product.** Write Û·g = Σ_mH_mq^mv^m.
  - For m ≤ q−2−j, every P_{j+r} with r ≤ m vanishes mod q, so q | H_m.
  - For larger m, v(H_mq^m) ≥ m ≥ q−1−j.
- **Residues.** As in (ii) of Lemma 4.3, ∮_{D_ξ}R_ng = q^{E+1}Σ_mH_mq^m[y^{m+E+1}]r_ξ, and only m ≥ max(0, −E−1)
  contribute. Each term has valuation ≥ E+1+m+1 ≥ 1 (first range) or ≥ E+1+q−1−j ≥ 1 (second range, by the
  hypothesis on q).
- **Conclusion.** Multiply by 24q^{j−5}c_j. ∎

**Theorem 4.6 (collective bound for the bad part). PROVED.** Let q ≥ 29 with q > 2x+2, and let 𝒯 be the set of local
types realised by the q classes. Then

  v_q(B) ≥ 𝔅_q := max(L_a, L_b, L_κ),   L_a := min_{ξ exposed}Lev₀(ξ),   L_b := min_{ξ}Lev₁(ξ).

Here L_κ is defined as follows:
- Put P₀ := L_b and j := P₀ + 5.
- If j ≥ 0, and every type with E+1 ≤ j has the same coefficient c := [y^j]D_{ξ,1} ≠ 0, set κ := 1 + c·y^j and
  L_κ := min(min_ξLev_κ(ξ), P₀+1).
- Otherwise set L_κ := P₀.

*Proof.* By Lemma 4.4, B = Σ_ξ[β_ξ − 24q^{−5}∮_{D_ξ}R_nΨ] for each admissible Ψ:
- Ψ = 0 gives the plain bound L_a;
- Ψ = 1 gives L_b;
- the κ-kernel gives L_κ. For j = 0 it is Ψ = 1 + c, with no far part. For j ≥ 1 it is c₀ = 1, c_j = c.

Each bracket is (4.1), plus, for j ≥ 1, the far part of Lemma 4.5, which costs j − 4 = P₀ + 1.
- For every type with E+1 ≤ j: [y^p]D_{ξ,κ} = [y^p]D_{ξ,1} = 0 for E+1 ≤ p < j, and [y^j]D_{ξ,κ} = c − c = 0. So
  Lev_κ ≥ P₀ + 1.
- Types with E+1 > j have Lev_κ ≥ −5 + E + 1 ≥ P₀ + 1 whatever κ is.
- Lemma 4.5 applies with q ≥ j + 1 − E_ξ, because E_ξ ≥ −10 (Lemma 4.8) and j ≤ 4 (the step only matters when
  P₀ < 0).

**Only j ≥ 0 is admissible.** For j < 0 the "kernel" is a polynomial, deg(R_nΨ) may be ≥ −1, and Lemmas 4.4–4.5
fail. This was the bug of the killed attempt, which gave bounds below the truth at 19 primes. It is fixed, and the
verifier re-derived the fix. ∎

### 4.5 Good part and c₃

**Lemma 4.7 (per-pole bounds). PROVED.** Let q > 2x+2 and q ≥ 11. Let −k be a pole in the class ξ with net local
order a (so a = a_k, or 3 at −n/2), and write τ_k(w) := w^aRR_ξ(v_k+w) = Σ_lτ_lw^l (τ₀ ≠ 0). Put
ℓ_k(i) := max{l ≤ a−i : τ_l ≠ 0}. Then v_q(r_{i,k}) ≥ E_ξ + a − ℓ_k(i).

Hence v_q(G) ≥ 𝔊_q := min over the realised types, poles and i ≤ a of (E + a − ℓ(i)), and v_q(c₃) ≥ ℭ_q := min over
the poles with a ≥ 3 of (E + a − ℓ(3)).

*Proof.* Expand around the centre t_k = −k as in Lemma 4.1: R_n(t_k+qw) = q^E·Û(t_k+qw)·w^{−a}τ_k(w), with
Û(t_k+qw) = Σ_mF′_mq^mw^m and F′_m ∈ ℤ_q. So r_{i,k} = q^{E+i}Σ_{l+m=a−i}F′_mq^mτ_l, and every term has valuation
≥ E + a − l. For a good pair, h is a q-unit and (i)₄ ∈ {24, 120, 360, 840} is a q-unit. ∎

### 4.6 Theorem K

**Theorem K (per prime). PROVED.** Let q ≥ 29 be prime with q² > 2n + 3q. Then

  e_q(n) ≤ f_n(q) := max(0, −min(𝔅_q, 𝔊_q), −ℭ_q).

*Proof.* q² > 2n + 3q gives q > 2x + 3, so Lemmas 4.2–4.7 apply. Then ρ_n = G + B with v_q(B) ≥ 𝔅_q and
v_q(G) ≥ 𝔊_q, and v_q(c₃) ≥ ℭ_q. ∎

f_n(q) is a finite exact computation on the local models (`disc_bound.py`; independently the verifier's
`vlevels.py`, which formulates it through residue moments).

### 4.7 The other primes

**Theorem C (primes above n). PROVED.** If q > n is an odd prime, then v_q(ρ_n) ≥ 0 and v_q(c₃) ≥ 0, so q ∤ D_n.

*Proof.*
- Pole differences satisfy |k′−k| ≤ n < q. The factor n − 2k is a unit, or 0 at k = n/2 (G = 2εH there). The values
  h ∈ H_k satisfy |2h| ≤ n − 1 < q. So all of these are q-units.
- Numerator values 2(c−k)+1 may be divisible by q. They enter G_k(ε) = G_k(0)∏(1+ε/β)^{e_β} with e_β ≥ 0, and
  G_k(0) contains β^{e_β}. So G_k(0)·C(e_β, j_β)β^{−j_β} is q-integral for j_β ≤ e_β, and vanishes for j_β > e_β
  (Lemma D2).
- Hence every r_{i,k} ∈ ℤ_(q), every X(k,h) ∈ ℤ_(q) (h is a unit), and c₃ ∈ ℤ_(q). ∎

(Certified numerically too: no prime in (n, 2n+2] divides D_n at any n tested, up to n = 40000.)

**Lemma 4.8 (crude level bounds and exposure). PROVED.** For every n, every prime q ≥ 5 and every class:
1. **E_ξ ≥ −10.** So if q ≥ 29 and q² > 2n + 3q, then e_q(n) ≤ 14.
2. **Exposure.** If x > 3, every class is exposed, and e_q(n) ≤ max(0, 4 − E_min(n,q)), where E_min(n,q) is the
   minimum of E_ξ over the q classes.

*Proof.* (1) Block m contributes at least ⌊L_m/q⌋ > L_m/q − 1 zeros to the class, because its values 2(c−k₀)+1 are
L_m consecutive odd numbers. Pole level ℓ contributes fewer than |I_ℓ|/q + 1 poles, where I_ℓ := {k : a_k ≥ ℓ}.
Since ΣL_m = N and Σ_ℓ|I_ℓ| = N + 4, this gives E > −10 − 4/q, so E ≥ −10. Then Theorem K gives:
- L_a ≥ E − 4 ≥ −14;
- 𝔊 ≥ E + 1;
- ℭ ≥ E + 3.

(2) The pole k = k₀ ≤ q−1 of the class has |d_{k₀}|/q ≥ x/2 − 1 + 1/q > ½, so σ = 1 gives a bad pair. The bound
then follows from L_a ≥ E_min − 4. ∎

**Lemma 4.9 (small primes). PROVED.** For every prime q ≥ 5 and every n, e_q(n) ≤ 18·⌊log_q(2n+1)⌋. Also
e₃(n) ≤ 19·⌊log₃(2n+1)⌋.

*Proof.* Put λ₁ := ⌊log_q(2n+1)⌋.
- **Taylor factors.** G_k(ε) = G_k(0)∏_β(1+ε/β)^{e_β}, where β ∈ ½ℤ∖0 and |2β| ≤ 2n+1. So v_q(β) ≤ λ₁, and Lemma D2
  gives v_q([ε^λ]∏) ≥ −λλ₁.
- **Terms.** For h ∈ H_k we have |2h| < n. X(k,h) = 24[ε^{a−1}]G_k(ε)(h−ε)^{−5}, and [ε^r](h−ε)^{−5} = C(r+4,4)h^{−5−r}.
  So v_q(X(k,h)) ≥ s_k − 8λ₁ and v_q(r_{3,k}) ≥ s_k − λ₁, where s_k := v_q(G_k(0)).
- **The constant term.** v_q(G_k(0)) is at least the numerator count minus the denominator count:
  - numerator: the L_m values of block m are consecutive odd numbers, so their q-part is ≥ Σ_e⌊L_m/q^e⌋;
  - denominator: for each level ℓ, with I_ℓ ∩ ℤ = [α, β], the product ∏_{k′∈[α,β], k′≠k}|k′−k| is either
    (β−α)!/C(β−α, k−α) or |I_ℓ|!·C(β−k, |I_ℓ|) (or the mirror). Its q-part is ≤ v_q(|I_ℓ|!) + ⌊log_q n⌋ (Kummer).
- **Summation.** So s_k ≥ Σ_{e≥1}[Σ_m⌊L_m/q^e⌋ − Σ_ℓ⌊|I_ℓ|/q^e⌋] − 4⌊log_q n⌋.
  - Each bracket is an integer > −6 − 4/q^e, so it is ≥ −6 (≥ −7 if q = 3).
  - The bracket vanishes once q^e > n + 1.
  - Hence s_k ≥ −10λ₁ (−11λ₁ if q = 3). ∎

Consequently Σ_{q ≤ Q}e_q(n)·log q ≤ 19·π(Q)·log(2n+1) = O(√n) for Q := max(40, √(3n)). (Numerically the worst
ratio e_q/(18λ₁) at n = 2000 and 8000 is 0.39.)

### 4.8 The continuum function f

**Dictionary.** With y := k₀/q ∈ [0,1) the local model of a class is a function of (x, y):
- **Poles.** The pole j exists iff y + j ≤ x. Its order is a(κ) with κ = (y+j)/x, by the cell rule.
- **Zeros.** The zero at v = −s/2 has multiplicity #{m : η_mx < y + s/2 < (1−η_m)x}. The discrete endpoints are never
  hit: 2k₀ + sq is odd while 2η_mn is even.
- **Bad pairs.** d_k/q = y + j − x/2, and (k, σ) is a bad pair iff σ < 2|y+j−x/2|. Equality never occurs, because
  |2k−n| is even and σq is odd.
- **Centre class.** It is the class y ≡ x/2 (mod 1). There the δ-zero sits on the pole at v = −⌊x/2⌋.

**Events.** As y runs over [0,1) with x fixed, the local model changes only when y crosses a point ≡ γx + e (mod 1),
with γ ∈ {b/40 : 0 ≤ b ≤ 40} and e ∈ ½ℤ, or crosses y ≡ 0. The sources of events are:
- pole existence (γ = 1);
- the cells b/40;
- the block ends η_m and 1−η_m;
- exposure and the centre (γ = ½).

The **candidate set** is 𝒞 := ⋃_{d=1}^{40}(20/d)ℤ.

**Lemma 4.10 (piecewise constancy). PROVED.**
- Two events γx+e and γ′x+e′ coincide mod 1 only if (γ−γ′)x ∈ ½ℤ, i.e. x ∈ (20/d)ℤ with d = 40|γ−γ′|.
- An event meets y ≡ 0 only if γx ∈ ½ℤ.
- Hence, on each open interval of ℝ∖𝒞, the cyclic order of the events is constant.

Let 𝒯(x) be the set of continuum types: the local model in each y-gap, together with the centre type. 𝒯(x) and the
continuum bound

  f(x) := max(0, −min(𝔅(𝒯(x)), 𝔊(𝒯(x))), −ℭ(𝒯(x)))

are constant on each such interval. ∎

**Lemma 4.11 (discrete ⊆ continuum). PROVED.** Let q > 40 be prime with q ∤ n/40. Then x = n/q ∉ 𝒞, every local type
realised by the q classes at (n, q) lies in 𝒯(x), and f_n(q) ≤ f(x). Every prime q > n/40 satisfies q ∤ n/40.

*Proof.*
(i) x = 20m′/d with d ≤ 40 means 2(n/40)d = m′q. Since q > 40 ≥ d and q is odd, q | n/40.
(ii) By the parity remarks in the dictionary, a discrete class never sits on a zero event or an exposure event.
- A class on a pole-existence event or a cell event takes that event's one-sided state.
- Since x ∉ 𝒞, no other event is at the same place, so the type is that of an adjacent gap.
- The class k₀ ≡ n/2 is the centre type.
(iii) **Monotonicity.** Over fewer types L_a, L_b, 𝔊 and ℭ can only increase. For L_κ there are two cases:
- The discrete P₀ equals the continuum P₀. Some discrete type attains P₀, so the discrete step is admissible with the
  same (j, c), and its levels are among the continuum ones.
- The discrete P₀ is larger. Then 𝔅(discrete) ≥ P₀(discrete) ≥ P₀ + 1 ≥ L_κ(continuum). ∎

**Lemma 4.12 (periodicity). PROVED.** E(x+40, y) = E(x, y) for all (x, y), and 𝒞 + 40 = 𝒞. Hence the residue level
f⁰(x) := max(0, 4 − min_{𝒯(x)}E) is 40-periodic. Also f(x) ≤ f⁰(x) for x > 3 (Lemma 4.8(2)).

*Proof.* Let I_ℓ^c := {κ ∈ [0,1] : a(κ) ≥ ℓ}. These are the intervals [0,1], [1/20, 19/20], [1/10, 9/10] and
[3/20, 17/20], of total length 3.4. Write

  E = Σ_m#{s odd : y + s/2 ∈ (η_mx, (1−η_m)x)} − Σ_{ℓ=1}^{4}#{j ≥ 0 : y + j ∈ x·I_ℓ^c} + δ.

Under x ↦ x+40:
- every endpoint 40η_m, 40(1−η_m) and 40·∂I_ℓ^c is an integer, so each count grows by exactly 40(1−2η_m) or
  40|I_ℓ^c|;
- Σ_m(1−2η_m) = 3.4 = Σ_ℓ|I_ℓ^c|, so these changes cancel;
- the δ-point y ≡ x/2 moves by 20. ∎

### 4.9 Theorem A and the numbers

**Theorem A. PROVED (computer-assisted for the value of E\*).** As n → ∞ through 40ℤ,

  (1/n)·log D_n ≤ E* + o(1),   E* := ∫_1^{60}f(x)dx/x² + ∫_{60}^{∞}f⁰(x)dx/x² = 3.880843104676… .

*Proof.* Split the odd primes q ≤ n into five ranges.
1. **q > n.** By Theorem C, q ∤ D_n.
2. **n/60 < q ≤ n, q ∤ n/40.**
   - For n ≥ n₀ we have q > 40 and q² > 2n + 3q, so e_q ≤ f(n/q) by Theorem K and Lemma 4.11.
   - f is constant on the finitely many candidate intervals [a_i, b_i] of [1, 60]. By the PNT,
     Σ f(n/q)log q = Σ_if_i(θ(n/a_i) − θ(n/b_i)) = n∫_1^{60}f dx/x² + o(n).
3. **√(3n) < q ≤ n/60, q ∤ n/40.**
   - Here q² > 3n ≥ 2n + 3q, so e_q ≤ f⁰(n/q) by Lemma 4.8(2), with Lemma 4.11 for the types.
   - f⁰ ≤ 14 is piecewise constant and 40-periodic. For any X₂ > 60, the PNT on [60, X₂] and Chebyshev for q ≤ n/X₂
     give n∫_{60}^{∞}f⁰dx/x² + 14.3n/X₂ + o(n).
4. **q | n/40, q > √(3n).** There are at most log₂n such primes, each with e_q ≤ 14 (Lemma 4.8(1)), so they
   contribute O(log²n).
5. **q ≤ max(40, √(3n)).** O(√n), by Lemma 4.9.

Let X₂ → ∞. ∎

| piece | value | how computed |
|---|---|---|
| ∫_1^{4}f dx/x² | 51/20 = 2.55 | exact, 77 intervals (`head_1_4_fixed.json`) |
| ∫_4^{20}f dx/x² | 2989163/2882880 = 1.0368669525 | exact, 392 intervals |
| ∫_{20}^{60}f dx/x² | 5263504492683945763/27401381122591476000 = 0.1920890217 | exact, 980 intervals |
| ∫_{60}^{∞}f⁰dx/x² | 0.101887130498 | one period (980 intervals, exact f⁰), Σ_if⁰_i(ψ(b_i/40) − ψ(a_i/40))/40 by (P9) |
| **E\*** | **3.880843104676** | recomputed exactly by the verifier and re-summed by the assembler |

Remarks on the numbers:
- **Tail by periodicity.** f⁰ has mean 6.0753 and maximum 10 over one period.
- **The tail value is not delicate.** Using only max f⁰ = 10 beyond 60 gives E ≤ 3.9456 (margin −0.061).
- **Values of f.** On [1, 3.2), f equals the empirical exponent step function of notes §5.1: 0, 1, 2, 3, 4, 5, 4, 2,
  3, 4, 5, with breaks at 20/19, 10/9, 20/17, 5/4, 4/3, 20/13, 2, 20/9, 40/17, 20/7. Its integral there is 181/80.
- **Where the kernel step is used.** The kernel step with j ≥ 1 (Lemma 4.5) is used only on [2, 20/9), with j = 2 and
  c = −5/4. 𝔊 and ℭ are never binding on [1, 60].

**Where the saving comes from** (asymptotic E, same tail):

| ingredient | residue level 4 − E | + class lemma (L_a) | + κ = 1 identity (L_b) | + one-step kernel (L_κ) = f |
|---|---|---|---|---|
| E | 5.0818 | 4.3593 | 3.9843 | **3.8808** |

### 4.10 Evidence and a second proof (NUMERICAL, apart from the second proof)

- **Theorem K against the TRUE exponents.** These are exact odd denominators from independent engines.
  - Theory track: 1431 primes at n = 480, …, 20000.
  - Its verifier: 11665 pairs (n, q) at 22 values of n up to 200000, including every prime at n = 20000.
  - Result: 0 violations; the bound equals the truth at 11560 pairs.
  - Of the 1449 head intervals, the truth attains f on 775, which carry 97.3% of ∫_1^{60}f dx/x². So E* is
    essentially sharp for this method.
- **The class lemma as an identity.** 19,827 class tests (24 primes, n = 480 and 2000): the valuation equals the level
  every time, and the leading digit mod q equals 24·F_{m₀}·M_{m₀}.
- **Discrete versus continuum.** Discrete types are always among the continuum types, and the continuum f equals the
  discrete bound at every tested prime not dividing n/40.
  - An independent event set, sampled at 150 random x and 2000 random y, finds no missing type.
  - The class lemma also predicts the exact leading term of ρ_n mod ℓ for ℓ ∈ (0.9n, 0.95n). This was confirmed at
    22 + 48 primes (remark 10.6 of the theory track).
- **Second, independent proof** (denominators-search track, confirmed by its verifier with 19,063 prime-by-prime
  comparisons over several configurations, 0 violations).
  - Same class expansion. The kernel subtractions c₀∮R + Σ_jc_j∮Rq^jΣ(t+i)^{−j} are chosen by exact Gaussian
    elimination for the largest feasible level T.
  - The first-order bound is used beyond x = 40.
  - Result: E_prov(cand3) = 3.8801844, margin −0.1265142.
  - The two implementations agree interval by interval where the methods coincide (∫_1^4 f = 51/20, and the same
    values on [20, 40]).

---------------------------------------------------------------------------------------------------

## 5. Theorem G (archimedean growth)

Source: the growth-nonvanishing track, §2, confirmed by its verifier (verify-growth-nonvanishing).

**Potential.** Let a(z) be the continuum profile: (1,1,2,2,3,3,4,…,4,3,3,2,2,1,1)[⌊40z⌋] on [0,1]. Put

  U(κ) := Σ_m∫_{η_m}^{1−η_m}log|z−κ|dz − ∫_0^1a(z)log|z−κ|dz   (κ ∈ [0,1]).

With F(x) := x log|x| − x, U(κ) = Σ_jw_jF(p_j−κ) is a finite sum: 18 terms, integer weights w_j, breakpoints
p_j ∈ (1/40)ℤ ∩ [0,1].

**Lemma G1 (Cauchy). PROVED.** |r_{i,k}| ≤ 2^{−i}M_k, where M_k := max_{|ε|=½}|R_n(−k+ε)|.

*Proof.* G_k is holomorphic on |ε| < 1. Cauchy's estimate on |ε| = ½ gives |[ε^λ]G_k| ≤ 2^{λ−a_k}M_k. Take
λ = a_k − i. ∎

**Lemma G2 (triangle inequality). PROVED.**

  log M_k ≤ log(|n−2k|+1) + a_k log 2 + Σ_mΣ_{c∈C_m}log(|c−k+½|+½) − Σ_{k′≠k}a_{k′}log(|k′−k|−½).

**Lemma G3 (sums versus integrals). PROVED.** Let f(y) := log|y−k| and C₃ := 2(1−log 2) + π²/72 + 2 = 2.750783.
1. For an integer interval [lo, hi] of length L:
   Σ_{c=lo}^{hi}log(|c−k+½|+½) ≤ ∫_{lo}^{hi+1}f + C₃ + log(2L).
2. Σ_{k′≠k}a_{k′}log(|k′−k|−½) ≥ ∫_{−1/2}^{n+1/2}ã_n f − 8(1 + log n), where ã_n := a_{k′} on [k′−½, k′+½).

*Proof.* (1) Split log(|u|+½) = log|u| + log(1+1/(2|u|)).
- The second part is ≤ Σ1/|2(c−k)+1| ≤ 2 + log(2L).
- For the first part use the midpoint rule on the cells [c, c+1]:
  - each of the two cells adjacent to k contributes 1 − log 2;
  - a cell at distance d ≥ 1 contributes at most 1/(24d²), since |f″| ≤ 1/d².

(2) Use log(d−½) ≥ log d − 1/d, together with Σa_{k′}/|k′−k| ≤ 8H_n. On each cell not containing k, f is concave
(midpoint ≥ mean). The omitted cell of k contributes −a_k(1+log 2) ≤ 0 to the full integral. ∎

**Lemma G4 (scaling) and G5 (discretisation). PROVED.**
- Substituting y = nz gives ∫_{α n}^{β n}f = (β−α)n log n + n∫_α^β log|z−k/n|dz, and similarly for ã_n.
- The discrete profile ã_n(nz) differs from a(z) only on P = 8 intervals, each of length ≤ 1/(2n), and there by
  Δ = 1. These are the 6 interior jumps and the 2 end half-cells.
- So n·|∫(ã_n(nz) − a(z))log|z−κ|dz| ≤ 4(1 + 1/(2n) + log 4n).
- P = 8, Δ = 1 and the maximal exceptional length 1/(2n) were computed exactly by the verifier.

**Proposition G6. PROVED.** For all 0 ≤ k ≤ n,

  log M_k ≤ n·U(k/n) + E(n),   E(n) = log(n+1) + 14 log n + 37.386 + 2/n ≤ log(n+1) + 14 log n + 37.44   (n ≥ 40).

The two log n terms combine to (N − Σa_k)log n = −4 log n. Σ_mlog(2−4η_m) = 0.5635.

**Lemma G7 (certified maximum). PROVED (computer-assisted).**

  0.7067022241 ≤ max_{[0,1]}U ≤ U* := 0.70670223,

with maximum at κ* = 0.1067347196… and 1 − κ*.

*Certification* (`umax_cert.py`).
- Each F(p_j−κ) is monotone in κ on [−1, 1]. The script combines a monotone box bound, a centred first-order bound on
  boxes without breakpoints, and bisection from the 1/40 grid.
- 152 boxes, in two arithmetics: mpmath.iv with outward rounding at 120 bits, and exact rationals with the script's
  own atanh-series log enclosures and explicit remainders.
- The negative control 0.70670222 fails.
- The verifier certified it a third time (`vumax.py`), by a different method: convex terms bounded by chords, concave
  terms by tangents, exact rationals and correctly rounded decimal logs, 109 boxes. The verifier found
  max U = 0.7067022242140760.

**Theorem G. PROVED (computer-assisted through G7).** For every n ∈ 40ℤ_{>0},

  log max(|ρ_n|, |Z_n|) ≤ U*·n + 14 log n + 2 log(n+1) + 47.5.

*Proof.*
- **ρ_n.** By (3.1) and G1,
  |ρ_n| ≤ Σ_{k,i}(i)₄2^{−i}M_k·Σ_{h∈H_k}|h|^{−i−4} ≤ 16Σ_{i=1}^{4}(i)₄(1−2^{−i−4})ζ(i+4)·Σ_kM_k ≤ 21514(n+1)max_kM_k.
  The middle step uses Σ_{h}|h|^{−s} ≤ 2^s(1−2^{−s})ζ(s) for distinct half-integers of one sign.
- **Z_n.** |Z_n| = 46080|Σ_kr_{3,k}| ≤ 5760(n+1)max_kM_k.
- **Conclusion.** By G6 and G7, and since log 21600 + 37.44 ≤ 47.5, the bound follows. ∎

**Remarks (NUMERICAL, not used).**
- The true growth of cand3 is g ≈ 0.684 < U*. The maximal residues sit in an order-3 stretch where the residue signs
  alternate, and they cancel. Measured: raw/n = 0.6837 at n = 96000; fitted limit 0.6839 ± 0.0002.
- A contour or saddle-point argument could lower U* by about 0.023. It is not needed.
- Checked by the verifier: the per-n form of the bound is 0.7593, 0.7338 and 0.7201 at n = 480, 960 and 2000, and the
  chain of G1–G6 holds at every pole for n = 40, …, 2000.

---------------------------------------------------------------------------------------------------

## 6. Theorem V (2-adic size)

Source: the growth-nonvanishing track, §3. It is the pair's Theorem G4 with the factorisation lemma adapted, and it
was confirmed by the verifier, including 3240 random configurations checked against a direct Mahler-series
evaluation.

### 6.1 Statement

**Theorem V. PROVED.** Let n ≥ 1, j ≥ 0, δ ∈ {0,1} and m ∈ ℤ. Take integer intervals [lo_ν, hi_ν] of lengths
L_ν ≥ 0 (ν = 1, …, B), and integers a_k ≥ 0 (0 ≤ k ≤ n). Put

  R(t) := (2t+n)^δ∏_ν∏_{c=lo_ν}^{hi_ν}(t+½+c)/∏_k(t+k)^{a_k},   S := ∫_{ℤ₂}R^{(j)}(t+½−m)dt,

with N := ΣL_ν, σ := Σ_νs₂(L_ν) and λ := ⌊log₂ max(1, L_ν)⌋ + 1. Then

  v₂(S) ≥ N + Σ_ka_k + j − σ − (j+1)λ.

**For cand3** (B = 6, j = 3, m = n/2, max L_ν = 3n/4):

  v₂(S_n) ≥ 6.8n + 7 − σ_n − 4λ_n ≥ 6.8n + 7 − 10λ_n,   λ_n = ⌊log₂(3n/4)⌋ + 1.        (6.1)

### 6.2 Tools

For f: ℤ₂ → ℚ₂ put Δ₀(f) := inf_{k≥1}v₂((f(k)−f(k₋))/(k−k₋)) and Δ(f) := min(1 + v₂f(0), Δ₀(f)).
- **(D1)** f ∈ S¹ ⇒ v₂(∫f) ≥ Δ(f) − 1. *Proof:* 2^{−M}Σ_{k<2^M}f(k) = f(0) + Σ_{l<M}Σ_{k=2^l}^{2^{l+1}−1}(f(k)−f(k₋))/2^{l+1}.
- **(D2)** For ℤ₂-valued f and g, Δ(fg) ≥ min(Δf, Δg). *Proof:* the product rule for divided differences.
- **(D3)** A power series with ℤ₂ coefficients tending to 0 has Δ ≥ 0.
- **(D4)** For x ∈ ℤ, Δ(C(t+x, L)) ≥ −⌊log₂L⌋. *Proof:* Vandermonde:
  (f(k)−f(k₋))/(k−k₋) = Σ_{i=1}^{L}(1/i)C(k−k₋−1, i−1)C(k₋+x, L−i).
- **(D5)** (d/dt)^μC(t+x, L) = Σ_{r=μ}^{L}c_{μ,r}C(t+x, L−r), with c_{μ,r} = [z^r](log(1+z))^μ and
  v₂(c_{μ,r}) ≥ −μ⌊log₂r⌋.

### 6.3 Proof

**Lemma V1 (factorisation).** R(t+½−m) = 2^{Σa_k}·E(t)·∏_νL_ν!·C(t+x_ν, L_ν), where x_ν := hi_ν + 1 − m and
E(t) := (2t+1+n−2m)^δ∏_k(2t+2k+1−2m)^{−a_k}.

For cand3, x_ν = (½−η_ν)n ≥ 0. So the binomials are exactly those of the pair's `binom` lemma.

**Lemma V2.** E_β := E^{(β)}/(β!2^β) is ℤ₂-valued with Δ(E_β) ≥ 0. Every factor 2t + odd is a 2-adic unit on ℤ₂, so
(D3) and (D2) apply.

**Lemma V3 (terms).** By Leibniz and (D5), R^{(j)}(t+½−m) = ΣK(β,μ,r)Φ_{β,r}(t) with Φ_{β,r} = E_β∏_νC(t+x_ν, L_ν−r_ν).
- v₂(K) ≥ Σa_k + β + (N − σ) − (j−β)(λ−1), using Legendre v₂(L!) = L − s₂(L).
- Δ(Φ) ≥ −(λ−1).

Hence v₂(K∫Φ) ≥ N + Σa_k + j − σ − (j+1)λ + βλ, which proves the theorem. ∎

**Checks (NUMERICAL).** For cand3, bound versus true v₂(S_n):
- n = 480: 3214 vs 3237;
- n = 960: 6474 vs 6499;
- n = 2000: 13534 vs 13560.

The slack is 18–27 bits at all 18 values of n = 40, …, 2000. The verifier reproduced every value.

---------------------------------------------------------------------------------------------------

## 7. Theorem N (nonvanishing via ℓ = 19n/20 − 1)

Source: the growth-nonvanishing track, §4, confirmed by the verifier. The verifier checked it step by step on exact
data at all 10 n ∈ I with n ≤ 960, and ℓ-adically at all 334 n ∈ I with n ≤ 60000, plus samples up to about 2·10⁵.

**Theorem N. PROVED.** Let n ∈ 40ℤ_{>0} and suppose ℓ := 19n/20 − 1 is prime. Then

  v_ℓ(ρ_n) = −1,   v_ℓ(Z_n) ≥ 0,   and   ℓρ_n ≡ (6864/7)·r_{1,0}/ℓ⁴ (mod ℓ),

where u₀ := r_{1,0}/ℓ⁴ is an ℓ-unit.

The subsequence is I := {40m : 38m−1 prime} = {40, 120, 160, 240, 400, 600, 640, 720, 840, 960, …}. It is infinite by
(P6), and ℓ ≥ 37 on I.

*Proof.* Throughout, ℓ ≥ 37, 2n < 3ℓ and ℓ² > 2n.

**Size facts.**
- (S1) |k′−k| ≤ n < 2ℓ, so ℓ | k′−k iff k′−k = ±ℓ.
- (S2) The numerator values 2(c−k)+1 are odd with absolute value ≤ 2n−1 < 3ℓ. So ℓ divides one only if it equals ±ℓ,
  that is, c = k + (ℓ−1)/2 or c = k − (ℓ+1)/2, and then v_ℓ = 1.
- (S3) n − 2k is even and |n−2k| < 2ℓ, so ℓ ∤ n − 2k.
- (S4) For h ∈ H_k, |2h| ≤ n−1 < 2ℓ. So ℓ | 2h iff 2h = ±ℓ, which forces |k − n/2| ≥ 19n/40, i.e. k ≤ n/40 or
  k ≥ 39n/40.
- (S5) Every block contains the window [19n/40 − 1, 21n/40]. Also (i)₄ and 46080 are ℓ-units.

**N1 (local data).** Write s_k := v_ℓ(G_k(0)).
- (a) **End poles 0 ≤ k ≤ n/20 + 1.**
  - c = k + 19n/40 − 1 lies in the window, hence in all six blocks. The branch c = k − 19n/40 < 0 lies in none.
  - The pole partner k + ℓ has order 2 for k ∈ {0,1} and order 1 for k ≥ 2.
  - So s₀ = s₁ = 6 − 2 = 4, and s_k = 5 for 2 ≤ k ≤ n/20+1.
  - By Lemma D2, v_ℓ(r_{i,k}) ≥ s_k − (a_k − i) ≥ 3. The mirror poles obey the same bounds by symmetry.
- (b) **Middle poles n/20+1 < k < ℓ.** Only numerator factors (e ≥ 0) are ℓ-divisible, so Lemma D2 gives
  v_ℓ(r_{i,k}) ≥ 0.
- (c) **Consequence.** Every c_i is ℓ-integral, so v_ℓ(Z_n) ≥ 0.

**N2 (two terms).** ρ_n ≡ −2(X₀ + X₁) (mod ℤ_(ℓ)), where X_k := X(k, −ℓ/2) = 24r_{1,k}(−ℓ/2)^{−5} = −768r_{1,k}/ℓ⁵.
- Good terms (ℓ ∤ 2h) are ℓ-integral by N1.
- The terms with 2h = −ℓ need k ≤ n/40, where a_k = 1. They have valuation s_k − 5, which is −1 for k ∈ {0,1} and 0
  otherwise.
- Both terms occur, because h = −ℓ/2 ∈ H_k iff k ≤ n/40.
- Use the symmetric form of (3.1).

**N3 (ratio).**

  Θ(n) := r_{1,1}/r_{1,0} = ((n−2)/n)·∏_m(2η_mn−1)/(2(1−η_m)n−1)·(−1)·n(17n/20)(9n/10)(19n/20)/((n/20−1)(n/10−1)(3n/20−1)).

*Derivation.* r_{1,k} = G_k(0) = (n−2k)·Num(−k)/∏_{k′≠k}(k′−k)^{a_{k′}}.
- The numerator products telescope blockwise.
- The denominator ratio is (−1)^{a₀}n^{a_n}∏_jj^{a_j−a_{j+1}}. Its only jumps are at n/20−1, n/10−1, 3n/20−1 (−1) and
  at 17n/20, 9n/10, 19n/20 (+1).

**Reduction mod ℓ.** Since 19n/20 = ℓ + 1, we have n ≡ 20/19 (mod ℓ). Then:
- (n−2)/n ≡ −9/10;
- the block product ≡ 9/28;
- the pole factor ≡ 5/4;
- so Θ ≡ θ₀ = −81/224 and 1 + θ₀ = 143/224 = 11·13/(2⁵·7).

Every factor involves only the primes 2, 3, 5, 7, 11, 13, 17, 19 < 37 ≤ ℓ, so the reduction is legitimate.

**Conclusion.** ℓρ_n ≡ 1536(1 + θ₀)u₀ = (6864/7)u₀ ≢ 0 (mod ℓ), and 6864/7 = 2⁴·3·11·13/7 is an ℓ-unit. ∎

(Recomputed by the assembler's `constants.py`: θ₀ = −81/224 and 1536(1+θ₀) = 6864/7. The leading residues ℓρ_n mod ℓ at the
10 n ∈ I with n ≤ 960 are 24, 64, 54, 26, 101, 510, 271, 224, 704, 434, as predicted.)

---------------------------------------------------------------------------------------------------

## 8. Proof of the Main Theorem, and the total margin

Suppose ζ₂(7) = u/b with u ∈ ℤ and b ∈ ℤ_{≥1}. For n ∈ I:
- choose e_n ≥ 0 with A_n := 2^{e_n}D_nρ_n ∈ ℤ and B_n := 2^{e_n}D_nZ_n ∈ ℤ;
- put N_n := bA_n + uB_n ∈ ℤ. In ℚ₂, N_n = b·2^{e_n}D_n·S_n by Lemma L.

**Step 1 (N_n ≠ 0).** Take n ∈ I with ℓ := 19n/20 − 1 > b.
- By Theorem N, v_ℓ(bA_n) = v_ℓ(D_n) − 1, since ℓ ∤ 2b.
- Also v_ℓ(uB_n) ≥ v_ℓ(D_n), or uB_n = 0.
- So v_ℓ(N_n) = v_ℓ(D_n) − 1 < ∞, and N_n ≠ 0.

**Step 2 (Liouville).** A nonzero integer N satisfies 1 ≤ |N|·|N|₂. Here:
- |N_n| ≤ (b+|u|)·2^{e_n}D_n·max(|ρ_n|, |Z_n|);
- |N_n|₂ ≤ 2^{−e_n}·2^{−v₂(S_n)}, since D_n is odd.

Hence

  1 ≤ (b+|u|)·D_n·max(|ρ_n|,|Z_n|)·2^{−v₂(S_n)}   for all n ∈ I with ℓ(n) > b.        (8.1)

**Step 3 (the right side → 0).** By Theorem A (valid for all n ∈ 40ℤ, hence along I), Theorem G and (6.1), the
logarithm of the right side of (8.1) is at most

  log(b+|u|) + (E* + U* − 6.8 log 2)·n + o(n) = −0.1258555·n + o(n) → −∞.

This contradicts (8.1), because I is infinite (P6). Hence ζ₂(7) ∉ ℚ. ∎

**Remarks on the logic.**
- Step 1 is condition 2 of [LS, Lemma 2.2] with ℓ(n) = 19n/20 − 1. Steps 2–3 are [Lai, Lemma 2.1], written out.
- Only asymptotic forms are needed: E* + U* < 6.8 log 2. That is, G is needed only with growth < 0.8326 given E*,
  and A only with E < 4.0067 given U*.
- The o(1) of Theorem A is ineffective (PNT). The theorem is an irrationality statement only; no irrationality
  measure is claimed.
- The subsequence I requires only 40 | n and 38m − 1 prime. Theorems A, G and V hold for all n ∈ 40ℤ.

**Finite-n illustration (NUMERICAL; not part of the proof).** The table gives the criterion quantity
(1/n)·log(D_n·max(|ρ_n|,|Z_n|)·2^{−v₂(S_n)}); all entries are negative.

| n | 480 | 640 (∈ I) | 960 (∈ I) | 1440 (∈ I) | 2000 | 6000 |
|---|---|---|---|---|---|---|
| proved G (per-n form) + proved (6.1) + true D_n | −0.112 | −0.117 | −0.149 | −0.122 | −0.134 | — |
| true sizes, true D_n, true v₂ | −0.2296 | −0.2161 | −0.2226 | −0.1802 | −0.1829 | −0.1768 |
| true sizes and v₂, Theorem K exponents (search-track version) for q² > 2n+2, true small primes | −0.2296 | −0.2161 | −0.2184 | −0.1802 | −0.1806 | — |

Finite n is far from the asymptotic regime for the prime sums:
- the large-prime part of log D_n/n grows from about 3.3 (n = 480) to 3.70 (n = 6000), toward E* = 3.88;
- the small-prime part decays like n^{−1/2}, from 0.44 to 0.15.

---------------------------------------------------------------------------------------------------

## 9. Referee report (assembler)

### 9.1 What I checked myself

1. **Interfaces between the tracks.** All tracks use the same objects:
   - the same R_n, the same S_n (centred evaluation), and the same ρ_n (formula (3.1), in the forms Σ_kΣ_{t∈T_k}PP_k⁗
     and Σ_kΣ_{h∈H_k}X(k,h), which are identical with h = t+k);
   - the same Z_n = −46080c₃;
   - the same D_n (least odd D with Dρ_n, DZ_n ∈ ℤ[½]).

   The n-ranges are compatible: A, G and V hold for all n ∈ 40ℤ, and N holds on I ⊂ 40ℤ. The growth exponent of G
   is the constant used in the margin of A.
2. **Re-derivations.** I re-derived by hand:
   - the Volkenborn translation signs of (3.1);
   - the class lemma (both halves, including the q-adic re-expansion of Û at v_k);
   - the kernel identity, the far-part lemma, and the admissibility logic of the one-step kernel (j ≥ 0);
   - the per-pole bound;
   - Theorem C;
   - the crude bounds E ≥ −10 and exposure for x > 3;
   - the small-prime lemma, including the Kummer step;
   - the event and parity analysis behind Lemmas 4.10–4.11;
   - the prime split of Theorem A;
   - Theorem G's constants (21513.3, 5760, E(n));
   - (6.1) at n = 480 (σ = 21, λ = 9, bound 3214);
   - θ₀ = −81/224;
   - the Liouville step.
3. **Recomputations.** I recomputed every number of §0.2, §4.9 and §7 (`constants.py`):
   - The three head files were re-summed exactly. They give 51/20, 2989163/2882880 and
     5263504492683945763/27401381122591476000.
   - One period of f⁰ gives ∫_{20}^{60}f⁰ = 0.2074181758, which equals tail(20) − tail(60).
   - E* = 3.88084310467576, and the margin is −0.1258554931.
   - The truncated Lean variant gives E = 3.9240892, margin −0.0826.
   - The integral 181/80 of the step function of notes §5.1 on [1, 3.2) was recomputed by hand.

### 9.2 Points an external referee should examine (none is a known gap)

1. **The denominator theorem (§4) is the new mathematics.**
   - The class lemma is a clean residue identity.
   - The weight of the argument is in the continuum reduction (Lemmas 4.10–4.11) and in the exact computation of f on
     1449 intervals.
   - Both were done twice, independently, and agree exactly. The resulting per-prime bound was never below the true
     exponent in about 30,000 tests.
   - A Lean certificate (§10) would remove the remaining trust in Python.
2. **Computer-assisted steps rely on Python `fractions` and `mpmath.iv`.** The max-U certificate was re-done by three
   methods.
3. **Cited identification.** ζ₂(7) = J₆/768 is the Kubota–Leopoldt value by LSZ Lemma 2.8. The project's Lean
   repositories cite the same lemma.
4. **Corrections found by the verifiers.** None affects a theorem:
   - Local points lie in [−x−½, ½], not [−x−½, 1].
   - The residue-level row of the ingredient ladder is descriptive only.
   - Denominators-search: C(X₁) is not explicit (the theory track's q > 2x + 2 is explicit), and there is a typo
     v_q(β) → v_q(β−k).
   - Growth track: the wording "only exposed poles are k ∈ {0,1,n−1,n}" is loose, but the proof handles every pole.
     The EVOP7 remark is wrong; it concerns another configuration.
   - Notes §5: "residue-dominated" is false for cand3 (true growth 0.684). E∞ ≈ 3.87 ± 0.02, not 3.83. The true
     asymptotic margin is ≈ −0.16 (−0.14 with U*), not −0.18. The proved margin −0.126 is consistent with these
     corrected values: E* = 3.8808 exceeds the true E∞ ≈ 3.87 by about 0.01.
5. **Plausibility.**
   - The margin is 2.7% of the 2-adic gain, with −0.16 true.
   - Every finite-n margin computed with the true data is negative. All lie between −0.29 and −0.16, for every
     n = 40, …, 2000 (step 40) and at n = 2400, …, 6000.
   - At n = 6000 the exact data imply, through (8.1), that any representation ζ₂(7) = u/b would need
     log(b+|u|) > 0.1768·6000 ≈ 1060. The data used are S_6000 ≠ 0, the true D_n, the true sizes and v₂(S_n) = 40751.
     This is NUMERICAL, since it relies on J₆ to 84000 bits, and it is not part of the proof.
   - The holonomy (CDT) track found numerically that the Eisenstein X₀(2) template, used as it stands, does not reach
     ζ₂(7). The present route is a different mechanism: the centred evaluation removes the critical-zero constraint
     (research notes §3), pole-order ramps lower both growth and exponents, and the collective residue-class
     cancellation of §4 does the rest.

### 9.3 Optional improvements (not needed)

- **Configuration ga1a** (denominators-search) has provable margin −0.195. It still needs:
  (i) a certified max U = 0.822480 (umax_cert.py, minutes);
  (ii) a Theorem N* check (b₀ = n/40, b₁ = n/20, α = 1, α′ = 2, τ* = −1, β = −768, ℓ = 37n/40 − 1 with 80 | n).
  After these two checks it would be a second, more robust instance.
- **Pointwise minimum of the two denominator bounds.** Taking the minimum of the theory and search bounds gives
  E ≈ 3.874.
- **Growth.** A saddle-point growth bound would allow g ≈ 0.684.

---------------------------------------------------------------------------------------------------

## 10. Lean plan

Base: fork the Lean formalisation of the pair (https://github.com/gmDevi/zeta2-7-9-lean; namespace `Zeta2.Pair`, all
gaps closed, no `sorry`), with new code in a new namespace. Keep the trusted definitions verbatim, so that the
conclusion is literally about `J 6 / 768`. (The formalisation in this repository uses the namespace `Zeta2.Z7` and the
files `Zeta2Lean/Z7/*.lean` where the plan below says `Zeta2.Seven` and `Zeta2Lean/Seven/`; its main theorem is
`Zeta2.Z7.zeta2_7_irrational`, with the rates g = 0.71 and δ = 3.99.)

**Target.**

```lean
def SevenStatement : Prop :=
  (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧ ¬ ∃ q : ℚ, zeta2 7 = q
theorem Zeta2.Seven.zeta2_7_irrational : SevenStatement
```

`Stmt_Criterion` (reused) is already stated for any number k of constants; use k = 1 with α = `zeta2 7`.

### 10.1 Reuse verbatim

| file(s) | provides |
|---|---|
| `Zeta2Lean/Defs.lean` | trusted `volkenbornSum`, `HasVolkenborn`, `volkenborn`, `halfPow`, `J`, `zeta2`; `Ahalf`, `dn`, `DeltaGe`, `DeltaAll`, `IntValued` |
| `Zeta2Lean/Statements.lean` + `Zeta2Lean/Proofs/{JConvergence, Translation, Criterion, DeltaCalculus, DeltaFunctions}.lean` | `Stmt_JConv`, `Stmt_Translation` (positive shifts), `Stmt_Criterion`, `Stmt_Delta`, `Stmt_DeltaFun` (the `binom` field is exactly (D4) for x ≥ 0) |
| `Zeta2Lean/Cited/PNT.lean`, `Cited/Vendor/PNT/*` | `PNT_proof : PNT_Stmt` |
| `Pair/Proofs/Landscape/Numerics.lean` | certified rational enclosures of `log` (for the max-U certificate) |

### 10.2 Adapt (same proof pattern, new objects)

| pair file | new statement (namespace `Zeta2.Seven`) | change |
|---|---|---|
| `Pair/Defs.lean` | `Seven/Defs.lean` | blocks `η = (5,7,7,9,11,13)/40`; pole profile `apole m k ∈ {1,2,3,4}`; `Gser m k = (n−2k+2ε)·numSer(−k)·(∏_{j≠k}(j−k+ε)^{a_j})⁻¹`; `rcoef m i k = [ε^{a_k−i}]Gser`; `halfPowZ s (z : ℤ)`; centred `integrand7`, `rho7`; `Z7 := 46080·c₃`; the sign convention S = −∫R'''(t+½−n/2) as in the pair |
| `Pair/Proofs/GenLinearForm.lean` (109 lines) | `Stmt_GenLinearFormZ` | pole positions k − n/2 of both signs; uses `Stmt_TranslationNeg` |
| `Pair/Proofs/PartialFractions.lean` (353) | `Stmt_PF7` | variable pole orders `a_k` instead of the uniform 6 |
| `Pair/Proofs/CoeffVanish.lean` (280) | `Stmt_CoeffVanish7` | symmetry r_{i,n−k} = (−1)^{i+1}r_{i,k}; c₁ = 0 (deg −3); c_even = 0; a ≤ 4 |
| `Pair/Proofs/LinearForm.lean` (63) | `Stmt_L7` | `HasVolkenborn integrand7 (rho7 + 60·c₃·J 6)`: only `J 6` survives |
| `Pair/Proofs/IntegrandTaylor.lean` (91) | `Stmt_IntegrandTaylor7` | centred product form |
| `Pair/Proofs/Valuation.lean` (826) | `Stmt_Valuation7` (Theorem V): `‖I‖·2^{272m} ≤ c(m+1)^A` | factor 2^{Σa_k}; blocks L!·C(x + x_ν, L) with x_ν = (½−η_ν)n ∈ ℕ (so `binom` applies unchanged); odd shifts 2x + 2k + 1 − n of both signs in E(t) |
| `Pair/Proofs/NonvanishingLS.lean` (171) | `Nonvanishing7_of_LaiSprang` | drop the Z₉ clause |
| `Pair/Proofs/Nonvanishing.lean` (1557) | `Stmt_LaiSprangCond7` (Theorem N) | ℓ = 38m − 1 (Dirichlet mod 38, `Nat.frequently_atTop_prime_and_modEq`); Lemma D2 infrastructure reused; the new content is the two-term argument and θ₀ = −81/224 |
| `Pair/Assembly.lean`, `Pair/Main.lean` | `main7_of_stmts`, `zeta2_7_irrational` | two coefficients (ρ, Z₇) in `bound_core`; gain 2^{272m}; margin `g + δ < (34/5)·log 2` with g = 0.7068 and δ = 3.96 (4.6668 < 4.7134, `Real.log_two_gt_d9`) |

### 10.3 New

| statement | content | estimate |
|---|---|---|
| `Stmt_TranslationNeg` | ∫(t+½−d)^{−s} = J_s + s·Σ_{l=1}^{d}(½−l)^{−s−1} for d ∈ ℕ, via Riemann sums (the pattern of `Proofs/Translation.lean`) | ~150 lines |
| `Stmt_Growth7 g` (Theorem G) | G1 via Cauchy (Mathlib) **or**, avoiding complex analysis, a majorant bound on [ε^λ]∏(1+ε/β)^{e} (costs only poly(n)); G2–G6 (sums versus integrals, `Real.log` inequalities); `Stmt_MaxU` = 152 box certificates with the enclosures of `Numerics.lean` | ~1200 lines; replaces the pair's contour-integral `Growth.lean` |
| `Stmt_BigPrimes7` | Theorem C | ~150 |
| `Stmt_ClassLemma` | Lemma 4.3: residue calculus of rational functions over ℚ (principal parts, residue at ∞) plus the q-adic expansion of Û | ~800 |
| `Stmt_KernelIdentity` | Lemma 4.4: sum of all residues of a rational function of degree ≤ −2 is 0 (the coefficient c₁ of its partial fractions) | ~150 |
| `Stmt_FarPart` | Lemma 4.5: power sums over 𝔽_q^× (Mathlib `FiniteField.sum_pow_units`) | ~200 |
| `Stmt_ThmK` | Theorem K (Lemmas 4.6–4.7 plus q-integrality, Lemma 4.2) | ~600 |
| `Stmt_TypeCert` | kernel-checked certificates (`decide +kernel`, as in the pair's 766 `certs*_ok`). (a) **469 kernel-level intervals on [1, 20]**: for each interval the list of local types (~24) and, per type, the first nonzero index of D_{ξ,κ} in exact ℚ-series arithmetic to order 12. (b) **980 residue-level intervals on one period [20, 60]**: E-counts only, like the pair's `Vl` certificates. | the main cost: data generator in Python (exact), kernel check possibly split into ~20 files |
| `Stmt_Continuum7` | Lemmas 4.10–4.12: events, candidate set ⋃_{d≤40}(20/d)ℤ, discrete ⊆ continuum, 40-periodicity | ~800 |
| `Stmt_SmallPrimes7` | Lemma 4.9 (Legendre/Kummer; reuse `card_odd_dvd` and the q-adic norm helpers of `Pair/Proofs/Denominators.lean`) | ~400 |
| `Stmt_Denominators7 δ` | Theorem A with δ = 3.96. Head: kernel level on [1,20]. Residue level f⁰ on [20,140] by periodicity. For √(3n) < q ≤ n/140: f⁰ ≤ 10 (the period maximum from certificate (b)), which gives 10/140. For q \| n/40: Lemma 4.8(1), e_q ≤ 14, O(log²n) in total. For q ≤ √(3n): Lemma 4.9. Value 3.9240892 (the assembler's `constants.py`). Reuse `theta_tendsto`, `chain_sum` and the `log_sum_bound` pattern of the pair | ~1200 |

**Order of work.**
1. Defs7 and the routine statements (L7, PF7, CoeffVanish7, TranslationNeg), since they unblock everything.
2. Valuation7 (closest to existing code).
3. Nonvanishing7.
4. Growth7 and its max-U certificate.
5. Denominators7: certificates first, because they are the risk; then ThmK and the continuum lemmas.

**Rates.** g = 0.7068 ≥ U*; δ = 3.96 ≥ 3.9240892; g + δ = 4.6668 < 6.8 log 2 = 4.71340.

**Estimate.** About 9–12k new or adapted lines (the pair had 15.8k). As in the pair, run `#print axioms` and the
kernel replay (`scripts/kernels.sh`) at the end.

---------------------------------------------------------------------------------------------------

## 11. Sources

The research tracks behind this proof, with their own proofs, scripts, data and logs, are not part of this repository;
the exceptions are the verbatim copies of the reference engines in `python/z7_ref/` and the certified interval data in
`python/z7_ref/data/`.

| content | research track |
|---|---|
| starting notes, Theorem C, cand3, exact data | hypergeometric notes (§5) and exact data (`verify_cand.py`, `genpole.py`) |
| candidate verification (exact margins to n = 6000, E∞ ≈ 3.87, g ≈ 0.684) | verify-candidate (`vc_*.py`) |
| Theorems K and A (primary denominator proof) | denominators-theory (`cont.py`, `levels.py`, `kernel.py`, `integrate.py`, `tail.py`, `disc_bound.py`, head/tail data) |
| its verification | verify-denominators-theory (`vlevels.py`, `vinteg.py`) |
| second denominator proof and search (ga1a) | denominators-search (`pcl2.py`, `certify.py`) |
| its verification | verify-denominators-search (`trueq.py`, `thk.py`, `v2check.py`) |
| Theorems G, V, N (and N*) | growth-nonvanishing (`umax_cert.py`, `nv_ladic.py`, `nv_general.py`, `val_check.py`) |
| its verification | verify-growth-nonvanishing (`v*.py`) |
| assembler's recomputation | assembly (`constants.py`) |
| holonomy (CDT) track and its verification | holonomy, verify-holonomy |
| pair proof (Lemma D2, Theorem G4, criterion §8) | the informal proof `docs/proof.md` of https://github.com/gmDevi/zeta2-7-9-lean and its Lean formalisation |
