# Review of C. D. Long, "Hybrid arithmetic holonomy and twenty-two individual p-adic zeta values"

Draft: GitHub `octonion/p-adic-zeta-irrationality`, commit `b46a1770901551961710e155d775aae7c5ea39e7` (2026-08-25),
`hybrid_arithmetic_holonomy.tex` (2317 lines). Line numbers below refer to that TeX file.

**Status of this review.**
* It is an internal review, produced on 2026-09-28 with AI agents (Anthropic Claude models) under the direction of
  the maintainer of this repository. It used four review lenses, three adversarial verifiers whose task was to defend
  the draft against each claimed error, and a handling editor.
* No human expert has checked it, and it is not a refereed report. The author of the draft has not been contacted.
* The draft's own code was not run. All computations used independent code, which is not included here.
* It is published here because this repository proves one of the values the draft claims, ζ₂(7), by a different
  method. We want to state clearly why we do not regard the draft as settling that question.

**Summary.** The draft's large-prime step, the torsor decomposition and Prop. "Torsor Cartier strictness", does not
appear to hold for the actual Eisenstein–Eichler leaf. Without it, the argument as written establishes only the
values ζ₂(3), ζ₂(5), ζ₃(3) and ζ₅(3). These already follow from the plain Calegari–Dimitrov–Tang (CDT) method, and the
first three were known. The other 18 claims, including ζ₂(7), are therefore unproved by the draft; nothing here
shows them false. All 22 numerical margins printed in the draft reproduce exactly from its formulas. The small-prime
(Hasse) mechanism and most of the setup check out (§3).

## 1. What the draft claims
- The irrationality of 22 Kubota–Leopoldt values: ζ₂(s) for odd 3 ≤ s ≤ 29; ζ₃(s) for odd 3 ≤ s ≤ 11; ζ₅(3), ζ₅(5)
  and ζ₇(3).
- The method refines CDT arithmetic holonomy on X₀(p), using the Eisenstein–Eichler leaf of rank s+1.
- It adds two new local mechanisms: a Hasse-invariant saving at small primes, and a "de Rham torsor / Cartier"
  argument at large primes, meant to recover CDT's prime window without scalarizing the packet.
- These are combined with Calegari's overconvergent Eisenstein family, Buzzard's continuation, a modular Jensen formula
  and Bost's slopes inequality.
- The resulting cost τ_{p,s}(ξ) = 2/(s+1)²·(S_{p,s}(ξ) + s·I^{s+1}_ξ(ξ)) is said to give a positive margin in all 22
  cases.

## 2. Issues

**1. MAJOR (load-bearing): the torsor decomposition.** Confirmed by all three verifiers.
- **Where:** lem:neat-descent(ii), eq. torsor-decomp-bridge (lines 887–898, proof 918–925). It is restated as
  eq. torsor-eval (1528–1537) and used in 1539–1546.
- **Claim:** f^D⟨λ,S⟩ = H_λ(f,u) + Σ_e Q_{e,λ}(f,u)·R_e(f). Here u is a free fibre coordinate,
  supp_f Q ⊂ [−C, D+C], and the value does not depend on the torsor point.
- **Why it does not appear to hold:** the argument mixes two charts. λ has finite f-support only in an algebraic
  chart, while S is written through the raw rows D^jK only in Urban's Tate chart (line 694). The two charts differ by
  H = D log f and x_σ = −E₂/(12H) + r_σ, which are both transcendental over Q(f).
- **Consistency with the draft itself:**
  - lem:actual-deepest-row (1335–1350) gives the multiplier of J as H^r·q₀(f, x_σ(f)), which has infinite f-support.
  - Freezing u at a rational point would give the global scalar realization that the draft itself rules out (lines
    111–113, 287–294, 2139–2146).
- **Evidence:**
  - A rank certificate mod 2^61−1 shows that the algebraic-frame coordinates are not Q[f]-combinations of the raw rows
    of polynomial degree ≤ 40. This was checked for (p, s) = (2, 3), (2, 5) and (5, 3).
  - A "peeling" lemma shows that any finite-support decomposition would force the window of Issue 2, and the window
    fails.

**2. MAJOR (load-bearing): the large-prime window (prop:Cartier, 1677–1750; eq. large-local-height, 1685–1693).**
Confirmed by all three verifiers, with matching numbers.
- **Setup:** exact ℓ-adic Padé / echelon computations on primitive λ in the unmodified lattice, with coordinates
  {1, θ^k(H^r K)}.
- **Result:** there are poles of full order s at primes ℓ > N# with no multiple in [n−D−C, n+C]. Each entry in the
  table is (ℓ, least C needed); every pole has order ℓ^{−3}.

| D | pivot n | worst prime(s) |
|---|---|---|
| 12 | 51 | (31, 8) |
| 20 | 83 | (47, 11) |
| 30 | 123 | (73, 20), (71, 19) |
| 40 | 163 | (97, 26) |

- **Growth:** the needed C grows like about 0.6·D, so no fixed C works.
- **Other cells:** the same failure appears at (p, s) = (2, 5), (5, 3), (7, 3), and at p = 7.
- **Controls:** raw rows with polynomial multipliers, in both the f and q coordinates, show 0 violations. The scalar
  lemmas are correct; they do not apply to the actual packet.
- **Mechanism:** ℓ^{−s}·H^r·q₀·J(q^ℓ) reaches every n ≥ ℓ.

**3. MAJOR (consequence): Theorem main and Table 1 (2038–2059).** Confirmed by all three verifiers.
- **The draft's numbers reproduce:** all 22 τ fractions and margins reproduce exactly. For example M₅,₅ = 0.131799356827,
  and for ζ₂(7) τ = 105585/25856 with margin 15.8055 at Y = 1/11.
- **With the window-free cost:** we replaced s·I by the window-free large-prime cost s(m−ξ)²/2 that the argument does
  support, kept the Hasse saving, and optimized over ξ and Y.
  - Still positive: (2,3) +8.22, (2,5) +5.41, (3,3) +4.65, (5,3) +0.93.
  - Negative: (2,7) −5.04, (3,5) −1.15, (7,3) −1.17, (5,5) −8.03, (2,9) −23.25, (3,11) −65.5, (2,29) −641.
- **A Hasse-widened window does not help:** a window of length D + (s−1)c_p·ℓ rescues none of the 18 cells, because
  (s−1)c_p ≥ 1 in each of them.

**4. Minor: carries in the pole-grade induction** (prop:Cartier proof, 1702–1706 and 1730–1733).
- Sums of digits taken from different rows can carry between grades.
- Explicit s = 3 example: B₁ = ℓ−1, B₂ = 1, B₃ = (ℓ−1)·ℓ.
- The peeling argument would repair this, but only if Issue 1 held.

**5. Minor: the support claim in lem:actual-deepest-row (1344–1345).** The multiplier q₀(f, x_σ)·H^r is an infinite
series. This does not affect the small-prime argument, which needs only lower support and integrality.

**6. Minor: the justification of torsor-point independence (1536–1537).** Independence of the frame comes from the
B-equivariance of the contraction, not from horizontality.

**7. Minor: scope of the cited prime-window function** ((E5) at 353–359, lem:fixed-bundle at 1100–1104, abstract).
- CDT (7.3.10) and (7.3.15) apply to literal n^{e_i} denominators in the Padé coordinate.
- CDT's own ICM §5.2 treats this packet as lcm-type.
- The draft labels the window as its own result in the body; only the abstract's wording ("published prime-window
  function") is misleading.

**8. Minor: unstated positivity hypotheses** (1106–1111, 1852–1855). Λ > 0 (and in effect Λ > τ) is used without being
stated. It holds for every witness; the minimum of Λ − τ is 0.705, at (2, 29).

**9. Minor: lem:BGG (548–561, 613–618).** The exact oper normal form exists only in a flat or analytic coordinate. On
algebraic charts, algebraicity should come from uniqueness plus descent. The conclusion is right.

**10. Minor: the proof of prop:single-unipotent (975–1015) is only sketched.** The claim was re-derived for s = 3 and
is true.

Items 5, 8, 9 and 10 come from single reviewers and had no separate verification pass. The small-primes lens had no
verifier.

## 3. Checked and apparently correct
- **U_p eigenvalue:** it equals 1, and (E1) matches Calegari 2005, Thm 2.3 and Lemma 2.4.
- **Raw depths:** n^e·[q^n]R_e ∈ Z holds, and the depths are exact.
- **Exact Dwork relation:** holds.
- **Coordinate Frobenius:** φ_ℓ(f) = f^ℓ + ℓ·Δ, checked for ℓ = 5, 7, 11.
- **Packet:** the BGG recursion, split extension, Rees–Bol coefficients, functional rank and independence, and the
  zero-estimate count are all correct.
- **Hasse algebraization:** the degree bound is about c_p·ℓ, checked by mod-ℓ Padé for p = 2, 3, 7.
- **Small primes:** the genuine-source Hasse codimension, the rank–nullity count, small-prime integrality, the
  determinant cost, the absence of double counting and the residual-prime bound are all correct.
- **Abstract lemmas:** lem:no-backflow and lem:pivot-truncation are correct as abstract statements.
- **Prime-window function:** I^m_ξ(ξ) equals the integral of CDT (7.3.11) (to about 1e−10 at six test points).
- **Bost assembly:** signs and normalizations agree with CDT24 Thm 7.0.1 and ICM Thm 2.6. With no Hasse term it
  reduces to CDT τ(e) for e = (0, s, …, s).
- **Continuation radii:** R_p = p^{12/(p−1)}, checked by Newton polygons for p = 2, 3, 5, 7.
- **Buzzard:** it is used as in Calegari 2005 and CDT ICM.
- **Modular Jensen formula:** re-derived; a numerical check agrees to about 1e−4 at four points.
- **Witnesses:** all 22 ξ values, τ values and margins reproduce exactly.
- **Dependencies:** there is no circularity.

## 4. Not checked
- The content of GPRJ 2025 Props A.14–A.15, Katz 1973 and Bost–Charles 2022, beyond whether the draft applies them in
  the right shape.
- lem:fixed-bundle, beyond its shape.
- The draft's interval-certificate script, which was not run. The margins were recomputed independently.
- Whether some other, unwritten window argument could rescue any of the 18 cells. Only the Hasse-widened window was
  examined.
- The companion density draft.
- **Model caveat:** all counterexamples use the same model of the leaf: the cyclic algebraic frame with H = D log f and
  the Serre splitting, and λ primitive in a sublattice of M_D. The verifiers argued that pole counts on a sublattice
  transfer to the full lattice. The failure in Issue 1 also follows from the draft's own statements, independently
  of any computation.

## 5. Consequence for ζ₂(7)
- The draft prints a margin of +15.81 for ζ₂(7).
- About 20.8 nats of that comes from the large-prime window of Issue 2, and about 1.4 from the Hasse saving.
- With the window-free large-prime cost, keeping the Hasse saving, the margin is −5.04. The plain CDT method gives
  −6.65. An independent third-party computation (GitHub `rain-1/math-modular-sources`, Remark 6.4) reports about
  −6.46 for an optimized CDT template.
- So the draft does not establish the irrationality of ζ₂(7). It does not refute it either.
