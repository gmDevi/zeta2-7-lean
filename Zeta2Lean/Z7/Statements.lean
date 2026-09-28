module

public import Zeta2Lean.Statements
public import Zeta2Lean.Z7.Defs
public import Zeta2Lean.Z7.DenTable

@[expose] public section

/-!
# Zeta2Lean.Z7.Statements — one `Prop` per lemma of the `ζ₂(7)` blueprint

Every lemma of the proof (`BLUEPRINT_Z7.md`; informal proof "proof §x" = `docs/proof.md`) is a
`def Stmt_X : Prop` (or a `structure Stmt_X : Prop` with named fields) in the namespace
`Zeta2.Z7`.  The proof files `Zeta2Lean/Z7/Proofs/*.lean` prove them, taking the statements they
depend on as hypotheses; `Zeta2Lean/Z7/Assembly.lean` derives the main theorem from the top-level
statements (complete, no gaps); `Zeta2Lean/Z7/Main.lean` wires everything together.

Reused from `Zeta2Lean/Statements.lean` (namespace `Zeta2`, proved): `PNT_Stmt`
(`Cited/PNT.lean`), `Stmt_JConv`, `Stmt_Translation`, `Stmt_Criterion`, `Stmt_Delta`,
`Stmt_DeltaFun` (`Proofs/*.lean`).

Layers (the arrows are the hypotheses of the proof files):
* **linear form**: `TranslationNeg`, `GenLinearFormZ ← JConv, Translation, TranslationNeg`,
  `PF7`, `CoeffVanish7 ← PF7`, `L7 ← GenLinearFormZ, CoeffVanish7`, `IntegrandTaylor7 ← PF7`;
* **2-adic size**: `Valuation7 ← IntegrandTaylor7, Delta, DeltaFun` (Theorem V);
* **nonvanishing**: `AuxPrime7 ← PF7, CoeffVanish7` (Theorem N), `Nonvanishing7 ← L7, AuxPrime7`;
* **growth**: `MaxU7 g7` (certificate), `ResidueBound7 ← PF7` (Lemmas G1–G6),
  `Growth7 g7 ← MaxU7, ResidueBound7` (Theorem G);
* **denominators**: `BigPrimes7` (Theorem C), `SmallPrimes7` (Lemma 4.9), `Emin7` (Lemma 4.8),
  `ClassLemma7 ← PF7` (Lemma 4.3), `KernelIdentity7 ← CoeffVanish7` (Lemma 4.4),
  `FarPart7 ← PF7` (Lemma 4.5), `PerPole7 ← PF7` (Lemma 4.7),
  `ThmK7 ← ClassLemma7, KernelIdentity7, FarPart7, PerPole7, Emin7` (Theorem K),
  `HeadCert7` (continuum + kernel-level certificates on `[1,20)`, Lemmas 4.10–4.11),
  `ResCert7` (residue-level certificates on one period + periodicity, Lemma 4.12),
  `ExpBounds7 ← ThmK7, HeadCert7, ResCert7, Emin7, SmallPrimes7, BigPrimes7`,
  `Denominators7 delta7 ← ExpBounds7` (Theorem A, PNT).

Normalisation: `rho u = -ρ_n`, `Zc u = -Z_n` relative to proof §3 (the pair's convention
`S = -∫ R'''`); the degree is `n = 40 u`.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

/-! ## The main statement -/

/-- **Main theorem** (target): the Riemann sums defining every `J s` converge, and `ζ₂(7)` is
irrational (`zeta2 7 = J 6 / 768`, `Zeta2Lean/Defs.lean`). -/
def SevenStatement : Prop :=
  (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧ ¬ ∃ q : ℚ, zeta2 7 = q

/-! ## The linear form (proof §2–§3) -/

/-- **Translation by a negative shift** (proof (P1)): for `e ∈ ℕ`,
`∫ (t + 1/2 - e)^{-s} dt = ∫ (t + 1/2)^{-s} dt + s ∑_{l=1}^{e} (1/2 - l)^{-s-1}`, in Riemann-sum
form. -/
def Stmt_TranslationNeg : Prop :=
  ∀ (s e : ℕ) (I : ℚ_[2]), HasVolkenborn (halfPow s) I →
    HasVolkenborn (fun x => halfPowZ s ((x : ℤ) - e))
      (I + (s : ℚ_[2]) * ∑ l ∈ Icc 1 e, halfPowZ (s + 1) (-(l : ℤ)))

/-- **Generic centred linear form** (any pole order `a`, degree `n`, shift `m`, coefficients `r`):
the Riemann sums of `∑_{i ≤ a, k ≤ n} (i)₃ r_{i,k} (x + k - m + 1/2)^{-(i+3)}` converge to
`genRhoZ a n m r + ∑_{i=1}^{a} (i)₃ c_i J_{i+3}`. -/
def Stmt_GenLinearFormZ : Prop :=
  ∀ (a n m : ℕ) (r : ℕ → ℕ → ℚ),
    HasVolkenborn (fun x => ((genIntegrandZ a n m r x : ℚ) : ℚ_[2]))
      ((genRhoZ a n m r : ℚ_[2]) +
        ∑ i ∈ Icc 1 a, ((i : ℚ_[2]) * (i + 1) * (i + 2)) * (genCsum n r i : ℚ_[2]) * J (i + 3))

/-- **Partial fractions** (proof Lemma 0(a)): `R_n(t) = ∑_{k ≤ n} ∑_{i=1}^{a_k} r_{i,k} (t+k)^{-i}`,
as a polynomial identity after multiplying by `∏_k (t+k)^{a_k}`, and as an identity of Taylor
expansions at every non-pole `y`. -/
structure Stmt_PF7 : Prop where
  poly : ∀ u : ℕ, Rnum u = PFpoly u
  series : ∀ (u : ℕ) (y : ℚ), (∀ j ≤ 40 * u, y + (j : ℚ) ≠ 0) →
    Rser u y = ∑ k ∈ range (40 * u + 1), ∑ i ∈ Icc (1 : ℕ) 4,
      C (rcoef u i k) * ((C (y + k) + X) ^ i)⁻¹

/-- **Symmetry and vanishing sums** (proof Lemma 0(b)–(d)): `r_{i,n-k} = (-1)^{i+1} r_{i,k}` (from
`R_n(-n-t) = -R_n(t)`), `c₁ = 0` (`deg R_n = -3`) and `c_i = 0` for even `i`. -/
structure Stmt_CoeffVanish7 : Prop where
  symm : ∀ u i k : ℕ, k ≤ 40 * u → rcoef u i (40 * u - k) = (-1) ^ (i + 1) * rcoef u i k
  c1 : ∀ u : ℕ, csum u 1 = 0
  ceven : ∀ u i : ℕ, Even i → csum u i = 0

/-- **Lemma L** (proof §3): `S_n = ρ + 60 c₃ J₆` (`= ρ + Z ζ₂(7)`), with convergence of the Riemann
sums.  Only `ζ₂(7)` survives. -/
def Stmt_L7 : Prop :=
  ∀ u : ℕ, HasVolkenborn (fun x => ((integrand u x : ℚ) : ℚ_[2]))
    ((rho u : ℚ_[2]) + 60 * (csum u 3 : ℚ_[2]) * J 6)

/-- **Product form of the integrand**: `integrand u x = -R_n'''(y) = -6 [ε³] R_n(y + ε)` at the
centred point `y = x - n/2 + 1/2`. -/
def Stmt_IntegrandTaylor7 : Prop :=
  ∀ u x : ℕ, integrand u x = -6 * coeff 3 (Rser u ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2))

/-! ## Theorem V: 2-adic size (proof §6) -/

/-- **Theorem V**: `v₂(S_n) ≥ 6.8 n - O(log n)` (`6.8 n = 272 u`), for every limit `I` of the
Riemann sums, in the form `‖I‖ · 2^{272 u} ≤ c (u+1)^A`.  (Proved bound:
`v₂(S_n) ≥ 272u + 7 - 10(⌊log₂ 30u⌋ + 1)`.) -/
def Stmt_Valuation7 : Prop :=
  ∃ (c : ℝ) (A : ℕ), ∀ (u : ℕ) (I : ℚ_[2]),
    HasVolkenborn (fun x => ((integrand u x : ℚ) : ℚ_[2])) I →
      ‖I‖ * (2 : ℝ) ^ (272 * u) ≤ c * ((u : ℝ) + 1) ^ A

/-! ## Theorem N: nonvanishing (proof §7) -/

/-- **Theorem N** (auxiliary prime `ℓ = 19n/20 - 1 = 38u - 1`): if `ℓ` is prime then
`v_ℓ(ρ) = -1` and `v_ℓ(Z) ≥ 0` (for all large `u`; the proof works for every `u ≥ 1`). -/
def Stmt_AuxPrime7 : Prop :=
  ∃ U : ℕ, ∀ u : ℕ, U ≤ u → (38 * u - 1).Prime →
    padicValRat (38 * u - 1) (rho u) = -1 ∧ 0 ≤ padicValRat (38 * u - 1) (Zc u)

/-- **Nonvanishing**: if `ζ₂(7)` is rational, then `S_n ≠ 0` for infinitely many `u` (every limit
of the Riemann sums is non-zero).  From `Stmt_AuxPrime7` along `u` with `38u - 1` prime
(Dirichlet) and Lai–Sprang's Lemma 2.2. -/
def Stmt_Nonvanishing7 : Prop :=
  (∃ q : ℚ, zeta2 7 = q) → ∃ᶠ u in atTop, ∀ I : ℚ_[2],
    HasVolkenborn (fun x => ((integrand u x : ℚ) : ℚ_[2])) I → I ≠ 0

/-! ## Theorem G: growth (proof §5) -/

/-- **Lemma G7** (certified maximum): `U(κ) ≤ Ubar` on `[0, 1]`.  True for `Ubar ≥ 0.7067022243`;
used with `Ubar = g7 = 0.71`. -/
def Stmt_MaxU7 (Ubar : ℝ) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 → Upot κ ≤ Ubar

/-- **Lemmas G1–G6** (residue sizes): `|r_{i,k}| ≤ C (u+1)^B e^{n U(k/n)}` for `n = 40u`,
`u ≥ 1`.  (Proved constants: `log|r_{i,k}| ≤ n U(k/n) + log(n+1) + 14 log n + 37.44`.) -/
def Stmt_ResidueBound7 : Prop :=
  ∃ (C : ℝ) (B : ℕ), ∀ u i k : ℕ, 1 ≤ u → k ≤ 40 * u →
    |(rcoef u i k : ℝ)| ≤ C * ((u : ℝ) + 1) ^ B * Real.exp (40 * u * Upot ((k : ℝ) / (40 * u)))

/-- **Theorem G**: `|ρ|, |Z| ≤ e^{(g + ε) n}` eventually, for every `ε > 0` (`n = 40u`). -/
def Stmt_Growth7 (g : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ u in atTop,
    |(rho u : ℝ)| ≤ Real.exp ((g + ε) * (40 * u)) ∧ |(Zc u : ℝ)| ≤ Real.exp ((g + ε) * (40 * u))

/-! ## The odd denominator: prime-by-prime statements (proof §4) -/

/-- **Theorem C** (primes above `n`): an odd prime `q > n` does not divide the denominators. -/
def Stmt_BigPrimes7 : Prop :=
  ∀ u q : ℕ, q.Prime → q ≠ 2 → 40 * u < q → eq7 u q = 0

/-- **Lemma 4.9** (small primes): `e_q(n) ≤ 19 ⌊log_q(2n+1)⌋` for every odd prime `q`. -/
def Stmt_SmallPrimes7 : Prop :=
  ∀ u q : ℕ, q.Prime → q ≠ 2 → eq7 u q ≤ 19 * Nat.log q (80 * u + 1)

/-- **Lemma 4.8(1)**: every class has `E_ξ ≥ -10` (`q ≥ 5`). -/
def Stmt_Emin7 : Prop :=
  ∀ u q k₀ : ℕ, q.Prime → 5 ≤ q → k₀ < q → -10 ≤ (localModel u q k₀).E

/-- **Lemma 4.3 (class lemma)**, with Lemma 4.2 (`q`-integrality for `q > 2x + 2`): for a kernel
`κ(y) = c₀ + c y^j` with `q`-integral coefficients, if `[y^p] D_{ξ,κ} = 0` for `E + 1 ≤ p < P`
then `v_q(β_ξ - 24 q^{-5} ∮_{D_ξ} R_n K dt) ≥ P - 5`. -/
def Stmt_ClassLemma7 : Prop :=
  ∀ (u q k₀ : ℕ) (c0 c : ℚ) (j : ℕ) (P : ℤ),
    q.Prime → 5 ≤ q → 80 * u + 2 * q < q ^ 2 → k₀ < q → 1 ≤ j →
    ValGe q 0 c0 → ValGe q 0 c → LevGe (localModel u q k₀) c0 j c P →
    ValGe q (P - 5) (classBad u q k₀ - 24 * ((q : ℚ) ^ 5)⁻¹ * kerRes u q k₀ c0 j c)

/-- **Lemma 4.4 (kernel identity)**: `∑_ξ ∮_{D_ξ} R_n Ψ dt = 0` for
`Ψ = c₀ + c q^j ∑_{i<q} (t+i)^{-j}` (the sum of all residues of a rational function of degree
`≤ -2`), split per class as `∮ R_n K_ξ + c q^j ∮ R_n g_{j,ξ}`. -/
def Stmt_KernelIdentity7 : Prop :=
  ∀ (u q : ℕ) (c0 c : ℚ) (j : ℕ), 1 ≤ q → 1 ≤ j →
    ∑ k₀ ∈ range q, (kerRes u q k₀ c0 j c + c * (q : ℚ) ^ j * farRes u q k₀ j) = 0

/-- **Lemma 4.5 (far part)**: `v_q(24 q^{-5} · c q^j ∮_{D_ξ} R_n g_{j,ξ} dt) ≥ j - 4` when
`q ≥ j + 1 - E_ξ` (power sums over `𝔽_q^×`). -/
def Stmt_FarPart7 : Prop :=
  ∀ (u q k₀ j : ℕ) (c : ℚ), q.Prime → 5 ≤ q → 80 * u + 2 * q < q ^ 2 → k₀ < q → 1 ≤ j →
    ValGe q 0 c → (j : ℤ) + 1 ≤ q + (localModel u q k₀).E →
    ValGe q ((j : ℤ) - 4) (24 * ((q : ℚ) ^ 5)⁻¹ * (c * (q : ℚ) ^ j * farRes u q k₀ j))

/-- **Lemma 4.7 (per-pole bound)**: if the pole `-k` (local point `w = -2⌊k/q⌋` of the class
`k mod q`) has per-pole level `≥ T`, then `v_q(r_{i,k}) ≥ T` for every `i`. -/
def Stmt_PerPole7 : Prop :=
  ∀ (u q k : ℕ) (T : ℤ), q.Prime → 5 ≤ q → 80 * u + 2 * q < q ^ 2 → k ≤ 40 * u →
    PoleLevAt (localModel u q (k % q)) (-(2 * ((k / q : ℕ) : ℤ))) T →
    ∀ i : ℕ, ValGe q T (rcoef u i k)

/-- **Theorem K** (per prime, proof §4.6): a kernel certificate for all `q` classes (level
`≥ T` for the bad part, per-pole levels `≥ T`) bounds the exponent: `e_q(n) ≤ -T`. -/
def Stmt_ThmK7 : Prop :=
  ∀ (u q : ℕ) (c0 c : ℚ) (j : ℕ) (T : ℤ),
    q.Prime → 29 ≤ q → 80 * u + 3 * q < q ^ 2 → T ≤ 0 → 1 ≤ j → j ≤ 4 →
    ValGe q 0 c0 → ValGe q 0 c → (c ≠ 0 → T + 4 ≤ j) →
    (∀ k₀ < q, LevGe (localModel u q k₀) c0 j c (T + 5)) →
    (∀ k₀ < q, PoleLevGe (localModel u q k₀) T) →
    (eq7 u q : ℤ) ≤ -T

/-- **Kernel-level certificates on `[1, 20)`** (proof Lemmas 4.10–4.11 + the certified interval
data): for every row of `headRows7` and every prime `q > 1000`, `q ∤ u`, `q² > 2n + 3q` with
`n/q ∈ [a, b)`, every class satisfies the row's certificate (level `≥ -f` for the kernel
`c0 + c y^j`, per-pole level `≥ -f`). -/
def Stmt_HeadCert7 : Prop :=
  ∀ row ∈ headRows7, ∀ u q : ℕ, q.Prime → 1000 < q → ¬ q ∣ u → 80 * u + 3 * q < q ^ 2 →
    row.a ≤ ((40 * u : ℕ) : ℚ) / q → ((40 * u : ℕ) : ℚ) / q < row.b →
    (∀ k₀ < q, LevGe (localModel u q k₀) row.c0 row.j row.c (5 - row.f)) ∧
      (∀ k₀ < q, PoleLevGe (localModel u q k₀) (-(row.f : ℤ)))

/-- **Residue-level certificates** (proof Lemma 4.12 + the period data): for every row of
`resRows7` (one period `[20, 60)`) and every shift `40 t`, every class of an admissible prime with
`n/q ∈ [a + 40t, b + 40t)` has `E_ξ ≥ 4 - f`. -/
def Stmt_ResCert7 : Prop :=
  ∀ row ∈ resRows7, ∀ t u q : ℕ, q.Prime → 1000 < q → ¬ q ∣ u → 80 * u + 3 * q < q ^ 2 →
    row.a + 40 * t ≤ ((40 * u : ℕ) : ℚ) / q → ((40 * u : ℕ) : ℚ) / q < row.b + 40 * t →
    ∀ k₀ < q, 4 - (row.f : ℤ) ≤ (localModel u q k₀).E

/-- **The prime-by-prime exponent bounds** used by Theorem A (proof §4.9, five ranges). -/
structure Stmt_ExpBounds7 : Prop where
  /-- `q > n`: Theorem C. -/
  big : ∀ u q : ℕ, q.Prime → q ≠ 2 → 40 * u < q → eq7 u q = 0
  /-- every odd prime: Lemma 4.9. -/
  small : ∀ u q : ℕ, q.Prime → q ≠ 2 → eq7 u q ≤ 19 * Nat.log q (80 * u + 1)
  /-- `q ≥ 29`, `q² > 2n + 3q` (in particular `q ∣ n/40`): Lemma 4.8(1), `e_q ≤ 14`. -/
  crude : ∀ u q : ℕ, q.Prime → 29 ≤ q → 80 * u + 3 * q < q ^ 2 → eq7 u q ≤ 14
  /-- `n/q ≥ 20`, `q ∤ n/40`: the residue level is `≤ 10` (`E_ξ ≥ -6`). -/
  tail : ∀ u q : ℕ, q.Prime → 1000 < q → ¬ q ∣ u → 80 * u + 3 * q < q ^ 2 → 20 * q ≤ 40 * u →
    eq7 u q ≤ 10
  /-- `n/q ∈ [a, b)` for a row of the table: `e_q ≤ f`. -/
  rows : ∀ row ∈ denTable7, ∀ u q : ℕ, q.Prime → 1000 < q → ¬ q ∣ u → 80 * u + 3 * q < q ^ 2 →
    row.a ≤ ((40 * u : ℕ) : ℚ) / q → ((40 * u : ℕ) : ℚ) / q < row.b → eq7 u q ≤ row.f

/-! ## Theorem A: the odd denominator (proof §4.9) -/

/-- **Theorem A** (assuming PNT): there are odd `D u` and exponents `e u` with
`2^{e u} D u · ρ, 2^{e u} D u · Z ∈ ℤ` (eventually) and `D u ≤ e^{(δ + ε) n}` eventually, for every
`ε > 0`.  (The power of `2` is free: it cancels against `‖S_n‖₂` in the criterion.)  Proved
constant: `3.9240892` (proof §0.2, "Lean-friendly truncation"); target `delta7 = 3.99`. -/
def Stmt_Denominators7 (δ : ℝ) : Prop :=
  PNT_Stmt → ∃ D e : ℕ → ℕ,
    (∀ᶠ u in atTop, Odd (D u) ∧ (∃ z : ℤ, (2 : ℚ) ^ e u * D u * rho u = z) ∧
      ∃ z : ℤ, (2 : ℚ) ^ e u * D u * Zc u = z) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ u in atTop, (D u : ℝ) ≤ Real.exp ((δ + ε) * (40 * u))

end Zeta2.Z7

end
