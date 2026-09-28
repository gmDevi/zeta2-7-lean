module

public import Zeta2Lean.Statements
public import Zeta2Lean.Pair.Defs

@[expose] public section

/-!
# Zeta2Lean.Pair.Statements — one `Prop` per lemma of the pair blueprint

*In this repository.* This file is the pair repository's (https://github.com/gmDevi/zeta2-7-9-lean),
unchanged apart from this paragraph and the module-system header.
It is imported by the pair proof files that the `ζ₂(7)` proof reuses; the `ζ₂(7)` proof uses
none of its statements.
Its references to documents, scripts and pair files that are not included here (such as
`BLUEPRINT_PAIR.md`, `docs/proof.md`, `python/pair_mirror.py` or `Pair/Main.lean`) are to
that repository.

Every lemma of the pair proof is a `def Stmt_X : Prop` (or a `structure Stmt_X : Prop` with named
fields), in the namespace `Zeta2.Pair`.  Proof files `Zeta2Lean/Pair/Proofs/*.lean` prove them,
taking the statements they depend on as *hypotheses*; `Zeta2Lean/Pair/Assembly.lean` derives the
main theorem (complete, no gaps); `Zeta2Lean/Pair/Main.lean` wires everything together.

Reused from the `{7,9,11}` repository (namespace `Zeta2`, file `Zeta2Lean/Statements.lean`):
`PNT_Stmt` (proved in `Zeta2Lean/Cited/PNT.lean`), `Stmt_JConv`, `Stmt_Translation`,
`Stmt_Criterion`, `Stmt_Delta`, `Stmt_DeltaFun` and their proof files
`Zeta2Lean/Proofs/{JConvergence, Translation, Criterion, DeltaCalculus, DeltaFunctions}.lean`.

Kinds of statements here (all are proved):
* **routine** (proof files with `gap = ''`): `Stmt_GenLinearForm`, `Stmt_PF`, `Stmt_CoeffVanish`,
  `Stmt_L1`, `Stmt_IntegrandTaylor`, `Stmt_CrudeInt`, and `Stmt_Valuation` (GAP 4: the Lai/Sprang
  Δ-calculus bound).  `Pair/Main.lean` uses their proofs.
* **the three gap statements** `Stmt_Growth` (GAP 1), `Stmt_Denominators` (GAP 2),
  `Stmt_Nonvanishing` (GAP 3), proved for configuration E in `Pair/Proofs/Growth.lean`,
  `Denominators.lean` and `Nonvanishing.lean`.  They are parametrised by a configuration
  `cfg : Config` and by the rates `g`, `δ`, and stated in exactly the form `main_of_stmts`
  consumes; the margin condition is `g + δ < 12 log 2`.

Normalisation reminder: `R_n` carries **no** power of `2`; `ρ₀, Z₇, Z₉` have 2-adic denominators of
size `≈ 2^{12n}`, `v₂(S_n) ≈ 12 n`, and only the *odd part* `D · ‖D‖₂` of a common denominator `D`
enters the margin.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

/-! ## The main statement -/

/-- **Main theorem** (target): the Riemann sums defining every `J s` converge, and `ζ₂(7)`, `ζ₂(9)`
are not both rational. -/
def PairStatement : Prop :=
  (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧ ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q))

/-! ## Routine statements: the linear form -/

/-- **Generic linear form** (any pole order `a`, any coefficient array `r`; LSZ Lemma 3.3 /
proof.md Lemma 1 before any vanishing): the Riemann sums of
`∑_{i ≤ a, k ≤ n} (i)₃ r_{i,k} (x + k + 1/2)^{-(i+3)}` converge to
`ρ₀ + ∑_{i=1}^{a} (i)₃ c_i J_{i+3}`. -/
def Stmt_GenLinearForm : Prop :=
  ∀ (a n : ℕ) (r : ℕ → ℕ → ℚ),
    HasVolkenborn (fun x => ((genIntegrand a n r x : ℚ) : ℚ_[2]))
      ((genRho0 a n r : ℚ_[2]) +
        ∑ i ∈ Icc 1 a, ((i : ℚ_[2]) * (i + 1) * (i + 2)) * (genCsum n r i : ℚ_[2]) * J (i + 3))

/-- **Partial fractions**: `R_n(t) = ∑_{i=1}^{6} ∑_{k=0}^{n} r_{i,k} (t+k)^{-i}`, as a polynomial
identity after multiplying by `(t)_{n+1}^6`, and as an identity of Taylor expansions at every
non-pole `y`. -/
structure Stmt_PF : Prop where
  poly : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → Rnum n h = PFpoly n h
  series : ∀ (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ), Admissible n h → (∀ j ≤ n, y + (j : ℚ) ≠ 0) →
    Rser n h y =
      ∑ i ∈ Icc (1 : ℕ) 6, ∑ k ∈ range (n + 1), C (rcoef n h i k) * ((C (y + k) + X) ^ i)⁻¹

/-- **Parity lemma and vanishing sums**: `r_{i,n-k} = (-1)^{i+1} r_{i,k}`
(from `R_n(-t-n) = -R_n(t)`;
each shifted factor `(t+1/2-h)_{n+2h}` is individually symmetric), `c₁ = 0` (`deg R_n = -5`) and
`c_i = 0` for even `i`. -/
structure Stmt_CoeffVanish : Prop where
  symm : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i k : ℕ, k ≤ n →
    rcoef n h i (n - k) = (-1) ^ (i + 1) * rcoef n h i k
  c1 : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → csum n h 1 = 0
  ceven : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i : ℕ, Even i → csum n h i = 0

/-- **L1 (the linear form)**: `S_n = ρ₀ + 60 c₃ J₆ + 210 c₅ J₈` `(= ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9))`, with
convergence of the Riemann sums.  Only `ζ₂(7)` and `ζ₂(9)` survive. -/
def Stmt_L1 : Prop :=
  ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h →
    HasVolkenborn (fun x => ((integrand n h x : ℚ) : ℚ_[2]))
      ((rho0 n h : ℚ_[2]) + 60 * (csum n h 3 : ℚ_[2]) * J 6 + 210 * (csum n h 5 : ℚ_[2]) * J 8)

/-- **Product form of the integrand**:
`integrand n h x = -R_n'''(x + 1/2) = -6 [ε³] R_n(x + 1/2 + ε)`.
(Bridge from the partial-fraction definition to the product form used by the 2-adic estimates.) -/
def Stmt_IntegrandTaylor : Prop :=
  ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ x : ℕ,
    integrand n h x = -6 * coeff 3 (Rser n h ((x : ℚ) + 1 / 2))

/-- **Crude integrality** (certainly true, elementary, useless for the margin):
`2^{6n} (k!(n-k)!)^6 d_n^{6-i} r_{i,k} ∈ ℤ`, hence `Dcrude n = 2^{6n} n!^6 d_{2n}^{10}` clears the
denominators of `ρ₀`, `Z₇`, `Z₉`.  (It does **not** claim any `d_n^{a+j}`-type bound: in the shifted
families prime exponents up to `a + j + 2 = 11` occur, see `BLUEPRINT_PAIR.md`.) -/
structure Stmt_CrudeInt : Prop where
  coef : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i k : ℕ, 1 ≤ i → i ≤ 6 → k ≤ n →
    ∃ z : ℤ, (2 : ℚ) ^ (6 * n) * ((k.factorial * (n - k).factorial : ℕ) : ℚ) ^ 6 *
      (dn n : ℚ) ^ (6 - i) * rcoef n h i k = z
  forms : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ClearsDen (Dcrude n) n h

/-! ## GAP 4: 2-adic smallness (proved in `Pair/Proofs/Valuation.lean`) -/

/-- **GAP 4 (valuation)**: `v₂(S_n) ≥ 12 n - A log₂(n+1) - log₂ c` uniformly over admissible
`(n, h)` (unnormalised; `2a = 12`), in the form `‖S_n‖ · 2^{12n} ≤ c (n+1)^A`.  Stated for every
limit `I` of the Riemann sums, so no convergence proof is needed.  Numerically
`12n - v₂(S_n) = 23 … 39` for configuration E, `n ≤ 640`. -/
def Stmt_Valuation : Prop :=
  ∃ (c : ℝ) (A : ℕ), ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ I : ℚ_[2],
    HasVolkenborn (fun x => ((integrand n h x : ℚ) : ℚ_[2])) I →
      ‖I‖ * (2 : ℝ) ^ (12 * n) ≤ c * ((n : ℝ) + 1) ^ A

/-! ## The three gap statements (proved for configuration E in `Pair/Proofs/`) -/

/-- **GAP 1 (growth)**: along the configuration, `max(|ρ₀|, |Z₇|, |Z₉|) ≤ exp((g + ε) n)`
eventually, for every `ε > 0`.  Configuration E: measured `g ≈ -0.79` (fits: limit `≈ -0.786`;
saddle-point value `-0.78128`, see `Pair/Proofs/Growth.lean`); the naive residue bound gives
`+0.77` — about `1.6` nats per `n` of cancellation must be proved.  Proved for configuration E
with `gE = -0.72` (`Growth_proof`, `Pair/Proofs/Growth.lean`). -/
def Stmt_Growth (cfg : Config) (g : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
    |(rho0 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m) ∧
      |(Z7 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m) ∧
      |(Z9 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m)

/-- **GAP 2 (denominators)**: assuming PNT, there is a common denominator `D m` of
`ρ₀, Z₇, Z₉` (eventually) whose **odd part** `D · ‖D‖₂` is `≤ exp((δ + ε) n)` eventually, for every
`ε > 0`.  (The power of `2` in `D` is free: it cancels against `‖D S_n‖₂`.)  Configuration E:
residue-level provable estimate `δ = 10 - R_∞ ≈ 8.91` (`R_∞ = ∫_1^∞ s(x) dx/x² ≈ 1.09`); observed
true denominators `≈ 8.37`.  Proved for configuration E with `deltaE = 9` (`Denominators_proof`,
`Pair/Proofs/Denominators.lean`, constant `8.97`).  It does **not** assume
`odd part ∣ d_n^{a+j}`: prime exponents `a + j + 2 = 11` occur for many `q > √n`. -/
def Stmt_Denominators (cfg : Config) (δ : ℝ) : Prop :=
  PNT_Stmt → ∃ D : ℕ → ℕ, (∀ᶠ m in atTop, ClearsDen (D m) (cfg.n m) (cfg.h m)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      (D m : ℝ) * ‖(D m : ℚ_[2])‖ ≤ Real.exp ((δ + ε) * cfg.n m)

/-- **GAP 3 (nonvanishing)**: if `ζ₂(7)` and `ζ₂(9)` are both rational, then `S_n ≠ 0` for
infinitely many steps of the configuration.  (The rationality hypotheses allow the Lai–Sprang
`ℓ(n)`-adic route; an unconditional proof — dominant term, Casoratian — simply ignores them.)
Stated for every limit `I` of the Riemann sums.  Proved for configuration E
(`Nonvanishing_proof`, `Pair/Proofs/Nonvanishing.lean`, through `Stmt_LaiSprangCond` at the
primes `q = n - 1`). -/
def Stmt_Nonvanishing (cfg : Config) : Prop :=
  (∃ q : ℚ, zeta2 7 = q) → (∃ q : ℚ, zeta2 9 = q) →
    ∃ᶠ m in atTop, ∀ I : ℚ_[2],
      HasVolkenborn (fun x => ((integrand (cfg.n m) (cfg.h m) x : ℚ) : ℚ_[2])) I → I ≠ 0

/-- **Lai–Sprang condition** (a purely arithmetic sufficient condition for GAP 3; Lai–Sprang,
arXiv:2306.10393, Lemma 2.2): for every bound `B`, frequently along the configuration there is a
prime `q > B` at which `ρ₀ ≠ 0` has strictly smaller `q`-adic valuation than both non-zero
`ζ`-coefficients.  Numerically (configuration E, `n = 40, 80, 120, 160, 200, 400`) **every**
prime `q ∈ (√n, n]` satisfies it, with `v_q(Z₇) - v_q(ρ₀) ≥ 6` and `v_q(Z₉) - v_q(ρ₀) ≥ 7`
(typically `7` and `9`).  Recommended witness: `q = n - 1` when it is prime (infinitely many `m`
by Dirichlet, `frequently_prime_forty_mul_sub_one_gt`); there `(v_q ρ₀, v_q Z₇, v_q Z₉) =
(-9, -2, 0)` at `n = 80, 240, 360` (`docs/proof.md` §7, Theorem A;
`python/pair_audit_independent.py`).
`Stmt_LaiSprangCond cfg → Stmt_Nonvanishing cfg` is the proved lemma `Nonvanishing_of_LaiSprang`
(`Pair/Proofs/NonvanishingLS.lean`). -/
def Stmt_LaiSprangCond (cfg : Config) : Prop :=
  ∀ B : ℕ, ∃ᶠ m in atTop, ∃ q : ℕ, q.Prime ∧ B < q ∧ rho0 (cfg.n m) (cfg.h m) ≠ 0 ∧
    (Z7 (cfg.n m) (cfg.h m) = 0 ∨
      padicValRat q (rho0 (cfg.n m) (cfg.h m)) < padicValRat q (Z7 (cfg.n m) (cfg.h m))) ∧
    (Z9 (cfg.n m) (cfg.h m) = 0 ∨
      padicValRat q (rho0 (cfg.n m) (cfg.h m)) < padicValRat q (Z9 (cfg.n m) (cfg.h m)))

end Zeta2.Pair

end
