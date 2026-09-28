module

public import Zeta2Lean.Defs

@[expose] public section

/-!
# Zeta2Lean.Statements — the shared statements

The statements that the pair development took over from the `{7,9,11}` repository
(https://github.com/gmDevi/zeta2-7-9-11-lean, file of the same name; the statements of that
project's construction are omitted here), as in the pair repository
(https://github.com/gmDevi/zeta2-7-9-lean).  Each is a `def Stmt_X : Prop` (or a `structure` with
named fields).  The `ζ₂(7)` statements (`Zeta2Lean/Z7/Statements.lean`) and proofs take them as
hypotheses, and `Zeta2Lean/Z7/Main.lean` supplies their proofs:

* `PNT_Stmt`: the prime number theorem, proved in `Zeta2Lean/Cited/PNT.lean` (`PNT_proof`);
* `Stmt_JConv`: convergence of the Riemann sums of `(x + 1/2)^{-s}` (`Proofs/JConvergence.lean`);
* `Stmt_Translation`: the translation formula of the Volkenborn integral
  (`Proofs/Translation.lean`);
* `Stmt_Criterion`: Lai's irrationality criterion (`Proofs/Criterion.lean`);
* `Stmt_Delta`, `Stmt_DeltaFun`: the 2-adic Δ-calculus (`Proofs/DeltaCalculus.lean`,
  `Proofs/DeltaFunctions.lean`).

The five files `Zeta2Lean/Proofs/*.lean` are those of the `{7,9,11}` repository (identical apart
from the module-system header).  In this file and in them, "proof.md P1–P4", "proof.md §5" and
"proof.md §8" refer to the informal proof of the `{7,9,11}` repository (`docs/proof.md` there;
P1–P4 are the Volkenborn integral, the 2-adic zeta values, the Δ-calculus and Lai's criterion).
The same tools are (P1)–(P3) of this repository's `docs/proof.md` §1 and the criterion of its §8.
"Lai" = arXiv:2304.00816, "LSZ" = arXiv:2505.05005.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ## The prime number theorem -/

/-- **Prime number theorem**: `ψ(x) / x → 1` where `ψ = Chebyshev.psi` is the second Chebyshev
function (`ψ n = log lcm(1,…,n)`, Mathlib `Chebyshev.psi_eq_log_lcmUpto`).  Proved in
`Zeta2Lean/Cited/PNT.lean` (`Zeta2.PNT_proof`). -/
def PNT_Stmt : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)

/-! ## Volkenborn integral (proof.md P1, P2) -/

/-- The Riemann sums of `(x+1/2)^{-s}` converge (to `J s`), for every `s`. -/
def Stmt_JConv : Prop :=
  ∀ s : ℕ, HasVolkenborn (halfPow s) (J s)

/-- Translation (proof.md P1; LSZ Lemma 2.4) for `f(t) = (t+1/2)^{-s}`, `f' = -s (t+1/2)^{-s-1}`:
`∫ f(t+k) dt = ∫ f(t) dt - s ∑_{ℓ<k} (ℓ+1/2)^{-s-1}`. -/
def Stmt_Translation : Prop :=
  ∀ (s k : ℕ) (I : ℚ_[2]), HasVolkenborn (halfPow s) I →
    HasVolkenborn (fun x => halfPow s (x + k)) (I - (s : ℚ_[2]) * ∑ l ∈ range k, halfPow (s + 1) l)

/-- Lai's irrationality criterion (Lai Lemma 2.1; it is used as in proof.md §8). -/
def Stmt_Criterion : Prop :=
  ∀ (k : ℕ) (α : Fin k → ℚ_[2]) (a₀ : ℕ → ℤ) (a : ℕ → Fin k → ℤ) (B : ℕ → ℝ),
    (∀ m, |(a₀ m : ℝ)| ≤ B m) → (∀ m j, |(a m j : ℝ)| ≤ B m) →
    (∃ᶠ m in atTop, (a₀ m : ℚ_[2]) + ∑ j, (a m j : ℚ_[2]) * α j ≠ 0) →
    Tendsto (fun m => B m * ‖(a₀ m : ℚ_[2]) + ∑ j, (a m j : ℚ_[2]) * α j‖) atTop (𝓝 0) →
    ¬ ∀ j, ∃ q : ℚ, α j = q

/-! ## 2-adic Δ-calculus (proof.md P3; Lai Lemmas 2.4, 2.5; LSZ Lemmas 2.5, 2.6) -/

/-- The general Δ-calculus, in Riemann-sum form (no convergence assumptions needed). -/
structure Stmt_Delta : Prop where
  /-- Lai Lemma 2.4 (2.3), Riemann-sum form: `Δ_m(f) ≥ c ⇒ R_M ≡ R_m mod 2^{c-1}` (`M ≥ m`). -/
  riemann : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), DeltaGe m c f →
    ∀ M, m ≤ M → ‖volkenbornSum f M - volkenbornSum f m‖ ≤ (2 : ℝ) ^ (1 - c)
  /-- Lai Lemma 2.4 (2.2), Riemann-sum form: `Δ(f) ≥ c ⇒ v₂(R_M) ≥ c - 1`. -/
  riemannAll : ∀ (f : ℕ → ℚ_[2]) (c : ℤ), DeltaAll c f →
    ∀ M, ‖volkenbornSum f M‖ ≤ (2 : ℝ) ^ (1 - c)
  mono : ∀ (f : ℕ → ℚ_[2]) (m m' : ℕ) (c c' : ℤ), m ≤ m' → c' ≤ c → DeltaGe m c f → DeltaGe m' c' f
  monoAll : ∀ (f : ℕ → ℚ_[2]) (c c' : ℤ), c' ≤ c → DeltaAll c f → DeltaAll c' f
  ofAll : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), DeltaAll c f → DeltaGe m c f
  /-- Lai Lemma 2.5 / LSZ 2.6(a) (finite sums). -/
  sum : ∀ {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (m : ℕ) (c : ℤ),
    (∀ i ∈ s, DeltaGe m c (F i)) → DeltaGe m c (fun x => ∑ i ∈ s, F i x)
  sumAll : ∀ {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (c : ℤ),
    (∀ i ∈ s, DeltaAll c (F i)) → DeltaAll c (fun x => ∑ i ∈ s, F i x)
  /-- LSZ 2.6(b) (constant factor; only `≥` is needed). -/
  smul : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c e : ℤ) (a : ℚ_[2]), ‖a‖ ≤ (2 : ℝ) ^ (-e) →
    DeltaGe m c f → DeltaGe m (c + e) (fun x => a * f x)
  smulAll : ∀ (f : ℕ → ℚ_[2]) (c e : ℤ) (a : ℚ_[2]), ‖a‖ ≤ (2 : ℝ) ^ (-e) →
    DeltaAll c f → DeltaAll (c + e) (fun x => a * f x)
  /-- Lai Lemma 2.5(2) (products of `ℤ₂`-valued functions). -/
  mul : ∀ (f g : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), IntValued f → IntValued g →
    DeltaGe m c f → DeltaGe m c g → DeltaGe m c (fun x => f x * g x)
  mulAll : ∀ (f g : ℕ → ℚ_[2]) (c : ℤ), IntValued f → IntValued g →
    DeltaAll c f → DeltaAll c g → DeltaAll c (fun x => f x * g x)

/-- Δ-bounds for concrete building functions (Lai Lemma 2.5(1),(3); `binom` is (D4) of
proof.md §5).  The pair and the `ζ₂(7)` proof use only `binom`; the fields `hcoefInt` and `hcoefDelta` concern the
functions `h_β` of the `{7,9,11}` construction (`hcoef`). -/
structure Stmt_DeltaFun : Prop where
  /-- `Δ(C(t+j, N)) ≥ -⌊log₂ N⌋`. -/
  binom : ∀ j N : ℕ, DeltaAll (-(Nat.log 2 N : ℤ)) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2]))
  /-- `Δ_m(C(t+j, N)^2) ≥ 1 - ⌊log₂ N⌋` for `m > ⌊log₂ N⌋`. -/
  binomSq : ∀ j N m : ℕ, Nat.log 2 N < m →
    DeltaGe m (1 - (Nat.log 2 N : ℤ)) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2]) ^ 2)
  /-- `h_β` is `ℤ₂`-valued ... -/
  hcoefInt : ∀ n β : ℕ, IntValued (fun x => ((hcoef n β x : ℚ) : ℚ_[2]))
  /-- ... with `Δ(h_β) ≥ 0` (it is a polynomial in the `1/(2x+2k+1)` with integer coefficients). -/
  hcoefDelta : ∀ n β : ℕ, DeltaAll 0 (fun x => ((hcoef n β x : ℚ) : ℚ_[2]))

end Zeta2

end
