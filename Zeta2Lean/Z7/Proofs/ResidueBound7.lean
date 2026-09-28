module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Lemmas G1–G6: the residue sizes `|r_{i,k}| ≤ poly(n) e^{n U(k/n)}`

**Status: proved (round 4)**, no gaps; `#print axioms ResidueBound7_proof` gives
`[propext, Classical.choice, Quot.sound]`; elaborates in about 6 s.  The hypothesis `Stmt_PF7` is
not needed (only the definitions of `rcoef`/`Gser` are used).  Proof outline: last section of this
docstring; helpers in namespace `Zeta2.Z7.RB7`.

gap: 'growth'.  Difficulty 5 (long but elementary real analysis; no complex analysis needed).

**Task.** Prove `Stmt_ResidueBound7` from `Stmt_PF7` (only the definition of `rcoef` is really
used): `∃ C B, ∀ u ≥ 1, ∀ i, ∀ k ≤ 40u, |r_{i,k}| ≤ C (u+1)^B exp(40u · U(k/(40u)))`.
Proved constants (proof §5): `log|r_{i,k}| ≤ n U(k/n) + log(n+1) + 14 log n + 37.44`, so
`C = e^{38} 40^{15}`, `B = 15` work.

**Informal proof** (proof §5).
* **G1 (coefficients of `G_k`).**  Route without complex analysis (recommended): write
  `G_k(ε) = (n - 2k + 2ε) ∏_β (β + ε)^{e_β}` with `β` running over the numerator values
  `c - k + 1/2` (`e = 1`, `|β| ≥ 1/2`) and the pole values `j - k` (`e = -a_j`, `|β| ≥ 1`).  The
  coefficients of `(β + ε)^{e} = β^e (1 + ε/β)^e` are dominated by those of
  `|β|^e (1 - ε/|β|)^{-|e|}`, so for `0 < ρ ≤ 1/4`,
  `|[ε^λ] G_k| ≤ (|n - 2k| + 2) · ∏_β |β|^{e_β} · ∏_β (1 - ρ/|β|)^{-|e_β|} · ρ^{-λ}`
  and `∏_β (1 - ρ/|β|)^{-|e_β|} ≤ exp(2ρ ∑ |e_β|/|β|) ≤ exp(O(log n))`.  (Alternatively Cauchy's
  estimate on `|ε| = 1/2`: `|r_{i,k}| ≤ 2^{-i} M_k`, `M_k = max_{|ε|=1/2} |R_n(-k+ε)|`.)  So it
  suffices to bound the residue-level product
  `P_k := (|n - 2k| + 2) ∏_m ∏_{c ∈ C_m} (|c - k + 1/2| + 1/2) / ∏_{j ≠ k} (|j - k| - 1/2)^{a_j}`
  (**G2**, triangle inequality) up to `poly(n)`.
* **G3 (sums versus integrals).**  With `f(y) = log|y - k|`:
  (i) `∑_{c=lo}^{hi} log(|c - k + 1/2| + 1/2) ≤ ∫_{lo}^{hi+1} f + C₃ + log(2L)`
  (`C₃ = 2(1 - log 2) + π²/72 + 2`; midpoint rule, `|f''| ≤ 1/d²`);
  (ii) `∑_{j≠k} a_j log(|j - k| - 1/2) ≥ ∫_{-1/2}^{n+1/2} ã_n f - 8(1 + log n)` (concavity on
  cells, `log(d - 1/2) ≥ log d - 1/d`, `∑ a_j/|j - k| ≤ 8 H_n`).
* **G4 (scaling)** `y = nz`: the `log n` terms combine to `(N - ∑ a_k) log n = -4 log n`, and the
  integrals become `n U(k/n)` up to **G5** (discretisation: the discrete profile `ã_n(nz)` and
  `a(z)` differ on `8` intervals of length `≤ 1/(2n)` by `1`, costing `4(1 + 1/(2n) + log 4n)`).
* **G6**: `log M_k ≤ n U(k/n) + log(n+1) + 14 log n + 37.44` for `n ≥ 40`.

**Lean hints.** `Real.log_le_sub_one_of_pos`,
`Real.add_one_le_exp`, `intervalIntegral.integral_comp_mul_left`, `integral_log` (Mathlib has
`∫ log x = x log x - x`), and monotone/concave sum–integral comparisons
(`AntitoneOn.integral_le_sum`, `MonotoneOn.sum_le_integral`) on the runs where `f` is monotone.
The pair's `Growth.lean` has window-comparison lemmas of `∑ log|t + j|` with integrals
(`norm_Rc_le`) that can be adapted to real arguments.

**Numerical check.** `python/z7_mirror.py`, section "ResidueBound7" (`max_k (log|r_{i,k}| -
n U(k/n))` against `15 log(n+1) + 38` at `n = 40 … 200`).

## The Lean proof (no integrals)

* **G1 + G2** (`tnorm`): the truncated weighted norm `‖F‖ = ∑_{λ<4} |[ε^λ] F| 2^{-λ}` is
  submultiplicative on `ℚ⟦ε⟧`; `‖C b + ε‖ = |b| + 1/2`, `‖(C b + ε)⁻¹‖ ≤ (|b| - 1/2)⁻¹` for
  `|b| ≥ 1`, and `|[ε^λ] F| ≤ 8 ‖F‖` for `λ < 4`.  Hence `|r_{i,k}| ≤ 8 P_k` with
  `P_k = (|n - 2k| + 1) ∏_m ∏_{c∈C_m} (|c - k + 1/2| + 1/2) ∏_{j≠k} (|j - k| - 1/2)^{-a_j}`.
* **G3** by telescoping instead of integrals: with `F(z) = z log|z| - z` (`Fx`) and the elementary
  inequalities `F(b-a) ≤ F(b) - F(a) ≤ (b-a) log b`, `(b-a) log a ≤ F(b) - F(a)` (`0 ≤ a ≤ b`),
  the potentials `Phi`, `Psi` (shifts of `F(· - k)`) satisfy
  `log(|c-k+1/2|+1/2) ≤ Phi(c+1) - Phi(c)` and `Psi(j+1) - Psi(j) ≤ log(|j-k|-1/2)` (`j ≠ k`),
  and differ from `F(· - k)` by `O(log n)` at the block ends.
* **G4–G6**: `40u · U(k/(40u)) = ∑_t w_t F(u p_t - k)` exactly (`∑ w_t = ∑ w_t p_t = 0`), which is
  the combination of block and pole-interval endpoints (`a_j = ∑_{l<4} [2lu ≤ j ≤ n - 2lu]`).
  Result: `log P_k ≤ n U(k/n) + 21 log(n+1) + 20`, so `C = 8 e^{20} 40^{21}`, `B = 21`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace RB7

/-! ## Part A: the antiderivative `Fx` and telescoping bounds -/

theorem Fx_neg (z : ℝ) : Fx (-z) = -Fx z := by
  unfold Fx; rw [abs_neg]; ring

theorem Fx_zero : Fx 0 = 0 := by simp [Fx]

theorem Fx_one : Fx 1 = -1 := by simp [Fx]

theorem Fx_of_nonneg {z : ℝ} (hz : 0 ≤ z) : Fx z = z * Real.log z - z := by
  unfold Fx; rw [abs_of_nonneg hz]

theorem Fx_half : Fx (1 / 2) = -Real.log 2 / 2 - 1 / 2 := by
  rw [Fx_of_nonneg (by norm_num), one_div, Real.log_inv]; ring

theorem Fx_two : Fx 2 = 2 * Real.log 2 - 2 := by
  rw [Fx_of_nonneg (by norm_num)]

/-- `F(b) - F(a) ≤ (b - a) log b` for `0 ≤ a ≤ b`. -/
theorem Fx_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Fx b - Fx a ≤ (b - a) * Real.log b := by
  have hb : 0 ≤ b := ha.trans hab
  rw [Fx_of_nonneg ha, Fx_of_nonneg hb]
  rcases ha.eq_or_lt with h | h
  · subst h
    simp only [Real.log_zero, mul_zero, sub_zero]
    linarith
  · have hb' : 0 < b := h.trans_le hab
    have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb' h)
    rw [Real.log_div hb'.ne' h.ne'] at h1
    have h2 : a * (Real.log b - Real.log a) ≤ a * (b / a - 1) :=
      mul_le_mul_of_nonneg_left h1 h.le
    have h3 : a * (b / a - 1) = b - a := by field_simp
    nlinarith

/-- `(b - a) log a ≤ F(b) - F(a)` for `0 < a ≤ b`. -/
theorem le_Fx_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Real.log a ≤ Fx b - Fx a := by
  have hb : 0 < b := ha.trans_le hab
  rw [Fx_of_nonneg ha.le, Fx_of_nonneg hb.le]
  have h1 : 1 - (b / a)⁻¹ ≤ Real.log (b / a) := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h1
  have h2 : b * (1 - a / b) ≤ b * (Real.log b - Real.log a) := mul_le_mul_of_nonneg_left h1 hb.le
  have h3 : b * (1 - a / b) = b - a := by field_simp
  nlinarith

/-- Superadditivity: `F(b - a) ≤ F(b) - F(a)` for `0 ≤ a ≤ b`. -/
theorem Fx_sub_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : Fx (b - a) ≤ Fx b - Fx a := by
  have hb : 0 ≤ b := ha.trans hab
  have hba : 0 ≤ b - a := by linarith
  rw [Fx_of_nonneg ha, Fx_of_nonneg hb, Fx_of_nonneg hba]
  have h1 : (b - a) * Real.log (b - a) ≤ (b - a) * Real.log b := by
    rcases hba.eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (by linarith)) hba
  have h2 : a * Real.log a ≤ a * Real.log b := by
    rcases ha.eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h hab) ha
  linarith

theorem neg_one_le_Fx {z : ℝ} (hz : 0 ≤ z) : -1 ≤ Fx z := by
  rw [Fx_of_nonneg hz]
  rcases hz.eq_or_lt with h | h
  · rw [← h]; simp
  · have h1 : 1 - z⁻¹ ≤ Real.log z := Real.one_sub_inv_le_log_of_pos h
    have h2 : z * (1 - z⁻¹) ≤ z * Real.log z := mul_le_mul_of_nonneg_left h1 h.le
    have h3 : z * (1 - z⁻¹) = z - 1 := by field_simp
    linarith

theorem log_two_bounds : 0.69 < Real.log 2 ∧ Real.log 2 < 0.7 := by
  constructor
  · have := Real.log_two_gt_d9; linarith
  · have := Real.log_two_lt_d9; linarith

/-- The pole cell: `F(x - 1/2) - F(x - 3/2) ≤ log(x - 1/2)` for `x = 1` or `x ≥ 2`. -/
theorem pole_cell {x : ℝ} (hx : x = 1 ∨ 2 ≤ x) :
    Fx (x - 1 / 2) - Fx (x - 3 / 2) ≤ Real.log (x - 1 / 2) := by
  rcases hx with rfl | hx
  · have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    have e2 : (1 : ℝ) - 3 / 2 = -(1 / 2) := by norm_num
    rw [e1, e2, Fx_neg, Fx_half, one_div, Real.log_inv]
    linarith
  · have := Fx_sub_le (a := x - 3 / 2) (b := x - 1 / 2) (by linarith) (by linarith)
    have e : x - 1 / 2 - (x - 3 / 2) = 1 := by ring
    rw [e, one_mul] at this
    exact this

/-- `log(|c - k + 1/2| + 1/2)`: the size of the numerator factor `c - k + 1/2 + ε` at
`|ε| = 1/2`. -/
def numTerm (k c : ℕ) : ℝ :=
  Real.log (|(c : ℝ) - k + 1 / 2| + 1 / 2)

/-- Telescoping potential of the numerator sums (`≈ F(c - k)`). -/
def Phi (k c : ℕ) : ℝ :=
  if c ≤ k then Fx ((c : ℝ) - k - 1) else Fx ((c : ℝ) - k + 1) + 2

/-- `log(|j - k| - 1/2)` for `j ≠ k` (the size of the pole factor), `0` at `j = k`. -/
def poleTerm (k j : ℕ) : ℝ :=
  if j = k then 0 else Real.log (|(j : ℝ) - k| - 1 / 2)

/-- Telescoping potential of the pole sums (`≈ F(j - k)`). -/
def Psi (k j : ℕ) : ℝ :=
  if j ≤ k then Fx ((j : ℝ) - k + 1 / 2) else Fx ((j : ℝ) - k - 3 / 2) - 2

theorem num_step (k c : ℕ) : numTerm k c ≤ Phi k (c + 1) - Phi k c := by
  rcases lt_trichotomy c k with h | rfl | h
  · have h1 : c + 1 ≤ k := h
    have hx : (1 : ℝ) ≤ (k : ℝ) - c := by
      have : ((c + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h1
      push_cast at this; linarith
    simp only [numTerm, Phi, ite_eq_left h1, ite_eq_left h.le]
    push_cast
    rw [show (c : ℝ) - k + 1 / 2 = -((k : ℝ) - c - 1 / 2) by ring, abs_neg,
      abs_of_pos (by linarith), show (k : ℝ) - c - 1 / 2 + 1 / 2 = (k : ℝ) - c by ring,
      show (c : ℝ) + 1 - k - 1 = -((k : ℝ) - c) by ring,
      show (c : ℝ) - k - 1 = -(((k : ℝ) - c) + 1) by ring, Fx_neg, Fx_neg]
    have := le_Fx_sub (a := (k : ℝ) - c) (b := (k : ℝ) - c + 1) (by linarith) (by linarith)
    rw [show (k : ℝ) - c + 1 - ((k : ℝ) - c) = 1 by ring, one_mul] at this
    linarith
  · have h1 : ¬ (c + 1 ≤ c) := by omega
    simp only [numTerm, Phi, le_refl, ite_true, ite_eq_right h1]
    push_cast
    rw [show (c : ℝ) - c + 1 / 2 = 1 / 2 by ring, show (c : ℝ) + 1 - c + 1 = 2 by ring,
      show (c : ℝ) - c - 1 = -1 by ring, Fx_neg, Fx_one, Fx_two,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num,
      Real.log_one]
    have := log_two_bounds.1
    linarith
  · have h1 : ¬ (c + 1 ≤ k) := by omega
    have h2 : ¬ (c ≤ k) := by omega
    have hy : (1 : ℝ) ≤ (c : ℝ) - k := by
      have : ((k + 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast h
      push_cast at this; linarith
    simp only [numTerm, Phi, ite_eq_right h1, ite_eq_right h2]
    push_cast
    rw [abs_of_pos (by linarith), show (c : ℝ) - k + 1 / 2 + 1 / 2 = ((c : ℝ) - k) + 1 by ring,
      show (c : ℝ) + 1 - k + 1 = ((c : ℝ) - k + 1) + 1 by ring]
    have := le_Fx_sub (a := (c : ℝ) - k + 1) (b := (c : ℝ) - k + 1 + 1) (by linarith)
      (by linarith)
    rw [show (c : ℝ) - k + 1 + 1 - ((c : ℝ) - k + 1) = 1 by ring, one_mul] at this
    linarith

theorem pole_step (k j : ℕ) : Psi k (j + 1) - Psi k j ≤ poleTerm k j := by
  rcases lt_trichotomy j k with h | rfl | h
  · have h1 : j + 1 ≤ k := h
    have hne : j ≠ k := h.ne
    have hx : (k : ℝ) - j = 1 ∨ 2 ≤ (k : ℝ) - j := by
      rcases Nat.lt_or_ge (j + 1) k with h2 | h2
      · right
        have : ((j + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast h2
        push_cast at this; linarith
      · left
        have : k = j + 1 := by omega
        subst this; push_cast; ring
    have hx1 : (1 : ℝ) ≤ (k : ℝ) - j := by rcases hx with h | h <;> linarith
    simp only [poleTerm, Psi, ite_eq_left h1, ite_eq_left h.le, ite_eq_right hne]
    push_cast
    rw [abs_sub_comm, abs_of_pos (by linarith),
      show (j : ℝ) + 1 - k + 1 / 2 = -(((k : ℝ) - j) - 3 / 2) by ring,
      show (j : ℝ) - k + 1 / 2 = -(((k : ℝ) - j) - 1 / 2) by ring, Fx_neg, Fx_neg]
    have := pole_cell hx
    linarith
  · have h1 : ¬ (j + 1 ≤ j) := by omega
    simp only [poleTerm, Psi, le_refl, ite_true, ite_eq_right h1]
    push_cast
    rw [show (j : ℝ) + 1 - j - 3 / 2 = -(1 / 2) by ring, show (j : ℝ) - j + 1 / 2 = 1 / 2 by ring,
      Fx_neg, Fx_half]
    have := log_two_bounds.2
    linarith
  · have h1 : ¬ (j + 1 ≤ k) := by omega
    have h2 : ¬ (j ≤ k) := by omega
    have hne : j ≠ k := h.ne'
    have hy : (j : ℝ) - k = 1 ∨ 2 ≤ (j : ℝ) - k := by
      rcases Nat.lt_or_ge (k + 1) j with h3 | h3
      · right
        have : ((k + 2 : ℕ) : ℝ) ≤ j := by exact_mod_cast h3
        push_cast at this; linarith
      · left
        have : j = k + 1 := by omega
        subst this; push_cast; ring
    have hy1 : (1 : ℝ) ≤ (j : ℝ) - k := by rcases hy with h | h <;> linarith
    simp only [poleTerm, Psi, ite_eq_right h1, ite_eq_right h2, ite_eq_right hne]
    push_cast
    rw [abs_of_pos (by linarith),
      show (j : ℝ) + 1 - k - 3 / 2 = ((j : ℝ) - k) - 1 / 2 by ring]
    have := pole_cell hy
    linarith

theorem num_sum (k A : ℕ) : ∀ B, A ≤ B → ∑ c ∈ Ico A B, numTerm k c ≤ Phi k B - Phi k A := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ico_succ_top hAB]
    have := num_step k B
    linarith

theorem pole_sum (k A : ℕ) : ∀ B, A ≤ B → Psi k B - Psi k A ≤ ∑ j ∈ Ico A B, poleTerm k j := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ico_succ_top hAB]
    have := pole_step k B
    linarith

theorem phi_err (k c : ℕ) :
    -Real.log (|(c : ℝ) - k| + 1) ≤ Phi k c - Fx ((c : ℝ) - k) ∧
      Phi k c - Fx ((c : ℝ) - k) ≤ Real.log (|(c : ℝ) - k| + 1) + 2 := by
  by_cases h : c ≤ k
  · have hx : (0 : ℝ) ≤ (k : ℝ) - c := by
      have : (c : ℝ) ≤ k := by exact_mod_cast h
      linarith
    simp only [Phi, ite_eq_left h]
    rw [abs_sub_comm, abs_of_nonneg hx,
      show (c : ℝ) - k - 1 = -(((k : ℝ) - c) + 1) by ring,
      show (c : ℝ) - k = -((k : ℝ) - c) by ring, Fx_neg, Fx_neg]
    have h1 := Fx_sub_le (a := (k : ℝ) - c) (b := (k : ℝ) - c + 1) hx (by linarith)
    rw [show (k : ℝ) - c + 1 - ((k : ℝ) - c) = 1 by ring, one_mul] at h1
    have h2 := Fx_sub_ge (a := (k : ℝ) - c) (b := (k : ℝ) - c + 1) hx (by linarith)
    rw [show (k : ℝ) - c + 1 - ((k : ℝ) - c) = 1 by ring, Fx_one] at h2
    have h3 : 0 ≤ Real.log ((k : ℝ) - c + 1) := Real.log_nonneg (by linarith)
    constructor <;> linarith
  · have hy : (0 : ℝ) < (c : ℝ) - k := by
      have : (k : ℝ) < c := by exact_mod_cast (not_le.mp h)
      linarith
    simp only [Phi, ite_eq_right h]
    rw [abs_of_pos hy]
    have h1 := Fx_sub_le (a := (c : ℝ) - k) (b := (c : ℝ) - k + 1) hy.le (by linarith)
    rw [show (c : ℝ) - k + 1 - ((c : ℝ) - k) = 1 by ring, one_mul] at h1
    have h2 := Fx_sub_ge (a := (c : ℝ) - k) (b := (c : ℝ) - k + 1) hy.le (by linarith)
    rw [show (c : ℝ) - k + 1 - ((c : ℝ) - k) = 1 by ring, Fx_one] at h2
    have h3 : 0 ≤ Real.log ((c : ℝ) - k + 1) := Real.log_nonneg (by linarith)
    constructor <;> linarith

theorem psi_err_lo (k A : ℕ) : Psi k A - Fx ((A : ℝ) - k) ≤ Real.log (|(A : ℝ) - k| + 1) := by
  by_cases h : A ≤ k
  · have hx : (0 : ℝ) ≤ (k : ℝ) - A := by
      have : (A : ℝ) ≤ k := by exact_mod_cast h
      linarith
    simp only [Psi, ite_eq_left h]
    rw [abs_sub_comm, abs_of_nonneg hx,
      show (A : ℝ) - k + 1 / 2 = -(((k : ℝ) - A) - 1 / 2) by ring,
      show (A : ℝ) - k = -((k : ℝ) - A) by ring, Fx_neg, Fx_neg]
    rcases Nat.lt_or_ge A k with h2 | h2
    · have hx1 : (1 : ℝ) ≤ (k : ℝ) - A := by
        have : ((A + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h2
        push_cast at this; linarith
      have h3 := Fx_sub_le (a := (k : ℝ) - A - 1 / 2) (b := (k : ℝ) - A) (by linarith)
        (by linarith)
      rw [show (k : ℝ) - A - ((k : ℝ) - A - 1 / 2) = 1 / 2 by ring] at h3
      have h4 : 0 ≤ Real.log ((k : ℝ) - A) := Real.log_nonneg hx1
      have h5 : Real.log ((k : ℝ) - A) ≤ Real.log ((k : ℝ) - A + 1) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    · have : A = k := le_antisymm h h2
      subst this
      rw [show (A : ℝ) - A - 1 / 2 = -(1 / 2) by ring, show (A : ℝ) - A = 0 by ring, Fx_neg,
        Fx_zero, Fx_half, zero_add, Real.log_one]
      have := log_two_bounds.1
      linarith
  · have hy : (0 : ℝ) < (A : ℝ) - k := by
      have : (k : ℝ) < A := by exact_mod_cast (not_le.mp h)
      linarith
    simp only [Psi, ite_eq_right h]
    rw [abs_of_pos hy]
    have h0 : 0 ≤ Real.log ((A : ℝ) - k + 1) := Real.log_nonneg (by linarith)
    rcases Nat.lt_or_ge (k + 1) A with h2 | h2
    · have hy2 : (2 : ℝ) ≤ (A : ℝ) - k := by
        have : ((k + 2 : ℕ) : ℝ) ≤ A := by exact_mod_cast h2
        push_cast at this; linarith
      have h3 := Fx_sub_ge (a := (A : ℝ) - k - 3 / 2) (b := (A : ℝ) - k) (by linarith)
        (by linarith)
      rw [show (A : ℝ) - k - ((A : ℝ) - k - 3 / 2) = 3 / 2 by ring] at h3
      have h4 := neg_one_le_Fx (z := 3 / 2) (by norm_num)
      linarith
    · have : A = k + 1 := by omega
      subst this
      push_cast
      rw [show (k : ℝ) + 1 - k - 3 / 2 = -(1 / 2) by ring, show (k : ℝ) + 1 - k = 1 by ring,
        Fx_neg, Fx_half, Fx_one]
      have := log_two_bounds.1
      have h5 : 0 ≤ Real.log (1 + 1 : ℝ) := Real.log_nonneg (by norm_num)
      linarith

theorem psi_err_hi (k B : ℕ) :
    -Real.log (|(B : ℝ) - k| + 1) - 2 ≤ Psi k (B + 1) - Fx ((B : ℝ) - k) := by
  by_cases h : B + 1 ≤ k
  · have hx1 : (1 : ℝ) ≤ (k : ℝ) - B := by
      have : ((B + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h
      push_cast at this; linarith
    simp only [Psi, ite_eq_left h]
    push_cast
    rw [abs_sub_comm, abs_of_pos (by linarith),
      show (B : ℝ) + 1 - k + 1 / 2 = -(((k : ℝ) - B) - 3 / 2) by ring,
      show (B : ℝ) - k = -((k : ℝ) - B) by ring, Fx_neg, Fx_neg]
    have h0 : 0 ≤ Real.log ((k : ℝ) - B + 1) := Real.log_nonneg (by linarith)
    rcases Nat.lt_or_ge (B + 1) k with h2 | h2
    · have hx2 : (2 : ℝ) ≤ (k : ℝ) - B := by
        have : ((B + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast h2
        push_cast at this; linarith
      have h3 := Fx_sub_ge (a := (k : ℝ) - B - 3 / 2) (b := (k : ℝ) - B) (by linarith)
        (by linarith)
      rw [show (k : ℝ) - B - ((k : ℝ) - B - 3 / 2) = 3 / 2 by ring] at h3
      have h4 := neg_one_le_Fx (z := 3 / 2) (by norm_num)
      linarith
    · have : k = B + 1 := by omega
      subst this
      push_cast
      rw [show (B : ℝ) + 1 - B - 3 / 2 = -(1 / 2) by ring, show (B : ℝ) + 1 - B = 1 by ring,
        Fx_neg, Fx_half, Fx_one]
      have := log_two_bounds.1
      have h5 : 0 ≤ Real.log (1 + 1 : ℝ) := Real.log_nonneg (by norm_num)
      linarith
  · have hy : (0 : ℝ) ≤ (B : ℝ) - k := by
      have : (k : ℝ) ≤ B := by
        have : k ≤ B := by omega
        exact_mod_cast this
      linarith
    simp only [Psi, ite_eq_right h]
    push_cast
    rw [abs_of_nonneg hy, show (B : ℝ) + 1 - k - 3 / 2 = ((B : ℝ) - k) - 1 / 2 by ring]
    rcases Nat.lt_or_ge k B with h2 | h2
    · have hy1 : (1 : ℝ) ≤ (B : ℝ) - k := by
        have : ((k + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast h2
        push_cast at this; linarith
      have h3 := Fx_sub_le (a := (B : ℝ) - k - 1 / 2) (b := (B : ℝ) - k) (by linarith)
        (by linarith)
      rw [show (B : ℝ) - k - ((B : ℝ) - k - 1 / 2) = 1 / 2 by ring] at h3
      have h4 : 0 ≤ Real.log ((B : ℝ) - k) := Real.log_nonneg hy1
      have h5 : Real.log ((B : ℝ) - k) ≤ Real.log ((B : ℝ) - k + 1) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    · have : B = k := by omega
      subst this
      rw [show (B : ℝ) - B - 1 / 2 = -(1 / 2) by ring, show (B : ℝ) - B = 0 by ring, Fx_neg,
        Fx_zero, Fx_half, zero_add, Real.log_one]
      have := log_two_bounds.1
      linarith

/-- **G3 (numerator blocks)**. -/
theorem num_block (k A B : ℕ) (hAB : A ≤ B) :
    ∑ c ∈ Ico A B, numTerm k c ≤ Fx ((B : ℝ) - k) - Fx ((A : ℝ) - k) +
      Real.log (|(B : ℝ) - k| + 1) + Real.log (|(A : ℝ) - k| + 1) + 2 := by
  have h1 := num_sum k A B hAB
  have h2 := (phi_err k B).2
  have h3 := (phi_err k A).1
  linarith

/-- **G3 (pole intervals)**. -/
theorem pole_block (k A B : ℕ) (hAB : A ≤ B) :
    Fx ((B : ℝ) - k) - Fx ((A : ℝ) - k) - Real.log (|(B : ℝ) - k| + 1) -
      Real.log (|(A : ℝ) - k| + 1) - 2 ≤ ∑ j ∈ Icc A B, poleTerm k j := by
  have h1 := pole_sum k A (B + 1) (by omega)
  rw [Finset.Ico_add_one_right_eq_Icc] at h1
  have h2 := psi_err_hi k B
  have h3 := psi_err_lo k A
  linarith

/-! ## Part B: scaling (G4, G5) -/

theorem Fx_scale {N : ℝ} (hN : 0 < N) (x : ℝ) :
    N * Fx x = Fx (N * x) - N * x * Real.log N := by
  unfold Fx
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [abs_mul, abs_of_pos hN, Real.log_mul hN.ne' (abs_ne_zero.mpr hx)]
    ring

theorem upot_scale_list (L : List (ℤ × ℕ)) {N : ℝ} (hN : 0 < N) (κ : ℝ) :
    N * (L.map fun t => (t.1 : ℝ) * Fx ((t.2 : ℝ) / 40 - κ)).sum =
      (L.map fun t => (t.1 : ℝ) * Fx (N * ((t.2 : ℝ) / 40 - κ))).sum -
        Real.log N * (L.map fun t => (t.1 : ℝ) * (N * ((t.2 : ℝ) / 40 - κ))).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [mul_add, ih, show N * ((t.1 : ℝ) * Fx ((t.2 : ℝ) / 40 - κ)) =
      (t.1 : ℝ) * (N * Fx ((t.2 : ℝ) / 40 - κ)) by ring, Fx_scale hN]
    ring

/-- `n U(k/n) = ∑_t w_t F(u p_t - k)` (`n = 40u`; the `log n` terms cancel since
`∑ w_t = ∑ w_t p_t = 0`). -/
theorem Upot_scaled (u k : ℕ) (hu : 1 ≤ u) :
    40 * (u : ℝ) * Upot ((k : ℝ) / (40 * u)) =
      (upotTerms.map fun t => (t.1 : ℝ) * Fx ((u : ℝ) * t.2 - k)).sum := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hN : (0 : ℝ) < 40 * u := by positivity
  unfold Upot
  rw [upot_scale_list upotTerms hN]
  have e : ∀ p : ℝ, 40 * (u : ℝ) * (p / 40 - k / (40 * u)) = u * p - k := by
    intro p; field_simp
  simp only [e]
  have hsum : (upotTerms.map fun t => (t.1 : ℝ) * ((u : ℝ) * t.2 - k)).sum = 0 := by
    simp [upotTerms]; ring
  rw [hsum, mul_zero, sub_zero]

theorem eta_le (m : Fin 6) : eta m ≤ 13 := by
  fin_cases m <;> simp [eta]

/-- The blocks minus the four pole intervals give `n U(k/n)`. -/
theorem blocks_poles_eq (u k : ℕ) (hu : 1 ≤ u) :
    (∑ m : Fin 6, (Fx (((40 * u - eta m * u : ℕ) : ℝ) - k) - Fx (((eta m * u : ℕ) : ℝ) - k))) -
      (∑ l ∈ range 4,
        (Fx (((40 * u - 2 * l * u : ℕ) : ℝ) - k) - Fx (((2 * l * u : ℕ) : ℝ) - k))) =
    40 * (u : ℝ) * Upot ((k : ℝ) / (40 * u)) := by
  rw [Upot_scaled u k hu]
  simp only [Fin.sum_univ_six, Finset.sum_range_succ, Finset.sum_range_zero, eta,
    ← Nat.sub_mul]
  simp [upotTerms]
  ring_nf

/-! ## Part C: the truncated norm (G1, G2) -/

/-- The truncated weighted norm `∑_{λ<4} |[ε^λ] F| 2^{-λ}`. -/
def tnorm (F : PowerSeries ℚ) : ℝ :=
  ∑ l ∈ range 4, |((coeff l F : ℚ) : ℝ)| * (1 / 2 : ℝ) ^ l

theorem tnorm_eq (F : PowerSeries ℚ) :
    tnorm F = |((coeff 0 F : ℚ) : ℝ)| + |((coeff 1 F : ℚ) : ℝ)| / 2 +
      |((coeff 2 F : ℚ) : ℝ)| / 4 + |((coeff 3 F : ℚ) : ℝ)| / 8 := by
  simp only [tnorm, Finset.sum_range_succ, Finset.sum_range_zero]; ring

theorem tnorm_nonneg (F : PowerSeries ℚ) : 0 ≤ tnorm F :=
  Finset.sum_nonneg fun l _ => by positivity

theorem coeff_le_tnorm (F : PowerSeries ℚ) {l : ℕ} (hl : l < 4) :
    |((coeff l F : ℚ) : ℝ)| ≤ 8 * tnorm F := by
  rw [tnorm_eq]
  have h0 := abs_nonneg ((coeff 0 F : ℚ) : ℝ)
  have h1 := abs_nonneg ((coeff 1 F : ℚ) : ℝ)
  have h2 := abs_nonneg ((coeff 2 F : ℚ) : ℝ)
  have h3 := abs_nonneg ((coeff 3 F : ℚ) : ℝ)
  interval_cases l <;> linarith

theorem coeff_mul_small (F G : PowerSeries ℚ) :
    coeff 0 (F * G) = coeff 0 F * coeff 0 G ∧
    coeff 1 (F * G) = coeff 0 F * coeff 1 G + coeff 1 F * coeff 0 G ∧
    coeff 2 (F * G) = coeff 0 F * coeff 2 G + coeff 1 F * coeff 1 G + coeff 2 F * coeff 0 G ∧
    coeff 3 (F * G) = coeff 0 F * coeff 3 G + coeff 1 F * coeff 2 G + coeff 2 F * coeff 1 G +
      coeff 3 F * coeff 0 G := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ]

theorem abs_add3 (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| := by gcongr; exact abs_add_le _ _

theorem abs_add4 (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| + |d| := by gcongr; exact abs_add3 _ _ _

/-- Submultiplicativity of the truncated norm. -/
theorem tnorm_mul (F G : PowerSeries ℚ) : tnorm (F * G) ≤ tnorm F * tnorm G := by
  obtain ⟨e0, e1, e2, e3⟩ := coeff_mul_small F G
  rw [tnorm_eq, tnorm_eq, tnorm_eq, e0, e1, e2, e3]
  push_cast
  set f0 := ((coeff 0 F : ℚ) : ℝ)
  set f1 := ((coeff 1 F : ℚ) : ℝ)
  set f2 := ((coeff 2 F : ℚ) : ℝ)
  set f3 := ((coeff 3 F : ℚ) : ℝ)
  set g0 := ((coeff 0 G : ℚ) : ℝ)
  set g1 := ((coeff 1 G : ℚ) : ℝ)
  set g2 := ((coeff 2 G : ℚ) : ℝ)
  set g3 := ((coeff 3 G : ℚ) : ℝ)
  have h0 : |f0 * g0| = |f0| * |g0| := abs_mul _ _
  have h1 : |f0 * g1 + f1 * g0| ≤ |f0| * |g1| + |f1| * |g0| := by
    refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
  have h2 : |f0 * g2 + f1 * g1 + f2 * g0| ≤ |f0| * |g2| + |f1| * |g1| + |f2| * |g0| := by
    refine (abs_add3 _ _ _).trans ?_; rw [abs_mul, abs_mul, abs_mul]
  have h3 : |f0 * g3 + f1 * g2 + f2 * g1 + f3 * g0| ≤
      |f0| * |g3| + |f1| * |g2| + |f2| * |g1| + |f3| * |g0| := by
    refine (abs_add4 _ _ _ _).trans ?_; rw [abs_mul, abs_mul, abs_mul, abs_mul]
  have p1 := mul_nonneg (abs_nonneg f1) (abs_nonneg g3)
  have p2 := mul_nonneg (abs_nonneg f2) (abs_nonneg g2)
  have p3 := mul_nonneg (abs_nonneg f3) (abs_nonneg g1)
  have p4 := mul_nonneg (abs_nonneg f2) (abs_nonneg g3)
  have p5 := mul_nonneg (abs_nonneg f3) (abs_nonneg g2)
  have p6 := mul_nonneg (abs_nonneg f3) (abs_nonneg g3)
  nlinarith

theorem tnorm_one : tnorm 1 = 1 := by
  rw [tnorm_eq]; simp [PowerSeries.coeff_one]

theorem tnorm_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) :
    tnorm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, tnorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tnorm_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (tnorm_mul _ _).trans (mul_le_mul_of_nonneg_left ih (tnorm_nonneg _))

theorem tnorm_pow (F : PowerSeries ℚ) (a : ℕ) : tnorm (F ^ a) ≤ tnorm F ^ a := by
  induction a with
  | zero => simp [tnorm_one]
  | succ a ih =>
    rw [pow_succ, pow_succ]
    exact (tnorm_mul _ _).trans (mul_le_mul_of_nonneg_right ih (tnorm_nonneg _))

theorem tnorm_C_add_X (b : ℚ) : tnorm (C b + X) = |(b : ℝ)| + 1 / 2 := by
  rw [tnorm_eq]; simp [PowerSeries.coeff_X]

theorem tnorm_lin (b : ℚ) : tnorm (C b + C 2 * X) = |(b : ℝ)| + 1 := by
  rw [tnorm_eq]; simp [PowerSeries.coeff_C]

theorem inv_C_add_X (b : ℚ) (hb : b ≠ 0) :
    (C b + X : PowerSeries ℚ)⁻¹ = PowerSeries.mk fun l => (-1) ^ l * b⁻¹ ^ (l + 1) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hb])]
  ext l
  rcases l with _ | l
  · simp [mul_add, hb]
  · simp only [mul_add, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_mk, PowerSeries.coeff_one]
    simp
    field_simp
    ring

theorem tnorm_inv (b : ℚ) (hb : 1 ≤ |b|) : tnorm ((C b + X)⁻¹) ≤ (|(b : ℝ)| - 1 / 2)⁻¹ := by
  have hb0 : b ≠ 0 := by
    intro h; rw [h, abs_zero] at hb; norm_num at hb
  have hB : (1 : ℝ) ≤ |(b : ℝ)| := by
    have : ((|b| : ℚ) : ℝ) = |(b : ℝ)| := Rat.cast_abs b
    rw [← this]; exact_mod_cast hb
  rw [inv_C_add_X b hb0, tnorm_eq]
  simp only [PowerSeries.coeff_mk]
  have hc : ∀ l : ℕ, |((((-1 : ℚ)) ^ l * b⁻¹ ^ (l + 1) : ℚ) : ℝ)| = |(b : ℝ)|⁻¹ ^ (l + 1) := by
    intro l; push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_inv]
  rw [hc 0, hc 1, hc 2, hc 3]
  set t := |(b : ℝ)|⁻¹ with ht_def
  have ht : t * |(b : ℝ)| = 1 := inv_mul_cancel₀ (by linarith)
  have ht0 : 0 < t := by positivity
  have hden : 0 < |(b : ℝ)| - 1 / 2 := by linarith
  rw [← one_div, le_div_iff₀ hden]
  have key : (t ^ (0 + 1) + t ^ (1 + 1) / 2 + t ^ (2 + 1) / 4 + t ^ (3 + 1) / 8) *
      (|(b : ℝ)| - 1 / 2) = 1 - t ^ 4 / 16 := by
    linear_combination (1 + t / 2 + t ^ 2 / 4 + t ^ 3 / 8) * ht
  rw [key]
  have : 0 < t ^ 4 := by positivity
  linarith

theorem inv_prod_pow {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (a : ι → ℕ) :
    (∏ j ∈ s, f j ^ a j)⁻¹ = ∏ j ∈ s, (f j)⁻¹ ^ a j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, PowerSeries.mul_inv_rev, ih,
      ← PowerSeries.inv_pow, mul_comm]

theorem one_le_abs_sub {j k : ℕ} (h : j ≠ k) : (1 : ℚ) ≤ |(j : ℚ) - k| := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have : (j : ℚ) + 1 ≤ k := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  · have : (k : ℚ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith

theorem one_le_abs_sub_real {j k : ℕ} (h : j ≠ k) : (1 : ℝ) ≤ |(j : ℝ) - k| := by
  have := one_le_abs_sub h
  have e : ((|(j : ℚ) - k| : ℚ) : ℝ) = |(j : ℝ) - k| := by push_cast; rfl
  rw [← e]; exact_mod_cast this

theorem tnorm_numSer_le (u k : ℕ) :
    tnorm (numSer u (-(k : ℚ))) ≤
      ∏ m : Fin 6, ∏ c ∈ block u m, (|(c : ℝ) - k + 1 / 2| + 1 / 2) := by
  unfold numSer
  refine (tnorm_prod _ _).trans (Finset.prod_le_prod₀ (fun m _ => tnorm_nonneg _) fun m _ => ?_)
  refine (tnorm_prod _ _).trans (le_of_eq (Finset.prod_congr rfl fun c _ => ?_))
  rw [tnorm_C_add_X]; push_cast; ring_nf

theorem tnorm_poles_le (u k : ℕ) :
    tnorm ((∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k) + X) ^ apole u j)⁻¹) ≤
      ∏ j ∈ (range (40 * u + 1)).erase k, ((|(j : ℝ) - k| - 1 / 2)⁻¹) ^ apole u j := by
  rw [inv_prod_pow]
  refine (tnorm_prod _ _).trans (Finset.prod_le_prod₀ (fun j _ => tnorm_nonneg _) fun j hj => ?_)
  refine (tnorm_pow _ _).trans (pow_le_pow_left₀ (tnorm_nonneg _) ?_ _)
  refine (tnorm_inv _ (one_le_abs_sub (Finset.ne_of_mem_erase hj))).trans (le_of_eq ?_)
  push_cast; rfl

/-- **G1 + G2**: `‖G_k‖ ≤ P_k`. -/
theorem tnorm_Gser_le (u k : ℕ) :
    tnorm (Gser u k) ≤ (|40 * (u : ℝ) - 2 * k| + 1) *
      (∏ m : Fin 6, ∏ c ∈ block u m, (|(c : ℝ) - k + 1 / 2| + 1 / 2)) *
      ∏ j ∈ (range (40 * u + 1)).erase k, ((|(j : ℝ) - k| - 1 / 2)⁻¹) ^ apole u j := by
  unfold Gser
  refine (tnorm_mul _ _).trans (mul_le_mul ?_ (tnorm_poles_le u k) (tnorm_nonneg _)
    (by positivity))
  refine (tnorm_mul _ _).trans (mul_le_mul ?_ (tnorm_numSer_le u k) (tnorm_nonneg _)
    (by positivity))
  rw [tnorm_lin]; push_cast; rfl

/-! ## Part D: G6 -/

theorem log_abs_sub_le {x k n : ℕ} (hx : x ≤ n) (hk : k ≤ n) :
    Real.log (|(x : ℝ) - k| + 1) ≤ Real.log ((n : ℝ) + 1) := by
  have hx' : (x : ℝ) ≤ n := by exact_mod_cast hx
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0x : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have h0k : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  apply Real.log_le_log (by positivity)
  have : |(x : ℝ) - k| ≤ n := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  linarith

theorem num_block_n (k A B n : ℕ) (hAB : A ≤ B) (hB : B ≤ n) (hk : k ≤ n) :
    ∑ c ∈ Ico A B, numTerm k c ≤
      Fx ((B : ℝ) - k) - Fx ((A : ℝ) - k) + 2 * Real.log ((n : ℝ) + 1) + 2 := by
  have h1 := num_block k A B hAB
  have h2 := log_abs_sub_le hB hk
  have h3 := log_abs_sub_le (hAB.trans hB) hk
  linarith

theorem pole_block_n (k A B n : ℕ) (hAB : A ≤ B) (hB : B ≤ n) (hk : k ≤ n) :
    Fx ((B : ℝ) - k) - Fx ((A : ℝ) - k) - 2 * Real.log ((n : ℝ) + 1) - 2 ≤
      ∑ j ∈ Icc A B, poleTerm k j := by
  have h1 := pole_block k A B hAB
  have h2 := log_abs_sub_le hB hk
  have h3 := log_abs_sub_le (hAB.trans hB) hk
  linarith

/-- `a_j = ∑_{l<4} [2lu ≤ j ≤ n - 2lu]`. -/
theorem apole_eq_sum (u j : ℕ) (hj : j ≤ 40 * u) :
    (apole u j : ℝ) =
      ∑ l ∈ range 4, if 2 * l * u ≤ j ∧ j ≤ 40 * u - 2 * l * u then (1 : ℝ) else 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  unfold apole
  rw [min_def]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem pole_sum_decomp (u : ℕ) (g : ℕ → ℝ) :
    ∑ j ∈ range (40 * u + 1), (apole u j : ℝ) * g j =
      ∑ l ∈ range 4, ∑ j ∈ Icc (2 * l * u) (40 * u - 2 * l * u), g j := by
  have h1 : ∀ l ∈ range 4, ∑ j ∈ Icc (2 * l * u) (40 * u - 2 * l * u), g j =
      ∑ j ∈ range (40 * u + 1), if 2 * l * u ≤ j ∧ j ≤ 40 * u - 2 * l * u then g j else 0 := by
    intro l _
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [apole_eq_sum u j (by simp only [Finset.mem_range] at hj; omega), Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/-- **G6**: `P_k ≤ e^{20} (n+1)^{21} e^{n U(k/n)}`. -/
theorem P_bound (u k : ℕ) (hu : 1 ≤ u) (hk : k ≤ 40 * u) :
    (|40 * (u : ℝ) - 2 * k| + 1) *
      (∏ m : Fin 6, ∏ c ∈ block u m, (|(c : ℝ) - k + 1 / 2| + 1 / 2)) *
      ∏ j ∈ (range (40 * u + 1)).erase k, ((|(j : ℝ) - k| - 1 / 2)⁻¹) ^ apole u j ≤
    Real.exp 20 * (((40 * u : ℕ) : ℝ) + 1) ^ 21 *
      Real.exp (40 * u * Upot ((k : ℝ) / (40 * u))) := by
  have hnum_pos : ∀ c : ℕ, 0 < |(c : ℝ) - k + 1 / 2| + 1 / 2 := fun c => by positivity
  have hpole_pos : ∀ j ∈ (range (40 * u + 1)).erase k, 0 < |(j : ℝ) - k| - 1 / 2 := by
    intro j hj
    have := one_le_abs_sub_real (Finset.ne_of_mem_erase hj)
    linarith
  set L := |40 * (u : ℝ) - 2 * k| + 1 with hL
  set NP := ∏ m : Fin 6, ∏ c ∈ block u m, (|(c : ℝ) - k + 1 / 2| + 1 / 2) with hNP
  set PP := ∏ j ∈ (range (40 * u + 1)).erase k, ((|(j : ℝ) - k| - 1 / 2)⁻¹) ^ apole u j
    with hPP
  have hLpos : 0 < L := by positivity
  have hNPpos : 0 < NP := Finset.prod_pos fun m _ => Finset.prod_pos fun c _ => hnum_pos c
  have hPPpos : 0 < PP :=
    Finset.prod_pos fun j hj => pow_pos (inv_pos.mpr (hpole_pos j hj)) _
  have hlogNP : Real.log NP = ∑ m : Fin 6, ∑ c ∈ block u m, numTerm k c := by
    rw [hNP, Real.log_prod (fun m _ => (Finset.prod_pos fun c _ => hnum_pos c).ne')]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Real.log_prod (fun c _ => (hnum_pos c).ne')]
    rfl
  have hlogPP : Real.log PP =
      -∑ l ∈ range 4, ∑ j ∈ Icc (2 * l * u) (40 * u - 2 * l * u), poleTerm k j := by
    rw [hPP, Real.log_prod (fun j hj => (pow_pos (inv_pos.mpr (hpole_pos j hj)) _).ne'),
      ← pole_sum_decomp u (poleTerm k),
      ← Finset.sum_erase (range (40 * u + 1)) (f := fun j => (apole u j : ℝ) * poleTerm k j)
        (a := k) (by simp [poleTerm]),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Real.log_pow, Real.log_inv, poleTerm, ite_eq_right (Finset.ne_of_mem_erase hj)]
    ring
  have hn1 : (1 : ℝ) ≤ ((40 * u : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((40 * u : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hlogn : 0 ≤ Real.log (((40 * u : ℕ) : ℝ) + 1) := Real.log_nonneg hn1
  have hL_le : Real.log L ≤ Real.log (((40 * u : ℕ) : ℝ) + 1) := by
    apply Real.log_le_log hLpos
    have hk' : (k : ℝ) ≤ 40 * u := by exact_mod_cast hk
    have h0k : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : |40 * (u : ℝ) - 2 * k| ≤ 40 * u := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    push_cast
    linarith
  have hnum_le : ∑ m : Fin 6, ∑ c ∈ block u m, numTerm k c ≤
      ∑ m : Fin 6, (Fx (((40 * u - eta m * u : ℕ) : ℝ) - k) - Fx (((eta m * u : ℕ) : ℝ) - k) +
        2 * Real.log (((40 * u : ℕ) : ℝ) + 1) + 2) := by
    refine Finset.sum_le_sum fun m _ => ?_
    unfold block
    have h13 := eta_le m
    have : eta m * u ≤ 13 * u := Nat.mul_le_mul_right u h13
    exact num_block_n k _ _ (40 * u) (by omega) (by omega) hk
  have hpole_ge : ∑ l ∈ range 4, (Fx (((40 * u - 2 * l * u : ℕ) : ℝ) - k) -
      Fx (((2 * l * u : ℕ) : ℝ) - k) - 2 * Real.log (((40 * u : ℕ) : ℝ) + 1) - 2) ≤
      ∑ l ∈ range 4, ∑ j ∈ Icc (2 * l * u) (40 * u - 2 * l * u), poleTerm k j := by
    refine Finset.sum_le_sum fun l hl => ?_
    have hl4 : l < 4 := Finset.mem_range.mp hl
    have : 2 * l * u ≤ 6 * u := Nat.mul_le_mul_right u (by omega)
    exact pole_block_n k _ _ (40 * u) (by omega) (by omega) hk
  have hid := blocks_poles_eq u k hu
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Finset.card_range, Fintype.card_fin, nsmul_eq_mul] at hnum_le hpole_ge hid
  have hlog : Real.log (L * NP * PP) ≤
      20 + ((21 : ℕ) : ℝ) * Real.log (((40 * u : ℕ) : ℝ) + 1) +
        40 * u * Upot ((k : ℝ) / (40 * u)) := by
    rw [Real.log_mul (by positivity) hPPpos.ne', Real.log_mul hLpos.ne' hNPpos.ne', hlogNP,
      hlogPP]
    push_cast at hnum_le hpole_ge hid hL_le ⊢
    linarith
  calc L * NP * PP = Real.exp (Real.log (L * NP * PP)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (20 + ((21 : ℕ) : ℝ) * Real.log (((40 * u : ℕ) : ℝ) + 1) +
        40 * u * Upot ((k : ℝ) / (40 * u))) := Real.exp_le_exp.mpr hlog
    _ = Real.exp 20 * (((40 * u : ℕ) : ℝ) + 1) ^ 21 *
        Real.exp (40 * u * Upot ((k : ℝ) / (40 * u))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]

/-- The coefficients of `G_k` of degree `< 4`. -/
theorem coeff_Gser_bound (u k l : ℕ) (hu : 1 ≤ u) (hk : k ≤ 40 * u) (hl : l < 4) :
    |((coeff l (Gser u k) : ℚ) : ℝ)| ≤ 8 * Real.exp 20 * 40 ^ 21 * ((u : ℝ) + 1) ^ 21 *
      Real.exp (40 * u * Upot ((k : ℝ) / (40 * u))) := by
  have h1 := coeff_le_tnorm (Gser u k) hl
  have h2 := tnorm_Gser_le u k
  have h3 := P_bound u k hu hk
  have h4 : (((40 * u : ℕ) : ℝ) + 1) ^ 21 ≤ 40 ^ 21 * ((u : ℝ) + 1) ^ 21 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  have hE : 0 < Real.exp (40 * u * Upot ((k : ℝ) / (40 * u))) := Real.exp_pos _
  have hE20 : 0 < Real.exp 20 := Real.exp_pos _
  calc |((coeff l (Gser u k) : ℚ) : ℝ)| ≤ 8 * tnorm (Gser u k) := h1
    _ ≤ 8 * (Real.exp 20 * (((40 * u : ℕ) : ℝ) + 1) ^ 21 *
          Real.exp (40 * u * Upot ((k : ℝ) / (40 * u)))) := by
      have := h2.trans h3
      linarith
    _ ≤ 8 * (Real.exp 20 * (40 ^ 21 * ((u : ℝ) + 1) ^ 21) *
          Real.exp (40 * u * Upot ((k : ℝ) / (40 * u)))) := by
      gcongr
    _ = 8 * Real.exp 20 * 40 ^ 21 * ((u : ℝ) + 1) ^ 21 *
          Real.exp (40 * u * Upot ((k : ℝ) / (40 * u))) := by ring

end RB7

/-- **Lemmas G1–G6**: `|r_{i,k}| ≤ 8 e^{20} 40^{21} (u+1)^{21} e^{n U(k/n)}` (`n = 40u`). -/
theorem ResidueBound7_proof (hPF : Stmt_PF7) : Stmt_ResidueBound7 := by
  refine ⟨8 * Real.exp 20 * 40 ^ 21, 21, ?_⟩
  intro u i k hu hk
  unfold rcoef
  split_ifs with hi
  · exact RB7.coeff_Gser_bound u k (apole u k - i) hu hk (by have := apole_le u k; omega)
  · simp only [Rat.cast_zero, abs_zero]
    positivity

end Zeta2.Z7

end
