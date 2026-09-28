module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Zeta2Lean.Z7.Assembly — the logical skeleton of the `ζ₂(7)` theorem (complete, no gaps)

`main7_of_stmts` derives `SevenStatement` (convergence of all `J s`; `ζ₂(7)` irrational) for **any**
rates `g, δ` with `g + δ < 6.8 log 2` from
* `Stmt_JConv`, `Stmt_Criterion` (shared, proved), `Stmt_L7` (linear form), `Stmt_Valuation7`
  (Theorem V),
* `Stmt_Growth7 g` (Theorem G), `Stmt_Denominators7 δ` (Theorem A), `Stmt_Nonvanishing7`
  (Theorem N + Lai–Sprang), and PNT (only passed on to `Stmt_Denominators7`).

Argument (proof §8).  Suppose `ζ₂(7) = r` is rational.
* Eventually `D u` is odd and `A₀ = 2^{e} D ρ`, `A₁ = 2^{e} D Z` are integers (`Stmt_Denominators7`;
  the integers are taken as numerators of the rationals, so no choice is needed);
  `L_u := A₀ + A₁ ζ₂(7) = 2^{e} D · S_n` (`Stmt_L7`, `linear_form_zeta7`).
* `B_u := |A₀| + |A₁|` bounds both coefficients trivially.
* `L_u ≠ 0` frequently (`Stmt_Nonvanishing7`).
* `‖2^{e} D‖₂ = 2^{-e}` (`D` odd), so `B_u ‖L_u‖₂ = D (|ρ| + |Z|) ‖S_n‖₂
  ≤ 2c (u+1)^A e^{-(6.8 log 2 - g - δ - 2ε) 40u}` eventually (`bound_core7`), which tends to `0`
  with
  `ε = (6.8 log 2 - g - δ)/4`.
* Lai's criterion (`Stmt_Criterion` with one constant) gives the contradiction.

`margin7 : g7 + delta7 < 34/5 · log 2` checks the target constants (`0.71 + 3.99 = 4.70 < 4.71340`).
-/

set_option linter.style.longLine false

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

/-- The `J`-form of `Stmt_L7` is the `ζ₂`-form `ρ + Z ζ₂(7)` (`Z = 46080 c₃`, `ζ₂(7) = J₆/768`). -/
theorem linear_form_zeta7 (u : ℕ) :
    (rho u : ℚ_[2]) + 60 * (csum u 3 : ℚ_[2]) * J 6 = Lform u := by
  simp only [Lform, Zc, zeta2]
  push_cast
  norm_num
  ring

/-- Given `Stmt_L7`, the value `S_n` (defined by `limUnder`) is the linear form. -/
theorem Sn_eq_Lform (hL : Stmt_L7) (u : ℕ) : Sn u = Lform u := by
  have := hL u
  rw [linear_form_zeta7] at this
  exact this.volkenborn_eq

/-- The target rates satisfy the margin condition: `0.71 + 3.99 = 4.70 < 6.8 log 2 = 4.71340`. -/
theorem margin7 : g7 + delta7 < 34 / 5 * Real.log 2 := by
  have := Real.log_two_gt_d9
  unfold g7 delta7
  norm_num at this ⊢
  linarith

/-- `(x+1)^A e^{-κx} → 0` for `κ > 0`. -/
theorem tendsto_poly_mul_exp_neg7 {κ : ℝ} (hκ : 0 < κ) (A : ℕ) :
    Tendsto (fun x : ℝ => (x + 1) ^ A * Real.exp (-(κ * x))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => κ * (x + 1)) atTop atTop :=
    Tendsto.const_mul_atTop hκ (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp h1).const_mul
    ((κ ^ A)⁻¹ * Real.exp κ)
  rw [mul_zero] at h2
  refine h2.congr' (Eventually.of_forall fun x => ?_)
  have hk : κ ^ A ≠ 0 := pow_ne_zero _ hκ.ne'
  have he : Real.exp (-(κ * (x + 1))) = Real.exp (-(κ * x)) * (Real.exp κ)⁻¹ := by
    rw [show -(κ * (x + 1)) = -(κ * x) + -κ by ring, Real.exp_add, Real.exp_neg κ]
  simp only [Function.comp_apply]
  rw [he, mul_pow]
  field_simp

/-- `2^{272 u} = exp((34/5 · log 2) · 40 u)`. -/
theorem two_pow_eq_exp7 (u : ℕ) :
    (2 : ℝ) ^ (272 * u) = Real.exp (34 / 5 * Real.log 2 * (40 * (u : ℝ))) := by
  rw [show 34 / 5 * Real.log 2 * (40 * (u : ℝ)) = ((272 * u : ℕ) : ℝ) * Real.log 2 by
      push_cast; ring,
    Real.exp_nat_mul, Real.exp_log two_pos]

/-- The analytic core of the assembly: with the three bounds at one step,
`D (|ρ| + |Z|) ‖S‖₂ ≤ 2c (u+1)^A e^{-(6.8 log 2 - g - δ - 2ε) 40u}`. -/
theorem bound_core7 {g δ ε c : ℝ} {A u : ℕ} {D ρ z normI : ℝ}
    (hg : |ρ| ≤ Real.exp ((g + ε) * (40 * u)) ∧ |z| ≤ Real.exp ((g + ε) * (40 * u)))
    (hd : D ≤ Real.exp ((δ + ε) * (40 * u))) (hD0 : 0 ≤ D)
    (hv : normI * (2 : ℝ) ^ (272 * u) ≤ c * ((u : ℝ) + 1) ^ A) (hnI : 0 ≤ normI) :
    D * (|ρ| + |z|) * normI ≤
      2 * c * ((u : ℝ) + 1) ^ A *
        Real.exp (-((34 / 5 * Real.log 2 - g - δ - 2 * ε) * (40 * u))) := by
  obtain ⟨g0, g1⟩ := hg
  have hP : 0 < (2 : ℝ) ^ (272 * u) := by positivity
  have hX : |ρ| + |z| ≤ 2 * Real.exp ((g + ε) * (40 * u)) := by linarith
  have hX0 : 0 ≤ |ρ| + |z| := by positivity
  have hZ0 : 0 ≤ normI * (2 : ℝ) ^ (272 * u) := mul_nonneg hnI hP.le
  have hE0 : 0 ≤ 2 * Real.exp ((g + ε) * (40 * u)) := by positivity
  have hXY : (|ρ| + |z|) * D ≤ 2 * Real.exp ((g + ε) * (40 * u)) * Real.exp ((δ + ε) * (40 * u)) :=
    mul_le_mul hX hd hD0 hE0
  have hXYZ : (|ρ| + |z|) * D * (normI * (2 : ℝ) ^ (272 * u)) ≤
      2 * Real.exp ((g + ε) * (40 * u)) * Real.exp ((δ + ε) * (40 * u)) * (c * ((u : ℝ) + 1) ^ A) :=
    mul_le_mul hXY hv hZ0 (by positivity)
  have hE : Real.exp ((g + ε) * (40 * u)) * Real.exp ((δ + ε) * (40 * u)) =
      Real.exp (-((34 / 5 * Real.log 2 - g - δ - 2 * ε) * (40 * u))) * (2 : ℝ) ^ (272 * u) := by
    rw [two_pow_eq_exp7, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← mul_le_mul_iff_of_pos_right hP]
  calc D * (|ρ| + |z|) * normI * (2 : ℝ) ^ (272 * u)
      = (|ρ| + |z|) * D * (normI * (2 : ℝ) ^ (272 * u)) := by ring
    _ ≤ 2 * Real.exp ((g + ε) * (40 * u)) * Real.exp ((δ + ε) * (40 * u)) *
          (c * ((u : ℝ) + 1) ^ A) := hXYZ
    _ = 2 * c * ((u : ℝ) + 1) ^ A *
          (Real.exp ((g + ε) * (40 * u)) * Real.exp ((δ + ε) * (40 * u))) := by ring
    _ = 2 * c * ((u : ℝ) + 1) ^ A *
          Real.exp (-((34 / 5 * Real.log 2 - g - δ - 2 * ε) * (40 * u))) *
          (2 : ℝ) ^ (272 * u) := by rw [hE]; ring

/-- Cast of the numerator of a rational that is an integer. -/
theorem num_cast_of_eq_int7 {x : ℚ} {z : ℤ} (h : x = z) :
    ((x.num : ℤ) : ℚ_[2]) = ((x : ℚ) : ℚ_[2]) := by
  rw [h, Rat.num_intCast]
  simp

/-- Absolute value of the numerator of a rational that is an integer. -/
theorem num_abs_of_eq_int7 {x : ℚ} {z : ℤ} (h : x = z) :
    |((x.num : ℤ) : ℝ)| = |((x : ℚ) : ℝ)| := by
  rw [h, Rat.num_intCast]
  simp

/-- The 2-adic norm of `2^e D` for an odd `D`. -/
theorem norm_two_pow_mul_odd (e D : ℕ) (hD : Odd D) :
    ‖((2 : ℚ_[2]) ^ e * (D : ℚ_[2]))‖ = ((2 : ℝ) ^ e)⁻¹ := by
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := Padic.norm_p (p := 2)
    simpa using this
  have hD1 : ‖(D : ℚ_[2])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact Nat.coprime_two_left.mpr hD
  rw [norm_mul, norm_pow, h2, hD1, mul_one, inv_pow]

/-- **Assembly (proof §8).**  Any rates with `g + δ < 6.8 log 2`. -/
theorem main7_of_stmts (g δ : ℝ) (hmargin : g + δ < 34 / 5 * Real.log 2)
    (hJ : Stmt_JConv) (hL : Stmt_L7) (hVal : Stmt_Valuation7) (hCrit : Stmt_Criterion)
    (hG : Stmt_Growth7 g) (hD : Stmt_Denominators7 δ) (hNV : Stmt_Nonvanishing7)
    (hPNT : PNT_Stmt) : SevenStatement := by
  refine ⟨hJ, ?_⟩
  intro h7
  obtain ⟨D, e, hDint, hDbd⟩ := hD hPNT
  obtain ⟨c, A, hv⟩ := hVal
  have hNVf := hNV h7
  -- the value of the linear form
  have hI : ∀ u, HasVolkenborn (fun x => ((integrand u x : ℚ) : ℚ_[2])) (Lform u) := by
    intro u
    have := hL u
    rwa [linear_form_zeta7] at this
  -- the sequences of the criterion
  let α : Fin 1 → ℚ_[2] := ![zeta2 7]
  let a₀ : ℕ → ℤ := fun u => ((2 : ℚ) ^ e u * D u * rho u).num
  let a' : ℕ → Fin 1 → ℤ := fun u => ![((2 : ℚ) ^ e u * D u * Zc u).num]
  let B : ℕ → ℝ := fun u => |(a₀ u : ℝ)| + |(a' u 0 : ℝ)|
  have hform : ∀ u, (Odd (D u) ∧ (∃ z : ℤ, (2 : ℚ) ^ e u * D u * rho u = z) ∧
      ∃ z : ℤ, (2 : ℚ) ^ e u * D u * Zc u = z) →
      (a₀ u : ℚ_[2]) + ∑ j, (a' u j : ℚ_[2]) * α j =
        ((2 : ℚ_[2]) ^ e u * (D u : ℚ_[2])) * Lform u := by
    rintro u ⟨-, ⟨z0, hz0⟩, ⟨z1, hz1⟩⟩
    simp only [a₀, a', α, Fin.sum_univ_one, Matrix.cons_val_zero, Lform]
    rw [num_cast_of_eq_int7 hz0, num_cast_of_eq_int7 hz1]
    push_cast
    ring
  have hB : ∀ u, (Odd (D u) ∧ (∃ z : ℤ, (2 : ℚ) ^ e u * D u * rho u = z) ∧
      ∃ z : ℤ, (2 : ℚ) ^ e u * D u * Zc u = z) →
      B u = (2 : ℝ) ^ e u * (D u : ℝ) * (|(rho u : ℝ)| + |(Zc u : ℝ)|) := by
    rintro u ⟨-, ⟨z0, hz0⟩, ⟨z1, hz1⟩⟩
    simp only [B, a₀, a', Matrix.cons_val_zero]
    rw [num_abs_of_eq_int7 hz0, num_abs_of_eq_int7 hz1]
    push_cast
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast, abs_two]
    ring
  have hB0 : ∀ u, 0 ≤ B u := fun u => by simp only [B]; positivity
  apply hCrit 1 α a₀ a' B
  · -- `|a_{u,0}| ≤ B u`
    intro u
    have := abs_nonneg (a' u 0 : ℝ)
    simp only [B]
    linarith
  · -- `|a_{u,j}| ≤ B u`
    intro u j
    have := abs_nonneg (a₀ u : ℝ)
    fin_cases j
    simp only [B, Fin.zero_eta]
    linarith
  · -- the linear forms are frequently non-zero
    refine (hNVf.and_eventually hDint).mono fun u hu => ?_
    obtain ⟨hne, hcl⟩ := hu
    rw [hform u hcl]
    have hD0 : ((2 : ℚ_[2]) ^ e u * (D u : ℚ_[2])) ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
      exact_mod_cast (Nat.pos_of_ne_zero (fun h => by simp [h] at hcl)).ne'
    exact mul_ne_zero hD0 (hne _ (hI u))
  · -- `B u · ‖L_u‖ → 0`
    set ε : ℝ := (34 / 5 * Real.log 2 - g - δ) / 4 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hκ : 0 < 34 / 5 * Real.log 2 - g - δ - 2 * ε := by rw [hε]; linarith
    have hlim : Tendsto (fun u : ℕ => 2 * c * ((u : ℝ) + 1) ^ A *
        Real.exp (-((34 / 5 * Real.log 2 - g - δ - 2 * ε) * (40 * (u : ℝ))))) atTop (𝓝 0) := by
      have hκ' : 0 < (34 / 5 * Real.log 2 - g - δ - 2 * ε) * 40 := by positivity
      have h1 := ((tendsto_poly_mul_exp_neg7 hκ' A).comp tendsto_natCast_atTop_atTop).const_mul
        (2 * c)
      rw [mul_zero] at h1
      refine h1.congr' (Eventually.of_forall fun u => ?_)
      simp only [Function.comp_apply]
      ring_nf
    refine squeeze_zero' (Eventually.of_forall fun u => mul_nonneg (hB0 u) (norm_nonneg _)) ?_ hlim
    filter_upwards [hDint, hG ε hε0, hDbd ε hε0] with u hcl hgr hdb
    rw [hform u hcl, norm_mul, hB u hcl, norm_two_pow_mul_odd _ _ hcl.1]
    have h2e : (0 : ℝ) < (2 : ℝ) ^ e u := by positivity
    have key := bound_core7 (A := A) hgr hdb (Nat.cast_nonneg _) (hv _ _ (hI u)) (norm_nonneg _)
    calc (2 : ℝ) ^ e u * (D u : ℝ) * (|(rho u : ℝ)| + |(Zc u : ℝ)|) *
          (((2 : ℝ) ^ e u)⁻¹ * ‖Lform u‖)
        = (D u : ℝ) * (|(rho u : ℝ)| + |(Zc u : ℝ)|) * ‖Lform u‖ := by
          field_simp
      _ ≤ _ := key
  · -- `ζ₂(7)` rational
    intro j
    fin_cases j
    exact h7

end Zeta2.Z7

end
