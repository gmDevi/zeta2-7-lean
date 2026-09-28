module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Translation of the Volkenborn integral by a negative shift (proof (P1), centring)

gap: '' (routine, new).  **Proved** (architect, 2026-09-26).

**Task.** Prove `Stmt_TranslationNeg`: for `s, e ∈ ℕ` and `I` a limit of the Riemann sums of
`halfPow s`,
```
HasVolkenborn (fun x => halfPowZ s (x - e)) (I + s ∑_{l=1}^{e} halfPowZ (s+1) (-l)),
```
i.e. `∫ (t + 1/2 - e)^{-s} dt = ∫ (t + 1/2)^{-s} dt + s ∑_{l=1}^{e} (1/2 - l)^{-s-1}`.
(With `f(t) = (t+1/2)^{-s}`, `f' = -s (t+1/2)^{-s-1}`, this is `∫ f(t+d) = ∫ f - ∑_{l=d}^{-1} f'(l)`
for `d = -e`.)

**Proof** (the pattern of `Zeta2Lean/Proofs/Translation.lean`, which does `d ≥ 0`).
Put `f z := halfPowZ s z` (`z ∈ ℤ`), so `f x = halfPow s x` for `x ∈ ℕ`.  For `M = 2^N ≥ e`
(`tn_sum_shift`, induction on `e` with the one-step shift `tn_shift_one`):
```
∑_{x<M} f(x - e) = ∑_{x<M} f(x) + ∑_{l=1}^{e} (f(-l) - f(M - l)).
```
For fixed `l`, with `w = -l + 1/2 ≠ 0` and `h = 2^N → 0` in `ℚ_[2]`,
`2^{-N}(f(-l) - f(-l + 2^N)) = -h⁻¹((w+h)^{-s} - w^{-s}) → s w^{-s-1} = s · halfPowZ (s+1) (-l)`
(`tn_key`: the exact difference quotient `tn_diff_quot` and continuity of a polynomial in
`(w + h)⁻¹`).  Add the finitely many limits to `volkenbornSum (halfPow s) N → I`; the identity
only holds for `2^N ≥ e`, i.e. eventually (`Filter.Tendsto.congr'`).

**Numerical check.** `python/z7_mirror.py`, section "TranslationNeg / GenLinearFormZ / L7".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

/-- One step of the shift: `∑_{x<M+1} g(x - 1) = ∑_{x<M+1} g(x) + (g(-1) - g(M))`. -/
private theorem tn_shift_one (g : ℤ → ℚ_[2]) (M : ℕ) :
    ∑ x ∈ range (M + 1), g ((x : ℤ) - 1) = ∑ x ∈ range (M + 1), g x + (g (-1) - g M) := by
  rw [Finset.sum_range_succ' (fun x : ℕ => g ((x : ℤ) - 1)),
    Finset.sum_range_succ (fun x : ℕ => g (x : ℤ))]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.cast_zero, zero_sub]
  ring

/-- `∑_{x<M} f(x - e) = ∑_{x<M} f(x) + ∑_{l=1}^{e} (f(-l) - f(M - l))` for `e ≤ M`. -/
private theorem tn_sum_shift (f : ℤ → ℚ_[2]) : ∀ (e M : ℕ), e ≤ M →
    ∑ x ∈ range M, f ((x : ℤ) - e) =
      ∑ x ∈ range M, f x + ∑ l ∈ Icc 1 e, (f (-(l : ℤ)) - f ((M : ℤ) - l))
  | 0, M, _ => by simp
  | e + 1, M, he => by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have ih := tn_sum_shift f e (M' + 1) (by omega)
    have h1 := tn_shift_one (fun z => f (z - e)) M'
    have e1 : ∑ x ∈ range (M' + 1), f ((x : ℤ) - ((e + 1 : ℕ) : ℤ)) =
        ∑ x ∈ range (M' + 1), (fun z => f (z - e)) ((x : ℤ) - 1) := by
      refine sum_congr rfl fun x _ => ?_
      simp only
      congr 1
      push_cast
      ring
    have e2 : ∑ x ∈ range (M' + 1), (fun z => f (z - e)) (x : ℤ) =
        ∑ x ∈ range (M' + 1), f ((x : ℤ) - e) := rfl
    have a1 : (-1 : ℤ) - e = -((e + 1 : ℕ) : ℤ) := by push_cast; ring
    have a2 : ((M' : ℕ) : ℤ) - e = ((M' + 1 : ℕ) : ℤ) - ((e + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, h1, e2, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ e + 1)]
    simp only [a1, a2]
    ring

/-- `‖2‖ < 1` in `ℚ_[2]`. -/
private theorem tn_two_norm_lt_one : ‖(2 : ℚ_[2])‖ < 1 := by
  have h := Padic.norm_p_lt_one (p := 2)
  simpa using h

/-- `z + 1/2 ≠ 0` in `ℚ_[2]` for `z ∈ ℤ`. -/
private theorem tn_half_ne_zero (z : ℤ) : (z : ℚ_[2]) + 2⁻¹ ≠ 0 := by
  have h : ((((z : ℚ) + 2⁻¹ : ℚ)) : ℚ_[2]) = (z : ℚ_[2]) + 2⁻¹ := by push_cast; ring
  rw [← h]
  have : (z : ℚ) + 2⁻¹ ≠ 0 := by
    intro h0
    have h1 : ((2 * z + 1 : ℤ) : ℚ) = 0 := by
      push_cast
      linear_combination 2 * h0
    have h2 : (2 * z + 1 : ℤ) = 0 := by exact_mod_cast h1
    omega
  exact Rat.cast_ne_zero.mpr this

/-- Exact difference quotient of `u ↦ u^{-s}` (copied from `Proofs/Translation.lean`). -/
private theorem tn_diff_quot {K : Type*} [Field K] (u h : K) (hu : u ≠ 0)
    (huh : u + h ≠ 0) (hh : h ≠ 0) (s : ℕ) :
    h⁻¹ * ((u + h)⁻¹ ^ s - u⁻¹ ^ s) =
      -(∑ j ∈ range s, (u + h)⁻¹ ^ j * u⁻¹ ^ (s - 1 - j)) * u⁻¹ * (u + h)⁻¹ := by
  have hba : (u + h)⁻¹ - u⁻¹ = -h * u⁻¹ * (u + h)⁻¹ := by
    field_simp
    ring
  have hG := geom_sum₂_mul (u + h)⁻¹ u⁻¹ s
  have hhh : h⁻¹ * h = 1 := inv_mul_cancel₀ hh
  rw [← hG, hba]
  linear_combination
    (-(∑ j ∈ range s, (u + h)⁻¹ ^ j * u⁻¹ ^ (s - 1 - j)) * u⁻¹ * (u + h)⁻¹) * hhh

/-- For fixed `l`: `2^{-N} (f(-l) - f(2^N - l)) → s · halfPowZ (s+1) (-l)`, `f = halfPowZ s`. -/
private theorem tn_key (s l : ℕ) :
    Tendsto (fun N : ℕ => ((2 : ℚ_[2]) ^ N)⁻¹ *
        (halfPowZ s (-(l : ℤ)) - halfPowZ s (((2 ^ N : ℕ) : ℤ) - l))) atTop
      (𝓝 ((s : ℚ_[2]) * halfPowZ (s + 1) (-(l : ℤ)))) := by
  set w : ℚ_[2] := ((-(l : ℤ) : ℤ) : ℚ_[2]) + 2⁻¹ with hwdef
  have hw : w ≠ 0 := tn_half_ne_zero _
  have hpow : Tendsto (fun N : ℕ => (2 : ℚ_[2]) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one tn_two_norm_lt_one
  have hb : Tendsto (fun N : ℕ => (w + (2 : ℚ_[2]) ^ N)⁻¹) atTop (𝓝 w⁻¹) := by
    have h1 : Tendsto (fun N : ℕ => w + (2 : ℚ_[2]) ^ N) atTop (𝓝 (w + 0)) :=
      tendsto_const_nhds.add hpow
    rw [add_zero] at h1
    exact h1.inv₀ hw
  have hFc : Continuous (fun b : ℚ_[2] =>
      (∑ j ∈ range s, b ^ j * w⁻¹ ^ (s - 1 - j)) * w⁻¹ * b) := by
    fun_prop
  have hlim := (hFc.tendsto _).comp hb
  have hFu : (∑ j ∈ range s, w⁻¹ ^ j * w⁻¹ ^ (s - 1 - j)) * w⁻¹ * w⁻¹ =
      (s : ℚ_[2]) * halfPowZ (s + 1) (-(l : ℤ)) := by
    rw [geom_sum₂_self]
    unfold halfPowZ
    rw [← hwdef]
    cases s with
    | zero => simp
    | succ t =>
      simp only [add_tsub_cancel_right]
      push_cast
      ring
  have heq : ∀ N : ℕ, ((2 : ℚ_[2]) ^ N)⁻¹ *
      (halfPowZ s (-(l : ℤ)) - halfPowZ s (((2 ^ N : ℕ) : ℤ) - l)) =
      (∑ j ∈ range s, (w + (2 : ℚ_[2]) ^ N)⁻¹ ^ j * w⁻¹ ^ (s - 1 - j)) * w⁻¹ *
        (w + (2 : ℚ_[2]) ^ N)⁻¹ := by
    intro N
    have h2 : ((((2 ^ N : ℕ) : ℤ) - l : ℤ) : ℚ_[2]) + 2⁻¹ = w + (2 : ℚ_[2]) ^ N := by
      rw [hwdef]
      push_cast
      ring
    have hne : w + (2 : ℚ_[2]) ^ N ≠ 0 := by
      rw [← h2]
      exact tn_half_ne_zero _
    unfold halfPowZ
    rw [h2, ← hwdef]
    have := tn_diff_quot w ((2 : ℚ_[2]) ^ N) hw hne (pow_ne_zero _ two_ne_zero) s
    linear_combination -this
  rw [← hFu]
  exact hlim.congr (fun N => (heq N).symm)

theorem TranslationNeg_proof : Stmt_TranslationNeg := by
  intro s e I hI
  unfold HasVolkenborn at *
  have h1 : ∀ᶠ N in atTop, volkenbornSum (fun x : ℕ => halfPowZ s ((x : ℤ) - e)) N =
      volkenbornSum (halfPow s) N + ∑ l ∈ Icc 1 e, ((2 : ℚ_[2]) ^ N)⁻¹ *
        (halfPowZ s (-(l : ℤ)) - halfPowZ s (((2 ^ N : ℕ) : ℤ) - l)) := by
    filter_upwards [eventually_ge_atTop e] with N hN
    have he : e ≤ 2 ^ N := hN.trans (Nat.lt_two_pow_self).le
    unfold volkenbornSum
    rw [tn_sum_shift (halfPowZ s) e (2 ^ N) he, mul_add, Finset.mul_sum (Icc 1 e)]
    have hx : ∑ x ∈ range (2 ^ N), halfPowZ s (x : ℤ) = ∑ x ∈ range (2 ^ N), halfPow s x :=
      sum_congr rfl fun x _ => by simp [halfPowZ, halfPow]
    rw [hx]
  have h2 : I + (s : ℚ_[2]) * ∑ l ∈ Icc 1 e, halfPowZ (s + 1) (-(l : ℤ)) =
      I + ∑ l ∈ Icc 1 e, (s : ℚ_[2]) * halfPowZ (s + 1) (-(l : ℤ)) := by
    rw [Finset.mul_sum]
  rw [h2]
  exact (hI.add (tendsto_finsetSum _ fun l _ => tn_key s l)).congr' (h1.mono fun N hN => hN.symm)

end Zeta2.Z7

end
