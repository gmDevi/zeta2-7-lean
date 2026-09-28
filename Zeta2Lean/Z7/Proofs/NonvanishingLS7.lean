module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Nonvanishing from Theorem N (Lai–Sprang, Lemma 2.2; Dirichlet modulo 38)

gap: '' (routine).  **Proved** (architect).

**Task.** `Nonvanishing7_proof : Stmt_L7 → Stmt_AuxPrime7 → Stmt_Nonvanishing7`.

**Proof.** Let `ζ₂(7) = r = a/b` (`b = r.den ≥ 1`).  By Dirichlet's theorem
(`Nat.frequently_atTop_prime_and_modEq`, primes `≡ 37 (mod 38)`), for infinitely many `u` the number
`ℓ = 38u - 1` is a prime `> b` (`frequently_prime_38_sub_one_gt`).  For such `u ≥ U`
(`Stmt_AuxPrime7`): `v_ℓ(ρ) = -1` (so `ρ ≠ 0`) and `v_ℓ(Z) ≥ 0`.  If a limit `I` of the Riemann
sums were `0`, then `I = ρ + Z r` (`Stmt_L7`, `J 6 = 768 ζ₂(7)`, `HasVolkenborn.unique`) would give
the rational identity `b ρ = -a Z` with both sides non-zero; but `v_ℓ(b ρ) = -1` (`ℓ ∤ b`) while
`v_ℓ(a Z) ≥ v_ℓ(Z) ≥ 0`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

/-- `J 6 = 768 ζ₂(7)`. -/
private theorem J6_of_zeta2' : J 6 = 768 * zeta2 7 := by
  simp only [zeta2]
  norm_num
  ring

/-- `38 u - 1` is prime for infinitely many `u` (Dirichlet). -/
theorem frequently_prime_38_sub_one : ∃ᶠ u in atTop, (38 * u - 1).Prime := by
  have h := Nat.frequently_atTop_prime_and_modEq (q := 38) (a := 37) (by norm_num) (by norm_num)
  rw [Filter.frequently_atTop] at h ⊢
  intro B
  obtain ⟨p, hp, hpp, hmod⟩ := h (38 * B + 38)
  have hm : p % 38 = 37 := by
    unfold Nat.ModEq at hmod
    omega
  refine ⟨(p + 1) / 38, by omega, ?_⟩
  have hq : 38 * ((p + 1) / 38) - 1 = p := by omega
  rw [hq]
  exact hpp

/-- For every bound `B`, frequently `38 u - 1` is a prime `> B`. -/
theorem frequently_prime_38_sub_one_gt (B : ℕ) :
    ∃ᶠ u in atTop, (38 * u - 1).Prime ∧ B < 38 * u - 1 := by
  refine frequently_prime_38_sub_one.and_eventually ?_
  filter_upwards [eventually_ge_atTop (B + 1)] with u hu
  omega

/-- The valuation core: `b ρ + a Z = 0` is impossible when `v_ℓ(ρ) = -1`, `v_ℓ(Z) ≥ 0`, `ℓ > b`. -/
private theorem ls_core7 {ℓ : ℕ} [Fact ℓ.Prime] {b : ℕ} (hb : 0 < b) (hbℓ : b < ℓ) {ρ z : ℚ}
    {a : ℤ} (hρ : padicValRat ℓ ρ = -1) (hz : 0 ≤ padicValRat ℓ z)
    (key : (b : ℚ) * ρ + (a : ℚ) * z = 0) : False := by
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, padicValRat.zero] at hρ
    omega
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hvb : padicValRat ℓ (b : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have : ¬ ℓ ∣ b := fun h => absurd (Nat.le_of_dvd hb h) (not_le.2 hbℓ)
    simp [padicValNat.eq_zero_of_not_dvd this]
  have hbρ : padicValRat ℓ ((b : ℚ) * ρ) = -1 := by
    rw [padicValRat.mul hb0 hρ0, hvb, hρ]
    norm_num
  have hS : (a : ℚ) * z = -((b : ℚ) * ρ) := by linear_combination key
  have hS0 : (a : ℚ) * z ≠ 0 := by
    rw [hS]
    exact neg_ne_zero.2 (mul_ne_zero hb0 hρ0)
  have ha0 : (a : ℚ) ≠ 0 := left_ne_zero_of_mul hS0
  have hz0 : z ≠ 0 := right_ne_zero_of_mul hS0
  have hv : padicValRat ℓ ((a : ℚ) * z) = -1 := by
    rw [hS, padicValRat.neg, hbρ]
  rw [padicValRat.mul ha0 hz0, padicValRat.of_int] at hv
  have : (0 : ℤ) ≤ (padicValInt ℓ a : ℤ) := Int.natCast_nonneg _
  omega

theorem Nonvanishing7_proof (hL : Stmt_L7) (hA : Stmt_AuxPrime7) : Stmt_Nonvanishing7 := by
  rintro ⟨r, hr⟩
  obtain ⟨U, hU⟩ := hA
  set b : ℕ := r.den with hbdef
  have hb : 0 < b := r.den_pos
  have ha : (b : ℚ) * r = (r.num : ℚ) := by
    rw [hbdef, mul_comm]
    exact Rat.mul_den_eq_num r
  refine ((frequently_prime_38_sub_one_gt b).and_eventually (eventually_ge_atTop U)).mono
    fun u hu => ?_
  obtain ⟨⟨hℓ, hbℓ⟩, hUu⟩ := hu
  have := Fact.mk hℓ
  obtain ⟨hρ, hz⟩ := hU u hUu hℓ
  intro I hI hI0
  -- `I` is the linear form, a rational number
  have hIeq := hI.unique (hL u)
  have hlin : (((rho u + Zc u * r : ℚ)) : ℚ_[2]) = 0 := by
    rw [← hI0, hIeq, J6_of_zeta2', hr]
    simp only [Zc]
    push_cast
    ring
  have hlinQ : rho u + Zc u * r = 0 := by exact_mod_cast hlin
  refine ls_core7 hb hbℓ hρ hz (a := r.num) ?_
  rw [← ha]
  linear_combination (b : ℚ) * hlinQ

end Zeta2.Z7

end
