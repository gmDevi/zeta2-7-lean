module

public import Zeta2Lean.Pair.Statements

@[expose] public section

/-!
# The Lai–Sprang condition implies nonvanishing (reduction of GAP 3 to arithmetic)

*In this repository.* This file is the pair repository's (https://github.com/gmDevi/zeta2-7-9-lean),
unchanged apart from this paragraph and the module-system header.
It is imported by `Zeta2Lean/Pair/Proofs/Nonvanishing.lean`; the `ζ₂(7)` proof uses none of
its declarations.
Its references to documents, scripts and pair files that are not included here (such as
`BLUEPRINT_PAIR.md`, `docs/proof.md`, `python/pair_mirror.py` or `Pair/Main.lean`) are to
that repository.

gap: '' (routine).  **Proved** (architect, 2026-09-24).  The audit of 2026-09-24 added the proved
subsequence lemmas `frequently_prime_forty_mul_sub_one(_gt)` (Dirichlet: `40 m - 1` prime
infinitely often) for the recommended GAP 3 route at `q = n - 1`.

**Task.** Prove
`Nonvanishing_of_LaiSprang : Stmt_L1 → Stmt_LaiSprangCond cfg → Stmt_Nonvanishing cfg`
for every configuration `cfg`.  (Lai–Sprang, arXiv:2306.10393, Lemma 2.2.)

**Informal proof.** Let `ζ₂(7) = r₇`, `ζ₂(9) = r₉` with `r₇, r₉ ∈ ℚ`; put `b = r₇.den · r₉.den ≥ 1`,
`a₇ = b r₇ ∈ ℤ`, `a₉ = b r₉ ∈ ℤ`.  Apply the condition with `B = b`: frequently there is a prime
`q > b` with `ρ₀ ≠ 0`, `(Z₇ = 0 ∨ v_q ρ₀ < v_q Z₇)`, `(Z₉ = 0 ∨ v_q ρ₀ < v_q Z₉)`.  Fix such an `m`
and a limit `I` of the Riemann sums; by `Stmt_L1` (+ `linear_form_zeta`, `HasVolkenborn.unique`)
`I = Lform = ρ₀ + Z₇ r₇ + Z₉ r₉` (cast from `ℚ`).  If `I = 0` then the rational
`ρ₀ + Z₇ r₇ + Z₉ r₉` is `0` (`Rat.cast_injective`), so `b ρ₀ = -(a₇ Z₇ + a₉ Z₉)` with both sides
non-zero.  `v_q(b ρ₀) = v_q(ρ₀)` since `q ∤ b` (`q > b`).  On the other side, every non-zero
summand `a Z` has `v_q(a Z) = v_q(a) + v_q(Z) ≥ v_q(Z) > v_q(ρ₀)` (`a ∈ ℤ ∖ {0}`; `Z ≠ 0`), and
`v_q` of a non-zero sum is at least the minimum (`padicValRat.min_le_padicValRat_add`); if one
summand vanishes the other equals the sum.  Either way `v_q(ρ₀) > v_q(ρ₀)`, contradiction.

**Lean hints.** `Rat.num_div_den`, `Rat.mul_den_eq_num`, `Rat.den_pos`, `padicValRat.mul`,
`padicValRat.neg`, `padicValRat.of_int`, `padicValRat.of_nat`, `padicValInt.eq_zero_of_not_dvd`,
`padicValNat.eq_zero_of_not_dvd`, `Nat.le_of_dvd`, `padicValRat.min_le_padicValRat_add`,
`Rat.cast_injective`, `Rat.cast_add`, `Rat.cast_mul`, `HasVolkenborn.unique`,
`linear_form_zeta` (`Pair/Assembly.lean` is *not* imported here; reprove the one-line identity or
use `Stmt_L1` directly: the limit value `ρ₀ + 60 c₃ J₆ + 210 c₅ J₈` equals
`ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9)` by `simp [Z7, Z9, zeta2]; push_cast; norm_num; ring`).
`Fact (Nat.Prime q)` instances: `haveI := Fact.mk hq`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_LaiSprangCond".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

/-- `J 6 = 768 ζ₂(7)`. -/
private theorem J6_of_zeta2 : J 6 = 768 * zeta2 7 := by
  simp only [zeta2]
  norm_num
  ring

/-- `J 8 = 4096 ζ₂(9)`. -/
private theorem J8_of_zeta2 : J 8 = 4096 * zeta2 9 := by
  simp only [zeta2]
  norm_num
  ring

/-- Valuation core of the Lai–Sprang argument. -/
private theorem ls_core {q : ℕ} [Fact q.Prime] {b : ℕ} (hb : 0 < b) (hbq : b < q)
    {ρ z7 z9 : ℚ} {a7 a9 : ℤ} (hρ : ρ ≠ 0)
    (h7 : z7 = 0 ∨ padicValRat q ρ < padicValRat q z7)
    (h9 : z9 = 0 ∨ padicValRat q ρ < padicValRat q z9)
    (key : (b : ℚ) * ρ + (a7 : ℚ) * z7 + (a9 : ℚ) * z9 = 0) : False := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hvb : padicValRat q (b : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have : ¬ q ∣ b := fun h => absurd (Nat.le_of_dvd hb h) (not_le.2 hbq)
    simp [padicValNat.eq_zero_of_not_dvd this]
  have hbρ : padicValRat q ((b : ℚ) * ρ) = padicValRat q ρ := by
    rw [padicValRat.mul hb0 hρ, hvb, zero_add]
  -- the sum of the two ζ-terms
  have hS : (a7 : ℚ) * z7 + (a9 : ℚ) * z9 = -((b : ℚ) * ρ) := by linear_combination key
  have hS0 : (a7 : ℚ) * z7 + (a9 : ℚ) * z9 ≠ 0 := by
    rw [hS]; exact neg_ne_zero.2 (mul_ne_zero hb0 hρ)
  have hvS : padicValRat q ((a7 : ℚ) * z7 + (a9 : ℚ) * z9) = padicValRat q ρ := by
    rw [hS, padicValRat.neg, hbρ]
  -- `v(a z) ≥ v(z)` for a non-zero integer `a` and `z ≠ 0`
  have hint : ∀ (a : ℤ) (z : ℚ), (a : ℚ) ≠ 0 → z ≠ 0 →
      padicValRat q z ≤ padicValRat q ((a : ℚ) * z) := by
    intro a z ha hz
    rw [padicValRat.mul ha hz, padicValRat.of_int]
    have : (0 : ℤ) ≤ (padicValInt q a : ℤ) := Int.natCast_nonneg _
    linarith
  by_cases hA : (a7 : ℚ) * z7 = 0
  · -- only the `ζ₂(9)`-term survives
    rw [hA, zero_add] at hvS hS0
    have ha9 : (a9 : ℚ) ≠ 0 := left_ne_zero_of_mul hS0
    have hz9 : z9 ≠ 0 := right_ne_zero_of_mul hS0
    have h9' := h9.resolve_left hz9
    have := hint a9 z9 ha9 hz9
    linarith
  by_cases hB : (a9 : ℚ) * z9 = 0
  · -- only the `ζ₂(7)`-term survives
    rw [hB, add_zero] at hvS hS0
    have ha7 : (a7 : ℚ) ≠ 0 := left_ne_zero_of_mul hS0
    have hz7 : z7 ≠ 0 := right_ne_zero_of_mul hS0
    have h7' := h7.resolve_left hz7
    have := hint a7 z7 ha7 hz7
    linarith
  · -- both terms are non-zero
    have hz7 : z7 ≠ 0 := right_ne_zero_of_mul hA
    have hz9 : z9 ≠ 0 := right_ne_zero_of_mul hB
    have h7' := h7.resolve_left hz7
    have h9' := h9.resolve_left hz9
    have e7 := hint a7 z7 (left_ne_zero_of_mul hA) hz7
    have e9 := hint a9 z9 (left_ne_zero_of_mul hB) hz9
    have hmin := padicValRat.min_le_padicValRat_add (p := q) hS0
    rw [hvS] at hmin
    rcases min_le_iff.1 hmin with h | h <;> linarith

theorem Nonvanishing_of_LaiSprang (cfg : Config) (hL1 : Stmt_L1) (hLS : Stmt_LaiSprangCond cfg) :
    Stmt_Nonvanishing cfg := by
  rintro ⟨r7, hr7⟩ ⟨r9, hr9⟩
  -- a common denominator `b` of `r₇, r₉`
  set b : ℕ := r7.den * r9.den with hbdef
  have hb : 0 < b := Nat.mul_pos r7.den_pos r9.den_pos
  have ha7 : (b : ℚ) * r7 = ((r7.num * r9.den : ℤ) : ℚ) := by
    rw [hbdef]
    push_cast
    rw [show ((r7.den : ℚ) * r9.den) * r7 = (r7 * r7.den) * r9.den by ring, Rat.mul_den_eq_num]
  have ha9 : (b : ℚ) * r9 = ((r9.num * r7.den : ℤ) : ℚ) := by
    rw [hbdef]
    push_cast
    rw [show ((r7.den : ℚ) * r9.den) * r9 = (r9 * r9.den) * r7.den by ring, Rat.mul_den_eq_num]
  refine (hLS b).mono fun m hm => ?_
  obtain ⟨q, hq, hbq, hρ, h7, h9⟩ := hm
  have := Fact.mk hq
  intro I hI hI0
  -- `I` is the linear form, a rational number
  have hIeq := hI.unique (hL1 (cfg.n m) (cfg.h m) (cfg.adm m))
  have hlin : (((rho0 (cfg.n m) (cfg.h m) + Z7 (cfg.n m) (cfg.h m) * r7 +
      Z9 (cfg.n m) (cfg.h m) * r9 : ℚ)) : ℚ_[2]) = 0 := by
    rw [← hI0, hIeq, J6_of_zeta2, J8_of_zeta2, hr7, hr9]
    simp only [Z7, Z9]
    push_cast
    ring
  have hlinQ : rho0 (cfg.n m) (cfg.h m) + Z7 (cfg.n m) (cfg.h m) * r7 +
      Z9 (cfg.n m) (cfg.h m) * r9 = 0 := by exact_mod_cast hlin
  refine ls_core hb hbq hρ h7 h9 (a7 := r7.num * r9.den) (a9 := r9.num * r7.den) ?_
  rw [← ha7, ← ha9]
  linear_combination (b : ℚ) * hlinQ

/-! ### The subsequence `40 m - 1` prime (audit addition, 2026-09-24)

For configuration E (`n = 40 m`) the natural Lai–Sprang prime is `q = n - 1` (`docs/proof.md`
§7, Theorem A: `v_q(ρ₀) = -9 < v_q(Z₇), v_q(Z₉)`).  Dirichlet's theorem
(Mathlib `Nat.frequently_atTop_prime_and_modEq`, primes `≡ 39 (mod 40)`) makes that subsequence
infinite. -/

/-- `40 m - 1` is prime for infinitely many `m` (Dirichlet). -/
theorem frequently_prime_forty_mul_sub_one : ∃ᶠ m in atTop, (40 * m - 1).Prime := by
  have h := Nat.frequently_atTop_prime_and_modEq (q := 40) (a := 39) (by norm_num) (by norm_num)
  rw [Filter.frequently_atTop] at h ⊢
  intro B
  obtain ⟨p, hp, hpp, hmod⟩ := h (40 * B + 40)
  have hm : p % 40 = 39 := by
    unfold Nat.ModEq at hmod
    omega
  refine ⟨(p + 1) / 40, by omega, ?_⟩
  have hq : 40 * ((p + 1) / 40) - 1 = p := by omega
  rw [hq]
  exact hpp

/-- The form used with `Stmt_LaiSprangCond configE`: for every bound `B`, frequently `40 m - 1` is
a prime `> B`. -/
theorem frequently_prime_forty_mul_sub_one_gt (B : ℕ) :
    ∃ᶠ m in atTop, (40 * m - 1).Prime ∧ B < 40 * m - 1 := by
  refine frequently_prime_forty_mul_sub_one.and_eventually ?_
  filter_upwards [eventually_ge_atTop (B + 1)] with m hm
  omega

end Zeta2.Pair

end
