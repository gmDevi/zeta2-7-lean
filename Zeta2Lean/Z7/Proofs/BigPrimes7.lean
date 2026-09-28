module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Theorem C: no prime `q > n` divides the odd denominator (proof §4.7)

gap: 'denominators'.  Difficulty 3.  No dependencies.

**Task.** Prove `Stmt_BigPrimes7`: for an odd prime `q > n = 40u`, `eq7 u q = 0`, i.e.
`v_q(ρ) ≥ 0` and `v_q(Z) ≥ 0`.

**Informal proof** (proof Theorem C).
* Pole differences `|k' - k| ≤ n < q`, the linear factor `n - 2k` (`|·| ≤ n`, or `0` at `k = n/2`,
  where `G = 2ε H`), and the values `h ∈ H_k` (`|2h| ≤ n - 1 < q`) are `q`-units.
* Numerator values `2(c - k) + 1` may be divisible by `q`; they enter
  `G_k(ε) = G_k(0) ∏_β (1 + ε/β)^{e_β}` with `e_β ≥ 0`, and `G_k(0)` contains `β^{e_β}`.  So
  `G_k(0) · C(e_β, j_β) β^{-j_β}` is `q`-integral for `j_β ≤ e_β` and vanishes for `j_β > e_β`
  (Lemma D2 of the pair): every `r_{i,k} ∈ ℤ_(q)`.
* Hence every `X(k, h) ∈ ℤ_(q)` (`h` a unit), `ρ = -∑ sgn ∑ X ∈ ℤ_(q)` (`rho u = -rhoP u`), and
  `c₃ ∈ ℤ_(q)`, `Z = 46080 c₃ ∈ ℤ_(q)`; `padicValNat q den = 0` for both.
(Also a corollary of `Stmt_ThmK7` with the trivial kernel for `q ≥ 29`, `x = n/q < 1`: there are no
bad pairs and every per-pole level is `≥ 0`.)

**Lean proof (as formalised).**  No absorption is needed: the numerator factors
`(c - k + 1/2) + ε` of `G_k` are polynomials with `q`-integral coefficients (`q ≠ 2`), the linear
factor `(n - 2k) + 2ε` too, and the pole product `∏_{j ≠ k} ((j - k) + ε)^{a_j}` is inverted
factor by factor, `((j-k) + ε)⁻¹ = (j-k)⁻¹ ∑ (-ε/(j-k))^l` with `j - k` a `q`-unit.  So every
coefficient of `Gser u k` (`k ≤ n`) is `q`-integral (`Gser_int`), hence every `rcoef`
(`rcoef_int`).  The centred `A`-sums involve only `(2l+1)/2` with `0 < |2l+1| < q`
(`AhalfZ_int`), so `rho u` and `Zc u = 46080 c₃` are `q`-integral, and `padicValNat q den = 0`
(`den_val_zero`).

**Lean hints.** The pair's `Zeta2Lean/Pair/Proofs/Denominators.lean`: `PSB` (power series with
`q`-bounded coefficients), `numFactor_PSB`, `poles_PSB`, `rho_bound_big` (the analogue for the pair,
`q > n`, with "absorption" of the numerator factors), `int_of_padicNorm_le_one`.

**Numerical check.** `python/z7_mirror.py`, section "BigPrimes7 / SmallPrimes7 / Emin7".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace BigPrimes7

variable {q : ℕ} [hq : Fact q.Prime]

/-! ### `q`-adic norm helpers -/

lemma pn_pow (x : ℚ) (n : ℕ) : padicNorm q (x ^ n) = padicNorm q x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma pn_inv (x : ℚ) : padicNorm q x⁻¹ = (padicNorm q x)⁻¹ := by
  have := padicNorm.div (p := q) 1 x
  rw [one_div, padicNorm.one, one_div] at this
  exact this

lemma pn_two (hq2 : q ≠ 2) : padicNorm q (2 : ℚ) = 1 := by
  have h := (padicNorm.nat_eq_one_iff (p := q) 2).2 (by
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 hdvd
    exact hq2 this)
  exact_mod_cast h

/-- A non-zero integer of absolute value `< q` is a `q`-unit. -/
lemma pn_int_unit (z : ℤ) (hz0 : z ≠ 0) (h1 : -(q : ℤ) < z) (h2 : z < q) :
    padicNorm q (z : ℚ) = 1 := by
  rw [padicNorm.int_eq_one_iff]
  rintro ⟨c, hc⟩
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.out.pos
  subst hc
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have : (q : ℤ) * c ≤ -(q : ℤ) := by nlinarith
    omega
  · subst hc; simp at hz0
  · have : (q : ℤ) ≤ (q : ℤ) * c := by nlinarith
    omega

lemma pn_mul_le_one {a b : ℚ} (ha : padicNorm q a ≤ 1) (hb : padicNorm q b ≤ 1) :
    padicNorm q (a * b) ≤ 1 := by
  rw [padicNorm.mul]
  calc padicNorm q a * padicNorm q b ≤ 1 * 1 :=
        mul_le_mul ha hb (padicNorm.nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma pn_sum_le_one {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, padicNorm q (f i) ≤ 1) : padicNorm q (∑ i ∈ s, f i) ≤ 1 :=
  padicNorm.sum_le' h zero_le_one

/-- `q`-integral rationals have a denominator prime to `q`. -/
lemma den_val_zero (r : ℚ) (h : padicNorm q r ≤ 1) : padicValNat q r.den = 0 := by
  by_contra hne
  have hvden : 1 ≤ padicValNat q r.den := Nat.one_le_iff_ne_zero.2 hne
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hne
    simp at hne
  have hvnum : padicValInt q r.num = 0 := by
    rcases Rat.num_or_den_zero_padicVal r hq.out with h0 | h0
    · exact h0
    · omega
  have hv : padicValRat q r ≤ -1 := by
    rw [padicValRat_def, hvnum]
    omega
  rw [padicNorm.eq_zpow_of_nonzero hr0] at h
  have hp1 : (1 : ℚ) < q := by exact_mod_cast hq.out.one_lt
  have : (1 : ℚ) < (q : ℚ) ^ (-padicValRat q r) := one_lt_zpow₀ hp1 (by omega)
  linarith

/-! ### Power series with `q`-integral coefficients -/

/-- All coefficients are `q`-integral. -/
def PI (q : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ j : ℕ, padicNorm q (coeff j F) ≤ 1

lemma PI.mul {F G : PowerSeries ℚ} (hF : PI q F) (hG : PI q G) : PI q (F * G) := by
  intro j
  rw [coeff_mul]
  exact pn_sum_le_one _ _ fun p _ => pn_mul_le_one (hF _) (hG _)

omit hq in
lemma PI.one : PI q (1 : PowerSeries ℚ) := by
  intro j
  rw [coeff_one]
  split_ifs
  · simp
  · simp

lemma PI.prod {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ) (hF : ∀ i ∈ s, PI q (F i)) :
    PI q (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PI.one
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact PI.mul (hF a (mem_insert_self a s)) (ih fun i hi => hF i (mem_insert_of_mem hi))

lemma PI.pow {F : PowerSeries ℚ} (hF : PI q F) (n : ℕ) : PI q (F ^ n) := by
  have := PI.prod (range n) (fun _ => F) (fun _ _ => hF)
  simpa using this

omit hq in
lemma PI.lin {a b : ℚ} (ha : padicNorm q a ≤ 1) (hb : padicNorm q b ≤ 1) :
    PI q (C a + C b * X) := by
  intro j
  rcases j with _ | _ | j
  · simpa using ha
  · simpa using hb
  · have : coeff (j + 2) (C a + C b * X : PowerSeries ℚ) = 0 := by
      rw [map_add, coeff_C, coeff_C_mul, coeff_X]
      simp
    rw [this, padicNorm.zero]
    exact zero_le_one

omit hq in
lemma PI.lin1 {a : ℚ} (ha : padicNorm q a ≤ 1) : PI q (C a + X) := by
  have := PI.lin (q := q) (b := 1) ha (by rw [padicNorm.one])
  rwa [map_one, one_mul] at this

/-- `(β + ε)⁻¹ = β⁻¹ ∑_j (-1/β)^j ε^j`. -/
lemma inv_C_add_X (β : ℚ) (hβ : β ≠ 0) :
    (C β + X : PowerSeries ℚ)⁻¹ = C β⁻¹ * PowerSeries.mk (fun j => (-1 / β) ^ j) := by
  set G : PowerSeries ℚ := PowerSeries.mk fun j => (-1 / β) ^ j with hG
  have hGmul : G * (C β + X) = C β := by
    have h1 : G * (C β + X) = C β * G + G * X := by ring
    rw [h1]
    ext j
    rcases j with _ | j
    · simp [hG]
    · rw [map_add, coeff_C_mul, coeff_succ_mul_X, coeff_C]
      simp only [hG, coeff_mk, Nat.succ_ne_zero, ite_false]
      have hce : β * (-1 / β) = -1 := by field_simp
      calc β * (-1 / β) ^ (j + 1) + (-1 / β) ^ j
          = (-1 / β) ^ j * (β * (-1 / β) + 1) := by ring
        _ = 0 := by rw [hce]; ring
  have hconst : constantCoeff (C β + X : PowerSeries ℚ) ≠ 0 := by simp [hβ]
  rw [PowerSeries.inv_eq_iff_mul_eq_one hconst, mul_assoc, hGmul, ← map_mul,
    inv_mul_cancel₀ hβ, map_one]

lemma PI.inv_unit {β : ℚ} (hβ : padicNorm q β = 1) : PI q (C β + X)⁻¹ := by
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, padicNorm.zero] at hβ
    exact zero_ne_one hβ
  intro j
  rw [inv_C_add_X β hβ0, coeff_C_mul, coeff_mk, padicNorm.mul, pn_pow, pn_inv,
    padicNorm.div, padicNorm.neg, padicNorm.one, hβ]
  simp

lemma prod_inv' {ι : Type*} (s : Finset ι) (φ : ι → PowerSeries ℚ) :
    (∏ j ∈ s, φ j)⁻¹ = ∏ j ∈ s, (φ j)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, PowerSeries.mul_inv_rev, ih, mul_comm]

/-! ### `G_k` and the `r_{i,k}` -/

lemma pn_half_int (hq2 : q ≠ 2) (z : ℤ) : padicNorm q ((z : ℚ) + 1 / 2) ≤ 1 := by
  have e : ((z : ℚ) + 1 / 2) = ((2 * z + 1 : ℤ) : ℚ) / 2 := by push_cast; ring
  rw [e, padicNorm.div, pn_two hq2, div_one]
  exact padicNorm.of_int _

lemma numSer_int (hq2 : q ≠ 2) (u k : ℕ) : PI q (numSer u (-(k : ℚ))) := by
  unfold numSer
  apply PI.prod
  intro m _
  apply PI.prod
  intro c _
  apply PI.lin1
  have e : (-(k : ℚ) + 1 / 2 + (c : ℚ)) = (((c : ℤ) - k : ℤ) : ℚ) + 1 / 2 := by push_cast; ring
  rw [e]
  exact pn_half_int hq2 _

lemma Gser_int (hq2 : q ≠ 2) (u k : ℕ) (hk : k ≤ 40 * u) (hu : 40 * u < q) :
    PI q (Gser u k) := by
  unfold Gser
  refine PI.mul (PI.mul (PI.lin ?_ ?_) (numSer_int hq2 u k)) ?_
  · have := padicNorm.of_int (p := q) (((40 * u : ℕ) : ℤ) - 2 * k)
    push_cast at this ⊢
    exact this
  · rw [pn_two hq2]
  · rw [prod_inv']
    simp only [← PowerSeries.inv_pow]
    apply PI.prod
    intro j hj
    apply PI.pow
    apply PI.inv_unit
    have hjk := Finset.ne_of_mem_erase hj
    have hjn := mem_range.1 (Finset.mem_of_mem_erase hj)
    have e : ((j : ℚ) - k) = (((j : ℤ) - k : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    apply pn_int_unit
    · omega
    · omega
    · omega

lemma rcoef_int (hq2 : q ≠ 2) (u : ℕ) (hu : 40 * u < q) (i k : ℕ) :
    padicNorm q (rcoef u i k) ≤ 1 := by
  unfold rcoef
  split_ifs with h
  · exact Gser_int hq2 u k h.2.2 hu _
  · rw [padicNorm.zero]; exact zero_le_one

/-! ### The centred `A`-sums -/

lemma AhalfZ_int (hq2 : q ≠ 2) (d : ℤ) (s : ℕ) (h1 : 2 * d ≤ q) (h2 : -(2 * d) ≤ q) :
    padicNorm q (AhalfZ d s) ≤ 1 := by
  have hqodd : (q : ℤ) ≠ 2 * d ∧ (q : ℤ) ≠ -(2 * d) := by
    rcases hq.out.eq_two_or_odd' with h | h
    · exact absurd h hq2
    · obtain ⟨m, hm⟩ := h
      constructor <;> omega
  unfold AhalfZ
  split_ifs with hd
  · apply pn_sum_le_one
    intro l hl
    have hl' := mem_range.1 hl
    have hld : (l : ℤ) < d := by omega
    rw [pn_pow, pn_inv]
    have e : ((l : ℚ) + 1 / 2) = ((2 * l + 1 : ℤ) : ℚ) / 2 := by push_cast; ring
    rw [e, padicNorm.div, pn_two hq2, div_one, pn_int_unit _ (by omega) (by omega) (by omega)]
    simp
  · rw [padicNorm.neg]
    apply pn_sum_le_one
    intro l hl
    have hl' := mem_Icc.1 hl
    have hld : (l : ℤ) ≤ -d := by omega
    rw [pn_pow, pn_inv]
    have e : ((1 : ℚ) / 2 - l) = ((1 - 2 * l : ℤ) : ℚ) / 2 := by push_cast; ring
    rw [e, padicNorm.div, pn_two hq2, div_one, pn_int_unit _ (by omega) (by omega) (by omega)]
    simp

lemma poch_int (i : ℕ) : padicNorm q ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) ≤ 1 := by
  have := padicNorm.of_nat (p := q) (i * (i + 1) * (i + 2) * (i + 3))
  push_cast at this
  exact this

lemma rho_int (hq2 : q ≠ 2) (u : ℕ) (hu : 40 * u < q) : padicNorm q (rho u) ≤ 1 := by
  unfold rho genRhoZ
  rw [padicNorm.neg]
  apply pn_sum_le_one
  intro i _
  apply pn_sum_le_one
  intro k hk
  have hk' := mem_range.1 hk
  refine pn_mul_le_one (pn_mul_le_one (poch_int i) (rcoef_int hq2 u hu i k)) ?_
  apply AhalfZ_int hq2
  · push_cast; omega
  · push_cast; omega

lemma Zc_int (hq2 : q ≠ 2) (u : ℕ) (hu : 40 * u < q) : padicNorm q (Zc u) ≤ 1 := by
  unfold Zc csum genCsum
  refine pn_mul_le_one ?_ (pn_sum_le_one _ _ fun k _ => rcoef_int hq2 u hu 3 k)
  have := padicNorm.of_nat (p := q) 46080
  exact_mod_cast this

end BigPrimes7

open BigPrimes7 in
theorem BigPrimes7_proof : Stmt_BigPrimes7 := by
  intro u q hq hq2 hu
  have := Fact.mk hq
  unfold eq7
  rw [den_val_zero _ (rho_int hq2 u hu), den_val_zero _ (Zc_int hq2 u hu)]
  rfl

end Zeta2.Z7

end
