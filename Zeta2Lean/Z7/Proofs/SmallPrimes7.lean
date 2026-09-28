module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Lemma 4.9: small primes, `e_q(n) ≤ 19 ⌊log_q(2n+1)⌋`

gap: 'denominators'.  Difficulty 4.  No dependencies.

**Task.** Prove `Stmt_SmallPrimes7`: for every odd prime `q` and every `u`,
`eq7 u q ≤ 19 · Nat.log q (80u + 1)` (`λ₁ = ⌊log_q(2n+1)⌋`).

**Informal proof** (proof Lemma 4.9).
* *Taylor factors.* `G_k(ε) = G_k(0) ∏_β (1 + ε/β)^{e_β}` (for `k = n/2`: `G = 2εH`), `β ∈ ½ℤ ∖ 0`,
  `|2β| ≤ 2n + 1`, so `v_q(β) ≤ λ₁` and Lemma D2 gives `v_q([ε^λ] ∏) ≥ -λ λ₁`.
* *Terms.* For `h ∈ H_k`, `|2h| < n`; `X(k,h) = 24 [ε^{a-1}] G_k(ε)(h - ε)^{-5}` and
  `[ε^r](h - ε)^{-5} = C(r+4, 4) h^{-5-r}`: `v_q(X(k,h)) ≥ s_k - 8λ₁`, `v_q(r_{3,k}) ≥ s_k - λ₁`,
  where `s_k := v_q(G_k(0))`.
* *The constant term.* `s_k ≥ ∑_{e ≥ 1} [∑_m ⌊L_m/q^e⌋ - ∑_ℓ ⌊|I_ℓ|/q^e⌋] - 4⌊log_q n⌋`:
  the `L_m` numerator values of block `m` are consecutive odd numbers (`q`-part `≥ v_q(L_m!)`); for
  each level `ℓ` with `I_ℓ ∩ ℤ = [α, β]` the pole product `∏_{k'∈[α,β], k'≠k} |k' - k|` is
  `(β-α)!/C(β-α, k-α)` or `|I_ℓ|! · C(β-k, |I_ℓ|)` (or the mirror), whose `q`-part is
  `≤ v_q(|I_ℓ|!) + ⌊log_q n⌋` (Kummer).  Each bracket is an integer `> -6 - 4/q^e` (`∑ L_m = N`,
  `∑ |I_ℓ| = N + 4`), so `≥ -6` (`≥ -7` for `q = 3`), and it vanishes once `q^e > n + 1`.  So
  `s_k ≥ -10 λ₁` (`-11 λ₁` for `q = 3`).
* Hence `v_q(ρ) ≥ -18 λ₁` (`-19 λ₁` for `q = 3`) and `v_q(Z) ≥ v_q(c₃) ≥ -12 λ₁`.

**Lean hints.** The pair's `Denominators.lean` has the same kind of argument (`Wlev_ge`,
`card_odd_dvd`, `cntQ_ge`, `Eexp_le_small`: `E_q ≤ 15 ⌊log_q 2n⌋`), `pn_factorial`,
`Nat.Prime.multiplicity_choose` / `padicValNat_choose` (Kummer), `padicValNat_factorial`
(Legendre).

**Numerical check.** `python/z7_mirror.py`, section "BigPrimes7 / SmallPrimes7 / Emin7" (the
worst ratio `e_q / (19 λ₁)` is `≈ 0.4`).

**Lean proof (as formalised).**  Put `M = λ₁ = Nat.log q (80u+1)`, so `2n + 1 < q^{M+1}`.  No
factorials and no Kummer are needed: all valuations are handled level by level.
* `PSV q M L F`: the `r`-th coefficient of `F` has `v_q ≥ L - M r` (closed under products, powers,
  finite products).  Every factor of `Gser u k` is controlled: the linear factor `(n - 2k) + 2ε`
  with `L = 0` (this covers the centre `k = n/2` too, no division by `2ε` is needed), a numerator
  factor `(c - k + 1/2) + ε` with `L = cnt(2(c-k)+1)`, an inverted pole factor `((j-k) + ε)⁻¹` with
  `L = -cnt(j-k)`, where `cnt z = #{e ∈ [1, M] : q^e ∣ z}` is the capped valuation (it equals
  `v_q(j - k)` for the poles since `|j - k| ≤ n < q^{M+1}`).  So `v_q(r_{i,k}) ≥ W_k - M(a_k - i)`
  with `W_k = ∑_{m,c} cnt(2(c-k)+1) - ∑_{j ≠ k} a_j cnt(j-k)` (`Gser_PSV`, `rcoef_val`).
* `W_k = ∑_{e=1}^{M} Lev(q^e)` (`Wk_eq`, swap the sums), and every level has `Lev(Q) ≥ -10`
  (`Lev_ge`, `Q` odd): `Q · #(numerator multiples in block m) ≥ L_m - Q` (`card_odd_ge`,
  `L_m = (40 - 2η_m)u`, `∑ L_m = 136u`), and, writing `a_j = ∑_{ℓ<4} [2ℓu ≤ j ≤ n - 2ℓu]`,
  `Q · #(pole multiples in level ℓ) ≤ (n - 4ℓu) + Q` (`card_dvd_le`, `∑_ℓ (n - 4ℓu) = 136u`);
  so `Q · Lev ≥ -10Q`.  Hence `W_k ≥ -10M` (`Wk_ge`), also for `q = 3`.
* `v_q(AhalfZ d s) ≥ -sM` (`|2l+1| < 2n + 1`), so every term of `rho` has
  `v_q ≥ -10M - M(a_k - i) - M(i + 4) ≥ -18M` (`rho_val`) and `v_q(Z) ≥ -11M` (`Zc_val`); then
  `den_le` gives `eq7 u q ≤ 18M ≤ 19M`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace SmallPrimes7

variable {q : ℕ} [hqF : Fact q.Prime]

/-! ### `ValGe` calculus -/

theorem q_gt_one : (1 : ℚ) < q := by exact_mod_cast hqF.out.one_lt

theorem q_ne_zero : (q : ℚ) ≠ 0 := by exact_mod_cast hqF.out.ne_zero

omit hqF in
theorem zpow_q_nonneg (L : ℤ) : (0 : ℚ) ≤ (q : ℚ) ^ L := zpow_nonneg (by positivity) _

omit hqF in
theorem valGe_zero (L : ℤ) : ValGe q L 0 := by
  unfold ValGe
  rw [padicNorm.zero]
  exact zpow_q_nonneg _

omit hqF in
theorem valGe_neg {L : ℤ} {x : ℚ} (h : ValGe q L x) : ValGe q L (-x) := by
  unfold ValGe at *
  rwa [padicNorm.neg]

theorem valGe_add {L : ℤ} {x y : ℚ} (hx : ValGe q L x) (hy : ValGe q L y) :
    ValGe q L (x + y) :=
  le_trans padicNorm.nonarchimedean (max_le hx hy)

theorem valGe_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {L : ℤ}
    (h : ∀ i ∈ s, ValGe q L (f i)) : ValGe q L (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valGe_zero L
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact valGe_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem valGe_mul {L M N : ℤ} {x y : ℚ} (hx : ValGe q L x) (hy : ValGe q M y) (hN : L + M = N) :
    ValGe q N (x * y) := by
  unfold ValGe at *
  rw [padicNorm.mul, ← hN, neg_add, zpow_add₀ q_ne_zero]
  exact mul_le_mul hx hy (padicNorm.nonneg _) (zpow_q_nonneg _)

theorem valGe_mono {L M : ℤ} {x : ℚ} (h : ValGe q L x) (hML : M ≤ L) : ValGe q M x :=
  h.trans (zpow_le_zpow_right₀ q_gt_one.le (by omega))

theorem valGe_int (z : ℤ) : ValGe q 0 (z : ℚ) := by
  unfold ValGe
  simpa using padicNorm.of_int (p := q) z

theorem valGe_one : ValGe q 0 (1 : ℚ) := by
  simpa using valGe_int (q := q) 1

theorem valGe_pow {L : ℤ} {x : ℚ} (h : ValGe q L x) (n : ℕ) : ValGe q (n * L) (x ^ n) := by
  induction n with
  | zero => simpa using valGe_one (q := q)
  | succ n ih =>
    rw [pow_succ]
    exact valGe_mul ih h (by push_cast; ring)

theorem valGe_iff {L : ℤ} {x : ℚ} (hx : x ≠ 0) : ValGe q L x ↔ L ≤ padicValRat q x := by
  unfold ValGe
  rw [padicNorm.eq_zpow_of_nonzero hx, zpow_le_zpow_iff_right₀ q_gt_one]
  omega

theorem valGe_poch (i : ℕ) : ValGe q 0 ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) := by
  have e : ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) =
      (((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℤ) : ℚ) := by push_cast; ring
  rw [e]
  exact valGe_int _

theorem pn_two (hq2 : q ≠ 2) : padicNorm q (2 : ℚ) = 1 := by
  have h := (padicNorm.nat_eq_one_iff (p := q) 2).2 (by
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq hqF.out Nat.prime_two).1 hdvd
    exact hq2 this)
  exact_mod_cast h

theorem valGe_div_two (hq2 : q ≠ 2) {L : ℤ} {x : ℚ} : ValGe q L (x / 2) ↔ ValGe q L x := by
  unfold ValGe
  rw [padicNorm.div, pn_two hq2, div_one]

/-- `v_q(x) ≥ T` with `T ≤ 0` bounds the exponent of `q` in the denominator of `x` by `-T`. -/
theorem den_le {T : ℤ} {x : ℚ} (hT : T ≤ 0) (h : ValGe q T x) :
    (padicValNat q x.den : ℤ) ≤ -T := by
  by_cases hx : x = 0
  · subst hx
    simp
    omega
  by_cases hd : q ∣ x.den
  · have hnum : ¬ q ∣ x.num.natAbs := fun hn => by
      have h1 := Nat.dvd_gcd hn hd
      rw [x.reduced.gcd_eq_one] at h1
      exact hqF.out.one_lt.ne' (Nat.dvd_one.mp h1)
    have hv : padicValRat q x = -(padicValNat q x.den : ℤ) := by
      rw [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnum]
      simp
    rw [valGe_iff hx] at h
    omega
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    simp
    omega

/-! ### Capped valuations `cnt z = #{e ∈ [1, M] : q^e ∣ z}` -/

/-- `#{e ∈ [1, M] : q^e ∣ z}`, i.e. `min(v_q(z), M)` for `z ≠ 0`. -/
def cnt (q M : ℕ) (z : ℤ) : ℕ :=
  #{e ∈ Icc 1 M | (q : ℤ) ^ e ∣ z}

theorem cnt_eq (M : ℕ) {z : ℤ} (hz : z ≠ 0) : cnt q M z = min (padicValInt q z) M := by
  unfold cnt
  have hfilt : {e ∈ Icc 1 M | (q : ℤ) ^ e ∣ z} = Icc 1 (min (padicValInt q z) M) := by
    ext e
    simp only [mem_filter, mem_Icc, padicValInt_dvd_iff, hz, false_or, le_min_iff]
    omega
  rw [hfilt, Nat.card_Icc, Nat.add_sub_cancel]

omit hqF in
theorem cnt_le (M : ℕ) (z : ℤ) : cnt q M z ≤ M := by
  unfold cnt
  calc #{e ∈ Icc 1 M | (q : ℤ) ^ e ∣ z} ≤ #(Icc 1 M) := card_filter_le _ _
    _ = M := by simp

omit hqF in
theorem cnt_cast (M : ℕ) (z : ℤ) :
    (cnt q M z : ℤ) = ∑ e ∈ Icc 1 M, (if (q : ℤ) ^ e ∣ z then (1 : ℤ) else 0) := by
  unfold cnt
  rw [sum_boole]

omit hqF in
/-- A non-zero integer of absolute value `< q^{M+1}` has `v_q ≤ M`. -/
theorem padicValInt_le {z : ℤ} (hz : z ≠ 0) (M : ℕ) (hlt : z.natAbs < q ^ (M + 1)) :
    padicValInt q z ≤ M := by
  by_contra hv
  have hv' : M + 1 ≤ padicValInt q z := by omega
  have h1 : ((q : ℤ) ^ (M + 1)) ∣ z := (pow_dvd_pow (q : ℤ) hv').trans (padicValInt_dvd z)
  have h2 := Int.natAbs_dvd_natAbs.2 h1
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
  have := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h2
  omega

/-- Numerator values: `v_q(z/2) ≥ cnt z`. -/
theorem valGe_half (hq2 : q ≠ 2) (M : ℕ) {z : ℤ} (hz : z ≠ 0) :
    ValGe q (cnt q M z) ((z : ℚ) / 2) := by
  rw [valGe_div_two hq2, valGe_iff (by exact_mod_cast hz), padicValRat.of_int, cnt_eq M hz]
  exact_mod_cast Nat.min_le_left _ _

/-- Pole values: `v_q(z⁻¹) = -cnt z` when `0 < |z| < q^{M+1}`. -/
theorem valGe_inv_cnt (M : ℕ) {z : ℤ} (hz : z ≠ 0) (hlt : z.natAbs < q ^ (M + 1)) :
    ValGe q (-(cnt q M z : ℤ)) ((z : ℚ)⁻¹) := by
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [valGe_iff (inv_ne_zero hz'), padicValRat.inv, padicValRat.of_int, cnt_eq M hz,
    min_eq_left (padicValInt_le hz M hlt)]

/-- `v_q(z⁻¹) ≥ -M` when `0 < |z| < q^{M+1}`. -/
theorem valGe_inv_M (M : ℕ) {z : ℤ} (hz : z ≠ 0) (hlt : z.natAbs < q ^ (M + 1)) :
    ValGe q (-(M : ℤ)) ((z : ℚ)⁻¹) := by
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [valGe_iff (inv_ne_zero hz'), padicValRat.inv, padicValRat.of_int]
  have := padicValInt_le hz M hlt
  omega

/-- `v_q((z/2)⁻¹) ≥ -M` when `0 < |z| < q^{M+1}`. -/
theorem valGe_half_inv (M : ℕ) {z : ℤ} (hz : z ≠ 0) (hlt : z.natAbs < q ^ (M + 1)) :
    ValGe q (-(M : ℤ)) (((z : ℚ) / 2)⁻¹) := by
  rw [inv_div, div_eq_mul_inv]
  have h2 : ValGe q 0 (2 : ℚ) := by simpa using valGe_int (q := q) 2
  exact valGe_mul h2 (valGe_inv_M M hz hlt) (by ring)

/-! ### Power series with graded coefficient valuations -/

/-- `v_q([ε^r] F) ≥ L - M r` for every `r`. -/
def PSV (q M : ℕ) (L : ℤ) (F : PowerSeries ℚ) : Prop :=
  ∀ r : ℕ, ValGe q (L - M * r) (coeff r F)

theorem PSV.mul {M : ℕ} {L₁ L₂ : ℤ} {F G : PowerSeries ℚ} (hF : PSV q M L₁ F)
    (hG : PSV q M L₂ G) : PSV q M (L₁ + L₂) (F * G) := by
  intro r
  rw [coeff_mul]
  apply valGe_sum
  intro p hp
  have hpr := mem_antidiagonal.1 hp
  refine valGe_mul (hF p.1) (hG p.2) ?_
  rw [← hpr]
  push_cast
  ring

theorem PSV.one {M : ℕ} : PSV q M 0 (1 : PowerSeries ℚ) := by
  intro r
  rw [coeff_one]
  split_ifs with h
  · subst h
    simpa using valGe_one (q := q)
  · exact valGe_zero _

theorem PSV.prod {ι : Type*} (s : Finset ι) {M : ℕ} (L : ι → ℤ) (F : ι → PowerSeries ℚ)
    (hF : ∀ i ∈ s, PSV q M (L i) (F i)) : PSV q M (∑ i ∈ s, L i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (PSV.one (q := q) (M := M))
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact PSV.mul (hF a (mem_insert_self a s)) (ih fun i hi => hF i (mem_insert_of_mem hi))

theorem PSV.pow {M : ℕ} {L : ℤ} {F : PowerSeries ℚ} (hF : PSV q M L F) (n : ℕ) :
    PSV q M (n * L) (F ^ n) := by
  have := PSV.prod (range n) (fun _ => L) (fun _ => F) (fun _ _ => hF)
  simpa using this

omit hqF in
theorem PSV.lin {M : ℕ} {L : ℤ} {a b : ℚ} (ha : ValGe q L a) (hb : ValGe q (L - M) b) :
    PSV q M L (C a + C b * X) := by
  intro r
  rcases r with _ | _ | r
  · simpa using ha
  · simpa using hb
  · have : coeff (r + 2) (C a + C b * X : PowerSeries ℚ) = 0 := by
      rw [map_add, coeff_C, coeff_C_mul, coeff_X]
      simp
    rw [this]
    exact valGe_zero _

omit hqF in
/-- `(β + ε)⁻¹ = β⁻¹ ∑_j (-1/β)^j ε^j`. -/
theorem inv_C_add_X (β : ℚ) (hβ : β ≠ 0) :
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

theorem PSV.inv {M : ℕ} {L : ℤ} {β : ℚ} (hβ : β ≠ 0) (h1 : ValGe q L β⁻¹)
    (h2 : ValGe q (-(M : ℤ)) β⁻¹) : PSV q M L (C β + X)⁻¹ := by
  intro r
  rw [inv_C_add_X β hβ, coeff_C_mul, coeff_mk]
  have e : (-1 / β) ^ r = (-1) ^ r * (β⁻¹) ^ r := by
    rw [div_eq_mul_inv, mul_pow]
  rw [e]
  have hm1 : ValGe q 0 ((-1 : ℚ) ^ r) := by
    have := valGe_pow (valGe_int (q := q) (-1)) r
    simpa using this
  exact valGe_mul h1 (valGe_mul hm1 (valGe_pow h2 r) rfl) (by ring)

omit hqF in
theorem prod_inv' {ι : Type*} (s : Finset ι) (φ : ι → PowerSeries ℚ) :
    (∏ j ∈ s, φ j)⁻¹ = ∏ j ∈ s, (φ j)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, PowerSeries.mul_inv_rev, ih, mul_comm]

/-! ### The factors of `G_k` -/

theorem num_PSV (hq2 : q ≠ 2) (M k c : ℕ) :
    PSV q M (cnt q M (2 * ((c : ℤ) - k) + 1)) (C (-(k : ℚ) + 1 / 2 + (c : ℚ)) + X) := by
  have e : (C (-(k : ℚ) + 1 / 2 + (c : ℚ)) + X : PowerSeries ℚ) =
      C (((2 * ((c : ℤ) - k) + 1 : ℤ) : ℚ) / 2) + C 1 * X := by
    rw [map_one, one_mul]
    congr 2
    push_cast
    ring
  rw [e]
  apply PSV.lin (valGe_half hq2 M (by omega))
  apply valGe_mono (valGe_one (q := q))
  have := cnt_le (q := q) M (2 * ((c : ℤ) - k) + 1)
  omega

theorem pole_PSV (M j k : ℕ) (hjk : j ≠ k) (hlt : ((j : ℤ) - k).natAbs < q ^ (M + 1)) :
    PSV q M (-(cnt q M ((j : ℤ) - k) : ℤ)) (C ((j : ℚ) - k) + X)⁻¹ := by
  have hz : ((j : ℤ) - k) ≠ 0 := by omega
  have e : ((j : ℚ) - k) = (((j : ℤ) - k : ℤ) : ℚ) := by push_cast; ring
  have hz' : ((j : ℚ) - k) ≠ 0 := by rw [e]; exact_mod_cast hz
  apply PSV.inv hz'
  · rw [e]
    exact valGe_inv_cnt M hz hlt
  · rw [e]
    exact valGe_inv_M M hz hlt

theorem lin_PSV (M u k : ℕ) : PSV q M 0 (C (((40 * u : ℕ) : ℚ) - 2 * k) + C 2 * X) := by
  apply PSV.lin
  · have e : (((40 * u : ℕ) : ℚ) - 2 * k) = ((((40 * u : ℕ) : ℤ) - 2 * k : ℤ) : ℚ) := by
      push_cast
      ring
    rw [e]
    exact valGe_int _
  · have h2 : ValGe q 0 (2 : ℚ) := by simpa using valGe_int (q := q) 2
    apply valGe_mono h2
    omega

/-- The exponent `W_k`: numerator multiples of `q^e` minus the weighted pole multiples, `e ≤ M`. -/
def Wk (u q M k : ℕ) : ℤ :=
  ∑ m : Fin 6, ∑ c ∈ block u m, (cnt q M (2 * ((c : ℤ) - k) + 1) : ℤ) -
    ∑ j ∈ (range (40 * u + 1)).erase k, (apole u j : ℤ) * (cnt q M ((j : ℤ) - k) : ℤ)

/-- The coefficients of `G_k` (`k ≤ n`): `v_q([ε^r] G_k) ≥ W_k - M r`. -/
theorem Gser_PSV (hq2 : q ≠ 2) {u M : ℕ} (hM : 80 * u + 1 < q ^ (M + 1)) (k : ℕ)
    (hk : k ≤ 40 * u) : PSV q M (Wk u q M k) (Gser u k) := by
  have hnum : PSV q M (∑ m : Fin 6, ∑ c ∈ block u m, (cnt q M (2 * ((c : ℤ) - k) + 1) : ℤ))
      (numSer u (-(k : ℚ))) := by
    unfold numSer
    apply PSV.prod
    intro m _
    apply PSV.prod
    intro c _
    exact num_PSV hq2 M k c
  have hpole : PSV q M (∑ j ∈ (range (40 * u + 1)).erase k,
      (apole u j : ℤ) * (-(cnt q M ((j : ℤ) - k) : ℤ)))
      (∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k) + X) ^ apole u j)⁻¹ := by
    rw [prod_inv']
    simp only [← PowerSeries.inv_pow]
    apply PSV.prod
    intro j hj
    have hjk := ne_of_mem_erase hj
    have hjn := mem_range.1 (mem_of_mem_erase hj)
    exact PSV.pow (pole_PSV M j k hjk (by omega)) _
  have h := PSV.mul (PSV.mul (lin_PSV (q := q) M u k) hnum) hpole
  have hW : 0 + ∑ m : Fin 6, ∑ c ∈ block u m, (cnt q M (2 * ((c : ℤ) - k) + 1) : ℤ) +
      ∑ j ∈ (range (40 * u + 1)).erase k, (apole u j : ℤ) * (-(cnt q M ((j : ℤ) - k) : ℤ)) =
      Wk u q M k := by
    unfold Wk
    simp only [mul_neg, sum_neg_distrib]
    ring
  rw [hW] at h
  unfold Gser
  exact h

/-! ### Counting multiples -/

omit hqF in
/-- `Q` odd: among `Q` consecutive integers `c ≥ a` one has `Q ∣ 2(c - k) + 1`. -/
theorem exists_odd_dvd (a k Q : ℕ) (hQ : Odd Q) :
    ∃ t0 : ℕ, a ≤ t0 ∧ t0 < a + Q ∧ (Q : ℤ) ∣ 2 * ((t0 : ℤ) - k) + 1 := by
  obtain ⟨s, hs⟩ := hQ
  have hQs : (Q : ℤ) = 2 * s + 1 := by exact_mod_cast hs
  have hQpos : (0 : ℤ) < (Q : ℤ) := by omega
  set D : ℤ := (k : ℤ) + s - a with hD
  set r : ℤ := D % (Q : ℤ) with hr
  set X' : ℤ := D / (Q : ℤ) with hX'
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hQpos.ne'
  have hr1 : r < Q := Int.emod_lt_of_pos _ hQpos
  have hdec : r + (Q : ℤ) * X' = D := Int.emod_add_mul_ediv D (Q : ℤ)
  refine ⟨a + r.toNat, by omega, by omega, ⟨1 - 2 * X', ?_⟩⟩
  have e : (((a + r.toNat : ℕ) : ℤ)) = (a : ℤ) + r := by
    push_cast
    rw [Int.toNat_of_nonneg hr0]
  rw [e]
  linear_combination 2 * hdec + 2 * hD - hQs

omit hqF in
/-- `Q` odd: `Q · #{c ∈ [a, b) : Q ∣ 2(c - k) + 1} ≥ (b - a) - Q`. -/
theorem card_odd_ge (a b k Q : ℕ) (hQ : Odd Q) (hab : a ≤ b) :
    (b : ℤ) - a - Q ≤
      Q * (#((Ico a b).filter (fun c : ℕ => (Q : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) : ℤ) := by
  have hQpos : 0 < Q := hQ.pos
  obtain ⟨t0, h1, h2, h3⟩ := exists_odd_dvd a k Q hQ
  have hsub : (range ((b - a) / Q)).image (fun i => t0 + i * Q) ⊆
      (Ico a b).filter (fun c : ℕ => (Q : ℤ) ∣ 2 * ((c : ℤ) - k) + 1) := by
    intro c hc
    rw [mem_image] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    rw [mem_range] at hi
    have h4 : (i + 1) * Q ≤ (b - a) / Q * Q := Nat.mul_le_mul_right _ hi
    have h5 : (b - a) / Q * Q ≤ b - a := Nat.div_mul_le_self _ _
    have h6 : (i + 1) * Q = i * Q + Q := by ring
    rw [mem_filter, mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have e : 2 * (((t0 + i * Q : ℕ) : ℤ) - k) + 1 =
        (2 * ((t0 : ℤ) - k) + 1) + (Q : ℤ) * (2 * i) := by
      push_cast
      ring
    rw [e]
    exact dvd_add h3 (dvd_mul_right _ _)
  have hinj : Set.InjOn (fun i => t0 + i * Q) (range ((b - a) / Q) : Set ℕ) := by
    intro x _ y _ hxy
    have : x * Q = y * Q := by simpa using hxy
    exact Nat.eq_of_mul_eq_mul_right hQpos this
  have hcard := card_le_card hsub
  rw [card_image_of_injOn hinj, card_range] at hcard
  have h5 : b - a < (b - a) / Q * Q + Q := Nat.lt_div_mul_add hQpos
  have h7 : (b - a) / Q * Q ≤
      #((Ico a b).filter (fun c : ℕ => (Q : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) * Q :=
    Nat.mul_le_mul_right _ hcard
  generalize (b - a) / Q * Q = P at h5 h7
  generalize #((Ico a b).filter (fun c : ℕ => (Q : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) = N at h7 ⊢
  have h9 : ((b - a : ℕ) : ℤ) < (P : ℤ) + Q := by exact_mod_cast h5
  have h10 : (P : ℤ) ≤ (N : ℤ) * Q := by exact_mod_cast h7
  rw [Nat.cast_sub hab] at h9
  linarith

omit hqF in
/-- `Q · #S ≤ (β - α) + Q` for a set `S ⊆ [α, β]` inside one residue class modulo `Q`. -/
theorem card_dvd_le (S : Finset ℕ) (α β k Q : ℕ) (hQ : 0 < Q) (hαβ : α ≤ β)
    (hS : ∀ j ∈ S, α ≤ j ∧ j ≤ β ∧ (Q : ℤ) ∣ (j : ℤ) - k) :
    (Q : ℤ) * S.card ≤ (β : ℤ) - α + Q := by
  rcases S.eq_empty_or_nonempty with hE | hne
  · subst hE
    simp
    omega
  · set x := S.min' hne with hx
    have hxS := hS x (S.min'_mem hne)
    have hsub : S ⊆ (range ((β - x) / Q + 1)).image (fun t => x + t * Q) := by
      intro j hj
      obtain ⟨h1, h2, h3⟩ := hS j hj
      have hxj : x ≤ j := S.min'_le j hj
      have hdvd : (Q : ℤ) ∣ ((j - x : ℕ) : ℤ) := by
        rw [Nat.cast_sub hxj]
        have := dvd_sub h3 hxS.2.2
        rwa [show ((j : ℤ) - k) - ((x : ℤ) - k) = (j : ℤ) - x by ring] at this
      obtain ⟨t, ht⟩ := Int.natCast_dvd_natCast.1 hdvd
      have hcomm : t * Q = Q * t := mul_comm t Q
      rw [mem_image]
      refine ⟨t, mem_range.2 ?_, ?_⟩
      · have h4 : t * Q ≤ β - x := by omega
        have := (Nat.le_div_iff_mul_le hQ).2 h4
        omega
      · omega
    have hc := (card_le_card hsub).trans card_image_le
    rw [card_range] at hc
    have h5 : (β - x) / Q * Q ≤ β - x := Nat.div_mul_le_self _ _
    have h6 : S.card * Q ≤ (β - x) / Q * Q + Q := by
      calc S.card * Q ≤ ((β - x) / Q + 1) * Q := Nat.mul_le_mul_right _ hc
        _ = (β - x) / Q * Q + Q := by ring
    have hxα : α ≤ x := hxS.1
    have hxβ : x ≤ β := hxS.2.1
    generalize (β - x) / Q * Q = P at h5 h6
    have h7 : S.card * Q ≤ β - α + Q := by omega
    have h8 : ((S.card * Q : ℕ) : ℤ) ≤ ((β - α + Q : ℕ) : ℤ) := by exact_mod_cast h7
    push_cast [Nat.cast_sub hαβ] at h8
    linarith

/-! ### One level `Q = q^e` of `W_k` -/

/-- The level-`Q` part of `W_k`: numerator multiples of `Q` minus the `a_j`-weighted pole
multiples. -/
def Lev (u Q k : ℕ) : ℤ :=
  ∑ m : Fin 6, (#((block u m).filter (fun c : ℕ => (Q : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) : ℤ) -
    ∑ j ∈ (range (40 * u + 1)).erase k,
      (apole u j : ℤ) * (if (Q : ℤ) ∣ (j : ℤ) - k then 1 else 0)

omit hqF in
/-- Every level loses at most `10` (`Q` odd). -/
theorem Lev_ge (u Q k : ℕ) (hQ : Odd Q) : -10 ≤ Lev u Q k := by
  have hQpos : 0 < Q := hQ.pos
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQpos
  have heta : ∀ m, eta m ≤ 13 := by decide
  set A := ∑ m : Fin 6,
    (#((block u m).filter (fun c : ℕ => (Q : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) : ℤ) with hAdef
  set B := ∑ j ∈ (range (40 * u + 1)).erase k,
    (apole u j : ℤ) * (if (Q : ℤ) ∣ (j : ℤ) - k then 1 else 0) with hBdef
  -- numerator multiples
  have hA : (136 * u : ℤ) - 6 * Q ≤ Q * A := by
    have hm : ∀ m : Fin 6, (40 * u : ℤ) - 2 * ((eta m : ℤ) * u) - Q ≤
        Q * (#((block u m).filter (fun c : ℕ => (Q : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) : ℤ) := by
      intro m
      have he := Nat.mul_le_mul_right u (heta m)
      have := card_odd_ge (eta m * u) (40 * u - eta m * u) k Q hQ (by omega)
      have hcast : ((40 * u - eta m * u : ℕ) : ℤ) = 40 * u - (eta m : ℤ) * u := by
        have : ((eta m * u : ℕ) : ℤ) = (eta m : ℤ) * u := by push_cast; ring
        omega
      unfold block
      rw [hcast] at this
      push_cast at this
      linarith
    rw [hAdef, mul_sum]
    refine le_trans (le_of_eq ?_) (sum_le_sum fun m _ => hm m)
    simp [Fin.sum_univ_six, eta]
    ring
  -- pole multiples
  set F := ((range (40 * u + 1)).erase k).filter (fun j : ℕ => (Q : ℤ) ∣ (j : ℤ) - k) with hF
  have hB : Q * B ≤ 136 * u + 4 * Q := by
    have hB1 : B = ∑ j ∈ F, (apole u j : ℤ) := by
      rw [hBdef, hF, sum_filter]
      apply sum_congr rfl
      intro j _
      split_ifs <;> simp
    have hB2 : ∀ j ∈ F, (apole u j : ℤ) = ∑ l ∈ range 4,
        (if 2 * (l * u) ≤ j ∧ j + 2 * (l * u) ≤ 40 * u then (1 : ℤ) else 0) := by
      intro j hj
      have hjn : j ≤ 40 * u := by
        rw [hF, mem_filter, mem_erase, mem_range] at hj
        omega
      simp only [sum_range_succ, sum_range_zero, apole]
      split_ifs <;> omega
    have hcount : ∀ l ∈ range 4,
        (Q : ℤ) * (#(F.filter (fun j : ℕ => 2 * (l * u) ≤ j ∧ j + 2 * (l * u) ≤ 40 * u)) : ℤ) ≤
          40 * u - 4 * ((l : ℤ) * u) + Q := by
      intro l hl
      have hl3 : l ≤ 3 := by rw [mem_range] at hl; omega
      have hlu : l * u ≤ 3 * u := Nat.mul_le_mul_right _ hl3
      have := card_dvd_le (F.filter (fun j : ℕ => 2 * (l * u) ≤ j ∧ j + 2 * (l * u) ≤ 40 * u))
        (2 * (l * u)) (40 * u - 2 * (l * u)) k Q hQpos (by omega) (fun j hj => by
          rw [mem_filter, hF, mem_filter] at hj
          exact ⟨hj.2.1, by omega, hj.1.2⟩)
      have hcast : ((40 * u - 2 * (l * u) : ℕ) : ℤ) = 40 * u - 2 * ((l : ℤ) * u) := by
        have : ((l * u : ℕ) : ℤ) = (l : ℤ) * u := by push_cast; ring
        omega
      rw [hcast] at this
      push_cast at this
      linarith
    rw [hB1, sum_congr rfl hB2, sum_comm, mul_sum]
    simp only [sum_boole]
    calc ∑ l ∈ range 4, (Q : ℤ) *
          (#(F.filter (fun j : ℕ => 2 * (l * u) ≤ j ∧ j + 2 * (l * u) ≤ 40 * u)) : ℤ)
        ≤ ∑ l ∈ range 4, (40 * u - 4 * ((l : ℤ) * u) + Q) := sum_le_sum hcount
      _ = 136 * u + 4 * Q := by
        simp [sum_range_succ]
        ring
  unfold Lev
  rw [← hAdef, ← hBdef]
  by_contra hcon
  have h11 : A - B ≤ -11 := by omega
  have : (Q : ℤ) * (A - B) ≤ Q * (-11) := mul_le_mul_of_nonneg_left h11 hQ'.le
  nlinarith

omit hqF in
theorem card_cast {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (#(s.filter p) : ℤ) = ∑ x ∈ s, (if p x then (1 : ℤ) else 0) := by
  rw [sum_boole]

omit hqF in
/-- `W_k = ∑_{e=1}^{M} Lev(q^e)`. -/
theorem Wk_eq (u M k : ℕ) : Wk u q M k = ∑ e ∈ Icc 1 M, Lev u (q ^ e) k := by
  have h1 : ∀ m : Fin 6, ∑ c ∈ block u m, (cnt q M (2 * ((c : ℤ) - k) + 1) : ℤ) =
      ∑ e ∈ Icc 1 M, (#((block u m).filter
        (fun c : ℕ => ((q ^ e : ℕ) : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) : ℤ) := by
    intro m
    simp only [cnt_cast, card_cast, Nat.cast_pow]
    exact sum_comm
  have h1' : ∑ m : Fin 6, ∑ c ∈ block u m, (cnt q M (2 * ((c : ℤ) - k) + 1) : ℤ) =
      ∑ e ∈ Icc 1 M, ∑ m : Fin 6, (#((block u m).filter
        (fun c : ℕ => ((q ^ e : ℕ) : ℤ) ∣ 2 * ((c : ℤ) - k) + 1)) : ℤ) := by
    rw [sum_congr rfl fun m _ => h1 m]
    exact sum_comm
  have h2 : ∑ j ∈ (range (40 * u + 1)).erase k, (apole u j : ℤ) * (cnt q M ((j : ℤ) - k) : ℤ) =
      ∑ e ∈ Icc 1 M, ∑ j ∈ (range (40 * u + 1)).erase k,
        (apole u j : ℤ) * (if ((q ^ e : ℕ) : ℤ) ∣ (j : ℤ) - k then 1 else 0) := by
    simp only [cnt_cast, mul_sum, Nat.cast_pow]
    exact sum_comm
  unfold Wk Lev
  rw [sum_sub_distrib, h1', h2]

theorem Wk_ge (hq2 : q ≠ 2) (u M k : ℕ) : -(10 * M : ℤ) ≤ Wk u q M k := by
  rw [Wk_eq]
  have hodd : Odd q := hqF.out.odd_of_ne_two hq2
  calc -(10 * M : ℤ) = ∑ _e ∈ Icc 1 M, (-10 : ℤ) := by simp; ring
    _ ≤ _ := sum_le_sum fun e _ => Lev_ge u (q ^ e) k hodd.pow

/-! ### The `r_{i,k}`, `ρ` and `Z` -/

theorem rcoef_val (hq2 : q ≠ 2) {u M : ℕ} (hM : 80 * u + 1 < q ^ (M + 1)) (i k : ℕ) :
    ValGe q ((M : ℤ) * i - 14 * M) (rcoef u i k) := by
  unfold rcoef
  split_ifs with h
  · obtain ⟨_, hia, hk⟩ := h
    have hG := Gser_PSV hq2 hM k hk (apole u k - i)
    have hW := Wk_ge hq2 u M k
    have ha4 : (apole u k : ℤ) ≤ 4 := by exact_mod_cast apole_le u k
    apply valGe_mono hG
    have e : ((apole u k - i : ℕ) : ℤ) = (apole u k : ℤ) - i := by
      push_cast [Nat.cast_sub hia]
      ring
    rw [e]
    have hM0 : (0 : ℤ) ≤ M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ha4 hM0]
  · exact valGe_zero _

theorem AhalfZ_val {u M : ℕ} (hM : 80 * u + 1 < q ^ (M + 1)) (d : ℤ)
    (hd1 : -(20 * u : ℤ) ≤ d) (hd2 : d ≤ 20 * u) (s : ℕ) :
    ValGe q (-((s : ℤ) * M)) (AhalfZ d s) := by
  unfold AhalfZ
  split_ifs with hd
  · apply valGe_sum
    intro l hl
    have hl' := mem_range.1 hl
    have e : ((l : ℚ) + 1 / 2) = ((2 * l + 1 : ℤ) : ℚ) / 2 := by push_cast; ring
    rw [e]
    have := valGe_pow (valGe_half_inv (q := q) M (z := 2 * l + 1) (by omega) (by omega)) s
    simpa [mul_neg] using this
  · apply valGe_neg
    apply valGe_sum
    intro l hl
    have hl' := mem_Icc.1 hl
    have e : ((1 : ℚ) / 2 - l) = ((1 - 2 * l : ℤ) : ℚ) / 2 := by push_cast; ring
    rw [e]
    have := valGe_pow (valGe_half_inv (q := q) M (z := 1 - 2 * l) (by omega) (by omega)) s
    simpa [mul_neg] using this

theorem rho_val (hq2 : q ≠ 2) {u M : ℕ} (hM : 80 * u + 1 < q ^ (M + 1)) :
    ValGe q (-(18 * M : ℤ)) (rho u) := by
  unfold rho genRhoZ
  apply valGe_neg
  apply valGe_sum
  intro i hi
  have hi4 : i ≤ 4 := (mem_Icc.1 hi).2
  apply valGe_sum
  intro k hk
  have hkn : k ≤ 40 * u := by rw [mem_range] at hk; omega
  refine valGe_mul (valGe_mul (valGe_poch i) (rcoef_val hq2 hM i k) rfl)
    (AhalfZ_val hM _ (by push_cast; omega) (by push_cast; omega) (i + 4)) ?_
  push_cast
  ring

theorem Zc_val (hq2 : q ≠ 2) {u M : ℕ} (hM : 80 * u + 1 < q ^ (M + 1)) :
    ValGe q (-(11 * M : ℤ)) (Zc u) := by
  unfold Zc csum genCsum
  have h46 : ((46080 : ℚ)) = ((46080 : ℤ) : ℚ) := by norm_num
  rw [h46]
  refine valGe_mul (valGe_int _) (valGe_sum _ _ fun k _ => rcoef_val hq2 hM 3 k) ?_
  push_cast
  ring

end SmallPrimes7

open SmallPrimes7 in
theorem SmallPrimes7_proof : Stmt_SmallPrimes7 := by
  intro u q hq hq2
  have : Fact q.Prime := ⟨hq⟩
  have hM : 80 * u + 1 < q ^ (Nat.log q (80 * u + 1) + 1) :=
    Nat.lt_pow_succ_log_self hq.one_lt _
  have h1 := den_le (by omega) (rho_val hq2 hM)
  have h2 := den_le (by omega) (Zc_val hq2 hM)
  unfold eq7
  apply max_le
  · have : (padicValNat q (rho u).den : ℤ) ≤ 19 * (Nat.log q (80 * u + 1) : ℤ) := by linarith
    exact_mod_cast this
  · have : (padicValNat q (Zc u).den : ℤ) ≤ 19 * (Nat.log q (80 * u + 1) : ℤ) := by linarith
    exact_mod_cast this

end Zeta2.Z7

end
