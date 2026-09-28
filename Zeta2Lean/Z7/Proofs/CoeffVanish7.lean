module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Symmetry and vanishing sums (proof Lemma 0(b)–(d))

gap: '' (routine, adapted).  Difficulty 3.

**Status: proved** (complete, kernel-checked; `#print axioms CoeffVanish7_proof` gives
`[propext, Classical.choice, Quot.sound]`).  The configuration enters only through
`apole u (40u - k) = apole u k` (`cv7_apole_symm`), `∑_{j ≤ 40u} apole u j = 136u + 4`
(`cv7_apole_sum`, by splitting `[0, 40u]` into the seven intervals where `apole` is constant) and
`∑_m |C_m| = 136u` (`cv7_card_blocks`); all three hold for every `u`, including `u = 0`.

**Task.** Prove `Stmt_CoeffVanish7` (fields `symm`, `c1`, `ceven`) from `Stmt_PF7`.

**Informal proof** (as `Zeta2Lean/Pair/Proofs/CoeffVanish.lean`, with variable orders).
* `symm`: `G_{n-k}(ε) = -(-1)^{a_k} G_k(-ε)`, hence
  `r_{i,n-k} = [ε^{a_k-i}] G_{n-k} = -(-1)^{a_k} (-1)^{a_k-i} r_{i,k} = (-1)^{i+1} r_{i,k}`
  (`apole u (n-k) = apole u k`).  Factor by factor, with `ρ := PowerSeries.rescale (-1)`:
  - linear factor: `n - 2(n-k) + 2ε = -ρ(n - 2k + 2ε)`;
  - numerator: each block is invariant under `c ↦ n - 1 - c`, and
    `c' - (n-k) + 1/2 + ε = -((n-1-c') - k + 1/2 - ε)`; there are `136 u` factors (even), so the
    signs cancel;
  - poles: `j ↦ n - j` maps `(range (n+1)).erase (n-k)` onto `(range(n+1)).erase k`,
    `(n-j) - (n-k) + ε = -(j - k - ε)` with exponent `a_{n-j} = a_j`; the total sign is
    `(-1)^{∑_{j≠k} a_j} = (-1)^{136u + 4 - a_k} = (-1)^{a_k}`; `ρ` commutes with `⁻¹`.
* `c1`: compare the coefficients of `t^{136u+3}` in `Stmt_PF7.poly`: the left side has degree
  `136u + 1`; on the right only `i = 1` contributes, each `(t+k)^{a_k-1} ∏_{j≠k} (t+j)^{a_j}` being
  monic of degree `136u + 3`; so `0 = ∑_k r_{1,k} = c₁`.
* `ceven`: for even `i`, `symm` gives `r_{i,n-k} = -r_{i,k}`; reflect the sum
  (`Finset.sum_range_reflect`).

**Lean hints.** The pair file's `cvp_rescale_C`, `cvp_rescale_inv`, `cvp_block` (with
`Ico (η u) (40u - η u)` over `ℕ`, involution `c ↦ 40u - 1 - c`), `cvp_den` (exponent
`apole u j`, sign `(-1)^{apole u j}` per factor), `cvp_natDegree_term`, `cvp_coeff_PFpoly`.
Useful facts: `apole u (40u - k) = apole u k` (unfold, `omega`), `∑_{j ≤ 40u} apole u j = 136u + 4`.

**Numerical check.** `python/z7_mirror.py`, section "CoeffVanish7".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

/-! ### Combinatorics of the configuration -/

/-- `a_{n-k} = a_k`. -/
private lemma cv7_apole_symm (u k : ℕ) (hk : k ≤ 40 * u) : apole u (40 * u - k) = apole u k := by
  have h : min (40 * u - k) (40 * u - (40 * u - k)) = min k (40 * u - k) := by omega
  unfold apole
  rw [h]

/-- `∑_{j ≤ n} a_j = 136 u + 4` (`= N + 4`, `N = 136 u` numerator factors). -/
private lemma cv7_apole_sum (u : ℕ) : ∑ j ∈ range (40 * u + 1), apole u j = 136 * u + 4 := by
  have hc : ∀ a b c : ℕ, (∀ j, a ≤ j → j < b → apole u j = c) →
      ∑ j ∈ Ico a b, apole u j = (b - a) * c := by
    intro a b c h
    rw [Finset.sum_congr rfl (fun j hj => h j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2),
      Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  have s1 := hc 0 (2 * u) 1 (by intro j h1 h2; unfold apole; split_ifs <;> omega)
  have s2 := hc (2 * u) (4 * u) 2 (by intro j h1 h2; unfold apole; split_ifs <;> omega)
  have s3 := hc (4 * u) (6 * u) 3 (by intro j h1 h2; unfold apole; split_ifs <;> omega)
  have s4 := hc (6 * u) (34 * u + 1) 4 (by intro j h1 h2; unfold apole; split_ifs <;> omega)
  have s5 := hc (34 * u + 1) (36 * u + 1) 3 (by intro j h1 h2; unfold apole; split_ifs <;> omega)
  have s6 := hc (36 * u + 1) (38 * u + 1) 2 (by intro j h1 h2; unfold apole; split_ifs <;> omega)
  have s7 := hc (38 * u + 1) (40 * u + 1) 1 (by intro j h1 h2; unfold apole; split_ifs <;> omega)
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (2 * u)) (by omega : 2 * u ≤ 40 * u + 1),
    ← Finset.sum_Ico_consecutive _ (by omega : 2 * u ≤ 4 * u) (by omega : 4 * u ≤ 40 * u + 1),
    ← Finset.sum_Ico_consecutive _ (by omega : 4 * u ≤ 6 * u) (by omega : 6 * u ≤ 40 * u + 1),
    ← Finset.sum_Ico_consecutive _ (by omega : 6 * u ≤ 34 * u + 1)
      (by omega : 34 * u + 1 ≤ 40 * u + 1),
    ← Finset.sum_Ico_consecutive _ (by omega : 34 * u + 1 ≤ 36 * u + 1)
      (by omega : 36 * u + 1 ≤ 40 * u + 1),
    ← Finset.sum_Ico_consecutive _ (by omega : 36 * u + 1 ≤ 38 * u + 1)
      (by omega : 38 * u + 1 ≤ 40 * u + 1),
    s1, s2, s3, s4, s5, s6, s7]
  omega

/-- `∑_{j ≤ n, j ≠ k} a_j = 136 u + 4 - a_k`. -/
private lemma cv7_sum_erase (u k : ℕ) (hk : k ∈ range (40 * u + 1)) :
    ∑ j ∈ (range (40 * u + 1)).erase k, apole u j = 136 * u + 4 - apole u k := by
  have h := Finset.sum_erase_add (range (40 * u + 1)) (apole u) hk
  rw [cv7_apole_sum] at h
  omega

/-- The six blocks have `∑_m |C_m| = 136 u` elements. -/
private lemma cv7_card_blocks (u : ℕ) : ∑ m : Fin 6, (block u m).card = 136 * u := by
  have e0 : eta 0 = 5 := rfl
  have e1 : eta 1 = 7 := rfl
  have e2 : eta 2 = 7 := rfl
  have e3 : eta 3 = 9 := rfl
  have e4 : eta 4 = 11 := rfl
  have e5 : eta 5 = 13 := rfl
  simp only [Fin.sum_univ_six, block, Nat.card_Ico, e0, e1, e2, e3, e4, e5]
  omega

/-! ### `symm`: the reflection `ε ↦ -ε` -/

/-- `rescale a` fixes constants. -/
private lemma cv7_rescale_C (a r : ℚ) : rescale a (C r) = C r := by
  ext m
  rw [coeff_rescale, coeff_C]
  split_ifs with hm
  · subst hm
    simp
  · simp

/-- `rescale a` commutes with the power-series inverse (over a field; both sides are `0` when the
constant coefficient vanishes). -/
private lemma cv7_rescale_inv (a : ℚ) (φ : PowerSeries ℚ) :
    rescale a φ⁻¹ = (rescale a φ)⁻¹ := by
  have hc : constantCoeff (rescale a φ) = constantCoeff φ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
  by_cases hφ : constantCoeff φ = 0
  · rw [PowerSeries.inv_eq_zero.mpr hφ, map_zero, PowerSeries.inv_eq_zero.mpr (hc.trans hφ)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (hc ▸ hφ), ← map_mul, PowerSeries.inv_mul_cancel φ hφ,
      map_one]

/-- One numerator block under the reflection `c ↦ n - 1 - c` of `C_m`:
`∏_c (c - (n-k) + 1/2 + ε) = (-1)^{|C_m|} ∏_c (c - k + 1/2 - ε)`. -/
private lemma cv7_block (u k : ℕ) (hk : k ≤ 40 * u) (m : Fin 6) :
    ∏ c ∈ block u m, (C (-((40 * u - k : ℕ) : ℚ) + 1 / 2 + (c : ℚ)) + X) =
      (-1) ^ (block u m).card *
        rescale (-1 : ℚ) (∏ c ∈ block u m, (C (-(k : ℚ) + 1 / 2 + (c : ℚ)) + X)) := by
  rw [map_prod, ← Finset.prod_neg]
  refine Finset.prod_nbij' (fun c => 40 * u - 1 - c) (fun c => 40 * u - 1 - c) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [block, Finset.mem_Ico] at hc ⊢
    omega
  · intro c hc
    simp only [block, Finset.mem_Ico] at hc ⊢
    omega
  · intro c hc
    simp only [block, Finset.mem_Ico] at hc
    omega
  · intro c hc
    simp only [block, Finset.mem_Ico] at hc
    omega
  · intro c hc
    simp only [block, Finset.mem_Ico] at hc
    rw [map_add (rescale (-1 : ℚ)), cv7_rescale_C, rescale_neg_one_X]
    have e1 : ((40 * u - k : ℕ) : ℚ) + k = 40 * (u : ℚ) := by
      exact_mod_cast (by omega : 40 * u - k + k = 40 * u)
    have e2 : ((40 * u - 1 - c : ℕ) : ℚ) + c + 1 = 40 * (u : ℚ) := by
      exact_mod_cast (by omega : 40 * u - 1 - c + c + 1 = 40 * u)
    have e : (-((40 * u - k : ℕ) : ℚ) + 1 / 2 + (c : ℚ)) =
        -(-(k : ℚ) + 1 / 2 + ((40 * u - 1 - c : ℕ) : ℚ)) := by
      linear_combination (-1 : ℚ) * e1 + e2
    rw [e, map_neg]
    ring

/-- `numSer u (-(n-k)) = numSer u (-k)` evaluated at `-ε` (the signs cancel: `136 u` factors). -/
private lemma cv7_numSer (u k : ℕ) (hk : k ≤ 40 * u) :
    numSer u (-((40 * u - k : ℕ) : ℚ)) = rescale (-1 : ℚ) (numSer u (-(k : ℚ))) := by
  unfold numSer
  rw [map_prod, Finset.prod_congr rfl (fun m _ => cv7_block u k hk m),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, cv7_card_blocks,
    (show Even (136 * u) from ⟨68 * u, by ring⟩).neg_one_pow, one_mul]

/-- The pole factors under `j ↦ n - j`: `∏_{j ≠ n-k} (j - (n-k) + ε)^{a_j}
= (-1)^{a_k} ∏_{j ≠ k} (j - k - ε)^{a_j}`. -/
private lemma cv7_den (u k : ℕ) (hk : k ≤ 40 * u) :
    ∏ j ∈ (range (40 * u + 1)).erase (40 * u - k),
        (C ((j : ℚ) - ((40 * u - k : ℕ) : ℚ)) + X) ^ apole u j =
      C ((-1 : ℚ) ^ apole u k) *
        rescale (-1 : ℚ) (∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k) + X) ^ apole u j) := by
  have hkr : k ∈ range (40 * u + 1) := Finset.mem_range.mpr (by omega)
  have hpar : ((-1 : ℚ)) ^ (∑ j ∈ (range (40 * u + 1)).erase k, apole u j) =
      (-1) ^ apole u k := by
    rw [cv7_sum_erase u k hkr, neg_one_pow_eq_pow_mod_two,
      neg_one_pow_eq_pow_mod_two (n := apole u k)]
    have := apole_le u k
    congr 1
    omega
  rw [← hpar, ← Finset.prod_pow_eq_pow_sum, map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_nbij' (fun j => 40 * u - j) (fun j => 40 * u - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    rw [cv7_apole_symm u j (by omega)]
    simp only [map_pow, map_add, map_neg, map_one, cv7_rescale_C, rescale_neg_one_X]
    rw [← mul_pow]
    congr 1
    have e1 : ((40 * u - k : ℕ) : ℚ) + k = 40 * (u : ℚ) := by
      exact_mod_cast (by omega : 40 * u - k + k = 40 * u)
    have e2 : ((40 * u - j : ℕ) : ℚ) + j = 40 * (u : ℚ) := by
      exact_mod_cast (by omega : 40 * u - j + j = 40 * u)
    have e : ((j : ℚ) - ((40 * u - k : ℕ) : ℚ)) = -(((40 * u - j : ℕ) : ℚ) - k) := by
      linear_combination e2 - e1
    rw [e, map_neg]
    ring

/-- `((-1)^a)⁻¹ = (-1)^a` in `ℚ`. -/
private lemma cv7_inv_neg_one_pow (a : ℕ) : ((-1 : ℚ) ^ a)⁻¹ = (-1) ^ a := by
  rw [← inv_pow, inv_neg, inv_one]

/-- `G_{n-k}(ε) = -(-1)^{a_k} G_k(-ε)`. -/
private lemma cv7_Gser_reflect (u k : ℕ) (hk : k ≤ 40 * u) :
    Gser u (40 * u - k) = -(C ((-1 : ℚ) ^ apole u k) * rescale (-1 : ℚ) (Gser u k)) := by
  unfold Gser
  rw [cv7_numSer u k hk, cv7_den u k hk, PowerSeries.mul_inv_rev, PowerSeries.C_inv,
    cv7_inv_neg_one_pow]
  simp only [map_mul, map_add, cv7_rescale_C, rescale_neg_one_X, cv7_rescale_inv]
  have h1 : (C (((40 * u : ℕ) : ℚ) - 2 * ((40 * u - k : ℕ) : ℚ)) : PowerSeries ℚ) =
      -C (((40 * u : ℕ) : ℚ) - 2 * k) := by
    rw [← map_neg]
    congr 1
    rw [Nat.cast_sub hk]
    ring
  rw [h1]
  ring

/-- `r_{i,n-k} = (-1)^{i+1} r_{i,k}`. -/
private lemma cv7_symm (u i k : ℕ) (hk : k ≤ 40 * u) :
    rcoef u i (40 * u - k) = (-1) ^ (i + 1) * rcoef u i k := by
  unfold rcoef
  rw [cv7_apole_symm u k hk]
  by_cases hi : 1 ≤ i ∧ i ≤ apole u k
  · rw [ite_eq_left ⟨hi.1, hi.2, Nat.sub_le _ _⟩, ite_eq_left ⟨hi.1, hi.2, hk⟩,
      cv7_Gser_reflect u k hk, map_neg, coeff_C_mul, coeff_rescale]
    obtain ⟨d, hd⟩ : ∃ d, apole u k = i + d := ⟨apole u k - i, by omega⟩
    rw [hd, Nat.add_sub_cancel_left]
    have h2 : ((-1 : ℚ)) ^ (i + d) * (-1) ^ d = (-1) ^ i := by
      rw [pow_add, mul_assoc, ← pow_add, Even.neg_one_pow ⟨d, rfl⟩, mul_one]
    calc -((-1 : ℚ) ^ (i + d) * ((-1) ^ d * coeff d (Gser u k)))
        = -(((-1 : ℚ) ^ (i + d) * (-1) ^ d) * coeff d (Gser u k)) := by ring
      _ = (-1) ^ (i + 1) * coeff d (Gser u k) := by rw [h2]; ring
  · rw [ite_eq_right (fun hc => hi ⟨hc.1, hc.2.1⟩), ite_eq_right (fun hc => hi ⟨hc.1, hc.2.1⟩),
      mul_zero]

/-! ### `c1`: the top coefficient of `Stmt_PF7.poly` -/

private lemma cv7_natDegree_block (u : ℕ) (m : Fin 6) :
    (∏ c ∈ block u m, (Polynomial.X + Polynomial.C (1 / 2 + (c : ℚ)))).natDegree =
      (block u m).card := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

/-- `natDegree Rnum ≤ 136 u + 1`. -/
private lemma cv7_natDegree_Rnum (u : ℕ) : (Rnum u).natDegree ≤ 136 * u + 1 := by
  unfold Rnum
  have hprod : (∏ m : Fin 6, ∏ c ∈ block u m,
      (Polynomial.X + Polynomial.C (1 / 2 + (c : ℚ)))).natDegree = 136 * u := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun m _ =>
      Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _))]
    simp only [cv7_natDegree_block]
    exact cv7_card_blocks u
  have hA : (Polynomial.C (2 : ℚ) * Polynomial.X +
      Polynomial.C ((40 * u : ℕ) : ℚ)).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

/-- The `(i,k)` basis polynomial `(t+k)^{a_k-i} ∏_{j ≠ k} (t+j)^{a_j}` is monic ... -/
private lemma cv7_monic_term (u i k : ℕ) :
    ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (apole u k - i) *
      ∏ j ∈ (range (40 * u + 1)).erase k,
        (Polynomial.X + Polynomial.C (j : ℚ)) ^ apole u j).Monic :=
  ((Polynomial.monic_X_add_C _).pow _).mul
    (Polynomial.monic_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow _))

/-- ... of degree `(a_k - i) + (136 u + 4 - a_k)` (for `k ≤ n`). -/
private lemma cv7_natDegree_term (u i k : ℕ) (hk : k ∈ range (40 * u + 1)) :
    ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (apole u k - i) *
      ∏ j ∈ (range (40 * u + 1)).erase k,
        (Polynomial.X + Polynomial.C (j : ℚ)) ^ apole u j).natDegree =
      (apole u k - i) + (136 * u + 4 - apole u k) := by
  rw [Polynomial.Monic.natDegree_mul ((Polynomial.monic_X_add_C _).pow _)
      (Polynomial.monic_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow _)),
    Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow _)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  rw [cv7_sum_erase u k hk]

/-- The coefficient of `t^{136u+3}` in `PFpoly u` is `c₁`. -/
private lemma cv7_coeff_PFpoly (u : ℕ) : (PFpoly u).coeff (136 * u + 3) = csum u 1 := by
  unfold PFpoly csum genCsum
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have ha := apole_pos u k
  have hb := apole_le u k
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 1]
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    have hdeg := cv7_natDegree_term u 1 k hk
    rw [show apole u k - 1 + (136 * u + 4 - apole u k) = 136 * u + 3 by omega] at hdeg
    rw [← hdeg, (cv7_monic_term u 1 k).coeff_natDegree, mul_one]
  · intro i hi hi1
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [cv7_natDegree_term u i k hk]
    have := Finset.mem_Icc.mp hi
    omega
  · intro hc
    exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, ha⟩) hc

/-- `c₁ = 0`. -/
private lemma cv7_c1 (hPF : Stmt_PF7) (u : ℕ) : csum u 1 = 0 := by
  rw [← cv7_coeff_PFpoly u, ← hPF.poly u]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((cv7_natDegree_Rnum u).trans_lt (by omega))

/-! ### `ceven` -/

/-- `c_i = 0` for even `i`. -/
private lemma cv7_ceven (u i : ℕ) (hi : Even i) : csum u i = 0 := by
  have h1 := Finset.sum_range_reflect (fun k => rcoef u i k) (40 * u + 1)
  have h2 : ∑ j ∈ range (40 * u + 1), rcoef u i (40 * u + 1 - 1 - j) = -csum u i := by
    unfold csum genCsum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ 40 * u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.add_sub_cancel, cv7_symm u i j hj', hi.add_one.neg_one_pow, neg_one_mul]
  have h3 : ∑ j ∈ range (40 * u + 1), rcoef u i j = csum u i := rfl
  rw [h2, h3] at h1
  linarith

theorem CoeffVanish7_proof (hPF : Stmt_PF7) : Stmt_CoeffVanish7 where
  symm := cv7_symm
  c1 := cv7_c1 hPF
  ceven := cv7_ceven

end Zeta2.Z7

end
