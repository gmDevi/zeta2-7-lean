module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Partial fractions of `R_n` with variable pole orders (proof Lemma 0(a))

gap: '' (routine, adapted).  **Status: proved.**  `#print axioms Zeta2.Z7.PF7_proof` gives
`[propext, Classical.choice, Quot.sound]`.

`Stmt_PF7` has two fields, for every `u` (`n = 40u`, `a_k = apole u k`):
* `poly`: `Rnum u = PFpoly u`, i.e.
  `(2t+n) ∏_m ∏_{c ∈ C_m} (t + 1/2 + c)
     = ∑_k ∑_{i=1}^{a_k} r_{i,k} (t+k)^{a_k - i} ∏_{j≠k} (t+j)^{a_j}`;
* `series`: at every non-pole `y`, `Rser u y = ∑_{k ≤ n} ∑_{i=1}^{4} C r_{i,k} ((C (y+k) + X)^i)⁻¹`.
Everything follows from the definition `r_{i,k} = [ε^{a_k - i}] G_k(ε)`.

**Proof of `poly`** (`PF7.poly_eq`; the pair's `Zeta2Lean/Pair/Proofs/PartialFractions.lean`
with the uniform order `6` replaced by `a_k = apole u k`).  Let `Δ := Rnum u - PFpoly u`.
1. *Degrees.* `card (block u m) = 40u - 2 η_m u` (`PF7.card_block`, `Nat.card_Ico`) and
   `∑_m = 136u` (`PF7.sum_card_block`, `Fin.sum_univ_six`), so `natDegree Rnum ≤ 136u + 1`
   (`PF7.natDegree_Rnum_le`).  `∑_{j ≤ n} a_j = 136u + 4` (`PF7.sum_apole`): pointwise
   `a_j = 1 + [2u ≤ j ≤ 38u] + [4u ≤ j ≤ 36u] + [6u ≤ j ≤ 34u]` for `j ≤ n` (`PF7.apole_eq`),
   and the three level sets have `36u + 1`, `32u + 1`, `28u + 1` elements (`PF7.sum_ind`).  Every
   summand of `PFpoly` has `natDegree ≤ (a_k - i) + ∑_{j≠k} a_j = 136u + 4 - i ≤ 136u + 3`
   (`PF7.natDegree_PFpoly_le`).  Hence `natDegree Δ ≤ 136u + 3 < 136u + 4 = deg ∏_k (t+k)^{a_k}`.
2. *Local divisibility* (`PF7.X_add_C_pow_dvd`): for each `k₀ ≤ n`, `(t + k₀)^{a_{k₀}} ∣ Δ`.
   `PF7.substPS a : ℚ[t] →+* ℚ⟦ε⟧` is the substitution `t ↦ a + ε`, and `substPS (-k₀) Δ` is
   the coercion of the polynomial `Δ.comp (X - C k₀)` (`PF7.coe_comp_eq_substPS`).
   `PF7.dvd_subst` shows `ε^{a_{k₀}} ∣ substPS (-k₀) Δ`:
   * `substPS (-k₀) Rnum = (C (n - 2k₀) + C 2 · ε) · numSer u (-k₀) = G_{k₀} · V`, with
     `V := ∏_{j≠k₀} (C (j - k₀) + ε)^{a_j}`; the inverse in `Gser` cancels against `V`
     (constant coefficient `∏_{j≠k₀} (j-k₀)^{a_j} ≠ 0`).
   * `substPS (-k₀) PFpoly = T · V + E`, where `T := ∑_{i=1}^{a_{k₀}} r_{i,k₀} ε^{a_{k₀}-i}` (the
     `k = k₀` summand, split off with `Finset.add_sum_erase`) and `ε^{a_{k₀}} ∣ E`: every summand
     with `k ≠ k₀` contains the factor `(t + k₀)^{a_{k₀}} ↦ ε^{a_{k₀}}`.
   * `ε^{a_{k₀}} ∣ G_{k₀} - T`: the coefficient of `ε^μ`, `μ < a_{k₀}`, is
     `[ε^μ] G_{k₀} - r_{a_{k₀}-μ,k₀} = 0` (definition of `rcoef`).
   So the coefficients `< a_{k₀}` of `Δ.comp (X - C k₀)` vanish, and composing back with
   `X + C k₀` gives `(X + C k₀)^{a_{k₀}} ∣ Δ`.
3. *Coprimality.* The `(X + C k)^{a_k}`, `k ≤ n`, are pairwise coprime
   (`Polynomial.pairwise_coprime_X_sub_C`, `IsCoprime.pow`), so their product (monic, degree
   `136u + 4`) divides `Δ` (`Finset.prod_dvd_of_coprime`), and `Δ = 0`
   (`Polynomial.eq_zero_of_dvd_of_natDegree_lt`).

**Proof of `series`** (`PF7.series_eq`).  Apply `PF7.substPS y` to `poly`; the left side
becomes `(C (2y+n) + C 2 · ε) · numSer u y`.  Multiply by the inverse of
`W := ∏_{j ≤ n} (C (y+j) + ε)^{a_j}` (constant coefficient `∏ (y+j)^{a_j} ≠ 0`); each summand
`C r_{i,k} (C(y+k)+ε)^{a_k-i} ∏_{j≠k} (C(y+j)+ε)^{a_j} · W⁻¹` equals
`C r_{i,k} · ((C (y+k) + ε)^i)⁻¹`, checked with `PowerSeries.eq_inv_iff_mul_eq_one` since
`(C(y+k)+ε)^{a_k-i} (C(y+k)+ε)^i ∏_{j≠k} … = W`.  Finally the inner range `Icc 1 a_k` is extended
to `Icc 1 4` (`Finset.sum_subset`, `apole_le`): for `a_k < i ≤ 4`, `rcoef u i k = 0` by definition.

Helper names live in the namespace `Zeta2.Z7.PF7` and are `private`.

**Numerical check.** `python/z7_mirror.py`, section "PF7" (the identity at random rational
points, and the Taylor form at random `y`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace PF7

/-! ### Elementary power-series identities -/

private lemma C_add_X_add_C (a b : ℚ) : (C a + X : PowerSeries ℚ) + C b = C (a + b) + X := by
  rw [map_add]; ring

/-! ### The substitution `t ↦ a + ε` -/

/-- The substitution `t ↦ a + ε`, as a ring hom `ℚ[t] →+* ℚ⟦ε⟧`. -/
private def substPS (a : ℚ) : Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) (C a + X)

private lemma substPS_X (a : ℚ) : substPS a Polynomial.X = C a + X := by
  simp [substPS]

private lemma substPS_C (a c : ℚ) : substPS a (Polynomial.C c) = C c := by
  simp [substPS]

private lemma substPS_X_add_C (a c : ℚ) :
    substPS a (Polynomial.X + Polynomial.C c) = C (a + c) + X := by
  rw [map_add, substPS_X, substPS_C, C_add_X_add_C]

/-- The linear factor: `(2t + n)(a + ε) = (2a + n) + 2ε`. -/
private lemma substPS_lin (n : ℕ) (a : ℚ) :
    substPS a (Polynomial.C 2 * Polynomial.X + Polynomial.C (n : ℚ)) =
      C (2 * a + n) + C 2 * X := by
  rw [map_add, map_mul, substPS_C, substPS_X, substPS_C, map_add, map_mul]
  ring

/-- The numerator product: `∏_m ∏_{c ∈ C_m} (a + ε + 1/2 + c) = numSer u a`. -/
private lemma substPS_numProd (u : ℕ) (a : ℚ) :
    substPS a (∏ m : Fin 6, ∏ c ∈ block u m,
      (Polynomial.X + Polynomial.C (1 / 2 + (c : ℚ)))) = numSer u a := by
  unfold numSer
  rw [map_prod]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [substPS_X_add_C, add_assoc]

/-! ### Local divisibility at a pole `-k₀` -/

/-- Key step: `ε^{a_{k₀}} ∣ (Rnum - PFpoly)(-k₀ + ε)`. -/
private lemma dvd_subst (u k₀ : ℕ) (hk : k₀ ≤ 40 * u) :
    (X : PowerSeries ℚ) ^ apole u k₀ ∣ substPS (-(k₀ : ℚ)) (Rnum u - PFpoly u) := by
  have hmem : k₀ ∈ range (40 * u + 1) := Finset.mem_range.2 (by omega)
  have hfac : ∀ c : ℚ,
      substPS (-(k₀ : ℚ)) (Polynomial.X + Polynomial.C c) = C (c - k₀) + X := by
    intro c
    rw [substPS_X_add_C, neg_add_eq_sub]
  have hX : (C ((k₀ : ℚ) - k₀) + X : PowerSeries ℚ) = X := by
    rw [sub_self, map_zero, zero_add]
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℚ,
      V = ∏ j ∈ (range (40 * u + 1)).erase k₀, (C ((j : ℚ) - k₀) + X) ^ apole u j := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : PowerSeries ℚ,
      T = ∑ i ∈ Icc (1 : ℕ) (apole u k₀), C (rcoef u i k₀) * X ^ (apole u k₀ - i) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : PowerSeries ℚ,
      E = ∑ k ∈ (range (40 * u + 1)).erase k₀, ∑ i ∈ Icc (1 : ℕ) (apole u k),
        C (rcoef u i k) * (C ((k : ℚ) - k₀) + X) ^ (apole u k - i) *
          ∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k₀) + X) ^ apole u j := ⟨_, rfl⟩
  have hV0 : constantCoeff V ≠ 0 := by
    rw [hV, map_prod, Finset.prod_ne_zero_iff]
    intro j hj
    have hj' : j ≠ k₀ := Finset.ne_of_mem_erase hj
    rw [map_pow, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
    exact pow_ne_zero _ (sub_ne_zero.2 (by exact_mod_cast hj'))
  -- the `Rnum` side: `Rnum(-k₀+ε) = G_{k₀}(ε) · V(ε)`
  have hR : substPS (-(k₀ : ℚ)) (Rnum u) = Gser u k₀ * V := by
    unfold Rnum Gser
    rw [← hV, map_mul, substPS_lin, substPS_numProd, mul_assoc _ V⁻¹ V,
      PowerSeries.inv_mul_cancel V hV0, mul_one,
      show (2 * -(k₀ : ℚ) + ((40 * u : ℕ) : ℚ)) = ((40 * u : ℕ) : ℚ) - 2 * k₀ by ring]
  -- the `PFpoly` side: the `k = k₀` summand gives `T · V`, the others are divisible by `ε^{a_{k₀}}`
  have hPF : substPS (-(k₀ : ℚ)) (PFpoly u) = T * V + E := by
    unfold PFpoly
    simp only [map_sum, map_mul, map_pow, map_prod, substPS_C, hfac]
    rw [← Finset.add_sum_erase _ _ hmem, hT, hE, hV, Finset.sum_mul, hX]
  -- `T` is the degree-`< a_{k₀}` truncation of `G_{k₀}` (definition of `rcoef`)
  have hTdvd : (X : PowerSeries ℚ) ^ apole u k₀ ∣ Gser u k₀ - T := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hT, map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (apole u k₀ - m)]
    · rw [ite_eq_left (by omega)]
      unfold rcoef
      rw [ite_eq_left ⟨by omega, by omega, hk⟩, Nat.sub_sub_self (by omega), sub_self]
    · intro i hi hne
      rw [Finset.mem_Icc] at hi
      rw [ite_eq_right (by omega)]
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_Icc]; omega
  have hEdvd : (X : PowerSeries ℚ) ^ apole u k₀ ∣ E := by
    rw [hE]
    apply Finset.dvd_sum
    intro k hk'
    apply Finset.dvd_sum
    intro i _
    have hk0 : k₀ ∈ (range (40 * u + 1)).erase k :=
      Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hk').symm, hmem⟩
    apply Dvd.dvd.mul_left
    have := Finset.dvd_prod_of_mem
      (fun j : ℕ => (C ((j : ℚ) - k₀) + X : PowerSeries ℚ) ^ apole u j) hk0
    simp only [hX] at this
    exact this
  rw [map_sub, hR, hPF]
  have hsplit : Gser u k₀ * V - (T * V + E) = (Gser u k₀ - T) * V - E := by ring
  rw [hsplit]
  exact dvd_sub (dvd_mul_of_dvd_left hTdvd V) hEdvd

/-- `substPS (-k₀) P` is the power series of the polynomial `P(t - k₀)`. -/
private lemma coe_comp_eq_substPS (k₀ : ℚ) (P : Polynomial ℚ) :
    ((P.comp (Polynomial.X - Polynomial.C k₀) : Polynomial ℚ) : PowerSeries ℚ) =
      substPS (-k₀) P := by
  have h : (Polynomial.coeToPowerSeries.ringHom).comp
      (Polynomial.compRingHom (Polynomial.X - Polynomial.C k₀)) = substPS (-k₀) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [substPS]
    · simp only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.X_comp,
        Polynomial.coeToPowerSeries.ringHom_apply, substPS_X]
      rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg]
      ring
  exact RingHom.congr_fun h P

/-- `(t + k₀)^{a_{k₀}} ∣ Rnum - PFpoly` for every `k₀ ≤ n`. -/
private lemma X_add_C_pow_dvd (u k₀ : ℕ) (hk : k₀ ≤ 40 * u) :
    (Polynomial.X + Polynomial.C (k₀ : ℚ)) ^ apole u k₀ ∣ Rnum u - PFpoly u := by
  set P := Rnum u - PFpoly u with hP
  set Q := P.comp (Polynomial.X - Polynomial.C (k₀ : ℚ)) with hQ
  have hQdvd : Polynomial.X ^ apole u k₀ ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h1 := dvd_subst u k₀ hk
    rw [← hP, ← coe_comp_eq_substPS, ← hQ, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 d hd
    rwa [Polynomial.coeff_coe] at h2
  obtain ⟨S, hS⟩ := hQdvd
  have hPQ : P = Q.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)) := by
    rw [hQ, Polynomial.comp_assoc]
    simp
  refine ⟨S.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)), ?_⟩
  rw [hPQ, hS, Polynomial.mul_comp, Polynomial.X_pow_comp]

/-! ### Degree bounds -/

/-- `card C_m = 40u - 2 η_m u`. -/
private lemma card_block (u : ℕ) (m : Fin 6) :
    (block u m).card = 40 * u - eta m * u - eta m * u := by
  unfold block
  rw [Nat.card_Ico]

/-- `∑_m card C_m = (30 + 26 + 26 + 22 + 18 + 14) u = 136u`. -/
private lemma sum_card_block (u : ℕ) : ∑ m : Fin 6, (block u m).card = 136 * u := by
  simp only [card_block, Fin.sum_univ_six]
  have e0 : eta 0 = 5 := rfl
  have e1 : eta 1 = 7 := rfl
  have e2 : eta 2 = 7 := rfl
  have e3 : eta 3 = 9 := rfl
  have e4 : eta 4 = 11 := rfl
  have e5 : eta 5 = 13 := rfl
  rw [e0, e1, e2, e3, e4, e5]
  omega

/-- The numerator product has degree `≤ ∑_m card C_m = 136u`. -/
private lemma natDegree_numProd_le (u : ℕ) :
    (∏ m : Fin 6, ∏ c ∈ block u m,
      (Polynomial.X + Polynomial.C (1 / 2 + (c : ℚ)))).natDegree ≤ 136 * u := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have h3 : ∀ m : Fin 6, (∏ c ∈ block u m,
      (Polynomial.X + Polynomial.C (1 / 2 + (c : ℚ)))).natDegree ≤ (block u m).card := by
    intro m
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun c _ => (Polynomial.natDegree_X_add_C _).le)).trans ?_
    simp
  refine (Finset.sum_le_sum (fun m _ => h3 m)).trans (le_of_eq ?_)
  exact sum_card_block u

private lemma natDegree_Rnum_le (u : ℕ) : (Rnum u).natDegree ≤ 136 * u + 1 := by
  unfold Rnum
  have h1 : (Polynomial.C (2 : ℚ) * Polynomial.X +
      Polynomial.C ((40 * u : ℕ) : ℚ)).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  have h2 := natDegree_numProd_le u
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

/-- The pole order as a sum of level-set indicators: for `j ≤ n`,
`a_j = 1 + [2u ≤ j ≤ 38u] + [4u ≤ j ≤ 36u] + [6u ≤ j ≤ 34u]`. -/
private lemma apole_eq (u j : ℕ) (hj : j ≤ 40 * u) :
    apole u j = 1 + (if 2 * u ≤ j ∧ j ≤ 38 * u then 1 else 0) +
      (if 4 * u ≤ j ∧ j ≤ 36 * u then 1 else 0) +
        (if 6 * u ≤ j ∧ j ≤ 34 * u then 1 else 0) := by
  unfold apole
  split_ifs <;> omega

/-- `#{j ≤ N : a ≤ j ≤ b} = b + 1 - a` for `b ≤ N`. -/
private lemma sum_ind (N a b : ℕ) (hb : b ≤ N) :
    ∑ j ∈ range (N + 1), (if a ≤ j ∧ j ≤ b then 1 else 0 : ℕ) = b + 1 - a := by
  have h : (range (N + 1)).filter (fun j => a ≤ j ∧ j ≤ b) = Icc a b := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, h, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]

/-- `∑_{j ≤ n} a_j = (40u+1) + (36u+1) + (32u+1) + (28u+1) = 136u + 4`. -/
private lemma sum_apole (u : ℕ) : ∑ j ∈ range (40 * u + 1), apole u j = 136 * u + 4 := by
  rw [Finset.sum_congr rfl (fun j hj => apole_eq u j (by rw [Finset.mem_range] at hj; omega))]
  simp only [Finset.sum_add_distrib]
  rw [sum_ind _ _ _ (by omega), sum_ind _ _ _ (by omega), sum_ind _ _ _ (by omega)]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

private lemma natDegree_PFpoly_le (u : ℕ) : (PFpoly u).natDegree ≤ 136 * u + 3 := by
  unfold PFpoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hsum : ∑ j ∈ (range (40 * u + 1)).erase k, apole u j + apole u k = 136 * u + 4 := by
    rw [Finset.sum_erase_add _ _ hk, sum_apole]
  have h1 := (Polynomial.natDegree_mul_le (p := Polynomial.C (rcoef u i k))
    (q := (Polynomial.X + Polynomial.C (k : ℚ)) ^ (apole u k - i)))
  rw [Polynomial.natDegree_C, zero_add] at h1
  have h2 := (Polynomial.natDegree_pow_le (p := Polynomial.X + Polynomial.C (k : ℚ))
    (n := apole u k - i))
  rw [Polynomial.natDegree_X_add_C, mul_one] at h2
  have h3 : (∏ j ∈ (range (40 * u + 1)).erase k,
      (Polynomial.X + Polynomial.C (j : ℚ)) ^ apole u j).natDegree ≤
        ∑ j ∈ (range (40 * u + 1)).erase k, apole u j := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine Finset.sum_le_sum (fun j _ => Polynomial.natDegree_pow_le.trans ?_)
    rw [Polynomial.natDegree_X_add_C, mul_one]
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

/-! ### The two fields of `Stmt_PF7` -/

private theorem poly_eq (u : ℕ) : Rnum u = PFpoly u := by
  have hdvd : ∏ k ∈ range (40 * u + 1), (Polynomial.X + Polynomial.C (k : ℚ)) ^ apole u k ∣
      Rnum u - PFpoly u := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      have hinj : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
        intro a b hab
        simpa using hab
      have := Polynomial.pairwise_coprime_X_sub_C hinj hij
      simp only [Function.onFun, map_neg, sub_neg_eq_add] at this ⊢
      exact this.pow
    · intro k hk
      exact X_add_C_pow_dvd u k (by simpa [Nat.lt_succ_iff] using hk)
  have hdeg : (Rnum u - PFpoly u).natDegree <
      (∏ k ∈ range (40 * u + 1),
        (Polynomial.X + Polynomial.C (k : ℚ)) ^ apole u k).natDegree := by
    have hmon : ∀ k ∈ range (40 * u + 1),
        ((Polynomial.X + Polynomial.C (k : ℚ)) ^ apole u k).Monic :=
      fun k _ => (Polynomial.monic_X_add_C _).pow _
    rw [Polynomial.natDegree_prod_of_monic _ _ hmon]
    have h1 := Polynomial.natDegree_sub_le (Rnum u) (PFpoly u)
    have h2 := natDegree_Rnum_le u
    have h3 := natDegree_PFpoly_le u
    have h4 : ∑ k ∈ range (40 * u + 1),
        ((Polynomial.X + Polynomial.C (k : ℚ)) ^ apole u k).natDegree = 136 * u + 4 := by
      rw [← sum_apole u]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [(Polynomial.monic_X_add_C (k : ℚ)).natDegree_pow, Polynomial.natDegree_X_add_C,
        mul_one]
    rw [h4]
    omega
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg)

private theorem series_eq (u : ℕ) (y : ℚ) (hy : ∀ j ≤ 40 * u, y + (j : ℚ) ≠ 0) :
    Rser u y = ∑ k ∈ range (40 * u + 1), ∑ i ∈ Icc (1 : ℕ) 4,
      C (rcoef u i k) * ((C (y + k) + X) ^ i)⁻¹ := by
  have hpoly := congrArg (substPS y) (poly_eq u)
  have hF : ∀ c : ℚ, substPS y (Polynomial.X + Polynomial.C c) = C (y + c) + X :=
    substPS_X_add_C y
  have hF0 : ∀ j ∈ range (40 * u + 1),
      constantCoeff (C (y + (j : ℚ)) + X : PowerSeries ℚ) ≠ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    simpa using hy j (by omega)
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℚ,
      W = ∏ j ∈ range (40 * u + 1), (C (y + (j : ℚ)) + X) ^ apole u j := ⟨_, rfl⟩
  have hW0 : constantCoeff W ≠ 0 := by
    rw [hW, map_prod]
    exact Finset.prod_ne_zero_iff.2 (fun j hj => by rw [map_pow]; exact pow_ne_zero _ (hF0 j hj))
  have hLHS : Rser u y = substPS y (Rnum u) * W⁻¹ := by
    unfold Rser Rnum
    rw [map_mul, substPS_lin, substPS_numProd, hW]
  rw [hLHS, hpoly]
  unfold PFpoly
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  -- extend the inner range `Icc 1 a_k` to `Icc 1 4`: the extra `rcoef u i k` vanish
  have hsub : Icc (1 : ℕ) (apole u k) ⊆ Icc 1 4 := Finset.Icc_subset_Icc le_rfl (apole_le u k)
  rw [← Finset.sum_subset hsub]
  · rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    rw [map_mul, map_mul, substPS_C, map_pow (substPS y), hF, map_prod]
    simp_rw [map_pow (substPS y), hF]
    rw [mul_assoc, mul_assoc]
    congr 1
    have hFk : constantCoeff ((C (y + (k : ℚ)) + X) ^ i : PowerSeries ℚ) ≠ 0 := by
      rw [map_pow]; exact pow_ne_zero _ (hF0 k hk)
    rw [PowerSeries.eq_inv_iff_mul_eq_one hFk]
    have hWk : W = (C (y + (k : ℚ)) + X) ^ apole u k *
        ∏ j ∈ (range (40 * u + 1)).erase k, (C (y + (j : ℚ)) + X) ^ apole u j := by
      rw [hW]
      exact (Finset.mul_prod_erase _
        (fun j : ℕ => (C (y + (j : ℚ)) + X : PowerSeries ℚ) ^ apole u j) hk).symm
    calc (C (y + (k : ℚ)) + X) ^ (apole u k - i) *
          ((∏ j ∈ (range (40 * u + 1)).erase k, (C (y + (j : ℚ)) + X) ^ apole u j) * W⁻¹) *
          (C (y + (k : ℚ)) + X) ^ i
        = ((C (y + (k : ℚ)) + X) ^ (apole u k - i) * (C (y + (k : ℚ)) + X) ^ i *
            ∏ j ∈ (range (40 * u + 1)).erase k, (C (y + (j : ℚ)) + X) ^ apole u j) * W⁻¹ := by
          ring
      _ = W * W⁻¹ := by rw [← pow_add, Nat.sub_add_cancel hi.2, hWk]
      _ = 1 := PowerSeries.mul_inv_cancel W hW0
  · intro i hi hni
    rw [Finset.mem_Icc] at hi hni
    have hr : rcoef u i k = 0 := by
      unfold rcoef
      rw [ite_eq_right (by omega)]
    rw [hr, map_zero, zero_mul]

end PF7

theorem PF7_proof : Stmt_PF7 := ⟨PF7.poly_eq, PF7.series_eq⟩

end Zeta2.Z7

end
