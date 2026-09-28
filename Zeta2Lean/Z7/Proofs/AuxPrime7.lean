module

public import Zeta2Lean.Z7.Statements
public import Zeta2Lean.Pair.Proofs.Nonvanishing

@[expose] public section

/-!
# Theorem N: the auxiliary prime `ℓ = 19n/20 - 1 = 38u - 1` (proof §7)

gap: 'nonvanishing' (adapted).  Difficulty 4.

**Status: proved** (complete, kernel-checked; `#print axioms AuxPrime7_proof` gives
`[propext, Classical.choice, Quot.sound]`).  Only `hV.symm` is used; `hPF` belongs to the fixed
signature.  `U = 10` (so `ℓ > 300`).

**Task.** Prove `Stmt_AuxPrime7` from `Stmt_PF7` and `Stmt_CoeffVanish7`: for all large `u` with
`ℓ := 38u - 1` prime, `v_ℓ(ρ) = -1` and `v_ℓ(Z) ≥ 0`.  (The informal proof works for every `u ≥ 1`;
taking `U` large, e.g. `ℓ > 10⁶`, is allowed and makes all small constants `ℓ`-units.)

**Informal proof** (proof §7).  Write `n = 40u`, so
`19n/20 = ℓ + 1`, `ℓ ≥ 37`, `2n < 3ℓ`, `ℓ² > 2n`.
* (S1) pole differences: `ℓ ∣ k' - k` iff `k' - k = ±ℓ`; (S2) numerator values `2(c-k)+1` are odd,
  `|·| < 3ℓ`, so `ℓ` divides one iff `c = k + (ℓ-1)/2 = k + 19u - 1` or `c = k - 19u`, with
  `v_ℓ = 1`; (S3) `ℓ ∤ n - 2k`; (S4) for `h ∈ H_k`, `ℓ ∣ 2h` iff `2h = ±ℓ`, which needs `k ≤ u` or
  `k ≥ 39u`; (S5) every block contains the window `[19u - 1, 21u]`.
* **N1 (local data)** with `G_k(ε) = G_k(0) ∏_β (1 + ε/β)^{e_β}`, `s_k = v_ℓ(G_k(0))`, and the
  pair's
  Lemma D2 (`v_ℓ([ε^λ] ∏) ≥ -Top_λ`):
  (a) end poles `0 ≤ k ≤ 2u + 1`: `c = k + 19u - 1` lies in all six blocks; the partner pole
  `k + ℓ` has order `2` for `k ∈ {0, 1}` and `1` for `k ≥ 2`; so `s₀ = s₁ = 4`, `s_k = 5`
  (`2 ≤ k ≤ 2u+1`), and `v_ℓ(r_{i,k}) ≥ s_k - (a_k - i) ≥ 3`; the mirror poles by
  `Stmt_CoeffVanish7.symm`.  (b) middle poles: only numerator factors are `ℓ`-divisible, so
  `v_ℓ(r_{i,k}) ≥ 0`.  (c) hence every `c_i` is `ℓ`-integral: `v_ℓ(Z) ≥ 0`.
* **N2 (two terms)**: `ρ_n ≡ -2(X₀ + X₁) (mod ℤ_(ℓ))` with `X_k = 24 r_{1,k} (-ℓ/2)^{-5} =
  -768 r_{1,k}/ℓ⁵` (`k ∈ {0, 1}`, `a_k = 1`, `h = -ℓ/2 ∈ H_k` iff `k ≤ u`); the good terms and the
  terms with `2 ≤ k ≤ u` are `ℓ`-integral.  (Use `rho u = -ρ_n` and the symmetric form.)
* **N3 (ratio)**: `Θ := r_{1,1}/r_{1,0} = ((n-2)/n) ∏_m (2η_m n - 1)/(2(1-η_m)n - 1)
  · (-1) n (17n/20)(9n/10)(19n/20) / ((n/20 - 1)(n/10 - 1)(3n/20 - 1))` (telescoping); modulo `ℓ`
  (`n ≡ 20/19`): `Θ ≡ θ₀ = -81/224`, `1 + θ₀ = 143/224 = 11·13/(2⁵·7)`.
* **Conclusion**: `ℓ ρ_n ≡ 1536 (1 + θ₀) u₀ = (6864/7) u₀ (mod ℓ)`, `u₀ = r_{1,0}/ℓ⁴` a unit; so
  `v_ℓ(ρ) = -1`.

**Lean proof (as formalised; namespace `AP7`, names `ap_*`).**  We reuse the `q`-integral
machinery of the pair's `Zeta2Lean/Pair/Proofs/Nonvanishing.lean` (`NVq.Zq`, `HasRes`, `IsU`,
`ZqPS`, ...).  Throughout `q = ℓ`, `hqu : q + 1 = 38u`; the final theorem takes `U = 10`, so
`q > 300` and all constants below are `q`-units.
1. *Middle poles* `2u+2 ≤ k ≤ q-1` (`ap_Gser_mem_mid`): all `j - k` are `q`-units, `G_k` is
   `q`-integral.
2. *End poles* `k ≤ 2u+1` (`ap_Gser_end`): `G_k = Q_{a'} Γ_k`, `Q_a = (ε + q/2)⁶ (ε + q)^{-a}`,
   `a' = a_{k+q}` (`2` for `k ≤ 1`, else `1`, `ap_apole_partner`), `Γ_k = Gam7 u q k` `q`-integral
   (`ap_Gam7_mem`) with `Γ₀(0)` a unit (`ap_gam00_unit`).  Rescaling `ε ↦ qε`
   (`ap_rescale_Qser7`) gives `q^μ [ε^μ] G_k ∈ q^{6-a'} ℤ_(q)`, so every `r_{i,k}` is integral
   (`ap_rcoef_end_mem`); mirror poles by `hV.symm` (`ap_rcoef_mem`).  Hence `v_q(Z) ≥ 0`.
3. *`A`-sums* (`ap_AhalfZ_split`): the only non-integral term of `AhalfZ (k - 20u) s` is
   `(-2/q)^s` (`k ≤ u`, `l = 19u`) or `(2/q)^s` (`k ≥ 39u`, `l = 19u - 1`).
4. *Residue of `q ρ`* (`ap_rho_res`): per pole `F_k = ∑_i q (i)₄ r_{i,k} A_{k,i}` is `0 mod q` for
   `2 ≤ k ≤ n-2` (`ap_Fk_mid`) and `12 Γ_k(0)` for `k ∈ {0,1}` and their mirrors
   (`ap_Fk_low`, `ap_Fk_top`, via `r_{1,k} = q⁴ Γ_k(0)/64`); so `q ρ ≡ -24 (Γ₀(0) + Γ₁(0))`.
5. *Ratio* (`ap_cc_ratio`, `ap_gam_ratio`): telescoping the blocks (`ap_block_tel`) and the pole
   products (`ap_pole_tel`, from the exponent identity
   `a_j + [j ∈ {2u-1,4u-1,6u-1}] = a_{j+1} + [j ∈ {34u,36u,38u}]`) gives
   `Γ₁(0) A₀ = Γ₀(0) B₀` with explicit integer polynomials `A₀ = A0R u`, `B₀ = B0R u`; modulo `q`
   (`38u ≡ 1`, `ap_field_facts`): `224 B₀ ≡ -81 A₀`, `A₀ ≢ 0` (`θ₀ = -81/224`).
6. *Conclusion* (`ap_field_final`, `ap_rho_val`): `-24(Γ₀(0) + Γ₁(0)) ≢ 0`, so `v_q(ρ) = -1`.

**Numerical check.** `python/z7_mirror.py`, section "AuxPrime7" (`n = 40, 120, 160`: `v_ℓ(ρ) = -1`,
`v_ℓ(Z) ≥ 0`, and `ℓρ ≡ (6864/7) u₀`); the research engines checked all 229 `n ∈ I`, `n ≤ 40000`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace AP7

open Zeta2.Pair.NVq hiding inv_mem
open Zeta2.Pair.NVq renaming inv_mem → zinv_mem

variable {q : ℕ} [hqP : Fact q.Prime]

/-! ### Arithmetic of `q = 38 u - 1` -/

theorem ap_u_pos {u : ℕ} (hqu : q + 1 = 38 * u) : 1 ≤ u := by
  have := (Fact.out : q.Prime).two_le
  omega

omit hqP in
theorem ap_q_cast {u : ℕ} (hqu : q + 1 = 38 * u) : (q : ℚ) = 38 * u - 1 := by
  have : ((q + 1 : ℕ) : ℚ) = ((38 * u : ℕ) : ℚ) := by rw [hqu]
  push_cast at this
  linarith

theorem ap_q0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

theorem ap_apole_low {u k : ℕ} (hu : 1 ≤ u) (hk : k ≤ u) : apole u k = 1 := by
  unfold apole
  split_ifs <;> omega

theorem ap_apole_high {u k : ℕ} (hu : 1 ≤ u) (hk1 : 39 * u ≤ k) (hk2 : k ≤ 40 * u) :
    apole u k = 1 := by
  unfold apole
  split_ifs <;> omega

theorem ap_apole_end {u k : ℕ} (hu : 1 ≤ u) (hk : k ≤ 2 * u + 1) : apole u k ≤ 2 := by
  unfold apole
  split_ifs <;> omega

theorem ap_apole_partner {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ 2 * u + 1) :
    apole u (k + q) = if k ≤ 1 then 2 else 1 := by
  have hu := ap_u_pos hqu
  unfold apole
  split_ifs <;> omega

theorem ap_eta_bounds (m : Fin 6) : 5 ≤ eta m ∧ eta m ≤ 13 := by
  fin_cases m <;> simp [eta]

/-! ### Middle poles: `G_k` is `q`-integral -/

/-- `(∏_{j ∈ S} (C(j - k) + X)^{e_j})⁻¹` is `q`-integral when all `j - k` are prime to `q`. -/
theorem ap_pole_inv_mem (S : Finset ℕ) (k : ℕ) (e : ℕ → ℕ)
    (hS : ∀ j ∈ S, ¬ (q : ℤ) ∣ ((j : ℤ) - k)) :
    (∏ j ∈ S, (C ((j : ℚ) - k) + X) ^ e j)⁻¹ ∈ ZqPS q := by
  have hcast : ∀ j : ℕ, ((j : ℚ) - k) = (((j : ℤ) - k : ℤ) : ℚ) := fun j => by push_cast; ring
  have hne : ∀ j ∈ S, ((j : ℚ) - k) ≠ 0 := by
    intro j hj h0
    apply hS j hj
    have : ((j : ℤ) - k : ℤ) = 0 := by exact_mod_cast (hcast j).symm.trans h0
    rw [this]
    exact dvd_zero _
  refine zinv_mem (prod_mem fun j _ => pow_mem (lin1_mem (sub_mem (Zq_nat j) (Zq_nat k))) _) ?_ ?_
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    rw [map_pow, constantCoeff_lin1]
    exact pow_ne_zero _ (hne j hj)
  · rw [map_prod, ← Finset.prod_inv_distrib]
    refine prod_mem fun j hj => ?_
    rw [map_pow, constantCoeff_lin1, ← inv_pow, hcast j]
    exact pow_mem (Zq_inv_int (hS j hj)) _

theorem ap_numfac_mem (hq2 : q ≠ 2) (k c : ℕ) : (-(k : ℚ) + 1 / 2 + (c : ℚ)) ∈ Zq q :=
  add_mem (add_mem (neg_mem (Zq_nat k)) (half_mem hq2)) (Zq_nat c)

theorem ap_numSer_mem (hq2 : q ≠ 2) (u k : ℕ) : numSer u (-(k : ℚ)) ∈ ZqPS q := by
  unfold numSer
  exact prod_mem fun _ _ => prod_mem fun c _ => lin1_mem (ap_numfac_mem hq2 k c)

theorem ap_Gser_mem_mid (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u) (hk1 : 2 * u + 2 ≤ k)
    (hk2 : k + 1 ≤ q) : Gser u k ∈ ZqPS q := by
  unfold Gser
  refine mul_mem (mul_mem (linG_mem _ _) (ap_numSer_mem hq2 _ _)) (ap_pole_inv_mem _ _ _ ?_)
  intro j hj
  have hj' := Finset.mem_erase.1 hj
  have hjn : j < 40 * u + 1 := Finset.mem_range.1 hj'.2
  have hjk : j ≠ k := hj'.1
  refine not_dvd_small ?_ ?_ ?_ <;> omega

/-! ### End poles `k ≤ 2u + 1`: `G_k = Q_{a'} · Γ_k` -/

/-- Numerator of `Γ_k`: the six factors `ε + q/2` (`c = k + 19u - 1`) removed. -/
def Nprime7 (u k : ℕ) : PowerSeries ℚ :=
  ∏ m : Fin 6, ∏ c ∈ (block u m).erase (k + 19 * u - 1), (C (-(k : ℚ) + 1 / 2 + (c : ℚ)) + X)

/-- Pole product of `Γ_k`: the factor `(ε + q)^{a_{k+q}}` removed. -/
def Pprime7 (u q k : ℕ) : PowerSeries ℚ :=
  ∏ j ∈ ((range (40 * u + 1)).erase k).erase (k + q), (C ((j : ℚ) - k) + X) ^ apole u j

/-- `Γ_k = G_k / Q_{a'}`. -/
def Gam7 (u q k : ℕ) : PowerSeries ℚ :=
  (C (((40 * u : ℕ) : ℚ) - 2 * k) + C 2 * X) * Nprime7 u k * (Pprime7 u q k)⁻¹

/-- `Q_a(ε) = (ε + q/2)⁶ (ε + q)^{-a}`. -/
def Qser7 (q a : ℕ) : PowerSeries ℚ :=
  (C ((q : ℚ) / 2) + X) ^ 6 * ((C (q : ℚ) + X) ^ a)⁻¹

/-- `Q_a(q ε) = q^{6-a} Qhat_a(ε)/64`, `Qhat_a = (1 + 2ε)⁶ (1 + ε)^{-a}`. -/
def Qhat7 (a : ℕ) : PowerSeries ℚ :=
  (1 + 2 * X) ^ 6 * ((1 + X) ^ a)⁻¹

theorem ap_c0_mem {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ 2 * u + 1) (m : Fin 6) :
    k + 19 * u - 1 ∈ block u m := by
  have hu := ap_u_pos hqu
  have he := ap_eta_bounds m
  have h1 : eta m * u ≤ 13 * u := Nat.mul_le_mul_right u he.2
  have h2 : 5 * u ≤ eta m * u := Nat.mul_le_mul_right u he.1
  simp only [block, Finset.mem_Ico]
  omega

theorem ap_Gser_end {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ 2 * u + 1) :
    Gser u k = Qser7 q (apole u (k + q)) * Gam7 u q k := by
  have hu := ap_u_pos hqu
  set g : ℕ → PowerSeries ℚ := fun c => C (-(k : ℚ) + 1 / 2 + (c : ℚ)) + X with hg
  have hf : g (k + 19 * u - 1) = C ((q : ℚ) / 2) + X := by
    simp only [hg]
    congr 2
    rw [ap_q_cast hqu, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hB : ∀ m : Fin 6, ∏ c ∈ block u m, g c =
      (C ((q : ℚ) / 2) + X) * ∏ c ∈ (block u m).erase (k + 19 * u - 1), g c := by
    intro m
    rw [← hf, Finset.mul_prod_erase _ _ (ap_c0_mem hqu hk m)]
  have hnum : numSer u (-(k : ℚ)) = (C ((q : ℚ) / 2) + X) ^ 6 * Nprime7 u k := by
    unfold numSer Nprime7
    change ∏ m : Fin 6, ∏ c ∈ block u m, g c = _
    rw [Finset.prod_congr rfl (fun m _ => hB m), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hmemP : k + q ∈ (range (40 * u + 1)).erase k := by
    rw [Finset.mem_erase, Finset.mem_range]
    have := (Fact.out : q.Prime).pos
    omega
  have hpole : ∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k) + X) ^ apole u j =
      (C (q : ℚ) + X) ^ apole u (k + q) * Pprime7 u q k := by
    unfold Pprime7
    rw [← Finset.mul_prod_erase _ _ hmemP]
    congr 3
    push_cast
    ring_nf
  unfold Gser Gam7 Qser7
  rw [hnum, hpole, PowerSeries.mul_inv_rev]
  ring

theorem ap_Gam7_mem (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ 2 * u + 1) :
    Gam7 u q k ∈ ZqPS q := by
  have hu := ap_u_pos hqu
  unfold Gam7 Nprime7 Pprime7
  refine mul_mem (mul_mem (linG_mem _ _) ?_) (ap_pole_inv_mem _ _ _ ?_)
  · exact prod_mem fun _ _ => prod_mem fun c _ => lin1_mem (ap_numfac_mem hq2 k c)
  · intro j hj
    have hj1 := Finset.mem_erase.1 hj
    have hj2 := Finset.mem_erase.1 hj1.2
    have hjn : j < 40 * u + 1 := Finset.mem_range.1 hj2.2
    refine not_dvd_two ?_ ?_ ?_ ?_ <;> omega

/-- `Γ₀(0)` is a `q`-adic unit. -/
theorem ap_gam00_unit {u : ℕ} (hqu : q + 1 = 38 * u) : IsU q (coeff 0 (Gam7 u q 0)) := by
  have hu := ap_u_pos hqu
  rw [coeff_zero_eq_constantCoeff_apply]
  unfold Gam7 Nprime7 Pprime7
  simp only [map_mul, map_prod, map_pow, constantCoeff_inv, map_add, constantCoeff_C,
    constantCoeff_X, add_zero, mul_zero, Nat.cast_zero, sub_zero, neg_zero, zero_add]
  refine IsU.mul (IsU.mul ?_ ?_) (IsU.inv ?_)
  · have : ((40 * u : ℕ) : ℚ) = (((40 * u : ℕ) : ℤ) : ℚ) := by push_cast; ring
    rw [this]
    refine IsU.int (not_dvd_two ?_ ?_ ?_ ?_) <;> push_cast <;> omega
  · refine IsU.prod _ _ fun m _ => IsU.prod _ _ fun c hc => ?_
    have hc1 := Finset.mem_erase.1 hc
    have hc2 : c < 40 * u := by
      have := hc1.2
      simp only [block, Finset.mem_Ico] at this
      omega
    have e : (1 / 2 + (c : ℚ)) = ((2 * c + 1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    refine IsU.div_int ?_ ?_
    · refine not_dvd_odd ?_ ?_ ?_ ?_ <;> omega
    · intro h
      have := Int.le_of_dvd (by norm_num) h
      have := (Fact.out : q.Prime).two_le
      omega
  · refine IsU.prod _ _ fun j hj => IsU.pow ?_ _
    have hj1 := Finset.mem_erase.1 hj
    have hj2 := Finset.mem_erase.1 hj1.2
    have hjn : j < 40 * u + 1 := Finset.mem_range.1 hj2.2
    have e : (j : ℚ) = ((j : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    refine IsU.int (not_dvd_two ?_ ?_ ?_ ?_) <;> omega

omit hqP in
theorem ap_rescale_Qser7 (a : ℕ) :
    rescale (q : ℚ) (Qser7 q a) = C (((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ a)⁻¹) * Qhat7 a := by
  have e1 : C ((q : ℚ) / 2) + C (q : ℚ) * X = C ((q : ℚ) / 2) * (1 + 2 * X) := by
    rw [mul_add, mul_one, ← mul_assoc, show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm,
      ← map_mul]
    congr 3
    ring
  have e2 : C (q : ℚ) + C (q : ℚ) * X = C (q : ℚ) * (1 + X) := by rw [mul_add, mul_one]
  unfold Qser7 Qhat7
  rw [map_mul, map_pow, rescale_inv', map_pow, rescale_lin1, rescale_lin1, e1, e2, mul_pow, mul_pow,
    PowerSeries.mul_inv_rev, ← map_pow, ← map_pow, PowerSeries.C_inv, map_mul]
  ring

theorem ap_Qhat7_mem (a : ℕ) : Qhat7 a ∈ ZqPS q := by
  unfold Qhat7
  refine mul_mem (pow_mem (add_mem (one_mem _) (mul_mem two_mem_PS X_mem)) 6) ?_
  exact zinv_mem (pow_mem (add_mem (one_mem _) X_mem) a) (by simp) (by simp)

theorem ap_coeff_Gser_end (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ 2 * u + 1)
    (μ : ℕ) : ∃ z ∈ Zq q, (q : ℚ) ^ μ * coeff μ (Gser u k) =
      ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ apole u (k + q))⁻¹ * z := by
  refine ⟨coeff μ (Qhat7 (apole u (k + q)) * rescale (q : ℚ) (Gam7 u q k)), ?_, ?_⟩
  · exact mem_ZqPS.1 (mul_mem (ap_Qhat7_mem _) (rescale_mem (Zq_nat q) (ap_Gam7_mem hq2 hqu hk))) μ
  · rw [← coeff_rescale, ap_Gser_end hqu hk, map_mul, ap_rescale_Qser7, mul_assoc,
      coeff_C_mul]

theorem ap_mem_of_qpow (hq2 : q ≠ 2) {x z : ℚ} {μ a : ℕ} (hle : a + μ ≤ 6) (hz : z ∈ Zq q)
    (h : (q : ℚ) ^ μ * x = ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ a)⁻¹ * z) : x ∈ Zq q := by
  have hq0 : (q : ℚ) ≠ 0 := ap_q0
  have hpow : (q : ℚ) ^ 6 = (q : ℚ) ^ μ * (q : ℚ) ^ a * (q : ℚ) ^ (6 - a - μ) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hx : x = (q : ℚ) ^ (6 - a - μ) * (1 / 2) ^ 6 * z := by
    have hμ : (q : ℚ) ^ μ ≠ 0 := pow_ne_zero _ hq0
    have ha : (q : ℚ) ^ a ≠ 0 := pow_ne_zero _ hq0
    apply mul_left_cancel₀ hμ
    rw [h, div_pow, hpow]
    field_simp
  rw [hx]
  exact mul_mem (mul_mem (pow_mem (Zq_nat q) _) (pow_mem (half_mem hq2) 6)) hz

theorem ap_rcoef_end_mem (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ 2 * u + 1)
    (i : ℕ) : rcoef u i k ∈ Zq q := by
  have hu := ap_u_pos hqu
  unfold rcoef
  split_ifs with h
  · obtain ⟨z, hz, hze⟩ := ap_coeff_Gser_end hq2 hqu hk (apole u k - i)
    have ha1 := ap_apole_end hu hk
    have ha2 : apole u (k + q) ≤ 2 := by
      rw [ap_apole_partner hqu hk]
      split_ifs <;> omega
    exact ap_mem_of_qpow hq2 (by omega) hz hze
  · exact zero_mem _

/-- Every `r_{i,k}` is `q`-integral. -/
theorem ap_rcoef_mem (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u : ℕ} (hqu : q + 1 = 38 * u)
    (i k : ℕ) : rcoef u i k ∈ Zq q := by
  have hu := ap_u_pos hqu
  by_cases hkn : k ≤ 40 * u
  swap
  · unfold rcoef
    split_ifs with h
    · exact absurd h.2.2 hkn
    · exact zero_mem _
  by_cases h1 : k ≤ 2 * u + 1
  · exact ap_rcoef_end_mem hq2 hqu h1 i
  by_cases h2 : k + 1 ≤ q
  · unfold rcoef
    split_ifs
    · exact mem_ZqPS.1 (ap_Gser_mem_mid hq2 hqu (by omega) h2) _
    · exact zero_mem _
  · have hk' : 40 * u - k ≤ 2 * u + 1 := by omega
    have hs := hV.symm u i (40 * u - k) (by omega)
    rw [show 40 * u - (40 * u - k) = k by omega] at hs
    rw [hs]
    exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (ap_rcoef_end_mem hq2 hqu hk' i)

/-! ### The centred `A`-sums -/

theorem ap_half_hi {u : ℕ} (hqu : q + 1 = 38 * u) :
    (((19 * u - 1 : ℕ) : ℚ) + 1 / 2)⁻¹ = 2 / (q : ℚ) := by
  have hu := ap_u_pos hqu
  rw [ap_q_cast hqu, Nat.cast_sub (by omega)]
  push_cast
  rw [show (19 * (u : ℚ) - 1 + 1 / 2) = (38 * u - 1) / 2 by ring, inv_div]

omit hqP in
theorem ap_half_lo {u : ℕ} (hqu : q + 1 = 38 * u) :
    ((1 : ℚ) / 2 - ((19 * u : ℕ) : ℚ))⁻¹ = -2 / (q : ℚ) := by
  rw [ap_q_cast hqu]
  push_cast
  rw [show (1 / 2 - 19 * (u : ℚ)) = -((38 * u - 1) / 2) by ring, inv_neg, inv_div, neg_div]

theorem ap_AhalfZ_split {u : ℕ} (hqu : q + 1 = 38 * u) {k : ℕ} (hk : k ≤ 40 * u) (s : ℕ) :
    ∃ A ∈ Zq q, AhalfZ ((k : ℤ) - ((20 * u : ℕ) : ℤ)) s =
      A + ((if k ≤ u then -((-2 / (q : ℚ)) ^ s) else 0) +
        (if 39 * u ≤ k then (2 / (q : ℚ)) ^ s else 0)) := by
  have hu := ap_u_pos hqu
  unfold AhalfZ
  by_cases hd : (0 : ℤ) ≤ (k : ℤ) - ((20 * u : ℕ) : ℤ)
  · have hk20 : 20 * u ≤ k := by push_cast at hd; omega
    have htn : ((k : ℤ) - ((20 * u : ℕ) : ℤ)).toNat = k - 20 * u := by omega
    rw [ite_eq_left hd, ite_eq_right (by omega : ¬ k ≤ u), htn, zero_add]
    have hterm : ∀ l ∈ range (k - 20 * u), l ≠ 19 * u - 1 →
        (((l : ℚ) + 1 / 2)⁻¹) ^ s ∈ Zq q := by
      intro l hl hne
      have hlk := Finset.mem_range.1 hl
      refine pow_mem ?_ s
      have e : ((l : ℚ) + 1 / 2)⁻¹ = ((2 : ℤ) : ℚ) / ((2 * (l : ℤ) + 1 : ℤ) : ℚ) := by
        push_cast
        rw [show ((l : ℚ) + 1 / 2) = (2 * l + 1) / 2 by ring, inv_div]
      rw [e]
      refine Zq_div_int 2 (not_dvd_odd ?_ ?_ ?_ ?_) <;> omega
    by_cases h39 : 39 * u ≤ k
    · have hl0 : 19 * u - 1 ∈ range (k - 20 * u) := Finset.mem_range.2 (by omega)
      refine ⟨∑ l ∈ (range (k - 20 * u)).erase (19 * u - 1), (((l : ℚ) + 1 / 2)⁻¹) ^ s,
        sum_mem fun l hl => hterm l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl), ?_⟩
      rw [ite_eq_left h39, ← Finset.sum_erase_add _ _ hl0, ap_half_hi hqu]
    · refine ⟨∑ l ∈ range (k - 20 * u), (((l : ℚ) + 1 / 2)⁻¹) ^ s,
        sum_mem fun l hl => hterm l hl ?_, ?_⟩
      · have := Finset.mem_range.1 hl
        omega
      · rw [ite_eq_right h39, add_zero]
  · have hk20 : k < 20 * u := by push_cast at hd; omega
    have htn : (-((k : ℤ) - ((20 * u : ℕ) : ℤ))).toNat = 20 * u - k := by omega
    rw [ite_eq_right hd, ite_eq_right (by omega : ¬ 39 * u ≤ k), htn, add_zero]
    have hterm : ∀ l ∈ Icc 1 (20 * u - k), l ≠ 19 * u →
        (((1 : ℚ) / 2 - l)⁻¹) ^ s ∈ Zq q := by
      intro l hl hne
      have hlk := Finset.mem_Icc.1 hl
      refine pow_mem ?_ s
      have e : ((1 : ℚ) / 2 - l)⁻¹ = ((2 : ℤ) : ℚ) / ((2 * (-(l : ℤ)) + 1 : ℤ) : ℚ) := by
        push_cast
        rw [show ((1 : ℚ) / 2 - l) = (2 * -(l : ℚ) + 1) / 2 by ring, inv_div]
      rw [e]
      refine Zq_div_int 2 (not_dvd_odd ?_ ?_ ?_ ?_) <;> omega
    by_cases hlow : k ≤ u
    · have hl0 : 19 * u ∈ Icc 1 (20 * u - k) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      refine ⟨-∑ l ∈ (Icc 1 (20 * u - k)).erase (19 * u), (((1 : ℚ) / 2 - l)⁻¹) ^ s,
        neg_mem (sum_mem fun l hl => hterm l (Finset.mem_of_mem_erase hl)
          (Finset.ne_of_mem_erase hl)), ?_⟩
      rw [ite_eq_left hlow, ← Finset.sum_erase_add _ _ hl0, neg_add, ap_half_lo hqu]
    · refine ⟨-∑ l ∈ Icc 1 (20 * u - k), (((1 : ℚ) / 2 - l)⁻¹) ^ s,
        neg_mem (sum_mem fun l hl => hterm l hl ?_), ?_⟩
      · have := Finset.mem_Icc.1 hl
        omega
      · rw [ite_eq_right hlow, add_zero]

/-! ### The residue of `q ρ` -/

/-- The `(i, k)` term of `-q ρ`. -/
def Tt (u Q i k : ℕ) : ℚ :=
  (Q : ℚ) * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef u i k *
    AhalfZ ((k : ℤ) - ((20 * u : ℕ) : ℤ)) (i + 4))

/-- The pole `k` part of `-q ρ`. -/
def Fk (u Q k : ℕ) : ℚ :=
  ∑ i ∈ Icc (1 : ℕ) 4, Tt u Q i k

theorem ap_q_rho (u Q : ℕ) : (Q : ℚ) * rho u = -∑ k ∈ range (40 * u + 1), Fk u Q k := by
  unfold rho genRhoZ Fk Tt
  rw [mul_neg]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem ap_P4_mem (i : ℕ) : ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) ∈ Zq q := by
  have : ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) = ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by
    push_cast
    ring
  rw [this]
  exact Zq_nat _

theorem ap_c24 : (24 : ℚ) ∈ Zq q := by exact_mod_cast Zq_nat 24

theorem ap_Tt_zero {u Q i k : ℕ} (hi : apole u k < i) : Tt u Q i k = 0 := by
  unfold Tt rcoef
  rw [ite_eq_right (by omega)]
  ring

theorem ap_Fk_eq_T1 {u Q k : ℕ} (ha : apole u k = 1) : Fk u Q k = Tt u Q 1 k := by
  unfold Fk
  rw [Finset.sum_eq_single 1]
  · intro i hi hne
    have := Finset.mem_Icc.1 hi
    exact ap_Tt_zero (by omega)
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by norm_num⟩) h

theorem ap_Tt_mid (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u i k : ℕ} (hqu : q + 1 = 38 * u)
    (hk1 : u < k) (hk2 : k < 39 * u) : HasRes q (Tt u q i k) 0 := by
  obtain ⟨A, hA, hAe⟩ := ap_AhalfZ_split hqu (k := k) (by omega) (i + 4)
  unfold Tt
  rw [hAe, ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero]
  exact HasRes.q_mul (mul_mem (mul_mem (ap_P4_mem i) (ap_rcoef_mem hV hq2 hqu i k)) hA)

theorem ap_T1_bad {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ u ∨ 39 * u ≤ k)
    (hkn : k ≤ 40 * u) : ∃ A ∈ Zq q, Tt u q 1 k =
      (q : ℚ) * (24 * rcoef u 1 k * A) + 768 * (rcoef u 1 k / (q : ℚ) ^ 4) := by
  have hu := ap_u_pos hqu
  have hq0 : (q : ℚ) ≠ 0 := ap_q0
  obtain ⟨A, hA, hAe⟩ := ap_AhalfZ_split hqu hkn (1 + 4)
  refine ⟨A, hA, ?_⟩
  unfold Tt
  rw [hAe]
  have hqq : (q : ℚ) * (q : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hq0
  rcases hk with hk | hk
  · rw [ite_eq_left hk, ite_eq_right (by omega), add_zero]
    simp only [Nat.cast_one]
    linear_combination (768 * rcoef u 1 k * ((q : ℚ)⁻¹) ^ 4) * hqq
  · rw [ite_eq_right (by omega), ite_eq_left hk, zero_add]
    simp only [Nat.cast_one]
    linear_combination (768 * rcoef u 1 k * ((q : ℚ)⁻¹) ^ 4) * hqq

/-- `r_{1,k} = Q_{a'}(0) Γ_k(0)` for `k ≤ u`. -/
theorem ap_rcoef_small {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ u) :
    rcoef u 1 k = ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ apole u (k + q))⁻¹ * coeff 0 (Gam7 u q k) := by
  have hu := ap_u_pos hqu
  have ha : apole u k = 1 := ap_apole_low hu hk
  have hc : constantCoeff (Qser7 q (apole u (k + q))) =
      ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ apole u (k + q))⁻¹ := by
    unfold Qser7
    simp only [map_mul, map_pow, constantCoeff_inv, map_add, constantCoeff_C, constantCoeff_X,
      add_zero]
  unfold rcoef
  rw [ite_eq_left ⟨le_rfl, by omega, by omega⟩, ha, Nat.sub_self, ap_Gser_end hqu (by omega),
    coeff_zero_eq_constantCoeff_apply, map_mul, hc, coeff_zero_eq_constantCoeff_apply]

theorem ap_bad_res (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u) (hk : k ≤ u) :
    HasRes q (768 * (rcoef u 1 k / (q : ℚ) ^ 4))
      (if k ≤ 1 then 12 * ((coeff 0 (Gam7 u q k) : ℚ) : ZMod q) else 0) := by
  have hu := ap_u_pos hqu
  have hq0 : (q : ℚ) ≠ 0 := ap_q0
  have hγ : coeff 0 (Gam7 u q k) ∈ Zq q := mem_ZqPS.1 (ap_Gam7_mem hq2 hqu (by omega)) 0
  rw [ap_rcoef_small hqu hk, ap_apole_partner hqu (by omega)]
  split_ifs with h1
  · have e : 768 * (((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ 2)⁻¹ * coeff 0 (Gam7 u q k) / (q : ℚ) ^ 4) =
        12 * coeff 0 (Gam7 u q k) := by
      field_simp
      ring
    rw [e]
    have := (HasRes.nat (q := q) 12).mul (HasRes.of_mem hγ)
    simpa using this
  · have e : 768 * (((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ 1)⁻¹ * coeff 0 (Gam7 u q k) / (q : ℚ) ^ 4) =
        (q : ℚ) * (12 * coeff 0 (Gam7 u q k)) := by
      field_simp
      ring
    rw [e]
    exact HasRes.q_mul (mul_mem (by exact_mod_cast Zq_nat 12) hγ)

theorem ap_Fk_low (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u)
    (hk : k ≤ 1) : HasRes q (Fk u q k) (12 * ((coeff 0 (Gam7 u q k) : ℚ) : ZMod q)) := by
  have hu := ap_u_pos hqu
  rw [ap_Fk_eq_T1 (ap_apole_low hu (by omega))]
  obtain ⟨A, hA, hAe⟩ := ap_T1_bad hqu (k := k) (Or.inl (by omega)) (by omega)
  rw [hAe]
  have h1 := HasRes.q_mul (q := q) (mul_mem (mul_mem ap_c24 (ap_rcoef_mem hV hq2 hqu 1 k)) hA)
  have h2 := ap_bad_res hq2 hqu (k := k) (by omega)
  rw [ite_eq_left hk] at h2
  exact (h1.add h2).congr rfl (by simp)

theorem ap_Fk_top (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u)
    (hk : k ≤ 1) :
    HasRes q (Fk u q (40 * u - k)) (12 * ((coeff 0 (Gam7 u q k) : ℚ) : ZMod q)) := by
  have hu := ap_u_pos hqu
  rw [ap_Fk_eq_T1 (ap_apole_high hu (by omega) (by omega))]
  obtain ⟨A, hA, hAe⟩ := ap_T1_bad hqu (k := 40 * u - k) (Or.inr (by omega)) (by omega)
  have hs : rcoef u 1 (40 * u - k) = rcoef u 1 k := by
    rw [hV.symm u 1 k (by omega)]
    norm_num
  rw [hAe, hs]
  have h1 := HasRes.q_mul (q := q) (mul_mem (mul_mem ap_c24 (ap_rcoef_mem hV hq2 hqu 1 k)) hA)
  have h2 := ap_bad_res hq2 hqu (k := k) (by omega)
  rw [ite_eq_left hk] at h2
  exact (h1.add h2).congr rfl (by simp)

theorem ap_Fk_mid (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u k : ℕ} (hqu : q + 1 = 38 * u)
    (hk1 : 2 ≤ k) (hk2 : k + 2 ≤ 40 * u) : HasRes q (Fk u q k) 0 := by
  have hu := ap_u_pos hqu
  by_cases hlow : k ≤ u
  · rw [ap_Fk_eq_T1 (ap_apole_low hu hlow)]
    obtain ⟨A, hA, hAe⟩ := ap_T1_bad hqu (Or.inl hlow) (by omega)
    rw [hAe]
    have h1 := HasRes.q_mul (q := q) (mul_mem (mul_mem ap_c24 (ap_rcoef_mem hV hq2 hqu 1 k)) hA)
    have h2 := ap_bad_res hq2 hqu hlow
    rw [ite_eq_right (by omega)] at h2
    exact (h1.add h2).congr rfl (by simp)
  by_cases hhigh : 39 * u ≤ k
  · rw [ap_Fk_eq_T1 (ap_apole_high hu hhigh (by omega))]
    obtain ⟨A, hA, hAe⟩ := ap_T1_bad hqu (Or.inr hhigh) (by omega)
    have hs : rcoef u 1 k = rcoef u 1 (40 * u - k) := by
      have := hV.symm u 1 (40 * u - k) (by omega)
      rw [show 40 * u - (40 * u - k) = k by omega] at this
      rw [this]
      norm_num
    rw [hAe, hs]
    have h1 := HasRes.q_mul (q := q)
      (mul_mem (mul_mem ap_c24 (ap_rcoef_mem hV hq2 hqu 1 (40 * u - k))) hA)
    have h2 := ap_bad_res hq2 hqu (k := 40 * u - k) (by omega)
    rw [ite_eq_right (by omega)] at h2
    exact (h1.add h2).congr rfl (by simp)
  · have := HasRes.sum (Icc (1 : ℕ) 4) (fun i => Tt u q i k) (fun _ => (0 : ZMod q))
      fun i _ => ap_Tt_mid hV hq2 hqu (by omega) (by omega)
    exact this.congr rfl (by simp)

/-- The residue of `q ρ`: `-24 (Γ₀(0) + Γ₁(0))`. -/
theorem ap_rho_res (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u : ℕ} (hqu : q + 1 = 38 * u) :
    HasRes q ((q : ℚ) * rho u) (-(24 * (((coeff 0 (Gam7 u q 0) : ℚ) : ZMod q) +
      ((coeff 0 (Gam7 u q 1) : ℚ) : ZMod q)))) := by
  have hu := ap_u_pos hqu
  rw [ap_q_rho]
  have e2 : 40 * u + 1 = 40 * u - 3 + 1 + 1 + 1 + 1 := by omega
  rw [e2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ',
    Finset.sum_range_succ']
  have hmid := HasRes.sum (range (40 * u - 3)) (fun k => Fk u q (k + 1 + 1))
    (fun _ => (0 : ZMod q))
    fun k hk => ap_Fk_mid hV hq2 hqu (by omega) (by have := Finset.mem_range.1 hk; omega)
  have h1 : HasRes q (Fk u q (0 + 1)) (12 * ((coeff 0 (Gam7 u q 1) : ℚ) : ZMod q)) :=
    ap_Fk_low hV hq2 hqu (k := 1) le_rfl
  have h0 := ap_Fk_low hV hq2 hqu (k := 0) (by norm_num)
  have ht1 := ap_Fk_top hV hq2 hqu (k := 1) le_rfl
  have ht0 := ap_Fk_top hV hq2 hqu (k := 0) (by norm_num)
  rw [show 40 * u - 1 = 40 * u - 3 + 1 + 1 by omega] at ht1
  rw [show 40 * u - 0 = 40 * u - 3 + 1 + 1 + 1 by omega] at ht0
  refine (HasRes.neg ((((hmid.add h1).add h0).add ht1).add ht0)).congr rfl ?_
  rw [Finset.sum_const_zero]
  ring_nf

/-! ### The two singular poles: the telescoped ratio `r_{1,1} / r_{1,0}` -/

theorem ap_cc_Gser (u k : ℕ) : constantCoeff (Gser u k) =
    (((40 * u : ℕ) : ℚ) - 2 * k) * (∏ m : Fin 6, ∏ c ∈ block u m, (-(k : ℚ) + 1 / 2 + (c : ℚ))) *
      (∏ j ∈ (range (40 * u + 1)).erase k, ((j : ℚ) - k) ^ apole u j)⁻¹ := by
  unfold Gser numSer
  simp only [map_mul, map_prod, map_pow, constantCoeff_inv, map_add, constantCoeff_C,
    constantCoeff_X, add_zero, mul_zero]

/-- One block: `∏_{c ∈ [α, β)} (c - 1/2) · (2β - 1) = ∏_{c ∈ [α, β)} (c + 1/2) · (2α - 1)`. -/
theorem ap_block_tel (α β : ℕ) (h : α ≤ β) :
    (∏ c ∈ Ico α β, (-(1 : ℚ) + 1 / 2 + (c : ℚ))) * (2 * (β : ℚ) - 1) =
      (∏ c ∈ Ico α β, (1 / 2 + (c : ℚ))) * (2 * (α : ℚ) - 1) := by
  induction β, h using Nat.le_induction with
  | base => simp
  | succ β hαβ ih =>
    rw [Finset.prod_Ico_succ_top hαβ, Finset.prod_Ico_succ_top hαβ]
    push_cast
    linear_combination ((2 * (β : ℚ) + 1) / 2) * ih

theorem ap_prod_beta (u : ℕ) :
    ∏ m : Fin 6, (2 * ((40 * u - eta m * u : ℕ) : ℚ) - 1) =
      (70 * (u : ℚ) - 1) * (66 * u - 1) * (66 * u - 1) * (62 * u - 1) * (58 * u - 1) *
        (54 * u - 1) := by
  have e0 : eta 0 = 5 := rfl
  have e1 : eta 1 = 7 := rfl
  have e2 : eta 2 = 7 := rfl
  have e3 : eta 3 = 9 := rfl
  have e4 : eta 4 = 11 := rfl
  have e5 : eta 5 = 13 := rfl
  simp only [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5]
  rw [show 40 * u - 5 * u = 35 * u by omega, show 40 * u - 7 * u = 33 * u by omega,
    show 40 * u - 9 * u = 31 * u by omega, show 40 * u - 11 * u = 29 * u by omega,
    show 40 * u - 13 * u = 27 * u by omega]
  push_cast
  ring

theorem ap_prod_alpha (u : ℕ) :
    ∏ m : Fin 6, (2 * ((eta m * u : ℕ) : ℚ) - 1) =
      (10 * (u : ℚ) - 1) * (14 * u - 1) * (14 * u - 1) * (18 * u - 1) * (22 * u - 1) *
        (26 * u - 1) := by
  have e0 : eta 0 = 5 := rfl
  have e1 : eta 1 = 7 := rfl
  have e2 : eta 2 = 7 := rfl
  have e3 : eta 3 = 9 := rfl
  have e4 : eta 4 = 11 := rfl
  have e5 : eta 5 = 13 := rfl
  simp only [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5]
  push_cast
  ring

theorem ap_num_tel (u : ℕ) :
    (∏ m : Fin 6, ∏ c ∈ block u m, (-((1 : ℕ) : ℚ) + 1 / 2 + (c : ℚ))) *
      ((70 * (u : ℚ) - 1) * (66 * u - 1) * (66 * u - 1) * (62 * u - 1) * (58 * u - 1) *
        (54 * u - 1)) =
    (∏ m : Fin 6, ∏ c ∈ block u m, (-((0 : ℕ) : ℚ) + 1 / 2 + (c : ℚ))) *
      ((10 * (u : ℚ) - 1) * (14 * u - 1) * (14 * u - 1) * (18 * u - 1) * (22 * u - 1) *
        (26 * u - 1)) := by
  have hb : ∀ m : Fin 6, (∏ c ∈ block u m, (-((1 : ℕ) : ℚ) + 1 / 2 + (c : ℚ))) *
      (2 * ((40 * u - eta m * u : ℕ) : ℚ) - 1) =
      (∏ c ∈ block u m, (-((0 : ℕ) : ℚ) + 1 / 2 + (c : ℚ))) *
        (2 * ((eta m * u : ℕ) : ℚ) - 1) := by
    intro m
    have hle : eta m * u ≤ 40 * u - eta m * u := by
      have he := ap_eta_bounds m
      have : eta m * u ≤ 13 * u := Nat.mul_le_mul_right u he.2
      omega
    have := ap_block_tel (eta m * u) (40 * u - eta m * u) hle
    simp only [block, Nat.cast_one, Nat.cast_zero, neg_zero, zero_add]
    exact this
  rw [← ap_prod_beta, ← ap_prod_alpha, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => hb m

/-- The pole exponents jump by `+1` at `2u, 4u, 6u` and by `-1` after `34u, 36u, 38u`. -/
theorem ap_key_tel {u : ℕ} (hu : 1 ≤ u) :
    (∏ t ∈ range (40 * u - 1), ((1 + t : ℕ) : ℚ) ^ apole u (1 + t)) *
      ((2 * (u : ℚ) - 1) * (4 * u - 1) * (6 * u - 1)) =
    (∏ t ∈ range (40 * u - 1), ((1 + t : ℕ) : ℚ) ^ apole u (2 + t)) *
      (34 * (u : ℚ) * (36 * u) * (38 * u)) := by
  have hexp : ∀ t ∈ range (40 * u - 1),
      apole u (1 + t) +
          (if 1 + t = 2 * u - 1 ∨ 1 + t = 4 * u - 1 ∨ 1 + t = 6 * u - 1 then 1 else 0) =
        apole u (2 + t) + (if 1 + t = 34 * u ∨ 1 + t = 36 * u ∨ 1 + t = 38 * u then 1 else 0) := by
    intro t ht
    have := Finset.mem_range.1 ht
    unfold apole
    split_ifs <;> omega
  have hm : ∏ t ∈ range (40 * u - 1), ((1 + t : ℕ) : ℚ) ^
      (if 1 + t = 2 * u - 1 ∨ 1 + t = 4 * u - 1 ∨ 1 + t = 6 * u - 1 then 1 else 0) =
      (2 * (u : ℚ) - 1) * (4 * u - 1) * (6 * u - 1) := by
    have h1 : ∏ t ∈ range (40 * u - 1), ((1 + t : ℕ) : ℚ) ^
        (if 1 + t = 2 * u - 1 ∨ 1 + t = 4 * u - 1 ∨ 1 + t = 6 * u - 1 then 1 else 0) =
        ∏ t ∈ (range (40 * u - 1)).filter
          (fun t => 1 + t = 2 * u - 1 ∨ 1 + t = 4 * u - 1 ∨ 1 + t = 6 * u - 1),
          ((1 + t : ℕ) : ℚ) := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun t _ => ?_
      split_ifs <;> simp
    have h2 : (range (40 * u - 1)).filter
        (fun t => 1 + t = 2 * u - 1 ∨ 1 + t = 4 * u - 1 ∨ 1 + t = 6 * u - 1) =
        {2 * u - 2, 4 * u - 2, 6 * u - 2} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [h1, h2, Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_singleton, show 1 + (2 * u - 2) = 2 * u - 1 by omega,
      show 1 + (4 * u - 2) = 4 * u - 1 by omega, show 1 + (6 * u - 2) = 6 * u - 1 by omega,
      Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hp : ∏ t ∈ range (40 * u - 1), ((1 + t : ℕ) : ℚ) ^
      (if 1 + t = 34 * u ∨ 1 + t = 36 * u ∨ 1 + t = 38 * u then 1 else 0) =
      34 * (u : ℚ) * (36 * u) * (38 * u) := by
    have h1 : ∏ t ∈ range (40 * u - 1), ((1 + t : ℕ) : ℚ) ^
        (if 1 + t = 34 * u ∨ 1 + t = 36 * u ∨ 1 + t = 38 * u then 1 else 0) =
        ∏ t ∈ (range (40 * u - 1)).filter
          (fun t => 1 + t = 34 * u ∨ 1 + t = 36 * u ∨ 1 + t = 38 * u), ((1 + t : ℕ) : ℚ) := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun t _ => ?_
      split_ifs <;> simp
    have h2 : (range (40 * u - 1)).filter
        (fun t => 1 + t = 34 * u ∨ 1 + t = 36 * u ∨ 1 + t = 38 * u) =
        {34 * u - 1, 36 * u - 1, 38 * u - 1} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [h1, h2, Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_singleton, show 1 + (34 * u - 1) = 34 * u by omega,
      show 1 + (36 * u - 1) = 36 * u by omega, show 1 + (38 * u - 1) = 38 * u by omega]
    push_cast
    ring
  rw [← hm, ← hp, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [← pow_add, ← pow_add, hexp t ht]

/-- The pole products: `F₀ · (2u-1)(4u-1)(6u-1) = -n · 34u · 36u · 38u · F₁`. -/
theorem ap_pole_tel {u : ℕ} (hu : 1 ≤ u) :
    (∏ j ∈ (range (40 * u + 1)).erase 0, ((j : ℚ) - ((0 : ℕ) : ℚ)) ^ apole u j) *
      ((2 * (u : ℚ) - 1) * (4 * u - 1) * (6 * u - 1)) =
    -(40 * (u : ℚ)) * (34 * (u : ℚ) * (36 * u) * (38 * u)) *
      ∏ j ∈ (range (40 * u + 1)).erase 1, ((j : ℚ) - ((1 : ℕ) : ℚ)) ^ apole u j := by
  have hE0 : (range (40 * u + 1)).erase 0 = Ico 1 (40 * u + 1) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hE1 : (range (40 * u + 1)).erase 1 = insert 0 (Ico 2 (40 * u + 1)) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico, Finset.mem_insert]
    omega
  have h0 : (0 : ℕ) ∉ Ico 2 (40 * u + 1) := by simp
  rw [hE0, hE1, Finset.prod_insert h0, Finset.prod_Ico_eq_prod_range,
    Finset.prod_Ico_eq_prod_range, show 40 * u + 1 - 1 = (40 * u - 1) + 1 by omega,
    show 40 * u + 1 - 2 = 40 * u - 1 by omega, Finset.prod_range_succ]
  have ha0 : apole u 0 = 1 := ap_apole_low hu (Nat.zero_le _)
  have han : apole u (1 + (40 * u - 1)) = 1 := ap_apole_high hu (by omega) (by omega)
  have hn : ((1 + (40 * u - 1) : ℕ) : ℚ) = 40 * (u : ℚ) := by
    rw [show 1 + (40 * u - 1) = 40 * u by omega]
    push_cast
    ring
  have hR : ∀ t : ℕ, ((2 + t : ℕ) : ℚ) - 1 = ((1 + t : ℕ) : ℚ) := by
    intro t
    push_cast
    ring
  simp only [Nat.cast_zero, Nat.cast_one, sub_zero, hR, ha0, han, hn, pow_one, zero_sub]
  have key := ap_key_tel hu
  linear_combination (40 * (u : ℚ)) * key

theorem ap_ratio_alg {n N0 N1 F0 F1 Pα Pβ Dm Dp : ℚ} (hF0 : F0 ≠ 0) (hF1 : F1 ≠ 0)
    (hN : N1 * Pβ = N0 * Pα) (hP : F0 * Dm = -n * Dp * F1) :
    (n - 2) * N1 * F1⁻¹ * (n * Pβ * Dm) = n * N0 * F0⁻¹ * -((n - 2) * Pα * n * Dp) := by
  have e1 : F0 * F0⁻¹ = 1 := mul_inv_cancel₀ hF0
  have e2 : F1 * F1⁻¹ = 1 := mul_inv_cancel₀ hF1
  linear_combination ((n - 2) * n * Dm * F1⁻¹) * hN + ((n - 2) * n * N0 * Pα * F0⁻¹ * F1⁻¹) * hP
    - ((n - 2) * n * N0 * Pα * Dm * F1⁻¹) * e1 - ((n - 2) * n * N0 * Pα * n * Dp * F0⁻¹) * e2

/-- `A₀ = n ∏_m (2(1-η_m)n - 1) · (n/20 - 1)(n/10 - 1)(3n/20 - 1)` in the variable `u = n/40`. -/
def A0R {R : Type*} [CommRing R] (U : R) : R :=
  40 * U * ((70 * U - 1) * (66 * U - 1) * (66 * U - 1) * (62 * U - 1) * (58 * U - 1) *
    (54 * U - 1)) * ((2 * U - 1) * (4 * U - 1) * (6 * U - 1))

/-- `B₀ = -(n-2) ∏_m (2η_m n - 1) · n · (17n/20)(9n/10)(19n/20)`. -/
def B0R {R : Type*} [CommRing R] (U : R) : R :=
  -((40 * U - 2) * ((10 * U - 1) * (14 * U - 1) * (14 * U - 1) * (18 * U - 1) * (22 * U - 1) *
    (26 * U - 1)) * (40 * U) * (34 * U * (36 * U) * (38 * U)))

theorem ap_A0R_cast {R : Type*} [CommRing R] (U : ℤ) : ((A0R U : ℤ) : R) = A0R (U : R) := by
  unfold A0R
  push_cast
  ring

theorem ap_B0R_cast {R : Type*} [CommRing R] (U : ℤ) : ((B0R U : ℤ) : R) = B0R (U : R) := by
  unfold B0R
  push_cast
  ring

/-- The telescoped identity `r_{1,1} A₀ = r_{1,0} B₀`. -/
theorem ap_cc_ratio {u : ℕ} (hu : 1 ≤ u) :
    constantCoeff (Gser u 1) * A0R (u : ℚ) = constantCoeff (Gser u 0) * B0R (u : ℚ) := by
  have hN := ap_num_tel u
  have hP := ap_pole_tel hu
  have hF0 : ∏ j ∈ (range (40 * u + 1)).erase 0, ((j : ℚ) - ((0 : ℕ) : ℚ)) ^ apole u j ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ ?_
    have := Finset.ne_of_mem_erase hj
    rw [sub_ne_zero]
    exact_mod_cast this
  have hF1 : ∏ j ∈ (range (40 * u + 1)).erase 1, ((j : ℚ) - ((1 : ℕ) : ℚ)) ^ apole u j ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ ?_
    have := Finset.ne_of_mem_erase hj
    rw [sub_ne_zero]
    exact_mod_cast this
  have hl1 : (((40 * u : ℕ) : ℚ) - 2 * ((1 : ℕ) : ℚ)) = 40 * (u : ℚ) - 2 := by push_cast; ring
  have hl0 : (((40 * u : ℕ) : ℚ) - 2 * ((0 : ℕ) : ℚ)) = 40 * (u : ℚ) := by push_cast; ring
  rw [ap_cc_Gser, ap_cc_Gser, hl1, hl0]
  unfold A0R B0R
  exact ap_ratio_alg hF0 hF1 hN hP

/-- `Γ₁(0) A₀ = Γ₀(0) B₀`. -/
theorem ap_gam_ratio {u : ℕ} (hqu : q + 1 = 38 * u) :
    coeff 0 (Gam7 u q 1) * A0R (u : ℚ) = coeff 0 (Gam7 u q 0) * B0R (u : ℚ) := by
  have hu := ap_u_pos hqu
  have h := ap_cc_ratio (u := u) hu
  have hc : ∀ k ≤ 1, constantCoeff (Gser u k) =
      ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ 2)⁻¹ * coeff 0 (Gam7 u q k) := by
    intro k hk
    have hQ : constantCoeff (Qser7 q 2) = ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ 2)⁻¹ := by
      unfold Qser7
      simp only [map_mul, map_pow, constantCoeff_inv, map_add, constantCoeff_C, constantCoeff_X,
        add_zero]
    rw [ap_Gser_end hqu (by omega), ap_apole_partner hqu (by omega), ite_eq_left hk, map_mul, hQ,
      coeff_zero_eq_constantCoeff_apply]
  rw [hc 1 le_rfl, hc 0 (by norm_num)] at h
  have hq0 : (q : ℚ) ≠ 0 := ap_q0
  have hc0 : ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ 2)⁻¹ ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (div_ne_zero hq0 two_ne_zero)
    · exact inv_ne_zero (pow_ne_zero _ hq0)
  apply mul_left_cancel₀ hc0
  linear_combination h

/-! ### The arithmetic modulo `q` -/

/-- Modulo `q` (`38 u ≡ 1`): `A₀ ≢ 0` and `224 B₀ = -81 A₀` (`θ₀ = -81/224`). -/
theorem ap_field_facts {K : Type*} [Field K] (U : K) (h38 : 38 * U = 1)
    (hc : ∀ n : ℕ, 0 < n → n ≤ 300 → (n : K) ≠ 0) :
    A0R U ≠ 0 ∧ 224 * B0R U = -81 * A0R U := by
  have hU : U ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h38
    exact zero_ne_one h38
  have hA : A0R U = 40 * U * (32 * U * (28 * U) * (28 * U) * (24 * U) * (20 * U) * (16 * U)) *
      (-36 * U * (-34 * U) * (-32 * U)) := by
    unfold A0R
    have f70 : 70 * U - 1 = 32 * U := by linear_combination h38
    have f66 : 66 * U - 1 = 28 * U := by linear_combination h38
    have f62 : 62 * U - 1 = 24 * U := by linear_combination h38
    have f58 : 58 * U - 1 = 20 * U := by linear_combination h38
    have f54 : 54 * U - 1 = 16 * U := by linear_combination h38
    have f2 : 2 * U - 1 = -36 * U := by linear_combination h38
    have f4 : 4 * U - 1 = -34 * U := by linear_combination h38
    have f6 : 6 * U - 1 = -32 * U := by linear_combination h38
    rw [f70, f66, f62, f58, f54, f2, f4, f6]
  have hB : B0R U = -(-36 * U * (-28 * U * (-24 * U) * (-24 * U) * (-20 * U) * (-16 * U) *
      (-12 * U)) * (40 * U) * (34 * U * (36 * U) * 1)) := by
    unfold B0R
    have f40 : 40 * U - 2 = -36 * U := by linear_combination 2 * h38
    have f10 : 10 * U - 1 = -28 * U := by linear_combination h38
    have f14 : 14 * U - 1 = -24 * U := by linear_combination h38
    have f18 : 18 * U - 1 = -20 * U := by linear_combination h38
    have f22 : 22 * U - 1 = -16 * U := by linear_combination h38
    have f26 : 26 * U - 1 = -12 * U := by linear_combination h38
    rw [f40, f10, f14, f18, f22, f26, h38]
  refine ⟨?_, ?_⟩
  · have h40 : (40 : K) ≠ 0 := by exact_mod_cast hc 40 (by norm_num) (by norm_num)
    have h36 : (36 : K) ≠ 0 := by exact_mod_cast hc 36 (by norm_num) (by norm_num)
    have h34 : (34 : K) ≠ 0 := by exact_mod_cast hc 34 (by norm_num) (by norm_num)
    have h32 : (32 : K) ≠ 0 := by exact_mod_cast hc 32 (by norm_num) (by norm_num)
    have h28 : (28 : K) ≠ 0 := by exact_mod_cast hc 28 (by norm_num) (by norm_num)
    have h24 : (24 : K) ≠ 0 := by exact_mod_cast hc 24 (by norm_num) (by norm_num)
    have h20 : (20 : K) ≠ 0 := by exact_mod_cast hc 20 (by norm_num) (by norm_num)
    have h16 : (16 : K) ≠ 0 := by exact_mod_cast hc 16 (by norm_num) (by norm_num)
    rw [hA]
    simp [hU, h40, h36, h34, h32, h28, h24, h20, h16]
  · rw [hA, hB]
    ring

/-- The final linear algebra modulo `q`. -/
theorem ap_field_final {K : Type*} [Field K] {g0 g1 A B : K} (hr : g1 * A = g0 * B)
    (hAB : 224 * B = -81 * A) (hA : A ≠ 0) (hg0 : g0 ≠ 0) (h143 : (143 : K) ≠ 0)
    (h24 : (24 : K) ≠ 0) : -(24 * (g0 + g1)) ≠ 0 := by
  intro h
  have h1 : g0 + g1 = 0 := by
    have : 24 * (g0 + g1) = 0 := neg_eq_zero.1 h
    exact (mul_eq_zero.1 this).resolve_left h24
  have h2 : 143 * g0 * A = 0 := by
    linear_combination (224 * A) * h1 + (-224) * hr + (-g0) * hAB
  exact mul_ne_zero (mul_ne_zero h143 hg0) hA h2

theorem ap_res_ne_zero (hq2 : q ≠ 2) {u : ℕ} (hqu : q + 1 = 38 * u) (hbig : 300 < q) :
    -(24 * (((coeff 0 (Gam7 u q 0) : ℚ) : ZMod q) + ((coeff 0 (Gam7 u q 1) : ℚ) : ZMod q))) ≠
      0 := by
  have hu := ap_u_pos hqu
  have hid := ap_gam_ratio hqu
  have hγ0 : coeff 0 (Gam7 u q 0) ∈ Zq q := mem_ZqPS.1 (ap_Gam7_mem hq2 hqu (by omega)) 0
  have hγ1 : coeff 0 (Gam7 u q 1) ∈ Zq q := mem_ZqPS.1 (ap_Gam7_mem hq2 hqu (by omega)) 0
  have hA : HasRes q (A0R (u : ℚ)) (A0R (u : ZMod q)) := by
    refine (HasRes.int (q := q) (A0R (u : ℤ))).congr ?_ ?_
    · rw [ap_A0R_cast, Int.cast_natCast]
    · rw [ap_A0R_cast, Int.cast_natCast]
  have hB : HasRes q (B0R (u : ℚ)) (B0R (u : ZMod q)) := by
    refine (HasRes.int (q := q) (B0R (u : ℤ))).congr ?_ ?_
    · rw [ap_B0R_cast, Int.cast_natCast]
    · rw [ap_B0R_cast, Int.cast_natCast]
  have r := (HasRes.of_mem hγ1).mul hA
  rw [hid] at r
  have r' := r.2.symm.trans ((HasRes.of_mem hγ0).mul hB).2
  have h38 : (38 : ZMod q) * (u : ZMod q) = 1 := by
    have : ((q + 1 : ℕ) : ZMod q) = ((38 * u : ℕ) : ZMod q) := by rw [hqu]
    push_cast at this
    rw [ZMod.natCast_self, zero_add] at this
    exact this.symm
  have hc : ∀ n : ℕ, 0 < n → n ≤ 300 → (n : ZMod q) ≠ 0 :=
    fun n h1 h2 => zmod_ne_zero_of_lt h1 (by omega)
  obtain ⟨hA0, hAB⟩ := ap_field_facts (u : ZMod q) h38 hc
  have hg0 : ((coeff 0 (Gam7 u q 0) : ℚ) : ZMod q) ≠ 0 := (ap_gam00_unit hqu).2
  have h143 : (143 : ZMod q) ≠ 0 := by exact_mod_cast hc 143 (by norm_num) (by norm_num)
  have h24 : (24 : ZMod q) ≠ 0 := by exact_mod_cast hc 24 (by norm_num) (by norm_num)
  exact ap_field_final r' hAB hA0 hg0 h143 h24

/-- `v_q(ρ) = -1`. -/
theorem ap_rho_val (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u : ℕ} (hqu : q + 1 = 38 * u)
    (hbig : 300 < q) : padicValRat q (rho u) = -1 := by
  have hr := ap_rho_res hV hq2 hqu
  have hne := ap_res_ne_zero hq2 hqu hbig
  rw [← hr.2] at hne
  have hρ : rho u ≠ 0 := by
    intro h
    rw [h, mul_zero, Rat.cast_zero] at hne
    exact hne rfl
  have h0 := pv_eq_zero hr.1 hne
  rw [padicValRat.mul ap_q0 hρ, padicValRat.self (Fact.out : q.Prime).one_lt] at h0
  linarith

/-- `v_q(Z) ≥ 0`. -/
theorem ap_Zc_val (hV : Stmt_CoeffVanish7) (hq2 : q ≠ 2) {u : ℕ} (hqu : q + 1 = 38 * u) :
    0 ≤ padicValRat q (Zc u) := by
  apply pv_nonneg
  unfold Zc csum genCsum
  exact mul_mem (by exact_mod_cast Zq_nat 46080) (sum_mem fun k _ => ap_rcoef_mem hV hq2 hqu 3 k)

end AP7

-- The signature is fixed by the blueprint; only `hV` (the parity relation) is needed.
set_option linter.unusedVariables false in
theorem AuxPrime7_proof (hPF : Stmt_PF7) (hV : Stmt_CoeffVanish7) : Stmt_AuxPrime7 := by
  unfold Stmt_AuxPrime7
  refine ⟨10, fun u hu hp => ?_⟩
  have : Fact (38 * u - 1).Prime := ⟨hp⟩
  have hqu : 38 * u - 1 + 1 = 38 * u := by
    have := hp.two_le
    omega
  have hq2 : 38 * u - 1 ≠ 2 := by omega
  have hbig : 300 < 38 * u - 1 := by omega
  exact ⟨AP7.ap_rho_val hV hq2 hqu hbig, AP7.ap_Zc_val hV hq2 hqu⟩

end Zeta2.Z7

end
