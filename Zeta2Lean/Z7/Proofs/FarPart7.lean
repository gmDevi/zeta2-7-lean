module

public import Zeta2Lean.Z7.Proofs.LocalExpansion7

@[expose] public section

/-!
# Lemma 4.5: the far part of the kernel (power sums over `𝔽_q^×`)

gap: 'denominators'.  Difficulty 4.  **Status: proved** (no gaps;
`#print axioms FarPart7_proof` gives `[propext, Classical.choice, Quot.sound]`).  (Only needed for
the six rows of `[2, 20/9)` that use the kernel `1 - (5/4) y²`; without it those rows cost `+1`,
`E = 3.974 < delta7 = 3.99` still holds.)

**Statement** (`Stmt_FarPart7`): for a prime `q ≥ 5`, `q > 2x + 2`, `k₀ < q`, `j ≥ 1`, `c`
`q`-integral and `j + 1 ≤ q + E_ξ`: `v_q(24 q^{-5} · c q^j · farRes u q k₀ j) ≥ j - 4`, where
`farRes = ∮_{D_ξ} R_n g_{j,ξ} dt`, `g_{j,ξ}(t) = ∑_{i' < q, i' ≠ k₀} (t + i')^{-j}`.  The hypothesis
`Stmt_PF7` is not used: `g_{j,ξ}` has no pole in the disc, so only the class poles contribute.

## Proof (finite algebra, as in `ClassLemma7`; namespace `FP7`, shared helper `LE7`)

It suffices that `v_q(farRes) ≥ 1` (`FP7.farRes_val`).  Notation: `τ = localModel u q k₀`,
`E = τ.E`, class poles `k = k₀ + J q ≤ n` at the local positions `w = -2J`.

1. **Residue form** (`farRes_eq`): `farRes = q^{E+1} ResF τ Φ` with
   `Φ_w = rescale q ((Û g)(-k₀ + q w/2 + ε))` (`Phi`, `gser`).  Per pole (`farPole_eq`):
   `∑_i r_{i,k} [ε^{i-1}] g(-k+ε) = [ε^{a_k-1}] (G_k g)` (`LE7.coeff_Gser_mul_eq_sum`,
   `LE7.coeff_lin_neg`), then the per-pole factorisation `LE7.coeff_Gser_mul` (Lemma 4.1).
2. **Truncation** (`trunc_far`): one `LE7.trunc_general` per term `Û · (t + i')^{-j}`
   (`A = Onum`, `B = Oden · (t + i')^j`, a unit on the disc since `i' ≢ k₀`), summed over `i'`:
   `Φ_{-2J} ≡ ∑_{m<M} F_m q^m (ε - J)^m (mod q^M)` at every `J`, and (from `J = 0`)
   `F_m ≡ [ε^m] (Û g)(-k₀ + ε) (mod q^{M-m})`.
3. **Power sums** (`powsum_val`, `centre_coeff_val`): `[ε^b] g(-k₀+ε) = C(-j,b) P_{j+b}` with
   `P_s = ∑_{i' ≠ k₀} (i' - k₀)^{-s}`.  By Fermat `P_s ≡ ∑ (i' - k₀)^{q-1-s} (mod q)`, and the
   `i' - k₀` run over `𝔽_q^×`, so `FiniteField.sum_pow_lt_card_sub_one` gives `q ∣ P_s` for
   `1 ≤ s ≤ q - 2`.  Hence `q ∣ [ε^m] (Û g)(-k₀+ε)` for `m ≤ q - 2 - j`.
4. **Assembly** with `M = (-E).toNat`: `ResF τ T = ∑_{m<M} F_m q^m [y^{E+m+1}] r_τ`
   (`LE7.ResF_sum`, `LE7.grt_local`); a term is non-zero only if `-E - 1 ≤ m < -E`, and then
   `m ≤ q - 2 - j` (by `j + 1 ≤ q + E`), so `q ∣ F_m` and the term has `v_q ≥ 1 + m ≥ -E`.
   The remainder has `v_q(ResF τ (Φ - T)) ≥ M ≥ -E` (Lemma 4.2: `LE7.PSV_taylorAt_model`).
   So `v_q(farRes) ≥ E + 1 - E = 1`, and `v_q(24 q^{j-5} c farRes) ≥ j - 4`.

**Numerical check.** `python/z7_mirror.py`, section "ClassLemma7 / KernelIdentity7 / FarPart7";
a check in the research computations (not included here) found the gain of exactly one power
of `q`.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace FP7

open LE7

/-! ### Power sums over `𝔽_q^×` -/

/-- `∑_{i < q} f(i mod q) = ∑_{x ∈ ℤ/q} f(x)`. -/
theorem sum_range_zmod {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    ∑ i ∈ range q, f (i : ZMod q) = ∑ x : ZMod q, f x := by
  refine Finset.sum_nbij' (fun i => (i : ZMod q)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_univ _
  · intro x _
    exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro i hi
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro i _
    rfl

/-- `q ∣ ∑_{i < q, i ≠ k₀} (i - k₀)^e` for `1 ≤ e < q - 1`. -/
theorem int_powsum_dvd {q : ℕ} (hq : q.Prime) (k₀ : ℕ) {e : ℕ} (he1 : 1 ≤ e)
    (he2 : e + 1 < q) :
    (q : ℤ) ∣ ∑ i ∈ (range q).erase k₀, ((i : ℤ) - k₀) ^ e := by
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [Finset.sum_erase _ (by rw [sub_self]; exact zero_pow (by omega)),
    sum_range_zmod (fun x : ZMod q => (x - (k₀ : ZMod q)) ^ e),
    Fintype.sum_equiv (Equiv.subRight (k₀ : ZMod q)) (fun x => (x - (k₀ : ZMod q)) ^ e)
      (fun x => x ^ e) (fun x => rfl)]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod q) e (by rw [ZMod.card]; omega)

/-- An integer divisible by `q` has `v_q ≥ 1`. -/
theorem valGe_one_of_dvd {q : ℕ} [Fact q.Prime] {z : ℤ} (h : (q : ℤ) ∣ z) :
    ValGe q 1 (z : ℚ) := by
  unfold ValGe
  have := (padicNorm.dvd_iff_norm_le (p := q) (n := 1) (z := z)).1 (by simpa using h)
  simpa using this

/-- **Power sums** (proof (P4)): `v_q(∑_{i < q, i ≠ k₀} (i - k₀)^{-s}) ≥ 1` for `1 ≤ s ≤ q - 2`. -/
theorem powsum_val {q : ℕ} [hqF : Fact q.Prime] {k₀ : ℕ} (hk₀ : k₀ < q) {s : ℕ} (hs1 : 1 ≤ s)
    (hs2 : s + 2 ≤ q) :
    ValGe q 1 (∑ i ∈ (range q).erase k₀, (((i : ℚ) - k₀)⁻¹) ^ s) := by
  have hq := hqF.out
  have hz : ∀ i ∈ (range q).erase k₀, ¬ (q : ℤ) ∣ ((i : ℤ) - k₀) := by
    intro i hi hdvd
    rw [Finset.mem_erase, Finset.mem_range] at hi
    have h0 : (i : ℤ) - k₀ = 0 :=
      Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
    omega
  have hsplit : ∑ i ∈ (range q).erase k₀, (((i : ℚ) - k₀)⁻¹) ^ s =
      ∑ i ∈ (range q).erase k₀,
          ((((i : ℚ) - k₀)⁻¹) ^ s * ((1 - ((i : ℤ) - k₀) ^ (q - 1) : ℤ) : ℚ)) +
        ((∑ i ∈ (range q).erase k₀, ((i : ℤ) - k₀) ^ (q - 1 - s) : ℤ) : ℚ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : ((i : ℚ) - k₀) ≠ 0 := by
      intro h0
      apply hz i hi
      have : ((i : ℤ) - k₀ : ℤ) = 0 := by exact_mod_cast h0
      rw [this]
      exact dvd_zero _
    have hpow : ((i : ℚ) - k₀) ^ (q - 1) = ((i : ℚ) - k₀) ^ s * ((i : ℚ) - k₀) ^ (q - 1 - s) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, inv_pow]
    field_simp
    ring
  rw [hsplit]
  refine valGe_add (valGe_sum _ _ fun i hi => ?_) ?_
  · refine valGe_mul (L := 0) (M := 1) ?_ ?_ (by norm_num)
    · refine valGe_pow (valGe_of_unit (unit_inv ?_)) s
      have := unit_int (q := q) (hz i hi)
      push_cast at this
      exact this
    · apply valGe_one_of_dvd
      have h1 : ((((i : ℤ) - k₀) : ℤ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hz i hi
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at h1 ⊢
      rw [ZMod.pow_card_sub_one_eq_one h1, sub_self]
  · apply valGe_one_of_dvd
    exact int_powsum_dvd hq k₀ (by omega) (by omega)

/-! ### The far kernel `g_{j,ξ}` and the family `Φ = Û g` -/

/-- `g_{j,ξ}(y + ε) = ∑_{i' < q, i' ≠ k₀} (y + i' + ε)^{-j}` (Taylor series at `t = y`). -/
def gser (q k₀ j : ℕ) (y : ℚ) : PowerSeries ℚ :=
  ∑ i ∈ (range q).erase k₀, lin (y + i) (-(j : ℤ))

/-- `[ε^b] g(y + ε) = C(-j, b) ∑_{i'} (y + i')^{-(j+b)}`. -/
theorem coeff_gser (q k₀ j : ℕ) (hj : 1 ≤ j) (y : ℚ)
    (hy : ∀ i ∈ (range q).erase k₀, y + i ≠ 0) (b : ℕ) :
    coeff b (gser q k₀ j y) = negChoose j b * ∑ i ∈ (range q).erase k₀, ((y + i)⁻¹) ^ (j + b) := by
  unfold gser
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := coeff_lin_neg (y + i) (hy i hi) j hj (b + 1) (by omega)
  rw [Nat.add_sub_cancel] at this
  rw [this, show b + 1 + j - 1 = j + b by omega]

/-- `Φ_w = rescale q ((Û g)(-k₀ + q w/2 + ε))`: the Taylor series of `v ↦ (Û g)(-k₀ + q v)` at
`v = w/2`. -/
def Phi (u q k₀ j : ℕ) (w : ℤ) : PowerSeries ℚ :=
  rescale (q : ℚ) (Uhat u q k₀ (-(k₀ : ℚ) + (q : ℚ) * ((w : ℚ) / 2)) *
    gser q k₀ j (-(k₀ : ℚ) + (q : ℚ) * ((w : ℚ) / 2)))

/-- `Φ` at the class pole `w = -2J`. -/
theorem Phi_pole (u q k₀ j J : ℕ) :
    Phi u q k₀ j (-(2 * (J : ℤ))) = rescale (q : ℚ) (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) *
      gser q k₀ j (-((k₀ + J * q : ℕ) : ℚ))) := by
  unfold Phi
  have : (-(k₀ : ℚ) + (q : ℚ) * (((-(2 * (J : ℤ)) : ℤ) : ℚ) / 2)) = -((k₀ + J * q : ℕ) : ℚ) := by
    push_cast
    ring
  rw [this]

/-- The points `-k₀ - J q + i'` (`i' < q`, `i' ≠ k₀`) are `q`-units. -/
theorem unit_far {q k₀ : ℕ} [Fact q.Prime] (hk₀ : k₀ < q) {i : ℕ} (hi : i ∈ (range q).erase k₀)
    (J : ℕ) : padicNorm q (-((k₀ + J * q : ℕ) : ℚ) + i) = 1 := by
  apply unit_out_pole hk₀
  rw [Finset.mem_erase, Finset.mem_range] at hi
  rw [Nat.mod_eq_of_lt hi.2]
  exact hi.1

/-- The per-pole identity: the residue of `R_n g_{j,ξ}` at `-k` in local form. -/
theorem farPole_eq {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) {J : ℕ}
    (hJ : k₀ + J * q ≤ 40 * u) (j : ℕ) (hj : 1 ≤ j) :
    ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i (k₀ + J * q) * ∑ i' ∈ (range q).erase k₀,
        negChoose j (i - 1) * (((i' : ℚ) - ((k₀ + J * q : ℕ) : ℚ))⁻¹) ^ (i + j - 1) =
      (q : ℚ) ^ ((localModel u q k₀).E + 1) *
        coeff (ord (localModel u q k₀) (-(2 * (J : ℤ))) - 1)
          (Phi u q k₀ j (-(2 * (J : ℤ))) * taylorAt (localModel u q k₀) (-(2 * (J : ℤ)))) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hyi : ∀ i' ∈ (range q).erase k₀, -((k₀ + J * q : ℕ) : ℚ) + i' ≠ 0 := fun i' hi' =>
    unit_ne_zero (unit_far hk₀ hi' J)
  have h1 : ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i (k₀ + J * q) * ∑ i' ∈ (range q).erase k₀,
        negChoose j (i - 1) * (((i' : ℚ) - ((k₀ + J * q : ℕ) : ℚ))⁻¹) ^ (i + j - 1) =
      coeff (apole u (k₀ + J * q) - 1)
        (Gser u (k₀ + J * q) * gser q k₀ j (-((k₀ + J * q : ℕ) : ℚ))) := by
    rw [coeff_Gser_mul_eq_sum u _ hJ]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    congr 1
    rw [coeff_gser q k₀ j hj _ hyi (i - 1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [show j + (i - 1) = i + j - 1 by omega, neg_add_eq_sub]
  have h2 : ∀ g : PowerSeries ℚ,
      g = C ((q : ℚ) ^ (0 : ℤ)) * rescale ((q : ℚ)⁻¹) (rescale (q : ℚ) g) := by
    intro g
    rw [zpow_zero, map_one, one_mul, rescale_rescale, mul_inv_cancel₀ hq0, rescale_one,
      RingHom.id_apply]
  rw [h1, h2 (gser q k₀ j (-((k₀ + J * q : ℕ) : ℚ))),
    show apole u (k₀ + J * q) - 1 = apole u (k₀ + J * q) - 1 + 0 by rfl,
    coeff_Gser_mul hq hq2 hk₀ hJ 0 0, Nat.add_zero, Nat.cast_zero, sub_zero, add_zero, Ufam_pole,
    Phi_pole, map_mul (rescale (q : ℚ))]
  congr 2
  ring

/-- **Residue form** of the far part: `farRes = q^{E+1} ResF τ Φ`. -/
theorem farRes_eq {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (j : ℕ) (hj : 1 ≤ j) :
    farRes u q k₀ j = (q : ℚ) ^ ((localModel u q k₀).E + 1) *
      ResF (localModel u q k₀) (Phi u q k₀ j) := by
  unfold farRes ResF
  rw [sum_cls u q k₀ hq.pos hk₀, poleSet_eq u q k₀ hq.pos hk₀,
    Finset.sum_image (fun x _ y _ h => by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun J hJ => ?_
  exact farPole_eq hq hq2 hk₀ ((mem_clsJ u q k₀ hq.pos).1 hJ) j hj

/-! ### Truncation of `Φ` at the centre of the disc -/

/-- `Û(y + ε) (y + i' + ε)^{-j}` as the quotient `Onum / (Oden · (t + i')^j)` at `t = y`. -/
theorem AB_eq (u q k₀ j : ℕ) (y : ℚ) (i : ℕ) (hy : y + i ≠ 0) :
    substPS y (Onum u q k₀) *
        (substPS y (Oden u q k₀ * (Polynomial.X + Polynomial.C (i : ℚ)) ^ j))⁻¹ =
      Uhat u q k₀ y * lin (y + i) (-(j : ℤ)) := by
  unfold Uhat
  rw [map_mul, map_pow, substPS_X_add_C, PowerSeries.mul_inv_rev, lin_neg_nat hy]
  ring

/-- `v_q(q^m x) ≥ L` gives `v_q(x) ≥ L - m`. -/
theorem valGe_of_qpow_mul {q : ℕ} [Fact q.Prime] {L : ℤ} {m : ℕ} {x : ℚ}
    (h : ValGe q L ((q : ℚ) ^ m * x)) : ValGe q (L - m) x := by
  have h2 := valGe_qzpow_mul (e := -(m : ℤ)) h
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ q_ne_zero, neg_add_cancel, zpow_zero,
    one_mul] at h2
  convert h2 using 1
  ring

/-- **Truncation** of `Φ = Û g` (one `trunc_general` per term `(t + i')^{-j}` of `g`): there are
`F_m` with `Φ_{-2J} ≡ ∑_{m<M} F_m q^m (ε - J)^m (mod q^M)` at every `J`, and
`F_m ≡ [ε^m] (Û g)(-k₀ + ε) (mod q^{M-m})`. -/
theorem trunc_far {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (j M : ℕ) :
    haveI : Fact q.Prime := ⟨hq⟩
    ∃ F : ℕ → ℚ, (∀ J : ℕ, PSV q M (Phi u q k₀ j (-(2 * (J : ℤ))) -
        ∑ m ∈ range M, C (F m * (q : ℚ) ^ m) * (C (-(J : ℚ)) + X) ^ m)) ∧
      ∀ m < M, ValGe q (M - m)
        (coeff m (Uhat u q k₀ (-(k₀ : ℚ)) * gser q k₀ j (-(k₀ : ℚ))) - F m) := by
  have : Fact q.Prime := ⟨hq⟩
  set I := (range q).erase k₀ with hI
  have hne : ∀ i ∈ I, ∀ J : ℕ, (-((k₀ + J * q : ℕ) : ℚ) + i) ≠ 0 := fun i hi J =>
    unit_ne_zero (unit_far hk₀ hi J)
  have htr : ∀ i : ℕ, ∃ F : ℕ → ℚ, i ∈ I → ∀ J : ℕ,
      PSV q M (rescale (q : ℚ) (substPS (-((k₀ + J * q : ℕ) : ℚ)) (Onum u q k₀) *
          (substPS (-((k₀ + J * q : ℕ) : ℚ))
            (Oden u q k₀ * (Polynomial.X + Polynomial.C (i : ℚ)) ^ j))⁻¹) -
        ∑ m ∈ range M, C (F m * (q : ℚ) ^ m) * (C (-(J : ℚ)) + X) ^ m) := by
    intro i
    by_cases hi : i ∈ I
    · have hF : PSV q 0 (substPS (-(k₀ : ℚ)) (Onum u q k₀) *
          (substPS (-(k₀ : ℚ)) (Oden u q k₀ * (Polynomial.X + Polynomial.C (i : ℚ)) ^ j))⁻¹) := by
        have h0 := hne i hi 0
        have hu0 := unit_far hk₀ hi 0
        simp only [zero_mul, add_zero] at h0 hu0
        rw [AB_eq u q k₀ j _ i h0]
        refine (?_ : PSV q 0 _).mul' (PSV_lin hu0 _) (by simp)
        have := PSV_Uhat (u := u) hq2 hk₀ 0
        simpa using this
      have hBu : ∀ J : ℕ, padicNorm q (constantCoeff (substPS (-((k₀ + J * q : ℕ) : ℚ))
          (Oden u q k₀ * (Polynomial.X + Polynomial.C (i : ℚ)) ^ j))) = 1 := by
        intro J
        rw [map_mul, map_mul, map_pow, map_pow, substPS_X_add_C, map_add, constantCoeff_C,
          constantCoeff_X, add_zero]
        refine unit_mul (constantCoeff_substPS_Oden hk₀ J) ?_
        rw [pn_pow, unit_far hk₀ hi J, one_pow]
      have hBJ : ∀ J : ℕ, PSV q 0 (substPS (-((k₀ + J * q : ℕ) : ℚ))
          (Oden u q k₀ * (Polynomial.X + Polynomial.C (i : ℚ)) ^ j)) := by
        intro J
        rw [map_mul, map_pow, substPS_X_add_C]
        have h1 := PSV_Oden (u := u) (q := q) (k₀ := k₀) (-((k₀ + J * q : ℕ) : ℤ))
        have h2 : PSV q 0 ((C (-((k₀ + J * q : ℕ) : ℚ) + i) + X) ^ j) := by
          refine PSV.pow ((PSV.ofC ?_).add PSV.ofX) j
          have : (-((k₀ + J * q : ℕ) : ℚ) + i) = ((-((k₀ + J * q : ℕ) : ℤ) + i : ℤ) : ℚ) := by
            push_cast
            ring
          rw [this]
          exact valGe_int _
        push_cast at h1 h2 ⊢
        exact h1.mul' h2 (by simp)
      obtain ⟨F, hF'⟩ := trunc_general (k₀ := k₀) (Onum u q k₀)
        (Oden u q k₀ * (Polynomial.X + Polynomial.C (i : ℚ)) ^ j) M hF hBu hBJ
      exact ⟨F, fun _ => hF'⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Fi hFi using htr
  refine ⟨fun m => ∑ i ∈ I, Fi i m, fun J => ?_, fun m hm => ?_⟩
  · have hsum : Phi u q k₀ j (-(2 * (J : ℤ))) -
        ∑ m ∈ range M, C ((∑ i ∈ I, Fi i m) * (q : ℚ) ^ m) * (C (-(J : ℚ)) + X) ^ m =
        ∑ i ∈ I, (rescale (q : ℚ) (substPS (-((k₀ + J * q : ℕ) : ℚ)) (Onum u q k₀) *
          (substPS (-((k₀ + J * q : ℕ) : ℚ))
            (Oden u q k₀ * (Polynomial.X + Polynomial.C (i : ℚ)) ^ j))⁻¹) -
          ∑ m ∈ range M, C (Fi i m * (q : ℚ) ^ m) * (C (-(J : ℚ)) + X) ^ m) := by
      rw [Finset.sum_sub_distrib, Phi_pole]
      congr 1
      · unfold gser
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [AB_eq u q k₀ j _ i (hne i hi J)]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_mul, map_sum, Finset.sum_mul]
    rw [hsum]
    exact PSV.sum _ _ fun i hi => hFi i hi J
  · have hcoef : ∀ i ∈ I, ValGe q M ((q : ℚ) ^ m *
        (coeff m (Uhat u q k₀ (-(k₀ : ℚ)) * lin (-(k₀ : ℚ) + i) (-(j : ℤ))) - Fi i m)) := by
      intro i hi
      have h := hFi i hi 0 m
      have h0 := hne i hi 0
      simp only [zero_mul, add_zero, Nat.cast_zero, neg_zero, map_zero, zero_add] at h h0
      rw [AB_eq u q k₀ j _ i h0, map_sub, coeff_rescale, map_sum] at h
      simp only [coeff_C_mul_X_pow] at h
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 hm)] at h
      convert h using 1
      ring
    have hsum := valGe_sum _ _ hcoef
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← map_sum, ← Finset.mul_sum] at hsum
    have e : ∑ i ∈ I, lin (-(k₀ : ℚ) + i) (-(j : ℤ)) = gser q k₀ j (-(k₀ : ℚ)) := rfl
    rw [e] at hsum
    exact valGe_of_qpow_mul hsum

/-! ### The power sums at the centre -/

/-- `C(-j, b)` is an integer. -/
theorem negChoose_val {q : ℕ} [Fact q.Prime] (j b : ℕ) : ValGe q 0 (negChoose j b) := by
  have : negChoose j b = (((-1 : ℤ) ^ b * ((b + j - 1).choose b : ℤ) : ℤ) : ℚ) := by
    unfold negChoose
    push_cast
    ring
  rw [this]
  exact valGe_int _

/-- `q ∣ [ε^m] (Û g)(-k₀ + ε)` for `m ≤ q - 2 - j` (proof Lemma 4.5, "power sums"). -/
theorem centre_coeff_val {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (j : ℕ)
    (hj : 1 ≤ j) (m : ℕ) (hm : m + j + 2 ≤ q) :
    haveI : Fact q.Prime := ⟨hq⟩
    ValGe q 1 (coeff m (Uhat u q k₀ (-(k₀ : ℚ)) * gser q k₀ j (-(k₀ : ℚ)))) := by
  have : Fact q.Prime := ⟨hq⟩
  have hU : PSV q 0 (Uhat u q k₀ (-(k₀ : ℚ))) := by
    have := PSV_Uhat (u := u) hq2 hk₀ 0
    simpa using this
  have hy : ∀ i ∈ (range q).erase k₀, -(k₀ : ℚ) + i ≠ 0 := by
    intro i hi
    have := unit_ne_zero (unit_far hk₀ hi 0)
    simpa using this
  rw [coeff_mul]
  refine valGe_sum _ _ fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  refine valGe_mul (L := 0) (M := 1) (hU p.1) ?_ (by norm_num)
  rw [coeff_gser q k₀ j hj _ hy p.2]
  refine valGe_mul (L := 0) (M := 1) (negChoose_val j p.2) ?_ (by norm_num)
  have := powsum_val (q := q) hk₀ (s := j + p.2) (by omega) (by omega)
  simpa only [neg_add_eq_sub] using this

/-! ### Assembly -/

/-- `r_τ(y) = ∏ (1 - (w/2) y)^e` is `q`-integral for odd `q`. -/
theorem PSV_rSer {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (τ : LocalType) : PSV q 0 (rSer τ) := by
  unfold rSer
  apply PSV.list_prod
  intro f hf
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hf
  apply PSV_bser
  have : (-(p.1 : ℚ) / 2) = ((-p.1 : ℤ) : ℚ) / 2 := by push_cast; ring
  rw [this]
  exact valGe_half hq2 _

/-- **Lemma 4.5, core**: `v_q(∮_{D_ξ} R_n g_{j,ξ} dt) ≥ 1` when `q ≥ j + 1 - E_ξ`. -/
theorem farRes_val {u q k₀ : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hsq : 80 * u + 2 * q < q ^ 2)
    (hk₀ : k₀ < q) (j : ℕ) (hj : 1 ≤ j) (hE : (j : ℤ) + 1 ≤ q + (localModel u q k₀).E) :
    haveI : Fact q.Prime := ⟨hq⟩
    ValGe q 1 (farRes u q k₀ j) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  set τ := localModel u q k₀ with hτ
  set M : ℕ := (-τ.E).toNat with hM
  obtain ⟨F, hFJ, hFc⟩ := trunc_far (u := u) hq hq2 hk₀ j M
  set T : ℤ → PowerSeries ℚ := fun w =>
    ∑ m ∈ range M, C (F m * (q : ℚ) ^ m) * (C ((w : ℚ) / 2) + X) ^ m with hT
  have hsplit : ResF τ (Phi u q k₀ j) = ResF τ T + ResF τ (fun w => Phi u q k₀ j w - T w) := by
    rw [← ResF_add]
    congr 1
    funext w
    ring
  have hTpoly : ResF τ T = ∑ m ∈ range M, (F m * (q : ℚ) ^ m) * coeffZ (rSer τ) (τ.E + m + 1) := by
    rw [hT, ResF_sum τ (range M) (fun m => F m * (q : ℚ) ^ m)
      (fun m w => (C ((w : ℚ) / 2) + X) ^ m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← grt_local τ m]
    rfl
  have hrS := PSV_rSer hq2 τ
  have hTval : ValGe q (-τ.E) (ResF τ T) := by
    rw [hTpoly]
    refine valGe_sum _ _ fun m hm => ?_
    rw [Finset.mem_range] at hm
    by_cases hneg : τ.E + m + 1 < 0
    · rw [coeffZ, ite_eq_right (by omega), mul_zero]
      exact valGe_zero _
    · have hm1 : m + j + 2 ≤ q := by omega
      have hFm : ValGe q 1 (F m) := by
        have h1 := centre_coeff_val (u := u) hq hq2 hk₀ j hj m hm1
        have h2 := valGe_mono (hFc m hm) (by omega : (1 : ℤ) ≤ M - m)
        have := valGe_sub h1 h2
        simpa using this
      have hc : ValGe q 0 (coeffZ (rSer τ) (τ.E + m + 1)) := by
        unfold coeffZ
        split_ifs
        · exact hrS _
        · exact valGe_zero _
      have hqm : ValGe q m ((q : ℚ) ^ m) := by
        rw [← zpow_natCast]
        exact valGe_qzpow _
      exact valGe_mono (valGe_mul (valGe_mul hFm hqm rfl) hc rfl) (by omega)
  have hRval : ValGe q M (ResF τ (fun w => Phi u q k₀ j w - T w)) := by
    unfold ResF
    refine valGe_sum _ _ fun w hw => ?_
    rw [hτ, poleSet_eq u q k₀ hq.pos hk₀, Finset.mem_image] at hw
    obtain ⟨J, hJ, rfl⟩ := hw
    have h1 : PSV q M (Phi u q k₀ j (-(2 * (J : ℤ))) - T (-(2 * (J : ℤ)))) := by
      have hJ2 : (((-(2 * (J : ℤ)) : ℤ) : ℚ) / 2) = -(J : ℚ) := by push_cast; ring
      simp only [hT, hJ2]
      exact hFJ J
    have h2 := PSV_taylorAt_model hq hq2 hk₀ hsq (Or.inl ((mem_clsJ u q k₀ hq.pos).1 hJ))
    exact (h1.mul' h2 (by simp)) _
  rw [farRes_eq hq hq2 hk₀ j hj, hsplit]
  have hsum : ValGe q (-τ.E) (ResF τ T + ResF τ (fun w => Phi u q k₀ j w - T w)) :=
    valGe_add hTval (valGe_mono hRval (by omega))
  exact valGe_qzpow_mul' hsum (by ring)

end FP7

open FP7 LE7 in
/-- **Lemma 4.5 (far part)**. -/
theorem FarPart7_proof (_hPF : Stmt_PF7) : Stmt_FarPart7 := by
  intro u q k₀ j c hq hq5 hsq hk₀ hj hc hE
  have : Fact q.Prime := ⟨hq⟩
  have hfar := farRes_val hq hq5 hsq hk₀ j hj hE
  have h24 : ValGe q 0 (24 : ℚ) := by simpa using valGe_int (q := q) 24
  have h5 : ValGe q (-5) (((q : ℚ) ^ 5)⁻¹) := by
    rw [← zpow_natCast, ← zpow_neg]
    exact valGe_qzpow _
  have hqj : ValGe q j ((q : ℚ) ^ j) := by
    rw [← zpow_natCast]
    exact valGe_qzpow _
  have := valGe_mul (valGe_mul h24 h5 rfl) (valGe_mul (valGe_mul hc hqj rfl) hfar rfl) rfl
  exact valGe_mono this (by omega)

end Zeta2.Z7

end
