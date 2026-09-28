module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Theorem V: `v₂(S_n) ≥ 6.8 n - O(log n)` (proof §6)

gap: 'valuation' (adapted).  Difficulty 3.

**Task.** Prove `Stmt_Valuation7` from `Stmt_IntegrandTaylor7`, `Stmt_Delta` and `Stmt_DeltaFun`
(shared): there are `c, A` with `‖I‖ · 2^{272u} ≤ c (u+1)^A` for every `u` and every limit `I` of
the Riemann sums of `integrand u`.

**Status.** Complete (Valuation7 prover, round 2, 2026-09-26), with `c = 4 · 30^{10}`, `A = 10`:
for every `u` (including `u = 0`) and every limit `I`, `v₂(I) ≥ 272u - 2 - 10L`,
`L := ⌊log₂ 30u⌋` (`30u = 3n/4` is the longest block).  Before the crude Legendre step the proof
gives `v₂(I) ≥ 272u + 4 - σ - 4L`, `σ = ∑_m s₂(L_m)`, one more than proof §6's
`272u + 7 - σ - 4(L+1)` (the research form `272u + 7 - 10(L+1)` of the statement's docstring is
thus implied); e.g. `n = 480`: `3215` (proof §6: `3214`, true `3237`).
`#print axioms Zeta2.Z7.Valuation7_proof` gives `[propext, Classical.choice, Quot.sound]`;
`leanchecker Zeta2Lean.Z7.Proofs.Valuation7` replays the module (exit 0).
Used: `Stmt_Delta.{sumAll, smulAll, mulAll, monoAll, riemannAll}`, `Stmt_DeltaFun.binom` (not
`hcoefInt`/`hcoefDelta`), `Stmt_IntegrandTaylor7`.  No helper files.

**Informal proof** (proof §6 = the pair's Theorem G4 with the factorisation lemma V1 changed; the
pair's `Zeta2Lean/Pair/Proofs/Valuation.lean` is the template and most of it is reused verbatim).
1. *Product form* (`Stmt_IntegrandTaylor7`, lemma V1): at `y = x - 20u + 1/2`,
   `R_n(y + ε) = (2x + 1 + 2ε) · ∏_m (T_m + ε)^{\underline{L_m}} · 2^{∑ a_k} H(2ε)`, where
   - `2y + n = 2x + 1` (the linear factor is the pair's with `n = 0`),
   - block `m`: `y + ε + 1/2 + c = x + 1 - 20u + c + ε`, `c ∈ [η_m u, (40 - η_m) u)`, is the falling
     run of length `L_m = 2 d_m`, `d_m = (20 - η_m) u`, with top `T_m = x + d_m ∈ ℕ` — the top is a
     natural number, so `Stmt_DeltaFun.binom` applies unchanged (no negative binomial arguments);
   - `H(δ) := ∏_{k ≤ n} (2x + b_k + δ)^{-a_k}`, `b_k = 2k + 1 - 40u`: the factors
     `2x + (odd integer)` are 2-adic units, possibly with a negative odd offset `b_k`.
2. *Vandermonde / coefficient bounds / Δ-calculus*: the pair's `runPS`, `val_vand`, `coeff_runPS`,
   `sco`, `norm_sco`, `serGood_run`, `serGood_lin` verbatim.
3. *The `H` factor*: `vgood_inv_oddZ`, the pair's `vgood_inv_odd` for `x ↦ (2x + b)⁻¹` with an
   **integer** odd `b` (same proof: `(2y+b)⁻¹ - (2y'+b)⁻¹ = 2(y'-y)/((2y+b)(2y'+b))`, both factors
   units).  Instead of the pair's explicit coefficient formula (`val_H6_coeff`), the level-`0`
   bound for `H` is obtained structurally: `[δ^j] (C c + X)⁻¹ = (-1)^j c^{-(j+1)}` is good
   (`serGood_invZ`), and level `0` is stable under powers and products (`serGood_pow0`,
   `serGood_prod`).  Level of `2^{∑ a_k} H(2ε)`: `∑ a_k = 136u + 4` (`serGood_scaled`, `sum_apole`).
4. *Legendre*: `v₂(L_m!) = L_m - s₂(L_m) ≥ L_m - ⌊log₂ L_m⌋ - 1`; `∑ L_m = 136u`.  Total level
   `E ≥ 136u + 4 + 136u - 6(L + 1)`, and `Δ(integrand) ≥ E - 4L + 1`, so every Riemann sum and the
   limit have `v₂ ≥ E - 4L ≥ 272u - 2 - 10L`, and `‖I‖ 2^{272u} ≤ 4 · 2^{10L} ≤ 4 (30(u+1))^{10}`.

**Lean proof map.**
* Copied verbatim from the pair (namespace changed, all `private`): the norm helpers, `VGood` and
  its closure lemmas, `SerGood` (`serGood_mono`, `serGood_mul`, `serGood_one`, `serGood_prod`),
  `serGood_lin`, the runs (`fallPS`, `runPS`, `val_vand`, `sco`, `coeff_runPS`, `CBd`, `norm_sco`,
  `serGood_run`), `val_inv_C_add_X`, `val_rescale_C`, `val_rescale_lin`, `val_legendre`.
* New: `val_norm_odd_int`, `vgood_inv_oddZ`, `serGood_congr`, `serGood_invZ`, `serGood_pow0`,
  `boff`, `H7`, `serGood_H7base`, `serGood_scaled`, `val_den7`, `block_run`, `block_eq`,
  `val_Rser7` (product form), `apole_split`, `count_band`, `sum_apole` (`∑ a_k = 136u + 4`), and
  the assembly `Valuation7_proof`.

**Numerical check.** `python/z7_mirror.py`, section "Valuation7" (true `v₂(S_n)` versus the proved
bound; slack 18–27 bits for `n ≤ 2000` in proof §6).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

/-! ### 2-adic norm helpers -/

private lemma val_norm_two_zpow (z : ℤ) : ‖(2 : ℚ_[2]) ^ z‖ = (2 : ℝ) ^ (-z) := by
  have := Padic.norm_p_zpow (p := 2) z
  simpa using this

private lemma val_norm_natCast_le_one (a : ℕ) : ‖(a : ℚ_[2])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := 2) (a : ℤ)
  simpa using this

private lemma val_norm_natCast (a : ℕ) (ha : a ≠ 0) :
    ‖(a : ℚ_[2])‖ = (2 : ℝ) ^ (-(padicValNat 2 a : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast ha), Padic.valuation_natCast]
  norm_num

private lemma val_norm_inv_natCast_le (m : ℕ) (hm : m ≠ 0) :
    ‖((m : ℚ_[2]))⁻¹‖ ≤ (2 : ℝ) ^ (Nat.log 2 m : ℤ) := by
  rw [norm_inv, val_norm_natCast m hm, ← zpow_neg, neg_neg]
  apply zpow_le_zpow_right₀ (by norm_num)
  exact_mod_cast padicValNat_le_nat_log m

private lemma val_two_zpow_le_one {z : ℤ} (hz : z ≤ 0) : (2 : ℝ) ^ z ≤ 1 := by
  calc (2 : ℝ) ^ z ≤ (2 : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hz
    _ = 1 := zpow_zero 2

/-- An odd integer is a `2`-adic unit. -/
private lemma val_norm_odd_int (z : ℤ) (hz : Odd z) : ‖(z : ℚ_[2])‖ = 1 := by
  have h1 := Padic.norm_int_le_one (p := 2) z
  have h2 : ¬ ‖(z : ℚ_[2])‖ < 1 := by
    rw [Padic.norm_intCast_lt_one_iff]
    intro h
    obtain ⟨k, hk⟩ := hz
    obtain ⟨m, hm⟩ := h
    push_cast at hm
    omega
  exact le_antisymm h1 (not_lt.1 h2)

/-! ### `ℤ₂`-valued functions with `Δ ≥ -L` -/

/-- `ℤ₂`-valued with `Δ ≥ -L`. -/
private def VGood (L : ℕ) (f : ℕ → ℚ_[2]) : Prop :=
  IntValued f ∧ DeltaAll (-(L : ℤ)) f

private lemma vgood_congr {L : ℕ} {f g : ℕ → ℚ_[2]} (h : ∀ x, f x = g x) (hg : VGood L g) :
    VGood L f := by
  rw [show f = g from funext h]
  exact hg

private lemma vgood_const (L : ℕ) (a : ℚ_[2]) (ha : ‖a‖ ≤ 1) : VGood L (fun _ => a) := by
  refine ⟨fun _ => ha, fun k _ => ?_, ?_⟩
  · simp only [sub_self, norm_zero]
    positivity
  · exact ha.trans (one_le_zpow₀ (by norm_num) (by omega))

private lemma vgood_add (hD : Stmt_Delta) {L : ℕ} {f g : ℕ → ℚ_[2]} (hf : VGood L f)
    (hg : VGood L g) : VGood L (fun x => f x + g x) := by
  refine ⟨fun k => (Padic.nonarchimedean _ _).trans (max_le (hf.1 k) (hg.1 k)), ?_⟩
  have h := hD.sumAll (Finset.univ : Finset Bool) (fun b => if b then f else g) (-(L : ℤ))
    (by intro b _; cases b <;> simp [hf.2, hg.2])
  simpa [Fintype.sum_bool] using h

private lemma vgood_sum (hD : Stmt_Delta) {L : ℕ} {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2])
    (h : ∀ i ∈ s, VGood L (F i)) : VGood L (fun x => ∑ i ∈ s, F i x) :=
  ⟨fun k => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun i hi => (h i hi).1 k),
    hD.sumAll s F _ (fun i hi => (h i hi).2)⟩

private lemma vgood_mul (hD : Stmt_Delta) {L : ℕ} {f g : ℕ → ℚ_[2]} (hf : VGood L f)
    (hg : VGood L g) : VGood L (fun x => f x * g x) :=
  ⟨fun k => by
      rw [norm_mul]
      exact (mul_le_mul (hf.1 k) (hg.1 k) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1)),
    hD.mulAll f g _ hf.1 hg.1 hf.2 hg.2⟩

private lemma vgood_smul (hD : Stmt_Delta) {L : ℕ} (a : ℚ_[2]) (ha : ‖a‖ ≤ 1) {f : ℕ → ℚ_[2]}
    (hf : VGood L f) : VGood L (fun x => a * f x) := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul ha (hf.1 k) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1))
  · have h := hD.smulAll f (-(L : ℤ)) 0 a (by simpa using ha) hf.2
    simpa using h

private lemma vgood_mono (hD : Stmt_Delta) {L L' : ℕ} (hL : L ≤ L') {f : ℕ → ℚ_[2]}
    (hf : VGood L f) : VGood L' f :=
  ⟨hf.1, hD.monoAll _ _ _ (by omega) hf.2⟩

private lemma vgood_pow (hD : Stmt_Delta) {L : ℕ} {f : ℕ → ℚ_[2]} (hf : VGood L f) (p : ℕ) :
    VGood L (fun x => f x ^ p) := by
  induction p with
  | zero => simpa using vgood_const L 1 (by simp)
  | succ p ih => simpa [pow_succ] using vgood_mul hD ih hf

/-- `C(x + j, N)` with `⌊log₂ N⌋ ≤ L` (`Stmt_DeltaFun.binom`). -/
private lemma vgood_choose (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) (j N L : ℕ)
    (hN : Nat.log 2 N ≤ L) : VGood L (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2])) :=
  ⟨fun _ => val_norm_natCast_le_one _, hD.monoAll _ _ _ (by omega) (hDF.binom j N)⟩

/-- `x ↦ (2x + b)⁻¹` for an odd integer `b` (possibly negative): `ℤ₂`-valued with `Δ ≥ 0`. -/
private lemma vgood_inv_oddZ (b : ℤ) (hb : Odd b) :
    VGood 0 (fun x => (((2 * (x : ℤ) + b : ℤ) : ℚ_[2]))⁻¹) := by
  have hodd : ∀ x : ℕ, ‖((2 * (x : ℤ) + b : ℤ) : ℚ_[2])‖ = 1 := by
    intro x
    apply val_norm_odd_int
    obtain ⟨k, hk⟩ := hb
    exact ⟨x + k, by rw [hk]; ring⟩
  have hne : ∀ x : ℕ, ((2 * (x : ℤ) + b : ℤ) : ℚ_[2]) ≠ 0 := by
    intro x h0
    have h1 := hodd x
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨fun x => by rw [norm_inv, hodd x, inv_one], ?_, ?_⟩
  · intro y hy
    have hy0 : y ≠ 0 := by
      have : 1 ≤ y := by simpa using hy
      omega
    have hL : 2 ^ Nat.log 2 y ≤ y := Nat.pow_log_le_self 2 hy0
    set L := Nat.log 2 y with hLdef
    change ‖(((2 * (y : ℤ) + b : ℤ) : ℚ_[2]))⁻¹ -
      (((2 * ((y - 2 ^ L : ℕ) : ℤ) + b : ℤ) : ℚ_[2]))⁻¹‖ ≤ _
    rw [inv_sub_inv (hne y) (hne (y - 2 ^ L)), norm_div, norm_mul, hodd y, hodd (y - 2 ^ L)]
    have hdiff : ((2 * ((y - 2 ^ L : ℕ) : ℤ) + b : ℤ) : ℚ_[2]) - ((2 * (y : ℤ) + b : ℤ) : ℚ_[2]) =
        -(2 : ℚ_[2]) ^ (L + 1) := by
      have h1 : (2 * ((y - 2 ^ L : ℕ) : ℤ) + b : ℤ) - (2 * (y : ℤ) + b) = -(2 ^ (L + 1)) := by
        rw [Nat.cast_sub hL]
        push_cast
        ring
      rw [← Int.cast_sub, h1]
      push_cast
      ring
    rw [hdiff, norm_neg, ← zpow_natCast, val_norm_two_zpow, mul_one, div_one]
    apply zpow_le_zpow_right₀ (by norm_num)
    push_cast
    omega
  · rw [norm_inv, hodd 0, inv_one]
    exact one_le_zpow₀ (by norm_num) (by norm_num)

/-! ### Scaled Taylor coefficients -/

/-- The scaled Taylor coefficients `2^{jL - E} [ε^j] P_x(ε)` are `VGood L` (as functions of `x`). -/
private def SerGood (L : ℕ) (E : ℤ) (P : ℕ → PowerSeries ℚ) : Prop :=
  ∀ j : ℕ, VGood L (fun x => (2 : ℚ_[2]) ^ ((j : ℤ) * L - E) * ((coeff j (P x) : ℚ) : ℚ_[2]))

private lemma serGood_congr {L : ℕ} {E : ℤ} {P Q : ℕ → PowerSeries ℚ} (h : ∀ x, P x = Q x)
    (hQ : SerGood L E Q) : SerGood L E P := by
  rw [show P = Q from funext h]
  exact hQ

private lemma serGood_mono (hD : Stmt_Delta) {L : ℕ} {E E' : ℤ} (hE : E' ≤ E)
    {P : ℕ → PowerSeries ℚ} (hP : SerGood L E P) : SerGood L E' P := by
  intro j
  refine vgood_congr (fun x => ?_) (vgood_smul hD ((2 : ℚ_[2]) ^ (E - E')) ?_ (hP j))
  · rw [← mul_assoc, ← zpow_add₀ two_ne_zero]
    congr 2
    ring
  · rw [val_norm_two_zpow]
    exact val_two_zpow_le_one (by omega)

private lemma serGood_mul (hD : Stmt_Delta) {L : ℕ} {E E' : ℤ} {P Q : ℕ → PowerSeries ℚ}
    (hP : SerGood L E P) (hQ : SerGood L E' Q) : SerGood L (E + E') (fun x => P x * Q x) := by
  intro j
  refine vgood_congr (g := fun x => ∑ p ∈ antidiagonal j,
      ((2 : ℚ_[2]) ^ ((p.1 : ℤ) * L - E) * ((coeff p.1 (P x) : ℚ) : ℚ_[2])) *
      ((2 : ℚ_[2]) ^ ((p.2 : ℤ) * L - E') * ((coeff p.2 (Q x) : ℚ) : ℚ_[2]))) (fun x => ?_)
    (vgood_sum hD _ _ (fun p _ => vgood_mul hD (hP p.1) (hQ p.2)))
  rw [coeff_mul, Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  have e2 : (j : ℤ) * L - (E + E') = ((p.1 : ℤ) * L - E) + ((p.2 : ℤ) * L - E') := by
    rw [← hp]
    push_cast
    ring
  rw [e2, zpow_add₀ two_ne_zero, Rat.cast_mul]
  ring

private lemma serGood_one (L : ℕ) : SerGood L 0 (fun _ => 1) := by
  intro j
  by_cases hj : j = 0
  · subst hj
    exact vgood_congr (fun x => by simp) (vgood_const L 1 (by simp))
  · exact vgood_congr (fun x => by simp [coeff_one, hj]) (vgood_const L 0 (by simp))

private lemma serGood_prod (hD : Stmt_Delta) {L : ℕ} {ι : Type*} (s : Finset ι)
    (E : ι → ℤ) (P : ι → ℕ → PowerSeries ℚ) (h : ∀ i ∈ s, SerGood L (E i) (P i)) :
    SerGood L (∑ i ∈ s, E i) (fun x => ∏ i ∈ s, P i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using serGood_one L
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : (fun x => ∏ i ∈ insert a s, P i x) = fun x => P a x * ∏ i ∈ s, P i x := by
      funext x
      rw [Finset.prod_insert ha]
    rw [e]
    exact serGood_mul hD (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- Level `0` is stable under powers. -/
private lemma serGood_pow0 (hD : Stmt_Delta) {L : ℕ} {P : ℕ → PowerSeries ℚ}
    (hP : SerGood L 0 P) (a : ℕ) : SerGood L 0 (fun x => P x ^ a) := by
  induction a with
  | zero => simpa using serGood_one L
  | succ a ih =>
    have h := serGood_mul hD ih hP
    simpa [pow_succ] using h

/-! ### The linear factor `2x + 1 + n + 2ε` -/

private lemma serGood_lin (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) (n L : ℕ) :
    SerGood L 0 (fun x => C (((2 * x + 1 + n : ℕ) : ℚ)) + C 2 * X) := by
  intro j
  rcases j with _ | _ | j
  · refine vgood_congr (g := fun x => ((Nat.choose (x + 0) 1 : ℕ) : ℚ_[2]) +
      ((Nat.choose (x + (1 + n)) 1 : ℕ) : ℚ_[2])) (fun x => ?_)
      (vgood_add hD (vgood_choose hD hDF 0 1 L (by simp))
        (vgood_choose hD hDF (1 + n) 1 L (by simp)))
    rw [map_add, coeff_C, coeff_C_mul, coeff_X]
    simp only [Nat.choose_one_right, ite_true, zero_ne_one, ite_false, mul_zero, add_zero,
      Nat.cast_zero, zero_mul, sub_zero, zpow_zero, one_mul]
    push_cast
    ring
  · refine vgood_congr (g := fun _ => (2 : ℚ_[2]) ^ ((L : ℤ) + 1)) (fun x => ?_)
      (vgood_const L _ ?_)
    · rw [map_add, coeff_C, coeff_C_mul, coeff_X]
      simp only [one_ne_zero, ite_false, ite_true, zero_add, mul_one, Nat.cast_one, one_mul,
        sub_zero, Rat.cast_ofNat]
      rw [zpow_add₀ two_ne_zero, zpow_one]
    · rw [val_norm_two_zpow]
      exact val_two_zpow_le_one (by omega)
  · refine vgood_congr (g := fun _ => (0 : ℚ_[2])) (fun x => ?_) (vgood_const L 0 (by simp))
    rw [map_add, coeff_C, coeff_C_mul, coeff_X]
    simp

/-! ### Runs of consecutive factors: Vandermonde -/

/-- `ε (ε - 1) ⋯ (ε - k + 1)`. -/
private def fallPS (k : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ range k, (X - C (i : ℚ))

/-- `(T + ε) (T - 1 + ε) ⋯ (T - N + 1 + ε)`. -/
private def runPS (T N : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ range N, (C ((T : ℚ) - i) + X)

private lemma runPS_succ (T N : ℕ) : runPS T (N + 1) = runPS T N * (C ((T : ℚ) - N) + X) := by
  unfold runPS
  rw [prod_range_succ]

private lemma fallPS_succ (k : ℕ) : fallPS (k + 1) = fallPS k * (X - C (k : ℚ)) := by
  unfold fallPS
  rw [prod_range_succ]

private lemma val_desc_succ (T m : ℕ) :
    ((T.descFactorial (m + 1) : ℕ) : ℚ) = ((T : ℚ) - m) * ((T.descFactorial m : ℕ) : ℚ) := by
  rw [Nat.descFactorial_succ]
  rcases le_or_gt m T with hmT | hmT
  · rw [Nat.cast_mul, Nat.cast_sub hmT]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hmT]
    simp

/-- Vandermonde: `(T + ε)^{\underline N} = ∑_{i+j=N} C(N,i) ε^{\underline i} T^{\underline j}`. -/
private lemma val_vand (T N : ℕ) :
    runPS T N = ∑ ij ∈ antidiagonal N,
      ((N.choose ij.1 : ℕ) : PowerSeries ℚ) *
        (fallPS ij.1 * C ((T.descFactorial ij.2 : ℕ) : ℚ)) := by
  induction N with
  | zero => simp [runPS, fallPS]
  | succ N ih =>
    have hs : (∑ ij ∈ antidiagonal (N + 1), (((N + 1).choose ij.1 : ℕ) : PowerSeries ℚ) *
        (fallPS ij.1 * C ((T.descFactorial ij.2 : ℕ) : ℚ))) =
        (∑ ij ∈ antidiagonal N, ((N.choose ij.1 : ℕ) : PowerSeries ℚ) *
          (fallPS ij.1 * C ((T.descFactorial (ij.2 + 1) : ℕ) : ℚ))) +
        ∑ ij ∈ antidiagonal N, ((N.choose ij.2 : ℕ) : PowerSeries ℚ) *
          (fallPS (ij.1 + 1) * C ((T.descFactorial ij.2 : ℕ) : ℚ)) :=
      Finset.sum_antidiagonal_choose_succ_mul
        (fun i j => fallPS i * C ((T.descFactorial j : ℕ) : ℚ)) N
    rw [hs, runPS_succ, ih, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm, fallPS_succ, val_desc_succ]
    have hN : C ((T : ℚ) - (N : ℕ)) = C ((T : ℚ) - (ij.2 : ℕ)) - C ((ij.1 : ℕ) : ℚ) := by
      rw [← map_sub]
      congr 1
      rw [← hij]
      push_cast
      ring
    rw [hN, map_mul]
    ring

/-- `s μ k = [ε^μ] C(ε, k)`. -/
private def sco (μ k : ℕ) : ℚ :=
  coeff μ (fallPS k) / (k.factorial : ℚ)

private lemma coeff_natCast_mul' (a : ℕ) (F : PowerSeries ℚ) (μ : ℕ) :
    coeff μ ((a : PowerSeries ℚ) * F) = (a : ℚ) * coeff μ F := by
  rw [← map_natCast (C : ℚ →+* PowerSeries ℚ) a, coeff_C_mul]

/-- `[ε^μ] (T + ε)^{\underline N} = N! ∑_{i+j=N} [ε^μ] C(ε, i) · C(T, j)`. -/
private lemma coeff_runPS (T N μ : ℕ) :
    coeff μ (runPS T N) =
      ∑ ij ∈ antidiagonal N, (N.factorial : ℚ) * sco μ ij.1 * (T.choose ij.2 : ℚ) := by
  rw [val_vand, map_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [coeff_natCast_mul', coeff_mul_C, sco, Nat.descFactorial_eq_factorial_mul_choose]
  have h1 := Nat.choose_mul_factorial_mul_factorial (show ij.1 ≤ N by omega)
  rw [show N - ij.1 = ij.2 by omega] at h1
  have hf : (ij.1.factorial : ℚ) ≠ 0 := by positivity
  rw [← h1]
  push_cast
  field_simp

/-! ### Coefficient bounds for `[ε^μ] C(ε, k)` -/

/-- `‖[ε^j] F‖ ≤ 2^{jL}` for all `j`. -/
private def CBd (L : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ j : ℕ, ‖((coeff j F : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ ((j : ℤ) * L)

private lemma cbd_mul {L : ℕ} {F G : PowerSeries ℚ} (hF : CBd L F) (hG : CBd L G) :
    CBd L (F * G) := by
  intro j
  rw [coeff_mul, Rat.cast_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro p hp
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [Rat.cast_mul, norm_mul]
  calc _ ≤ (2 : ℝ) ^ ((p.1 : ℤ) * L) * (2 : ℝ) ^ ((p.2 : ℤ) * L) :=
        mul_le_mul (hF p.1) (hG p.2) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ ((j : ℤ) * L) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← hp]
        push_cast
        ring_nf

private lemma cbd_one (L : ℕ) : CBd L 1 := by
  intro j
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp only [Rat.cast_zero, norm_zero]
    positivity

private lemma cbd_prod {L : ℕ} {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, CBd L (F i)) : CBd L (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cbd_one L
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact cbd_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

private lemma cbd_lin {L : ℕ} (c d : ℚ) (hc : ‖((c : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (L : ℤ))
    (hd : ‖((d : ℚ) : ℚ_[2])‖ ≤ 1) : CBd L (C c * X + C d) := by
  intro j
  rcases j with _ | _ | j
  · simpa [coeff_X, coeff_C] using hd
  · simpa [coeff_X, coeff_C] using hc
  · simp only [map_add, coeff_succ_mul_X, coeff_succ_C, add_zero, Rat.cast_zero, norm_zero]
    positivity

private lemma fall_succ_eq (k : ℕ) :
    fallPS (k + 1) = C (((k + 1).factorial : ℕ) : ℚ) *
      ((C (1 / ((k : ℚ) + 1)) * X + C 0) *
        ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) := by
  have hfac : ∀ i : ℕ, (X - C (((i + 1 : ℕ) : ℚ)) : PowerSeries ℚ) =
      C ((i : ℚ) + 1) * (C (1 / ((i : ℚ) + 1)) * X + C (-1)) := by
    intro i
    have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
    have e1 : C ((i : ℚ) + 1) * C (1 / ((i : ℚ) + 1)) = (1 : PowerSeries ℚ) := by
      rw [← map_mul, mul_one_div_cancel hi, map_one]
    have e2 : C ((i : ℚ) + 1) * C (-1 : ℚ) = -C (((i + 1 : ℕ) : ℚ)) := by
      rw [← map_mul, ← map_neg]
      congr 1
      push_cast
      ring
    rw [mul_add, ← mul_assoc, e1, one_mul, e2, sub_eq_add_neg]
  unfold fallPS
  rw [prod_range_succ', Finset.prod_congr rfl (fun i _ => hfac i), prod_mul_distrib, ← map_prod]
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hprod : ∏ i ∈ range k, ((i : ℚ) + 1) = ((k.factorial : ℕ) : ℚ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  rw [hprod, Nat.factorial_succ]
  simp only [Nat.cast_zero, map_zero, sub_zero, add_zero]
  push_cast
  rw [map_mul]
  have e : C ((k : ℚ) + 1) * C (1 / ((k : ℚ) + 1)) = (1 : PowerSeries ℚ) := by
    rw [← map_mul, mul_one_div_cancel hk, map_one]
  linear_combination (C ((k.factorial : ℕ) : ℚ) * X *
    ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) * e.symm

private lemma sco_succ (μ k : ℕ) :
    sco μ (k + 1) = coeff μ ((C (1 / ((k : ℚ) + 1)) * X + C 0) *
      ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) := by
  rw [sco, fall_succ_eq, coeff_C_mul]
  have : (((k + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

/-- `‖[ε^μ] C(ε, k)‖ ≤ 2^{μ ⌊log₂ k⌋}`. -/
private lemma norm_sco (μ k : ℕ) :
    ‖((sco μ k : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ ((μ : ℤ) * Nat.log 2 k) := by
  rcases k with _ | k
  · simp only [sco, fallPS, range_zero, prod_empty, coeff_one, Nat.factorial_zero, Nat.cast_one,
      div_one, Nat.log_zero_right, Nat.cast_zero, mul_zero, zpow_zero]
    split_ifs <;> simp
  · rw [sco_succ]
    have hinv : ∀ m : ℕ, m ≤ k →
        ‖(((1 / ((m : ℚ) + 1)) : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ ((Nat.log 2 (k + 1) : ℕ) : ℤ) := by
      intro m hmk
      have e : (((1 / ((m : ℚ) + 1)) : ℚ) : ℚ_[2]) = (((m + 1 : ℕ) : ℚ_[2]))⁻¹ := by
        push_cast
        ring
      rw [e]
      refine (val_norm_inv_natCast_le (m + 1) (by omega)).trans ?_
      apply zpow_le_zpow_right₀ (by norm_num)
      exact_mod_cast Nat.log_mono_right (by omega : m + 1 ≤ k + 1)
    have hB : CBd (Nat.log 2 (k + 1)) ((C (1 / ((k : ℚ) + 1)) * X + C 0) *
        ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) := by
      apply cbd_mul
      · exact cbd_lin _ _ (hinv k le_rfl) (by simp)
      · apply cbd_prod
        intro i hi
        rw [Finset.mem_range] at hi
        exact cbd_lin _ _ (hinv i (by omega)) (by simp)
    exact hB μ

/-! ### A run `(T + ε)^{\underline N}`, `T = x + j`: `SerGood` with `E = v₂(N!)` -/

private lemma serGood_run (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) (j N L : ℕ)
    (hNL : Nat.log 2 N ≤ L) :
    SerGood L (padicValNat 2 N.factorial : ℤ) (fun x => runPS (x + j) N) := by
  intro μ
  have hNf : N.factorial ≠ 0 := Nat.factorial_ne_zero N
  refine vgood_congr (g := fun x => ∑ ij ∈ antidiagonal N,
      ((2 : ℚ_[2]) ^ (-(padicValNat 2 N.factorial : ℤ)) * ((N.factorial : ℕ) : ℚ_[2])) *
      (((2 : ℚ_[2]) ^ ((μ : ℤ) * L) * ((sco μ ij.1 : ℚ) : ℚ_[2])) *
        ((Nat.choose (x + j) ij.2 : ℕ) : ℚ_[2]))) (fun x => ?_) ?_
  · rw [coeff_runPS, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [sub_eq_add_neg, zpow_add₀ two_ne_zero]
    push_cast
    ring
  · refine vgood_sum hD _ _ fun ij hij => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hij
    refine vgood_smul hD _ ?_ (vgood_smul hD _ ?_ (vgood_choose hD hDF j ij.2 L ?_))
    · rw [norm_mul, val_norm_two_zpow, val_norm_natCast _ hNf, neg_neg,
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
    · rw [norm_mul, val_norm_two_zpow]
      have hlog : (μ : ℤ) * (Nat.log 2 ij.1 : ℤ) ≤ (μ : ℤ) * L := by
        have : Nat.log 2 ij.1 ≤ L := (Nat.log_mono_right (by omega)).trans hNL
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
      calc (2 : ℝ) ^ (-((μ : ℤ) * L)) * ‖((sco μ ij.1 : ℚ) : ℚ_[2])‖
          ≤ (2 : ℝ) ^ (-((μ : ℤ) * L)) * (2 : ℝ) ^ ((μ : ℤ) * L) := by
            gcongr
            exact (norm_sco μ ij.1).trans (zpow_le_zpow_right₀ (by norm_num) hlog)
        _ = 1 := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
    · exact (Nat.log_mono_right (by omega)).trans hNL

/-! ### The factor `H(δ) = ∏_{k ≤ n} (2x + b_k + δ)^{-a_k}`, `b_k = 2k + 1 - 40u` -/

/-- `(C u + X)⁻¹ = ∑_j (-1)^j u^{-(j+1)} X^j`. -/
private lemma val_inv_C_add_X (u : ℚ) (hu : u ≠ 0) :
    (C u + X : PowerSeries ℚ)⁻¹ = PowerSeries.mk (fun j => (-1) ^ j * u⁻¹ ^ (j + 1)) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hu])]
  ext n
  rcases n with _ | n
  · simp [hu]
  · rw [mul_add, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X]
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false]
    have h : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
    linear_combination (-(-1) ^ n * u⁻¹ ^ (n + 1)) * h

/-- `(C (2x + b) + X)⁻¹` (`b` odd) has level `0`: `[δ^j] = (-1)^j (2x + b)^{-(j+1)}`. -/
private lemma serGood_invZ (hD : Stmt_Delta) (b : ℤ) (hb : Odd b) :
    SerGood 0 0 (fun x => (C (((2 * (x : ℤ) + b : ℤ) : ℚ)) + X)⁻¹) := by
  intro j
  have hne : ∀ x : ℕ, (((2 * (x : ℤ) + b : ℤ) : ℚ)) ≠ 0 := by
    intro x h0
    obtain ⟨k, hk⟩ := hb
    have h1 : (2 * (x : ℤ) + b : ℤ) = 0 := by exact_mod_cast h0
    omega
  refine vgood_congr
    (g := fun x => (-1 : ℚ_[2]) ^ j * (((2 * (x : ℤ) + b : ℤ) : ℚ_[2]))⁻¹ ^ (j + 1))
    (fun x => ?_)
    (vgood_mul hD (vgood_const 0 _ (by simp)) (vgood_pow hD (vgood_inv_oddZ b hb) _))
  dsimp only
  rw [val_inv_C_add_X _ (hne x), coeff_mk]
  simp only [Nat.cast_zero, mul_zero, sub_zero, zpow_zero, one_mul]
  push_cast
  ring

/-- The odd offset `b_k = 2k + 1 - 40u` of the factor `2x + b_k` of `H`. -/
private def boff (u k : ℕ) : ℤ :=
  2 * (k : ℤ) + 1 - 40 * (u : ℤ)

private lemma boff_odd (u k : ℕ) : Odd (boff u k) :=
  ⟨(k : ℤ) - 20 * u, by unfold boff; ring⟩

/-- `H(δ) = ∏_{k ≤ n} (2x + b_k + δ)^{-a_k}`. -/
private def H7 (u x : ℕ) : PowerSeries ℚ :=
  ∏ k ∈ range (40 * u + 1), ((C (((2 * (x : ℤ) + boff u k : ℤ) : ℚ)) + X) ^ apole u k)⁻¹

/-- `H` has level `0` (the exponent-`a_k` analogue of the pair's `vgood_H6`). -/
private lemma serGood_H7base (hD : Stmt_Delta) (u : ℕ) : SerGood 0 0 (H7 u) := by
  have h := serGood_prod hD (range (40 * u + 1)) (fun _ => (0 : ℤ))
    (fun k x => ((C (((2 * (x : ℤ) + boff u k : ℤ) : ℚ)) + X) ^ apole u k)⁻¹)
    (fun k _ => serGood_congr (fun x => (PowerSeries.inv_pow _ _).symm)
      (serGood_pow0 hD (serGood_invZ hD (boff u k) (boff_odd u k)) (apole u k)))
  rw [Finset.sum_const_zero] at h
  exact h

/-- A level-`0` series `H`, rescaled: `2^A H(2ε)` has level `A`. -/
private lemma serGood_scaled (hD : Stmt_Delta) {H : ℕ → PowerSeries ℚ} (hH : SerGood 0 0 H)
    (A L : ℕ) : SerGood L (A : ℤ) (fun x => C ((2 : ℚ) ^ A) * rescale 2 (H x)) := by
  intro j
  have h0 : VGood 0 (fun x => ((coeff j (H x) : ℚ) : ℚ_[2])) :=
    vgood_congr (fun x => by simp) (hH j)
  refine vgood_congr (g := fun x => (2 : ℚ_[2]) ^ (j * L + j) * ((coeff j (H x) : ℚ) : ℚ_[2]))
    (fun x => ?_) (vgood_smul hD _ ?_ (vgood_mono hD (Nat.zero_le L) h0))
  · rw [coeff_C_mul, coeff_rescale]
    push_cast
    rw [← zpow_natCast (2 : ℚ_[2]) A, ← zpow_natCast (2 : ℚ_[2]) j,
      ← zpow_natCast (2 : ℚ_[2]) (j * L + j), ← mul_assoc, ← mul_assoc, ← zpow_add₀ two_ne_zero,
      ← zpow_add₀ two_ne_zero]
    congr 2
    push_cast
    ring
  · rw [← zpow_natCast, val_norm_two_zpow]
    exact val_two_zpow_le_one (by omega)

/-! ### Product form of `R_n(y + ε)`, `y = x - 20u + 1/2` -/

private lemma val_rescale_C (a r : ℚ) : rescale a (C r) = C r := by
  ext n
  simp only [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h
    simp
  · simp

private lemma val_rescale_lin (c : ℚ) : rescale (2 : ℚ) (C c + X) = C c + C 2 * X := by
  rw [map_add, val_rescale_C, rescale_X]

/-- The denominator: `(∏_{j ≤ n} (y + j + ε)^{a_j})⁻¹ = 2^{∑ a_k} H(2ε)`. -/
private lemma val_den7 (u x : ℕ) :
    (∏ j ∈ range (40 * u + 1),
        (C ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2 + (j : ℚ)) + X) ^ apole u j)⁻¹ =
      C ((2 : ℚ) ^ (∑ k ∈ range (40 * u + 1), apole u k)) * rescale 2 (H7 u x) := by
  have hc : ∀ k : ℕ, (((2 * (x : ℤ) + boff u k : ℤ) : ℚ)) ≠ 0 := by
    intro k h0
    have h1 : (2 * (x : ℤ) + boff u k : ℤ) = 0 := by exact_mod_cast h0
    unfold boff at h1
    omega
  have hφ : ∀ k : ℕ,
      constantCoeff ((C (((2 * (x : ℤ) + boff u k : ℤ) : ℚ)) + X) ^ apole u k) ≠ 0 := by
    intro k
    simp only [map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero]
    exact pow_ne_zero _ (hc k)
  have hj : ∀ j ∈ range (40 * u + 1),
      (C ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2 + (j : ℚ)) + X) ^ apole u j =
        C (((1 : ℚ) / 2) ^ apole u j) *
          rescale 2 ((C (((2 * (x : ℤ) + boff u j : ℤ) : ℚ)) + X) ^ apole u j) := by
    intro j _
    rw [map_pow (rescale (2 : ℚ)), val_rescale_lin, map_pow C, ← mul_pow]
    congr 1
    have e1 : (1 / 2 : ℚ) * (((2 * (x : ℤ) + boff u j : ℤ) : ℚ)) =
        (x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2 + (j : ℚ) := by
      unfold boff
      push_cast
      ring
    have e2 : (1 / 2 : ℚ) * 2 = 1 := by norm_num
    rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, e1, e2, map_one, one_mul]
  have hDen : ∏ j ∈ range (40 * u + 1),
      (C ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2 + (j : ℚ)) + X) ^ apole u j =
        C (((1 : ℚ) / 2) ^ (∑ k ∈ range (40 * u + 1), apole u k)) *
          rescale 2 (∏ k ∈ range (40 * u + 1),
            (C (((2 * (x : ℤ) + boff u k : ℤ) : ℚ)) + X) ^ apole u k) := by
    rw [map_prod, ← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hj
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · rw [hDen]
    calc C ((2 : ℚ) ^ (∑ k ∈ range (40 * u + 1), apole u k)) * rescale 2 (H7 u x) *
          (C (((1 : ℚ) / 2) ^ (∑ k ∈ range (40 * u + 1), apole u k)) *
            rescale 2 (∏ k ∈ range (40 * u + 1),
              (C (((2 * (x : ℤ) + boff u k : ℤ) : ℚ)) + X) ^ apole u k))
        = C ((2 : ℚ) ^ (∑ k ∈ range (40 * u + 1), apole u k) *
              ((1 : ℚ) / 2) ^ (∑ k ∈ range (40 * u + 1), apole u k)) *
            rescale 2 (H7 u x * ∏ k ∈ range (40 * u + 1),
              (C (((2 * (x : ℤ) + boff u k : ℤ) : ℚ)) + X) ^ apole u k) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by
          rw [← mul_pow, show (2 : ℚ) * (1 / 2) = 1 by norm_num, one_pow, map_one, one_mul]
          unfold H7
          rw [← Finset.prod_mul_distrib,
            Finset.prod_eq_one (fun k _ => PowerSeries.inv_mul_cancel _ (hφ k)), map_one]
  · rw [map_prod, Finset.prod_ne_zero_iff]
    intro j _
    rw [map_pow]
    apply pow_ne_zero
    simp only [map_add, constantCoeff_C, constantCoeff_X, add_zero]
    intro h0
    apply hc j
    unfold boff
    push_cast at h0 ⊢
    linear_combination 2 * h0

/-- A numerator block `∏_{c ∈ [s-d, s+d)} (x - s + 1 + c + ε)` is the run of length `2d` ending at
`x + d ≥ 0`. -/
private lemma block_run (x s d : ℕ) (hd : d ≤ s) :
    ∏ c ∈ Ico (s - d) (s + d), (C ((x : ℚ) - (s : ℚ) + 1 / 2 + 1 / 2 + (c : ℚ)) + X) =
      runPS (x + d) (2 * d) := by
  unfold runPS
  symm
  refine Finset.prod_nbij' (fun i : ℕ => s + d - 1 - i) (fun c : ℕ => s + d - 1 - c)
    ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico]
    omega
  · intro c hc
    rw [Finset.mem_Ico] at hc
    rw [Finset.mem_range]
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    omega
  · intro c hc
    rw [Finset.mem_Ico] at hc
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    have h1 : (s + d - 1 - i : ℕ) + i + 1 = s + d := by omega
    have h2 : ((s + d - 1 - i : ℕ) : ℚ) + i + 1 = s + d := by exact_mod_cast h1
    congr 2
    push_cast
    linear_combination -h2

/-- The block `C_m = [η_m u, (40 - η_m) u)` is centred at `20u` with half-width `(20 - η_m) u`. -/
private lemma block_eq (u : ℕ) (m : Fin 6) :
    block u m = Ico (20 * u - (20 - eta m) * u) (20 * u + (20 - eta m) * u) := by
  have he : eta m ≤ 20 := by fin_cases m <;> decide
  have h1 : (20 - eta m) * u = 20 * u - eta m * u := Nat.sub_mul 20 (eta m) u
  have h2 : eta m * u ≤ 20 * u := Nat.mul_le_mul_right u he
  unfold block
  rw [h1]
  congr 1 <;> omega

/-- **Product form** (lemma V1): `R_n(y + ε) = (2x + 1 + 2ε) · ∏_m (x + d_m + ε)^{\underline{2 d_m}}
· 2^{∑ a_k} H(2ε)` at `y = x - 20u + 1/2`, `d_m = (20 - η_m) u`. -/
private lemma val_Rser7 (u x : ℕ) :
    Rser u ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2) =
      (C (((2 * x + 1 + 0 : ℕ) : ℚ)) + C 2 * X) *
        ((∏ m : Fin 6, runPS (x + (20 - eta m) * u) (2 * ((20 - eta m) * u))) *
          (C ((2 : ℚ) ^ (∑ k ∈ range (40 * u + 1), apole u k)) * rescale 2 (H7 u x))) := by
  unfold Rser numSer
  rw [val_den7]
  have hb : ∀ m : Fin 6, ∏ c ∈ block u m,
      (C ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2 + 1 / 2 + (c : ℚ)) + X) =
        runPS (x + (20 - eta m) * u) (2 * ((20 - eta m) * u)) := by
    intro m
    rw [block_eq]
    exact block_run x (20 * u) ((20 - eta m) * u) (Nat.mul_le_mul_right u (Nat.sub_le 20 (eta m)))
  rw [Finset.prod_congr rfl (fun m _ => hb m)]
  have e1 : (2 : ℚ) * ((x : ℚ) - ((20 * u : ℕ) : ℚ) + 1 / 2) + ((40 * u : ℕ) : ℚ) =
      ((2 * x + 1 + 0 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [e1]
  ring

/-! ### `∑_k a_k = 136u + 4` -/

private lemma apole_split (u k : ℕ) : apole u k =
    1 + (if 2 * u ≤ min k (40 * u - k) then 1 else 0) +
      (if 4 * u ≤ min k (40 * u - k) then 1 else 0) +
      (if 6 * u ≤ min k (40 * u - k) then 1 else 0) := by
  unfold apole
  split_ifs <;> omega

private lemma count_band (u t : ℕ) (ht : 2 * t ≤ 40 * u) :
    ∑ k ∈ range (40 * u + 1), (if t ≤ min k (40 * u - k) then 1 else 0) =
      40 * u + 1 - 2 * t := by
  rw [← Finset.card_filter]
  have e : (range (40 * u + 1)).filter (fun k => t ≤ min k (40 * u - k)) = Icc t (40 * u - t) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [e, Nat.card_Icc]
  omega

private lemma sum_apole (u : ℕ) : ∑ k ∈ range (40 * u + 1), apole u k = 136 * u + 4 := by
  rw [Finset.sum_congr rfl (fun k _ => apole_split u k)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, card_range, smul_eq_mul, mul_one]
  rw [count_band u (2 * u) (by omega), count_band u (4 * u) (by omega),
    count_band u (6 * u) (by omega)]
  omega

/-! ### Legendre -/

/-- `v₂(N!) = N - s₂(N) ≥ N - ⌊log₂ N⌋ - 1`. -/
private lemma val_legendre (N L : ℕ) (hNL : Nat.log 2 N ≤ L) :
    (N : ℤ) - (L + 1) ≤ (padicValNat 2 N.factorial : ℤ) := by
  have h1 := sub_one_mul_padicValNat_factorial (p := 2) N
  have h3 := Nat.digit_sum_le 2 N
  have h2 : (Nat.digits 2 N).sum ≤ Nat.log 2 N + 1 := by
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0
      simp
    · calc (Nat.digits 2 N).sum ≤ (Nat.digits 2 N).length • 1 :=
            List.sum_le_length_nsmul _ _ (fun d hd => by
              have := Nat.digits_lt_base (by norm_num) hd
              omega)
        _ = Nat.log 2 N + 1 := by
            rw [smul_eq_mul, mul_one, Nat.length_digits 2 N (by norm_num) hN.ne']
  norm_num at h1
  omega

/-! ### The theorem -/

theorem Valuation7_proof (hIT : Stmt_IntegrandTaylor7) (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) :
    Stmt_Valuation7 := by
  refine ⟨4 * 30 ^ 10, 10, fun u I hI => ?_⟩
  set L : ℕ := Nat.log 2 (30 * u) with hL
  have heta : ∀ m : Fin 6, 5 ≤ eta m := by decide
  -- the run lengths `N_m = 2 (20 - η_m) u ≤ 30 u`
  have hlen : ∀ m : Fin 6, 2 * ((20 - eta m) * u) ≤ 30 * u := by
    intro m
    have h1 : (20 - eta m) * u ≤ 15 * u := Nat.mul_le_mul_right u (by have := heta m; omega)
    omega
  have hlog : ∀ m : Fin 6, Nat.log 2 (2 * ((20 - eta m) * u)) ≤ L := fun m =>
    Nat.log_mono_right (hlen m)
  -- `SerGood` for the product form
  have hQ : SerGood L (∑ m : Fin 6, (padicValNat 2 (2 * ((20 - eta m) * u)).factorial : ℤ))
      (fun x => ∏ m : Fin 6, runPS (x + (20 - eta m) * u) (2 * ((20 - eta m) * u))) :=
    serGood_prod hD univ _ _ (fun m _ => serGood_run hD hDF _ _ L (hlog m))
  have hTot := serGood_mul hD (serGood_lin hD hDF 0 L)
    (serGood_mul hD hQ
      (serGood_scaled hD (serGood_H7base hD u) (∑ k ∈ range (40 * u + 1), apole u k) L))
  set E : ℤ := 0 + ((∑ m : Fin 6, (padicValNat 2 (2 * ((20 - eta m) * u)).factorial : ℤ)) +
    ((∑ k ∈ range (40 * u + 1), apole u k : ℕ) : ℤ)) with hE
  have h3 := hTot 3
  -- the integrand is `(-6 · 2^{E - 3L}) ·` (a `VGood L` function)
  have hf : (fun x => ((integrand u x : ℚ) : ℚ_[2])) = fun x =>
      ((-6 : ℚ_[2]) * (2 : ℚ_[2]) ^ (E - 3 * L)) *
        ((2 : ℚ_[2]) ^ (((3 : ℕ) : ℤ) * L - E) *
          ((coeff 3 ((C (((2 * x + 1 + 0 : ℕ) : ℚ)) + C 2 * X) *
            ((∏ m : Fin 6, runPS (x + (20 - eta m) * u) (2 * ((20 - eta m) * u))) *
              (C ((2 : ℚ) ^ (∑ k ∈ range (40 * u + 1), apole u k)) * rescale 2 (H7 u x)))) :
                ℚ) : ℚ_[2])) := by
    funext x
    rw [hIT u x, val_Rser7 u x]
    have e0 : (E - 3 * L) + (((3 : ℕ) : ℤ) * L - E) = 0 := by
      push_cast
      ring
    have e1 : ∀ c : ℚ_[2], ((-6 : ℚ_[2]) * (2 : ℚ_[2]) ^ (E - 3 * L)) *
        ((2 : ℚ_[2]) ^ (((3 : ℕ) : ℤ) * L - E) * c) = -6 * c := by
      intro c
      rw [mul_assoc, ← mul_assoc ((2 : ℚ_[2]) ^ (E - 3 * L)), ← zpow_add₀ (two_ne_zero), e0,
        zpow_zero, one_mul]
    rw [e1]
    push_cast
    ring
  have h6 : ‖(-6 : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(1 : ℤ)) := by
    rw [norm_neg, show (6 : ℚ_[2]) = 2 * ((3 : ℕ) : ℚ_[2]) by norm_num, norm_mul]
    have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ) ^ (-(1 : ℤ)) := by
      have := val_norm_two_zpow 1
      simpa using this
    rw [h2]
    calc (2 : ℝ) ^ (-(1 : ℤ)) * ‖((3 : ℕ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(1 : ℤ)) * 1 := by
          gcongr
          exact val_norm_natCast_le_one 3
      _ = _ := mul_one _
  have hK : ‖(-6 : ℚ_[2]) * (2 : ℚ_[2]) ^ (E - 3 * L)‖ ≤ (2 : ℝ) ^ (-(E - 3 * L + 1)) := by
    rw [norm_mul, val_norm_two_zpow]
    calc ‖(-6 : ℚ_[2])‖ * (2 : ℝ) ^ (-(E - 3 * L)) ≤
        (2 : ℝ) ^ (-(1 : ℤ)) * (2 : ℝ) ^ (-(E - 3 * L)) := by gcongr
      _ = (2 : ℝ) ^ (-(E - 3 * L + 1)) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1
          ring
  have hΔ : DeltaAll (-(L : ℤ) + (E - 3 * L + 1)) (fun x => ((integrand u x : ℚ) : ℚ_[2])) := by
    rw [hf]
    exact hD.smulAll _ _ _ _ hK h3.2
  -- every Riemann sum, hence the limit, has `‖·‖ ≤ 2^{4L - E}`
  have hIle : ‖I‖ ≤ (2 : ℝ) ^ (1 - (-(L : ℤ) + (E - 3 * L + 1))) :=
    le_of_tendsto' hI.norm (fun M => hD.riemannAll _ _ hΔ M)
  -- Legendre: `E ≥ 272 u - 2 - 6 L`
  have hleg : ∀ m : Fin 6, ((2 * ((20 - eta m) * u) : ℕ) : ℤ) - (L + 1) ≤
      (padicValNat 2 (2 * ((20 - eta m) * u)).factorial : ℤ) := fun m =>
    val_legendre _ L (hlog m)
  have hsumN : ∑ m : Fin 6, ((2 * ((20 - eta m) * u) : ℕ) : ℤ) = 136 * (u : ℤ) := by
    simp only [Fin.sum_univ_six]
    have e0 : eta 0 = 5 := rfl
    have e1 : eta 1 = 7 := rfl
    have e2 : eta 2 = 7 := rfl
    have e3 : eta 3 = 9 := rfl
    have e4 : eta 4 = 11 := rfl
    have e5 : eta 5 = 13 := rfl
    rw [e0, e1, e2, e3, e4, e5]
    push_cast
    ring
  have hA : ((∑ k ∈ range (40 * u + 1), apole u k : ℕ) : ℤ) = 136 * (u : ℤ) + 4 := by
    rw [sum_apole]
    push_cast
    ring
  have hEge : 272 * (u : ℤ) - 2 - 6 * L ≤ E := by
    have hs := Finset.sum_le_sum (fun m (_ : m ∈ (univ : Finset (Fin 6))) => hleg m)
    rw [Finset.sum_sub_distrib, hsumN] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at hs
    rw [hE, hA]
    linarith
  have hIle' : ‖I‖ ≤ (2 : ℝ) ^ ((10 * L + 2 : ℤ) - (272 * u : ℤ)) :=
    hIle.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  -- final numerics: `4 · 2^{10L} ≤ 4 (30(u+1))^{10}`
  have h2L : (2 : ℝ) ^ L ≤ 30 * ((u : ℝ) + 1) := by
    have : 2 ^ L ≤ 30 * u + 1 := by
      rcases Nat.eq_zero_or_pos (30 * u) with h0 | hpos
      · rw [hL, h0]
        simp
      · exact (Nat.pow_log_le_self 2 hpos.ne').trans (Nat.le_succ _)
    calc (2 : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((30 * u + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ 30 * ((u : ℝ) + 1) := by push_cast; linarith
  have hpow : (2 : ℝ) ^ ((10 * L + 2 : ℤ) - (272 * u : ℤ)) * (2 : ℝ) ^ (272 * u) =
      4 * ((2 : ℝ) ^ L) ^ 10 := by
    rw [← zpow_natCast (2 : ℝ) (272 * u), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show ((10 * L + 2 : ℤ) - (272 * u : ℤ)) + ((272 * u : ℕ) : ℤ) = ((10 * L + 2 : ℕ) : ℤ) by
        push_cast
        ring,
      zpow_natCast, pow_add, pow_mul']
    ring
  calc ‖I‖ * (2 : ℝ) ^ (272 * u)
      ≤ (2 : ℝ) ^ ((10 * L + 2 : ℤ) - (272 * u : ℤ)) * (2 : ℝ) ^ (272 * u) := by gcongr
    _ = 4 * ((2 : ℝ) ^ L) ^ 10 := hpow
    _ ≤ 4 * (30 * ((u : ℝ) + 1)) ^ 10 := by gcongr
    _ = 4 * 30 ^ 10 * ((u : ℝ) + 1) ^ 10 := by ring

end Zeta2.Z7

end
