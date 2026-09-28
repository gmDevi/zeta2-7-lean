module

public import Zeta2Lean.Z7.Proofs.LocalExpansion7

@[expose] public section

/-!
# Lemma 4.3: the class lemma (the new mathematics of the denominator bound)

gap: 'denominators'.  Difficulty 5.

**Statement** (`Stmt_ClassLemma7`, from `Stmt_PF7`): for a prime `q ≥ 5` with `q > 2x + 2`
(`x = n/q`, i.e. `80u + 2q < q²`), a class `k₀ < q` and a kernel `κ(y) = c₀ + c y^j` (`j ≥ 1`,
`c₀, c` `q`-integral): if `[y^p] D_{ξ,κ} = 0` for `E_ξ + 1 ≤ p < P` (`LevGe`), then
`v_q(β_ξ - 24 q^{-5} ∮_{D_ξ} R_n(t) K((t + k₀)/q) dt) ≥ P - 5`,
with `β_ξ = classBad u q k₀` and `∮ R_n K = kerRes u q k₀ c₀ j c` (`K(v) = κ(1/v)`).

## Proof (finite algebra; the `q`-adic analysis of proof Lemma 4.3 is replaced by exact identities)

Notation: `τ = localModel u q k₀`, `E = τ.E`, class poles `k = k₀ + J q ≤ n` at the local
positions `w = -2J` (doubled coordinates), `Ũ_w = Ufam u q k₀ w = rescale q (Û(-k₀ + q w/2))`
the Taylor series of the outer factor `Û` (shared helper `LocalExpansion7.lean`, namespace `LE7`).

1. **Residue functionals** (`CL7.PairF`, `CL7.ResF`, `CL7.Psi`):
   `Ψ(Φ) = PairF τ Φ - c₀ ResF τ Φ - c ResF (kerType τ j) Φ` for a family `Φ : ℤ → ℚ⟦ε⟧`;
   `PairF` sums `sg [ε^{a-1}] (Φ_{w_k} gSer)` over the bad pairs, `ResF` sums
   `[ε^{a-1}] (Φ_w taylorAt)` over the poles; `kerType τ j` adds the kernel pole `v^{-j}`.
2. **Main identity** (`CL7.LHS_eq`): `β_ξ - 24 q^{-5} ∮ R_n K = 24 q^{E-4} Ψ(Ũ)`.  Per pole it is
   the per-pole factorisation `LE7.Gser_factor` (`G_k(ε) = q^{E+a} ε^{ctr} Û(-k+ε) τ_k(ε/q)`) and
   `coeff_mul_rescale_inv`: `X(k, sq/2) = 24 q^{E-4} [ε^{a-1}](Ũ gSer)` (`Xk_eq`),
   `r_{1,k} = q^{E+1} [ε^{a-1}] (Ũ taylorAt)` (`rcoef_one_eq`), the kernel part at `k ≠ k₀`
   (`kerPole_eq`) and at the kernel pole `-k₀` (`KP_eq`, via partial fractions at `-k₀`:
   `Gser_pf_pole` from `Stmt_PF7.poly`, or `Stmt_PF7.series` when `k₀ > n`).  The class sums are
   re-indexed by `J` (`LE7.sum_cls`, `LE7.poleSet_eq`, `LE7.pairs_sum`, `LE7.sum_oddBetween_dvd`).
3. **Polynomials** (`CL7.Psi_poly`): `Ψ((C(w/2) + X)^m) = coeffD τ c₀ j c (E + m + 1)`, by the
   residue theorem at infinity `LE7.grt_local` (for `τ` and `kerType τ j`) and a binomial
   identity for `ASer` (`pair_poly_term`).
4. **Truncation** (`LE7.trunc_exists`): with `M = (P - E - 1).toNat` there are `F_m` with
   `Ũ_w - ∑_{m<M} F_m q^m (w/2 + ε)^m ≡ 0 mod q^M` coefficientwise at every `w = -2J`.
   So `Ψ(Ũ) = Ψ(T) + Ψ(Ũ - T)`, `Ψ(T) = ∑_{m<M} F_m q^m coeffD(E+m+1) = 0` (`LevGe`), and
   `v_q(Ψ(Ũ - T)) ≥ M` (`CL7.Psi_val`, with the `q`-integrality of `taylorAt`/`gSer`,
   Lemma 4.2 = `LE7.PSV_taylorAt_model`, `PSV_taylorAt_ker`, `PSV_gSer_model`).
   Hence `v_q(LHS) ≥ E - 4 + M ≥ P - 5`.

**Numerical check.** `python/z7_mirror.py`, section "ClassLemma7 / KernelIdentity7 / FarPart7";
`python/z7_audit.py` (`n = 40 … 400`, every admissible prime, 0 failures).
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace CL7

open LE7

/-! ### Generalised binomial coefficients at negative integers -/

/-! ### The residue functionals -/

/-- The pair functional `∑_{pairs} sg · [ε^{ord-1}] (Φ_{w_k} · gSer)`. -/
def PairF (τ : LocalType) (Φ : ℤ → PowerSeries ℚ) : ℚ :=
  (τ.pairs.map fun pr => (pr.2.2 : ℚ) * coeff (ord τ pr.1 - 1) (Φ pr.1 * gSer τ pr.1 pr.2.1)).sum

/-- `Ψ = PairF - c₀ ResF - c ResF(kernel pole added)`. -/
def Psi (τ : LocalType) (c0 : ℚ) (j : ℕ) (c : ℚ) (Φ : ℤ → PowerSeries ℚ) : ℚ :=
  PairF τ Φ - c0 * ResF τ Φ - c * ResF (kerType τ j) Φ

theorem list_sum_map_add {α : Type*} (L : List α) (f g : α → ℚ) :
    (L.map fun x => f x + g x).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_map_finset_sum {α ι : Type*} (L : List α) (s : Finset ι) (f : α → ι → ℚ) :
    (L.map fun x => ∑ m ∈ s, f x m).sum = ∑ m ∈ s, (L.map fun x => f x m).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

theorem PairF_add (τ : LocalType) (Φ₁ Φ₂ : ℤ → PowerSeries ℚ) :
    PairF τ (fun w => Φ₁ w + Φ₂ w) = PairF τ Φ₁ + PairF τ Φ₂ := by
  unfold PairF
  rw [← list_sum_map_add]
  congr 1
  apply List.map_congr_left
  intro pr _
  rw [add_mul, map_add, mul_add]

theorem Psi_add (τ : LocalType) (c0 : ℚ) (j : ℕ) (c : ℚ) (Φ₁ Φ₂ : ℤ → PowerSeries ℚ) :
    Psi τ c0 j c (fun w => Φ₁ w + Φ₂ w) = Psi τ c0 j c Φ₁ + Psi τ c0 j c Φ₂ := by
  unfold Psi
  rw [PairF_add, ResF_add, ResF_add]
  ring

theorem PairF_sum (τ : LocalType) (s : Finset ℕ) (a : ℕ → ℚ) (Φ : ℕ → ℤ → PowerSeries ℚ) :
    PairF τ (fun w => ∑ m ∈ s, C (a m) * Φ m w) = ∑ m ∈ s, a m * PairF τ (Φ m) := by
  unfold PairF
  simp only [coeff_sum_C_mul, Finset.mul_sum]
  rw [list_sum_map_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro pr _
  ring

theorem Psi_sum (τ : LocalType) (c0 : ℚ) (j : ℕ) (c : ℚ) (s : Finset ℕ) (a : ℕ → ℚ)
    (Φ : ℕ → ℤ → PowerSeries ℚ) :
    Psi τ c0 j c (fun w => ∑ m ∈ s, C (a m) * Φ m w) = ∑ m ∈ s, a m * Psi τ c0 j c (Φ m) := by
  unfold Psi
  rw [PairF_sum, ResF_sum, ResF_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ### The functionals on polynomials: residue theorem and the `A`-series -/

/-- One pair: `sg [ε^{a-1}] ((v + ε)^m g) = [y^{m+1}] (sg ∑_i g_{a-i} y^i (1 - v y)^{-i})`. -/
theorem pair_poly_term (a : ℕ) (ha : 1 ≤ a) (v sg : ℚ) (g : PowerSeries ℚ) (m : ℕ) :
    sg * coeff (a - 1) ((C v + X) ^ m * g) =
      coeff (m + 1) (C sg * ∑ i ∈ Icc 1 a, C (coeff (a - i) g) * X ^ i * bser (-v) (-(i : ℤ))) := by
  rw [coeff_C_mul, map_sum, coeff_mul]
  congr 1
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
  have hR : ∀ i : ℕ, 1 ≤ i →
      coeff (m + 1) (C (coeff (a - i) g) * X ^ i * bser (-v) (-(i : ℤ))) =
        coeff (a - i) g * (if i - 1 ≤ m then (m.choose (i - 1) : ℚ) * v ^ (m - (i - 1)) else 0) := by
    intro i hi
    rw [mul_assoc, coeff_C_mul, PowerSeries.coeff_X_pow_mul', coeff_bser]
    by_cases him : i - 1 ≤ m
    · rw [ite_eq_left (by omega), ite_eq_left him, show m + 1 - i = m - (i - 1) by omega,
        gchoose_neg i hi (m - (i - 1))]
      unfold negChoose
      rw [show m - (i - 1) + i - 1 = m by omega, Nat.choose_symm him, neg_pow]
      have h1 : ((-1 : ℚ) ^ (m - (i - 1))) * ((-1 : ℚ) ^ (m - (i - 1))) = 1 := by
        rw [← mul_pow]; norm_num
      linear_combination (coeff (a - i) g * (m.choose (i - 1) : ℚ) * v ^ (m - (i - 1))) * h1
    · rw [ite_eq_right (by omega), ite_eq_right him]
  refine Finset.sum_nbij' (fun l => l + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_range] at hl
    simp only [Finset.mem_Icc]
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [Finset.mem_range]
    omega
  · intro l _
    simp
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  · intro l hl
    simp only [Finset.mem_range] at hl
    rw [hR (l + 1) (by omega), coeff_C_add_X_pow, Nat.add_sub_cancel,
      show a - 1 - l = a - (l + 1) by omega]
    split_ifs with hlm
    · ring
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; ring

theorem PairF_poly (τ : LocalType) (hτ : ∀ pr ∈ τ.pairs, 1 ≤ ord τ pr.1) (m : ℕ) :
    PairF τ (fun w => (C ((w : ℚ) / 2) + X) ^ m) = coeffZ (ASer τ) ((m : ℤ) + 1) := by
  unfold PairF ASer coeffZ
  rw [ite_eq_left (by omega), show ((m : ℤ) + 1).toNat = m + 1 by omega, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pr hpr
  simp only [Function.comp_apply]
  have := pair_poly_term (ord τ pr.1) (hτ pr hpr) ((pr.1 : ℚ) / 2) (pr.2.2 : ℚ)
    (gSer τ pr.1 pr.2.1) m
  rw [this]
  unfold ord
  congr 4
  ext i
  congr 2
  rw [neg_div]

theorem Psi_poly (τ : LocalType) (hτ : ∀ pr ∈ τ.pairs, 1 ≤ ord τ pr.1) (c0 : ℚ) (j : ℕ)
    (c : ℚ) (m : ℕ) :
    Psi τ c0 j c (fun w => (C ((w : ℚ) / 2) + X) ^ m) = coeffD τ c0 j c (τ.E + m + 1) := by
  unfold Psi coeffD
  rw [PairF_poly τ hτ m]
  have h1 : ResF τ (fun w => (C ((w : ℚ) / 2) + X) ^ m) = coeffZ (rSer τ) (τ.E + m + 1) :=
    grt_local τ m
  have h2 : ResF (kerType τ j) (fun w => (C ((w : ℚ) / 2) + X) ^ m) =
      coeffZ (rSer τ) (τ.E + m + 1 - j) := by
    unfold ResF
    rw [grt_local, kerType_rSer, kerType_E]
    congr 1
    ring
  rw [h1, h2]
  congr 2
  ring

/-! ### Valuation of `Ψ` -/

theorem Psi_val {q : ℕ} [Fact q.Prime] (τ : LocalType) (c0 : ℚ) (j : ℕ) (c : ℚ)
    (Φ : ℤ → PowerSeries ℚ) (M : ℤ) (hc0 : ValGe q 0 c0) (hc : ValGe q 0 c)
    (hpair : ∀ pr ∈ τ.pairs, PSV q M (Φ pr.1) ∧ PSV q 0 (gSer τ pr.1 pr.2.1))
    (hres : ∀ w ∈ poleSet τ, PSV q M (Φ w) ∧ PSV q 0 (taylorAt τ w))
    (hker : ∀ w ∈ poleSet (kerType τ j), PSV q M (Φ w) ∧ PSV q 0 (taylorAt (kerType τ j) w)) :
    ValGe q M (Psi τ c0 j c Φ) := by
  unfold Psi PairF ResF
  refine valGe_sub (valGe_sub ?_ ?_) ?_
  · refine valGe_list_sum _ fun x hx => ?_
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.1 hx
    have h : PSV q M (Φ pr.1 * gSer τ pr.1 pr.2.1) :=
      (hpair pr hpr).1.mul' (hpair pr hpr).2 (by simp)
    exact valGe_mul (L := 0) (M := M) (valGe_int _) (h _) (by simp)
  · refine valGe_mul (L := 0) (M := M) hc0 (valGe_sum _ _ fun w hw => ?_) (by simp)
    have h : PSV q M (Φ w * taylorAt τ w) := (hres w hw).1.mul' (hres w hw).2 (by simp)
    exact h _
  · refine valGe_mul (L := 0) (M := M) hc (valGe_sum _ _ fun w hw => ?_) (by simp)
    have h : PSV q M (Φ w * taylorAt (kerType τ j) w) :=
      (hker w hw).1.mul' (hker w hw).2 (by simp)
    exact h _

/-! ### The local Taylor family of the outer factor, and the per-pole identities -/

/-- The bad pairs: `X(k, o/2) = 24 q^{E-4} [ε^{a-1}] (Ũ · gSer)` for `o = s q`. -/
theorem Xk_eq {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) {J : ℕ}
    (hJ : k₀ + J * q ≤ 40 * u) (s : ℤ) (hs : s ≠ 0) :
    Xk u (k₀ + J * q) (s * q) = 24 * (q : ℚ) ^ ((localModel u q k₀).E - 4) *
      coeff (ord (localModel u q k₀) (-(2 * (J : ℤ))) - 1)
        (Ufam u q k₀ (-(2 * (J : ℤ))) *
          gSer (localModel u q k₀) (-(2 * (J : ℤ))) (-(2 * (J : ℤ)) + s)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  set h : ℚ := (s : ℚ) * q / 2 with hh
  have hh0 : h ≠ 0 := by rw [hh]; positivity
  set So : PowerSeries ℚ := C (h ^ (-5 : ℤ)) * bser (-h⁻¹) (-5) with hSo
  have hX : Xk u (k₀ + J * q) (s * q) = 24 * coeff (apole u (k₀ + J * q) - 1)
      (Gser u (k₀ + J * q) * So) := by
    rw [coeff_Gser_mul_eq_sum u _ hJ, Finset.mul_sum]
    unfold Xk
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    rw [hSo, coeff_C_mul, coeff_bser]
    have e2 : (2 : ℚ) / ((s * q : ℤ) : ℚ) = h⁻¹ := by rw [hh]; push_cast; field_simp
    rw [e2]
    obtain ⟨hi1, hi4⟩ := hi
    interval_cases i <;> simp [gchoose, Finset.prod_range_succ, zpow_neg] <;> ring
  have hSo' : So = C ((q : ℚ) ^ (-5 : ℤ)) * rescale ((q : ℚ)⁻¹)
      (C (((s : ℚ) / 2) ^ (-5 : ℤ)) * bser (-((s : ℚ) / 2)⁻¹) (-5)) := by
    rw [hSo, map_mul, rescale_C', rescale_bser, ← mul_assoc, ← map_mul, ← mul_zpow]
    congr 3
    · rw [hh]; ring
    · rw [hh]; field_simp
  rw [hX, hSo', show apole u (k₀ + J * q) - 1 = apole u (k₀ + J * q) - 1 + 0 by rfl,
    coeff_Gser_mul hq hq2 hk₀ hJ 0 (-5), Nat.add_zero]
  have hg : taylorAt (localModel u q k₀) (-(2 * (J : ℤ))) *
      (C (((s : ℚ) / 2) ^ (-5 : ℤ)) * bser (-((s : ℚ) / 2)⁻¹) (-5)) =
      gSer (localModel u q k₀) (-(2 * (J : ℤ))) (-(2 * (J : ℤ)) + s) := by
    unfold gSer
    congr 3
    · push_cast; ring
    · push_cast
      rw [show (-(2 * (J : ℚ)) + s - -(2 * J)) = s by ring, neg_div, inv_div]
  rw [hg, Nat.cast_zero, sub_zero]
  rw [show (localModel u q k₀).E + 1 + -5 = (localModel u q k₀).E - 4 by ring]
  ring

/-- `r_{1,k} = q^{E+1} [ε^{a-1}] (Ũ · taylorAt)`. -/
theorem rcoef_one_eq {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) {J : ℕ}
    (hJ : k₀ + J * q ≤ 40 * u) :
    rcoef u 1 (k₀ + J * q) = (q : ℚ) ^ ((localModel u q k₀).E + 1) *
      coeff (ord (localModel u q k₀) (-(2 * (J : ℤ))) - 1)
        (Ufam u q k₀ (-(2 * (J : ℤ))) * taylorAt (localModel u q k₀) (-(2 * (J : ℤ)))) := by
  have h1 : rcoef u 1 (k₀ + J * q) = coeff (apole u (k₀ + J * q) - 1 + 0)
      (Gser u (k₀ + J * q) * (C ((q : ℚ) ^ (0 : ℤ)) * rescale ((q : ℚ)⁻¹) 1)) := by
    unfold rcoef
    rw [ite_eq_left ⟨le_rfl, apole_pos u _, hJ⟩, map_one, zpow_zero, map_one, one_mul, mul_one,
      Nat.add_zero]
  rw [h1, coeff_Gser_mul hq hq2 hk₀ hJ 0 0 1, mul_one, Nat.add_zero, Nat.cast_zero, sub_zero,
    add_zero]

/-- The kernel part at a class pole `k ≠ k₀`. -/
theorem kerPole_eq {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) {J : ℕ}
    (hJ : k₀ + J * q ≤ 40 * u) (hJ0 : J ≠ 0) (j : ℕ) (hj : 1 ≤ j) :
    ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i (k₀ + J * q) * negChoose j (i - 1) *
        (((k₀ : ℚ) - ((k₀ + J * q : ℕ) : ℚ))⁻¹) ^ (i + j - 1) =
      (q : ℚ) ^ ((localModel u q k₀).E + 1 - j) *
        coeff (ord (kerType (localModel u q k₀) j) (-(2 * (J : ℤ))) - 1)
          (Ufam u q k₀ (-(2 * (J : ℤ))) *
            taylorAt (kerType (localModel u q k₀) j) (-(2 * (J : ℤ)))) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hz : ((k₀ : ℚ) - ((k₀ + J * q : ℕ) : ℚ)) = -(J : ℚ) * q := by push_cast; ring
  have hJq : (-(J : ℚ)) ≠ 0 := by
    have : (J : ℚ) ≠ 0 := by exact_mod_cast hJ0
    exact neg_ne_zero.2 this
  have hw0 : (-(2 * (J : ℤ))) ≠ 0 := by omega
  have h1 : ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i (k₀ + J * q) * negChoose j (i - 1) *
        (((k₀ : ℚ) - ((k₀ + J * q : ℕ) : ℚ))⁻¹) ^ (i + j - 1) =
      coeff (apole u (k₀ + J * q) - 1)
        (Gser u (k₀ + J * q) * lin ((k₀ : ℚ) - ((k₀ + J * q : ℕ) : ℚ)) (-(j : ℤ))) := by
    rw [coeff_Gser_mul_eq_sum u _ hJ]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    rw [coeff_lin_neg _ (by rw [hz]; exact mul_ne_zero hJq hq0) j hj i hi.1, mul_assoc]
  have h2 : lin ((k₀ : ℚ) - ((k₀ + J * q : ℕ) : ℚ)) (-(j : ℤ)) =
      C ((q : ℚ) ^ (-(j : ℤ))) * rescale ((q : ℚ)⁻¹) (lin (-(J : ℚ)) (-(j : ℤ))) := by
    rw [rescale_lin (inv_ne_zero hq0), ← mul_assoc, ← map_mul, inv_zpow', neg_neg, ← zpow_add₀ hq0,
      neg_add_cancel, zpow_zero, map_one, one_mul, div_inv_eq_mul, hz]
  rw [h1, h2, show apole u (k₀ + J * q) - 1 = apole u (k₀ + J * q) - 1 + 0 by rfl,
    coeff_Gser_mul hq hq2 hk₀ hJ 0 (-(j : ℤ)), Nat.add_zero, Nat.cast_zero, sub_zero,
    kerType_ord _ _ hw0, kerType_taylorAt, ite_eq_right hw0]
  have hlin : (((-(2 * (J : ℤ)) : ℤ) : ℚ) / 2) = -(J : ℚ) := by push_cast; ring
  rw [hlin, sub_eq_add_neg ((localModel u q k₀).E + 1)]

/-! ### The residue at the kernel pole `-k₀` (partial fractions at `-k₀`) -/

/-- `[ε^{j-1}]` of the regular part of `R_n` at `-k₀`, through the partial fractions. -/
def KP (u k₀ j : ℕ) : ℚ :=
  ∑ k ∈ (range (40 * u + 1)).erase k₀, ∑ i ∈ Icc (1 : ℕ) 4,
    rcoef u i k * negChoose i (j - 1) * (((k : ℚ) - k₀)⁻¹) ^ (i + j - 1)

/-- Partial fractions at the pole `-k₀`: `G_{k₀} = (principal part) + ε^{a} ∑_{k ≠ k₀} PP_k`. -/
theorem Gser_pf_pole (hPF : Stmt_PF7) (u k₀ : ℕ) (hk : k₀ ≤ 40 * u) :
    Gser u k₀ = (∑ i ∈ Icc (1 : ℕ) (apole u k₀), C (rcoef u i k₀) * X ^ (apole u k₀ - i)) +
      X ^ apole u k₀ * ∑ k ∈ (range (40 * u + 1)).erase k₀, ∑ i ∈ Icc (1 : ℕ) 4,
        C (rcoef u i k) * ((C ((k : ℚ) - k₀) + X) ^ i)⁻¹ := by
  have hmem : k₀ ∈ range (40 * u + 1) := Finset.mem_range.2 (by omega)
  have hfac : ∀ c : ℚ,
      substPS (-(k₀ : ℚ)) (Polynomial.X + Polynomial.C c) = C (c - k₀) + X := by
    intro c
    rw [substPS_X_add_C, neg_add_eq_sub]
  have hX : (C ((k₀ : ℚ) - k₀) + X : PowerSeries ℚ) = X := by
    rw [sub_self, map_zero, zero_add]
  set V : PowerSeries ℚ := ∏ j ∈ (range (40 * u + 1)).erase k₀,
    (C ((j : ℚ) - k₀) + X) ^ apole u j with hV
  set T : PowerSeries ℚ := ∑ i ∈ Icc (1 : ℕ) (apole u k₀),
    C (rcoef u i k₀) * X ^ (apole u k₀ - i) with hT
  set E' : PowerSeries ℚ := ∑ k ∈ (range (40 * u + 1)).erase k₀, ∑ i ∈ Icc (1 : ℕ) (apole u k),
    C (rcoef u i k) * (C ((k : ℚ) - k₀) + X) ^ (apole u k - i) *
      ∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k₀) + X) ^ apole u j with hE'
  have hne : ∀ j ∈ (range (40 * u + 1)).erase k₀, ((j : ℚ) - k₀) ≠ 0 := by
    intro j hj
    have := Finset.ne_of_mem_erase hj
    exact sub_ne_zero.2 (by exact_mod_cast this)
  have hV0 : constantCoeff V ≠ 0 := by
    rw [hV, map_prod, Finset.prod_ne_zero_iff]
    intro j hj
    rw [map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero]
    exact pow_ne_zero _ (hne j hj)
  have hR : substPS (-(k₀ : ℚ)) (Rnum u) = Gser u k₀ * V := by
    unfold Rnum Gser
    rw [map_mul, map_add, map_mul, substPS_C, substPS_X, substPS_C, map_prod]
    have hnum : ∏ m : Fin 6, substPS (-(k₀ : ℚ)) (∏ c ∈ block u m,
        (Polynomial.X + Polynomial.C (1 / 2 + (c : ℚ)))) = numSer u (-(k₀ : ℚ)) := by
      unfold numSer
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [substPS_X_add_C, add_assoc]
    rw [hnum, ← hV, mul_assoc _ V⁻¹ V, PowerSeries.inv_mul_cancel V hV0, mul_one]
    congr 1
    rw [show (C (((40 * u : ℕ) : ℚ) - 2 * (k₀ : ℚ)) : PowerSeries ℚ) =
        C ((40 * u : ℕ) : ℚ) - C 2 * C (k₀ : ℚ) by rw [map_sub, map_mul], map_neg]
    ring
  have hPFs : substPS (-(k₀ : ℚ)) (PFpoly u) = T * V + E' := by
    unfold PFpoly
    simp only [map_sum, map_mul, map_pow, map_prod, substPS_C, hfac]
    rw [← Finset.add_sum_erase _ _ hmem, hT, hE', hV, Finset.sum_mul, hX]
  have hGV : Gser u k₀ * V = T * V + E' := by
    rw [← hR, hPF.poly u, hPFs]
  have hG : Gser u k₀ = T + E' * V⁻¹ := by
    have := congrArg (· * V⁻¹) hGV
    rw [mul_assoc, PowerSeries.mul_inv_cancel V hV0, mul_one, add_mul, mul_assoc,
      PowerSeries.mul_inv_cancel V hV0, mul_one] at this
    exact this
  rw [hG]
  congr 1
  rw [hE', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk' => ?_
  have hkk : k ≠ k₀ := Finset.ne_of_mem_erase hk'
  have hk0 : k₀ ∈ (range (40 * u + 1)).erase k :=
    Finset.mem_erase.2 ⟨hkk.symm, hmem⟩
  set W : PowerSeries ℚ := ∏ j ∈ ((range (40 * u + 1)).erase k₀).erase k,
    (C ((j : ℚ) - k₀) + X) ^ apole u j with hW
  have hVk : V = (C ((k : ℚ) - k₀) + X) ^ apole u k * W := by
    rw [hV, hW]
    exact (Finset.mul_prod_erase _ (fun j : ℕ => (C ((j : ℚ) - k₀) + X) ^ apole u j) hk').symm
  have hPk : ∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k₀) + X) ^ apole u j =
      X ^ apole u k₀ * W := by
    rw [← Finset.mul_prod_erase _ (fun j : ℕ => (C ((j : ℚ) - k₀) + X) ^ apole u j) hk0, hX, hW,
      Finset.erase_right_comm]
  have hzk : ((k : ℚ) - k₀) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hkk)
  rw [Finset.sum_mul, Finset.mul_sum]
  -- extend `Icc 1 a_k` to `Icc 1 4`
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (apole_le u k))
    (f := fun i => X ^ apole u k₀ * (C (rcoef u i k) * ((C ((k : ℚ) - k₀) + X) ^ i)⁻¹))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    rw [hPk]
    have hc : constantCoeff ((C ((k : ℚ) - k₀) + X : PowerSeries ℚ) ^ i) ≠ 0 := by
      rw [map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero]
      exact pow_ne_zero _ hzk
    have hinv : (C ((k : ℚ) - k₀) + X) ^ (apole u k - i) * W * V⁻¹ =
        ((C ((k : ℚ) - k₀) + X : PowerSeries ℚ) ^ i)⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one hc]
      calc (C ((k : ℚ) - k₀) + X) ^ (apole u k - i) * W * V⁻¹ * (C ((k : ℚ) - k₀) + X) ^ i
          = ((C ((k : ℚ) - k₀) + X) ^ (apole u k - i) * (C ((k : ℚ) - k₀) + X) ^ i * W) *
              V⁻¹ := by ring
        _ = V * V⁻¹ := by rw [← pow_add, Nat.sub_add_cancel hi.2, hVk]
        _ = 1 := PowerSeries.mul_inv_cancel V hV0
    calc C (rcoef u i k) * (C ((k : ℚ) - k₀) + X) ^ (apole u k - i) * (X ^ apole u k₀ * W) * V⁻¹
        = X ^ apole u k₀ * (C (rcoef u i k) *
            ((C ((k : ℚ) - k₀) + X) ^ (apole u k - i) * W * V⁻¹)) := by ring
      _ = _ := by rw [hinv]
  · intro i hi hni
    simp only [Finset.mem_Icc] at hi hni
    have : rcoef u i k = 0 := by
      unfold rcoef
      rw [ite_eq_right (by omega)]
    rw [this, map_zero, zero_mul, mul_zero]

theorem KP_le (hPF : Stmt_PF7) (u k₀ j : ℕ) (hk : k₀ ≤ 40 * u) (hj : 1 ≤ j) :
    KP u k₀ j = coeff (apole u k₀ - 1 + j) (Gser u k₀) := by
  have ha := apole_pos u k₀
  rw [Gser_pf_pole hPF u k₀ hk, map_add, map_sum, PowerSeries.coeff_X_pow_mul',
    ite_eq_left (by omega), show apole u k₀ - 1 + j - apole u k₀ = j - 1 by omega]
  rw [Finset.sum_eq_zero (fun i hi => by
    simp only [Finset.mem_Icc] at hi
    rw [coeff_C_mul_X_pow, ite_eq_right (by omega)]), zero_add, map_sum]
  unfold KP
  refine Finset.sum_congr rfl fun k hk' => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Icc] at hi
  have hkk : k ≠ k₀ := Finset.ne_of_mem_erase hk'
  rw [coeff_C_mul, coeff_inv_pow _ (sub_ne_zero.2 (by exact_mod_cast hkk)) i j hi.1 hj, mul_assoc]

theorem KP_gt (hPF : Stmt_PF7) (u k₀ j : ℕ) (hk : 40 * u < k₀) (hj : 1 ≤ j) :
    KP u k₀ j = coeff (j - 1) (Rser u (-(k₀ : ℚ))) := by
  have hy : ∀ j' ≤ 40 * u, -(k₀ : ℚ) + (j' : ℚ) ≠ 0 := by
    intro j' hj'
    have : (j' : ℚ) ≠ k₀ := by exact_mod_cast (by omega : j' ≠ k₀)
    intro h; apply this; linarith
  rw [hPF.series u _ hy, map_sum]
  unfold KP
  rw [Finset.erase_eq_of_notMem (by simp; omega)]
  refine Finset.sum_congr rfl fun k hk' => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Icc] at hi
  have hkk : (k : ℚ) - k₀ ≠ 0 := by
    have : k ≠ k₀ := by rw [Finset.mem_range] at hk'; omega
    exact sub_ne_zero.2 (by exact_mod_cast this)
  rw [coeff_C_mul, show -(k₀ : ℚ) + k = (k : ℚ) - k₀ by ring,
    coeff_inv_pow _ hkk i j hi.1 hj, mul_assoc]

/-- The residue at the kernel pole, in local form. -/
theorem KP_eq (hPF : Stmt_PF7) {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (j : ℕ) (hj : 1 ≤ j) :
    KP u k₀ j = (q : ℚ) ^ ((localModel u q k₀).E + 1 - j) *
      coeff (ord (kerType (localModel u q k₀) j) 0 - 1)
        (Ufam u q k₀ 0 * taylorAt (kerType (localModel u q k₀) j) 0) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [kerType_ord0 _ _ (netE_zero_nonpos u q k₀ hq.pos hk₀), kerType_taylorAt, ite_eq_left rfl,
    mul_one]
  rcases le_or_gt k₀ (40 * u) with hk | hk
  · -- `-k₀` is itself a pole of the class (`J = 0`)
    have hJ : k₀ + 0 * q ≤ 40 * u := by omega
    have h1 := coeff_Gser_mul hq hq2 hk₀ hJ j 0 1
    rw [zpow_zero, map_one, map_one, one_mul, mul_one, mul_one] at h1
    simp only [zero_mul, add_zero, Nat.cast_zero, neg_zero, mul_zero] at h1
    rw [KP_le hPF u k₀ j hk hj, h1]
    have ha := ord_pole_pos u q k₀ hq.pos hk₀ hJ
    simp only [Nat.cast_zero, mul_zero, neg_zero] at ha
    rw [show ord (localModel u q k₀) 0 - 1 + j = ord (localModel u q k₀) 0 + j - 1 by omega]
  · -- no pole at `-k₀`: Taylor expansion of `R_n` there
    rw [KP_gt hPF u k₀ j hk hj, Rser_factor u q k₀ hq hq2 hk₀ hk, coeff_C_mul,
      coeff_mul_rescale_inv hq0, ← Ufam_zero]
    have h0 : ord (localModel u q k₀) 0 = 0 := by
      unfold ord
      rw [netE_zero_of_gt u q k₀ hq.pos hk₀ hk]
      rfl
    rw [h0, zero_add, ← mul_assoc]
    congr 1
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0]
    congr 1
    omega

/-! ### The class sums as residue functionals -/

theorem sum_poleSet {u q k₀ : ℕ} (hq : 0 < q) (hk₀ : k₀ < q) (f : ℤ → ℚ) :
    ∑ w ∈ poleSet (localModel u q k₀), f w = ∑ J ∈ clsJ u q k₀, f (-(2 * (J : ℤ))) := by
  rw [poleSet_eq u q k₀ hq hk₀, Finset.sum_image]
  intro x _ y _ h
  simp only at h
  omega

theorem classBad_eq {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) :
    classBad u q k₀ = 24 * (q : ℚ) ^ ((localModel u q k₀).E - 4) *
      PairF (localModel u q k₀) (Ufam u q k₀) := by
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  unfold classBad PairF
  rw [sum_cls u q k₀ hq.pos hk₀, pairs_sum u q k₀ hq.pos, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hJ' : k₀ + J * q ≤ 40 * u := (Finset.mem_filter.1 hJ).2
  rw [sum_oddBetween_dvd q hqodd, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hd : (((k₀ + J * q : ℕ) : ℤ) - 20 * u) = (k₀ : ℤ) + J * q - 20 * u := by push_cast; ring
  rw [hd]
  split_ifs with hlt
  · have hd0 : ((k₀ : ℤ) + J * q - 20 * u) ≠ 0 := by
      intro h0; rw [h0] at hlt; simp at hlt; nlinarith
    have hsg : ((k₀ : ℤ) + J * q - 20 * u).sign ≠ 0 := by
      rcases lt_or_gt_of_ne hd0 with hneg | hpos
      · rw [Int.sign_eq_neg_one_of_neg hneg]; norm_num
      · rw [Int.sign_eq_one_of_pos hpos]; norm_num
    have hs : ((k₀ : ℤ) + J * q - 20 * u).sign * (2 * t + 1) ≠ 0 :=
      mul_ne_zero hsg (by omega)
    rw [Xk_eq hq hq2 hk₀ hJ' _ hs]
    simp only
    ring
  · simp

theorem r1_eq {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) :
    ∑ k ∈ (range (40 * u + 1)).filter (fun k => k % q = k₀), rcoef u 1 k =
      (q : ℚ) ^ ((localModel u q k₀).E + 1) * ResF (localModel u q k₀) (Ufam u q k₀) := by
  unfold ResF
  rw [sum_cls u q k₀ hq.pos hk₀, sum_poleSet hq.pos hk₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J hJ => ?_
  exact rcoef_one_eq hq hq2 hk₀ (Finset.mem_filter.1 hJ).2

theorem cpart_eq (hPF : Stmt_PF7) {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (j : ℕ) (hj : 1 ≤ j) :
    (∑ k ∈ (range (40 * u + 1)).filter (fun k => k % q = k₀ ∧ k ≠ k₀), ∑ i ∈ Icc (1 : ℕ) 4,
        rcoef u i k * negChoose j (i - 1) * (((k₀ : ℚ) - k)⁻¹) ^ (i + j - 1)) + KP u k₀ j =
      (q : ℚ) ^ ((localModel u q k₀).E + 1 - j) *
        ResF (kerType (localModel u q k₀) j) (Ufam u q k₀) := by
  unfold ResF
  rw [kerType_poleSet _ _ hj (netE_zero_nonpos u q k₀ hq.pos hk₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 _), Finset.erase_insert_eq_erase,
    mul_add, add_comm (_ * _) (_ * _)]
  congr 1
  · -- the class poles other than `-k₀`
    have hfilt : (range (40 * u + 1)).filter (fun k => k % q = k₀ ∧ k ≠ k₀) =
        ((range (40 * u + 1)).filter (fun k => k % q = k₀)).filter (fun k => k ≠ k₀) := by
      rw [Finset.filter_filter]
    have hinj : Function.Injective fun J : ℕ => -(2 * (J : ℤ)) := by
      intro x y h; simp only at h; omega
    have himg : ((clsJ u q k₀).image fun J : ℕ => -(2 * (J : ℤ))).erase 0 =
        ((clsJ u q k₀).erase 0).image fun J : ℕ => -(2 * (J : ℤ)) := by
      rw [Finset.image_erase hinj]
      simp
    have hcls : (clsJ u q k₀).filter (fun J => k₀ + J * q ≠ k₀) = (clsJ u q k₀).erase 0 := by
      rw [← Finset.filter_ne']
      congr 1
      ext J
      constructor
      · intro h h0; subst h0; simp at h
      · intro h h1
        apply h
        have : J * q = 0 := by omega
        rcases Nat.mul_eq_zero.1 this with h2 | h2
        · exact h2
        · exact absurd h2 hq.ne_zero
    rw [hfilt, Finset.sum_filter, sum_cls u q k₀ hq.pos hk₀, poleSet_eq u q k₀ hq.pos hk₀, himg,
      Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum, ← Finset.sum_filter, hcls]
    refine Finset.sum_congr rfl fun J hJ => ?_
    have hJ0 : J ≠ 0 := Finset.ne_of_mem_erase hJ
    have hJ' : k₀ + J * q ≤ 40 * u := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hJ)).2
    exact kerPole_eq hq hq2 hk₀ hJ' hJ0 j hj
  · exact KP_eq hPF hq hq2 hk₀ j hj

theorem kerRes_eq (hPF : Stmt_PF7) {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (c0 : ℚ) (j : ℕ) (hj : 1 ≤ j) (c : ℚ) :
    kerRes u q k₀ c0 j c = (q : ℚ) ^ ((localModel u q k₀).E + 1) *
      (c0 * ResF (localModel u q k₀) (Ufam u q k₀) +
        c * ResF (kerType (localModel u q k₀) j) (Ufam u q k₀)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h := cpart_eq (u := u) hPF hq hq2 hk₀ j hj
  unfold KP at h
  unfold kerRes
  rw [r1_eq hq hq2 hk₀, h]
  have hpow : (q : ℚ) ^ j * (q : ℚ) ^ ((localModel u q k₀).E + 1 - j) =
      (q : ℚ) ^ ((localModel u q k₀).E + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ hq0]
    congr 1
    ring
  linear_combination (c * ResF (kerType (localModel u q k₀) j) (Ufam u q k₀)) * hpow

theorem LHS_eq (hPF : Stmt_PF7) {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (c0 : ℚ) (j : ℕ) (hj : 1 ≤ j) (c : ℚ) :
    classBad u q k₀ - 24 * ((q : ℚ) ^ 5)⁻¹ * kerRes u q k₀ c0 j c =
      24 * (q : ℚ) ^ ((localModel u q k₀).E - 4) *
        Psi (localModel u q k₀) c0 j c (Ufam u q k₀) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [classBad_eq hq hq2 hk₀, kerRes_eq hPF hq hq2 hk₀ c0 j hj c]
  unfold Psi
  have hpow : ((q : ℚ) ^ 5)⁻¹ * (q : ℚ) ^ ((localModel u q k₀).E + 1) =
      (q : ℚ) ^ ((localModel u q k₀).E - 4) := by
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0]
    congr 1
    push_cast
    ring
  linear_combination (-24 * (c0 * ResF (localModel u q k₀) (Ufam u q k₀) +
    c * ResF (kerType (localModel u q k₀) j) (Ufam u q k₀))) * hpow

end CL7

open CL7 LE7 in
theorem ClassLemma7_proof (hPF : Stmt_PF7) : Stmt_ClassLemma7 := by
  intro u q k₀ c0 c j P hq hq5 hsq hk₀ hj hc0 hc hLev
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  obtain ⟨F, hF⟩ := trunc_exists u q k₀ hq hq2 hk₀ ((P - (localModel u q k₀).E - 1).toNat)
  set M : ℕ := (P - (localModel u q k₀).E - 1).toNat with hM
  set T : ℤ → PowerSeries ℚ := fun w =>
    ∑ m ∈ range M, C (F m * (q : ℚ) ^ m) * (C ((w : ℚ) / 2) + X) ^ m with hT
  have hpairs : ∀ pr ∈ (localModel u q k₀).pairs, 1 ≤ ord (localModel u q k₀) pr.1 := by
    intro pr hpr
    obtain ⟨J, hJ, t, -, rfl⟩ := pairs_mem u q k₀ hq.pos hpr
    exact ord_pole_pos u q k₀ hq.pos hk₀ (Finset.mem_filter.1 hJ).2
  have hT0 : Psi (localModel u q k₀) c0 j c T = 0 := by
    rw [hT, Psi_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [Psi_poly _ hpairs, hLev ((localModel u q k₀).E + m + 1) (by omega) (by omega), mul_zero]
  have hdiffJ : ∀ J : ℕ, PSV q M (Ufam u q k₀ (-(2 * (J : ℤ))) - T (-(2 * (J : ℤ)))) := by
    intro J
    have hJ2 : (((-(2 * (J : ℤ)) : ℤ) : ℚ) / 2) = -(J : ℚ) := by push_cast; ring
    rw [Ufam_pole, hT]
    simp only [hJ2]
    exact hF J
  have hval : ValGe q M (Psi (localModel u q k₀) c0 j c (fun w => Ufam u q k₀ w - T w)) := by
    apply Psi_val _ c0 j c _ M hc0 hc
    · intro pr hpr
      refine ⟨?_, PSV_gSer_model hq hq2 hk₀ hsq hpr⟩
      obtain ⟨J, hJ, t, -, hpr'⟩ := pairs_mem u q k₀ hq.pos hpr
      rw [hpr']
      exact hdiffJ J
    · intro w hw
      rw [poleSet_eq u q k₀ hq.pos hk₀, Finset.mem_image] at hw
      obtain ⟨J, hJ, rfl⟩ := hw
      exact ⟨hdiffJ J, PSV_taylorAt_model hq hq2 hk₀ hsq (Or.inl (Finset.mem_filter.1 hJ).2)⟩
    · intro w hw
      rw [kerType_poleSet _ _ hj (netE_zero_nonpos u q k₀ hq.pos hk₀), Finset.mem_insert,
        poleSet_eq u q k₀ hq.pos hk₀, Finset.mem_image] at hw
      rcases hw with rfl | ⟨J, hJ, rfl⟩
      · have h1 := hdiffJ 0
        have h2 := PSV_taylorAt_ker hq hq2 hk₀ hsq j (J := 0) (Or.inr rfl)
        simp only [Nat.cast_zero, mul_zero, neg_zero] at h1 h2
        exact ⟨h1, h2⟩
      · exact ⟨hdiffJ J, PSV_taylorAt_ker hq hq2 hk₀ hsq j (Or.inl (Finset.mem_filter.1 hJ).2)⟩
  have hsplit : Psi (localModel u q k₀) c0 j c (Ufam u q k₀) =
      Psi (localModel u q k₀) c0 j c T +
        Psi (localModel u q k₀) c0 j c (fun w => Ufam u q k₀ w - T w) := by
    rw [← Psi_add]
    congr 1
    funext w
    ring
  rw [LHS_eq hPF hq hq2 hk₀ c0 j hj c, hsplit, hT0, zero_add]
  have h24 : ValGe q 0 (24 : ℚ) := by simpa using valGe_int (q := q) 24
  have := valGe_mul (valGe_mul h24 (valGe_qzpow ((localModel u q k₀).E - 4)) rfl) hval rfl
  exact valGe_mono this (by omega)

end Zeta2.Z7

end
