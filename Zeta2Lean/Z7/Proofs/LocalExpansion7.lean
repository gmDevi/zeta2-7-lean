module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Local expansions on a residue disc (shared helper of `ClassLemma7`, `PerPole7`, `FarPart7`)

**Status: fully proved** (`#print axioms` of every lemma: `[propext, Classical.choice,
Quot.sound]`).  Namespace `Zeta2.Z7.LE7`.  Everything is exact algebra with `PowerSeries ℚ` and
`padicNorm`; no `q`-adic analysis is used.  Route and reuse notes: `notes/ClassLemma7.md`.

## Contents

1. `ValGe` calculus (`valGe_add`, `valGe_mul`, `valGe_sum`, `valGe_qzpow`, units `unit_int`,
   `unit_half`, `unit_zpow`, `not_dvd_of_small`).
2. `PSV q M f`: every coefficient of `f` has `v_q ≥ M` (`PSV.mul'`, `PSV.prod`, `PSV.inv` for a
   unit constant term, `PSV.resc`, `PSV.resc_q`, `PSV_substPS`).
3. Binomial series `bser c e = (1 + cX)^e`, `lin β e = (β + X)^e` for `e : ℤ` (`bser_add`,
   `lin_add`, `lin_nat`, `lin_neg_nat`, `rescale_lin`, `valGe_gchoose`, `PSV_lin`).
4. The Taylor substitution `substPS a : ℚ[t] →+* ℚ⟦ε⟧`, `t ↦ a + ε`.
5. Generic partial fractions (`pf_dvd`) and the residue theorem at infinity (`grt`).
6. **Residue theorem for local types** (`grt_local`): for any `τ : LocalType`,
   `∑_{w ∈ poleSet τ} [ε^{ord w - 1}] ((w/2 + ε)^m taylorAt τ w) = [y^{E+m+1}] rSer τ`;
   `taylorAt_eq_prod`, `rSer_eq_prod`, `E_eq_sum` (grouping items by position).
7. `kerType τ j`: the kernel pole `(0, -j)` added (`kerType_taylorAt`, `kerType_poleSet`, ...).
8. **Dictionary for `localModel u q k₀`**: `items_eq` (pole list `PLf`, zero list `ZLl` over the
   integer index `t`, δ list `DLl`), class poles `clsJ` (`k = k₀ + J q ≤ n` at position `-2J`),
   `sum_cls`/`prod_cls`, `netE_pole` (`-a_k + ctr`), `ord_pole` (`ord + ctr = a_k`),
   `ord_pole_pos`, `poleSet_eq`, `pairs_sum`, `pairs_mem`, `sum_oddBetween_dvd`; the outer factor
   `Onum`, `Oden`, `Uhat y` (Taylor series of `Û` at `t = y`).
9. **Lemma 4.2** (`q > 2x + 2`): `items_sep`, `PSV_taylorAt_model`, `PSV_taylorAt_ker`,
   `PSV_gSer_model`.
10. **Truncation** at the centre of the disc: `trunc_general` (any `A/B` with `q`-integral Taylor
    series at `-k₀` and unit denominator on the disc), `trunc_exists` (`A/B = Û`); `PSV_Uhat`,
    `PSV_Oden_inv`, `constantCoeff_substPS_Oden`.
11. **Per-pole factorisation** (Lemma 4.1 at `-k`): `Gser_factor`
    `G_k(ε) = q^{E + ord} ε^{ctr} Û(-k + ε) τ_k(ε/q)` for every class pole `k = k₀ + J q ≤ n`,
    and `Rser_factor` (`R_n(-k₀ + ε) = q^E Û(-k₀+ε) RR(ε/q)` when `k₀ > n`).  With `PSV_Uhat` and
    `PSV_taylorAt_model` this gives `PerPole7` directly (`r_{i,k} = [ε^{a_k - i}] G_k`).
12. **Residue tools**: `ResF` (residues of `Φ · RR` over the poles; `ResF_add`, `ResF_sum`),
    `Ufam` (the family `rescale q (Û(-k₀ + q w/2))`), `coeff_Gser_mul`, `coeff_Gser_mul_eq_sum`,
    `coeff_mul_rescale_inv`, `gchoose_neg` (`= negChoose`), `coeff_lin_neg`, `coeff_inv_pow`.
-/

set_option linter.style.longLine false

open Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace LE7

/-! ## 1. `ValGe` calculus -/

section ValGeCalc

variable {q : ℕ} [hqF : Fact q.Prime]

theorem q_pos : (0 : ℚ) < q := by exact_mod_cast hqF.out.pos

theorem q_gt_one : (1 : ℚ) < q := by exact_mod_cast hqF.out.one_lt

theorem q_ne_zero : (q : ℚ) ≠ 0 := q_pos.ne'

omit hqF in
theorem zpow_q_nonneg (L : ℤ) : (0 : ℚ) ≤ (q : ℚ) ^ L := zpow_nonneg (Nat.cast_nonneg _) _

omit hqF in
theorem valGe_zero (L : ℤ) : ValGe q L 0 := by
  unfold ValGe
  rw [padicNorm.zero]
  exact zpow_q_nonneg _

omit hqF in
theorem valGe_neg_iff {L : ℤ} {x : ℚ} : ValGe q L (-x) ↔ ValGe q L x := by
  unfold ValGe
  rw [padicNorm.neg]

omit hqF in
theorem valGe_neg {L : ℤ} {x : ℚ} (h : ValGe q L x) : ValGe q L (-x) := valGe_neg_iff.2 h

theorem valGe_add {L : ℤ} {x y : ℚ} (hx : ValGe q L x) (hy : ValGe q L y) :
    ValGe q L (x + y) :=
  le_trans padicNorm.nonarchimedean (max_le hx hy)

theorem valGe_sub {L : ℤ} {x y : ℚ} (hx : ValGe q L x) (hy : ValGe q L y) :
    ValGe q L (x - y) := by
  rw [sub_eq_add_neg]
  exact valGe_add hx (valGe_neg hy)

theorem valGe_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {L : ℤ}
    (h : ∀ i ∈ s, ValGe q L (f i)) : ValGe q L (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valGe_zero L
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact valGe_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem valGe_list_sum {L : ℤ} : ∀ l : List ℚ, (∀ x ∈ l, ValGe q L x) → ValGe q L l.sum
  | [], _ => by simpa using valGe_zero L
  | x :: l, h => by
    rw [List.sum_cons]
    exact valGe_add (h x (List.mem_cons_self ..))
      (valGe_list_sum l fun y hy => h y (List.mem_cons_of_mem _ hy))

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

theorem valGe_nat (m : ℕ) : ValGe q 0 (m : ℚ) := by
  simpa using valGe_int (q := q) (m : ℤ)

theorem valGe_one : ValGe q 0 (1 : ℚ) := by
  simpa using valGe_int (q := q) 1

theorem valGe_pow {x : ℚ} (h : ValGe q 0 x) (n : ℕ) : ValGe q 0 (x ^ n) := by
  induction n with
  | zero => simpa using valGe_one (q := q)
  | succ n ih => rw [pow_succ]; exact valGe_mul ih h (by simp)

theorem valGe_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, ValGe q 0 (f i)) :
    ValGe q 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valGe_one (q := q)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact valGe_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (by simp)

theorem pn_pow (x : ℚ) (n : ℕ) : padicNorm q (x ^ n) = padicNorm q x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

theorem pn_inv (x : ℚ) : padicNorm q x⁻¹ = (padicNorm q x)⁻¹ := by
  have := padicNorm.div (p := q) 1 x
  rw [one_div, padicNorm.one, one_div] at this
  exact this

theorem pn_zpow (x : ℚ) (e : ℤ) : padicNorm q (x ^ e) = padicNorm q x ^ e := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · rw [zpow_natCast, zpow_natCast, pn_pow]
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pn_inv, pn_pow]

/-- The `q`-adic norm of `q^e`. -/
theorem pn_qzpow (e : ℤ) : padicNorm q ((q : ℚ) ^ e) = (q : ℚ) ^ (-e) := by
  rw [pn_zpow, padicNorm.padicNorm_p_of_prime, inv_zpow', zpow_neg]

theorem valGe_qzpow (e : ℤ) : ValGe q e ((q : ℚ) ^ e) := by
  unfold ValGe
  rw [pn_qzpow]

theorem valGe_qzpow_mul {L e : ℤ} {x : ℚ} (h : ValGe q L x) : ValGe q (e + L) ((q : ℚ) ^ e * x) :=
  valGe_mul (valGe_qzpow e) h rfl

/-- `ValGe` of `q^e x` from `ValGe` of `x`, with the target stated freely. -/
theorem valGe_qzpow_mul' {L e N : ℤ} {x : ℚ} (h : ValGe q L x) (hN : e + L = N) :
    ValGe q N ((q : ℚ) ^ e * x) :=
  valGe_mul (valGe_qzpow e) h hN

omit hqF in
/-- A `q`-unit is `q`-integral. -/
theorem valGe_of_unit {x : ℚ} (h : padicNorm q x = 1) : ValGe q 0 x := by
  unfold ValGe
  rw [h]
  simp

theorem unit_zpow {x : ℚ} (h : padicNorm q x = 1) (e : ℤ) : padicNorm q (x ^ e) = 1 := by
  rw [pn_zpow, h, one_zpow]

theorem unit_inv {x : ℚ} (h : padicNorm q x = 1) : padicNorm q x⁻¹ = 1 := by
  rw [pn_inv, h, inv_one]

theorem unit_mul {x y : ℚ} (hx : padicNorm q x = 1) (hy : padicNorm q y = 1) :
    padicNorm q (x * y) = 1 := by
  rw [padicNorm.mul, hx, hy, one_mul]

omit hqF in
theorem unit_ne_zero {x : ℚ} (h : padicNorm q x = 1) : x ≠ 0 := by
  rintro rfl
  rw [padicNorm.zero] at h
  exact zero_ne_one h

/-- An integer not divisible by `q` is a `q`-unit. -/
theorem unit_int {z : ℤ} (hz : ¬ (q : ℤ) ∣ z) : padicNorm q (z : ℚ) = 1 :=
  (padicNorm.int_eq_one_iff z).2 hz

/-- For an odd prime, `2` is a `q`-unit. -/
theorem unit_two (hq2 : q ≠ 2) : padicNorm q (2 : ℚ) = 1 := by
  have h := unit_int (q := q) (z := 2) (by
    intro hd
    have : q ∣ 2 := by exact_mod_cast hd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqF.out Nat.prime_two).1 this))
  exact_mod_cast h

/-- `z/2` is a `q`-unit for an odd prime `q ∤ z`. -/
theorem unit_half {z : ℤ} (hq2 : q ≠ 2) (hz : ¬ (q : ℤ) ∣ z) : padicNorm q ((z : ℚ) / 2) = 1 := by
  rw [padicNorm.div, unit_int hz, unit_two hq2, div_one]

/-- `z/2` is `q`-integral for an odd prime `q`. -/
theorem valGe_half (hq2 : q ≠ 2) (z : ℤ) : ValGe q 0 ((z : ℚ) / 2) := by
  unfold ValGe
  rw [padicNorm.div, unit_two hq2, div_one]
  simpa using padicNorm.of_int (p := q) z

omit hqF in
/-- A non-zero integer `z` with `q |z| < q²` is not divisible by `q`. -/
theorem not_dvd_of_small {z : ℤ} (hz : z ≠ 0) (hlt : (q : ℤ) * |z| < (q : ℤ) ^ 2) :
    ¬ (q : ℤ) ∣ z := by
  rintro ⟨w, rfl⟩
  have hw : w ≠ 0 := by rintro rfl; simp at hz
  have hq0 : (0 : ℤ) ≤ q := by positivity
  rw [abs_mul, abs_of_nonneg hq0] at hlt
  have h1 : (1 : ℤ) ≤ |w| := Int.one_le_abs hw
  nlinarith

end ValGeCalc

/-! ## 2. Power series with `q`-adically bounded coefficients -/

/-- `PSV q M f`: every coefficient of `f` has `v_q ≥ M`. -/
def PSV (q : ℕ) (M : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ m : ℕ, ValGe q M (coeff m f)

section PSVCalc

variable {q : ℕ} [hqF : Fact q.Prime]

omit hqF in
theorem PSV.zero (M : ℤ) : PSV q M 0 := fun m => by simpa using valGe_zero M

theorem PSV.add {M : ℤ} {f g : PowerSeries ℚ} (hf : PSV q M f) (hg : PSV q M g) :
    PSV q M (f + g) := fun m => by rw [map_add]; exact valGe_add (hf m) (hg m)

omit hqF in
theorem PSV.neg {M : ℤ} {f : PowerSeries ℚ} (hf : PSV q M f) : PSV q M (-f) := fun m => by
  rw [map_neg]; exact valGe_neg (hf m)

theorem PSV.sub {M : ℤ} {f g : PowerSeries ℚ} (hf : PSV q M f) (hg : PSV q M g) :
    PSV q M (f - g) := fun m => by rw [map_sub]; exact valGe_sub (hf m) (hg m)

theorem PSV.sum {ι : Type*} (s : Finset ι) {M : ℤ} (f : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, PSV q M (f i)) : PSV q M (∑ i ∈ s, f i) := fun m => by
  rw [map_sum]
  exact valGe_sum _ _ fun i hi => h i hi m

theorem PSV.mul {M M' : ℤ} {f g : PowerSeries ℚ} (hf : PSV q M f) (hg : PSV q M' g) :
    PSV q (M + M') (f * g) := fun m => by
  rw [coeff_mul]
  exact valGe_sum _ _ fun p _ => valGe_mul (hf _) (hg _) rfl

theorem PSV.mul' {M M' N : ℤ} {f g : PowerSeries ℚ} (hf : PSV q M f) (hg : PSV q M' g)
    (hN : M + M' = N) : PSV q N (f * g) := hN ▸ hf.mul hg

theorem PSV.one : PSV q 0 (1 : PowerSeries ℚ) := fun m => by
  rw [coeff_one]
  split_ifs
  · exact valGe_one
  · exact valGe_zero 0

omit hqF in
theorem PSV.ofC {M : ℤ} {a : ℚ} (h : ValGe q M a) : PSV q M (PowerSeries.C a) := fun m => by
  rw [coeff_C]
  split_ifs
  · exact h
  · exact valGe_zero M

theorem PSV.ofX : PSV q 0 (PowerSeries.X : PowerSeries ℚ) := fun m => by
  rw [coeff_X]
  split_ifs
  · exact valGe_one
  · exact valGe_zero 0

theorem PSV.mono {M M' : ℤ} {f : PowerSeries ℚ} (h : PSV q M f) (hM : M' ≤ M) : PSV q M' f :=
  fun m => valGe_mono (h m) hM

theorem PSV.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, PSV q 0 (f i)) : PSV q 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PSV.one (q := q)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul' (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      (by simp)

theorem PSV.list_prod : ∀ l : List (PowerSeries ℚ), (∀ f ∈ l, PSV q 0 f) → PSV q 0 l.prod
  | [], _ => by simpa using PSV.one (q := q)
  | f :: l, h => by
    rw [List.prod_cons]
    exact (h f (List.mem_cons_self ..)).mul' (PSV.list_prod l fun g hg => h g (List.mem_cons_of_mem _ hg))
      (by simp)

theorem PSV.pow {f : PowerSeries ℚ} (h : PSV q 0 f) (n : ℕ) : PSV q 0 (f ^ n) := by
  induction n with
  | zero => simpa using PSV.one (q := q)
  | succ n ih => rw [pow_succ]; exact ih.mul' h (by simp)

theorem PSV.C_mul {M L : ℤ} {a : ℚ} {f : PowerSeries ℚ} (ha : ValGe q L a) (hf : PSV q M f) :
    PSV q (L + M) (PowerSeries.C a * f) := fun m => by
  rw [coeff_C_mul]
  exact valGe_mul ha (hf m) rfl

theorem PSV.resc {M : ℤ} {a : ℚ} {f : PowerSeries ℚ} (h : PSV q M f) (ha : ValGe q 0 a) :
    PSV q M (PowerSeries.rescale a f) := fun m => by
  rw [coeff_rescale]
  exact valGe_mul (valGe_pow ha m) (h m) (by simp)

/-- `rescale q` turns "`[ε^m] f` has `v_q ≥ M - m`" into `PSV q M`. -/
theorem PSV.resc_q {M : ℤ} {f : PowerSeries ℚ} (h : ∀ m : ℕ, ValGe q (M - m) (coeff m f)) :
    PSV q M (PowerSeries.rescale (q : ℚ) f) := fun m => by
  rw [coeff_rescale, ← zpow_natCast]
  exact valGe_qzpow_mul' (h m) (by ring)

/-- The inverse of a `q`-integral series with unit constant term is `q`-integral. -/
theorem PSV.inv {f : PowerSeries ℚ} (h : PSV q 0 f) (h0 : padicNorm q (constantCoeff f) = 1) :
    PSV q 0 f⁻¹ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [coeff_inv]
    split_ifs with hm
    · exact valGe_of_unit (unit_inv h0)
    · refine valGe_mul (L := 0) (M := 0) (valGe_neg (valGe_of_unit (unit_inv h0))) ?_ (by simp)
      refine valGe_sum _ _ fun p hp => ?_
      split_ifs with hp2
      · exact valGe_mul (h _) (ih _ hp2) (by simp)
      · exact valGe_zero 0

end PSVCalc

/-! ## 3. Binomial series -/

section Binomial

theorem gchoose_zero_right (e : ℤ) : gchoose e 0 = 1 := by
  simp [gchoose]

/-- Pascal's rule for the generalised binomial coefficients. -/
theorem gchoose_succ_succ (e : ℤ) (i : ℕ) :
    gchoose (e + 1) (i + 1) = gchoose e (i + 1) + gchoose e i := by
  unfold gchoose
  rw [Finset.prod_range_succ' (fun t => (((e + 1 : ℤ) : ℚ) - t)),
    Finset.prod_range_succ (fun t => ((e : ℚ) - t))]
  have h1 : ∀ t ∈ range i, (((e + 1 : ℤ) : ℚ) - ((t + 1 : ℕ) : ℚ)) = (e : ℚ) - t := by
    intro t _
    push_cast
    ring
  rw [Finset.prod_congr rfl h1, Nat.factorial_succ]
  have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  push_cast
  field_simp
  ring

theorem gchoose_zero_left (i : ℕ) : gchoose 0 (i + 1) = 0 := by
  unfold gchoose
  rw [Finset.prod_range_succ']
  simp

/-- The generalised binomial coefficients are integers. -/
theorem gchoose_isInt (i : ℕ) : ∀ e : ℤ, ∃ z : ℤ, gchoose e i = z := by
  induction i with
  | zero => intro e; exact ⟨1, by simp [gchoose_zero_right]⟩
  | succ i ih =>
    intro e
    induction e using Int.induction_on with
    | zero => exact ⟨0, by simp [gchoose_zero_left]⟩
    | succ e ihe =>
      obtain ⟨z₁, hz₁⟩ := ihe
      obtain ⟨z₂, hz₂⟩ := ih (e : ℤ)
      refine ⟨z₁ + z₂, ?_⟩
      rw [gchoose_succ_succ, hz₁, hz₂]
      push_cast
      ring
    | pred e ihe =>
      obtain ⟨z₁, hz₁⟩ := ihe
      obtain ⟨z₂, hz₂⟩ := ih (-(e : ℤ) - 1)
      refine ⟨z₁ - z₂, ?_⟩
      have := gchoose_succ_succ (-(e : ℤ) - 1) i
      rw [show -(e : ℤ) - 1 + 1 = -(e : ℤ) by ring] at this
      rw [hz₁, hz₂] at this
      rw [show gchoose (-(e : ℤ) - 1) (i + 1) = (z₁ : ℚ) - z₂ by linarith]
      push_cast
      ring

theorem valGe_gchoose {q : ℕ} [Fact q.Prime] (e : ℤ) (i : ℕ) : ValGe q 0 (gchoose e i) := by
  obtain ⟨z, hz⟩ := gchoose_isInt i e
  rw [hz]
  exact valGe_int z

theorem coeff_bser (c : ℚ) (e : ℤ) (i : ℕ) : coeff i (bser c e) = gchoose e i * c ^ i := by
  simp [bser]

theorem constantCoeff_bser (c : ℚ) (e : ℤ) : constantCoeff (bser c e) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bser, gchoose_zero_right]
  simp

theorem bser_zero (c : ℚ) : bser c 0 = 1 := by
  ext i
  rw [coeff_bser, coeff_one]
  rcases i with _ | i
  · simp [gchoose_zero_right]
  · simp [gchoose_zero_left]

theorem bser_succ (c : ℚ) (e : ℤ) : bser c (e + 1) = bser c e * (1 + C c * X) := by
  ext i
  rw [mul_add, mul_one, map_add, coeff_bser]
  rcases i with _ | i
  · simp [coeff_bser, gchoose_zero_right]
  · rw [show bser c e * (C c * X) = C c * (bser c e * X) by ring, coeff_C_mul, coeff_succ_mul_X,
      coeff_bser, coeff_bser, gchoose_succ_succ]
    ring

theorem bser_add_nat (c : ℚ) (e : ℤ) (m : ℕ) :
    bser c (e + m) = bser c e * (1 + C c * X) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc, bser_succ, ih, pow_succ, mul_assoc]

theorem bser_nat (c : ℚ) (m : ℕ) : bser c m = (1 + C c * X) ^ m := by
  have := bser_add_nat c 0 m
  rwa [zero_add, bser_zero, one_mul] at this

theorem constantCoeff_one_add (c : ℚ) (m : ℕ) :
    constantCoeff ((1 + C c * X : PowerSeries ℚ) ^ m) = 1 := by
  simp

theorem bser_neg_nat (c : ℚ) (m : ℕ) : bser c (-(m : ℤ)) = ((1 + C c * X) ^ m)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_one_add]; exact one_ne_zero),
    ← bser_add_nat, neg_add_cancel, bser_zero]

theorem bser_add (c : ℚ) (e₁ e₂ : ℤ) : bser c (e₁ + e₂) = bser c e₁ * bser c e₂ := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg e₂
  · rw [bser_add_nat, bser_nat]
  · rw [bser_neg_nat]
    have h := bser_add_nat c (e₁ + -(m : ℤ)) m
    rw [neg_add_cancel_right] at h
    rw [PowerSeries.eq_mul_inv_iff_mul_eq (by rw [constantCoeff_one_add]; exact one_ne_zero), h]

theorem rescale_bser (a c : ℚ) (e : ℤ) : rescale a (bser c e) = bser (a * c) e := by
  ext i
  rw [coeff_rescale, coeff_bser, coeff_bser, mul_pow]
  ring

theorem PSV_bser {q : ℕ} [Fact q.Prime] {c : ℚ} (hc : ValGe q 0 c) (e : ℤ) : PSV q 0 (bser c e) :=
  fun i => by rw [coeff_bser]; exact valGe_mul (valGe_gchoose e i) (valGe_pow hc i) (by simp)

/-- `(β + X)^e` for `e : ℤ` (`β ≠ 0`): `β^e (1 + X/β)^e`. -/
def lin (β : ℚ) (e : ℤ) : PowerSeries ℚ :=
  C (β ^ e) * bser β⁻¹ e

theorem lin_zero (β : ℚ) : lin β 0 = 1 := by
  simp [lin, bser_zero]

theorem lin_add {β : ℚ} (hβ : β ≠ 0) (e₁ e₂ : ℤ) : lin β (e₁ + e₂) = lin β e₁ * lin β e₂ := by
  unfold lin
  rw [zpow_add₀ hβ, map_mul, bser_add]
  ring

theorem lin_nat {β : ℚ} (hβ : β ≠ 0) (m : ℕ) : lin β m = (C β + X) ^ m := by
  unfold lin
  rw [bser_nat, zpow_natCast, map_pow, ← mul_pow]
  congr 1
  rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul]

theorem lin_one {β : ℚ} (hβ : β ≠ 0) : lin β 1 = C β + X := by
  have := lin_nat hβ 1
  simpa using this

theorem lin_neg_nat {β : ℚ} (hβ : β ≠ 0) (m : ℕ) : lin β (-(m : ℤ)) = ((C β + X) ^ m)⁻¹ := by
  have hc : constantCoeff ((C β + X : PowerSeries ℚ) ^ m) ≠ 0 := by
    simp [hβ]
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc, ← lin_nat hβ, ← lin_add hβ, neg_add_cancel, lin_zero]

theorem constantCoeff_lin (β : ℚ) (e : ℤ) : constantCoeff (lin β e) = β ^ e := by
  simp [lin, constantCoeff_bser]

theorem rescale_C' (a c : ℚ) : rescale a (C c : PowerSeries ℚ) = C c := by
  ext i
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

/-- `rescale a ((β + X)^e) = a^e ((β/a) + X)^e`. -/
theorem rescale_lin {a : ℚ} (ha : a ≠ 0) (β : ℚ) (e : ℤ) :
    rescale a (lin β e) = C (a ^ e) * lin (β / a) e := by
  unfold lin
  rw [map_mul, rescale_C', rescale_bser, ← mul_assoc, ← map_mul, div_zpow, mul_div_cancel₀ _
    (zpow_ne_zero e ha), inv_div, div_eq_mul_inv]

theorem PSV_lin {q : ℕ} [Fact q.Prime] {β : ℚ} (hβ : padicNorm q β = 1) (e : ℤ) :
    PSV q 0 (lin β e) := by
  unfold lin
  exact (PSV.ofC (valGe_of_unit (unit_zpow hβ e))).mul' (PSV_bser (valGe_of_unit (unit_inv hβ)) e)
    (by simp)

end Binomial

/-! ## 4. The Taylor substitution `t ↦ a + ε` -/

section Subst

/-- The substitution `t ↦ a + ε`, as a ring hom `ℚ[t] →+* ℚ⟦ε⟧`. -/
def substPS (a : ℚ) : Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) (C a + X)

theorem substPS_X (a : ℚ) : substPS a Polynomial.X = C a + X := by
  simp [substPS]

theorem substPS_C (a c : ℚ) : substPS a (Polynomial.C c) = C c := by
  simp [substPS]

theorem substPS_X_add_C (a c : ℚ) :
    substPS a (Polynomial.X + Polynomial.C c) = C (a + c) + X := by
  rw [map_add, substPS_X, substPS_C, map_add]
  ring

theorem substPS_X_sub_C (a c : ℚ) :
    substPS a (Polynomial.X - Polynomial.C c) = C (a - c) + X := by
  rw [map_sub, substPS_X, substPS_C, map_sub]
  ring

/-- `substPS (-k₀) P` is the power series of the polynomial `P(t - k₀)`. -/
theorem coe_comp_eq_substPS (k₀ : ℚ) (P : Polynomial ℚ) :
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

/-- `substPS a P` for a polynomial with `q`-integral coefficients at a `q`-integral point. -/
theorem PSV_substPS {q : ℕ} [Fact q.Prime] {a : ℚ} (ha : ValGe q 0 a) (P : Polynomial ℚ)
    (hP : ∀ i, ValGe q 0 (P.coeff i)) : PSV q 0 (substPS a P) := by
  have hP' : substPS a P = ∑ i ∈ P.support, C (P.coeff i) * (C a + X) ^ i := by
    conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, substPS_C, substPS_X]
  rw [hP']
  refine PSV.sum _ _ fun i _ => ?_
  exact (PSV.ofC (hP i)).mul' (PSV.pow ((PSV.ofC ha).add PSV.ofX) i) (by simp)

end Subst

/-! ## 5. Partial fractions and the residue theorem at infinity (generic)

For a finite family of distinct points `pos i` (`i ∈ S`) with orders `a i ≥ 1` and any numerator
`N ∈ ℚ[t]`, the Taylor series `tay … i` of `N / ∏_{i' ≠ i} (t - pos i')^{a i'}` at `pos i` give the
principal parts of `N / ∏ (t - pos i)^{a i}` (`pf_dvd`: the denominator divides `N - pfSum`), and
the sum of the residues is read off at infinity (`grt`):
`∑_i [ε^{a i - 1}] tay i = [y^{deg N - ∑ a + 1}] (y^{deg N} N(1/y)) / ∏ (1 - pos i y)^{a i}`. -/

section Residue

variable {ι : Type*} [DecidableEq ι]

/-- `∏_{i' ∈ S, i' ≠ i} (t - pos i')^{a i'}`. -/
def denE (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (i : ι) : Polynomial ℚ :=
  ∏ i' ∈ S.erase i, (Polynomial.X - Polynomial.C (pos i')) ^ a i'

/-- `∏_{i ∈ S} (t - pos i)^{a i}`. -/
def den (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) : Polynomial ℚ :=
  ∏ i ∈ S, (Polynomial.X - Polynomial.C (pos i)) ^ a i

/-- The Taylor series of `N / denE i` at `t = pos i`. -/
def tay (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (N : Polynomial ℚ) (i : ι) : PowerSeries ℚ :=
  substPS (pos i) N * (substPS (pos i) (denE S pos a i))⁻¹

/-- The partial-fraction numerator `∑_i ∑_{l ≤ a i} c_{i,l} (t - pos i)^{a i - l} denE i`. -/
def pfSum (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (N : Polynomial ℚ) : Polynomial ℚ :=
  ∑ i ∈ S, ∑ l ∈ Icc 1 (a i), Polynomial.C (coeff (a i - l) (tay S pos a N i)) *
    (Polynomial.X - Polynomial.C (pos i)) ^ (a i - l) * denE S pos a i

/-- `∏_{i ∈ S} (1 - pos i · y)^{a i}` (the reflected denominator), as a power series. -/
def drev (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) : PowerSeries ℚ :=
  ∏ i ∈ S, (1 - C (pos i) * X) ^ a i

theorem substPS_X_sub_C_pow (x y : ℚ) (m : ℕ) :
    substPS x ((Polynomial.X - Polynomial.C y) ^ m) = (C (x - y) + X) ^ m := by
  rw [map_pow, substPS_X_sub_C]

theorem constantCoeff_substPS_denE (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ)
    (hinj : Set.InjOn pos S) {i : ι} (hi : i ∈ S) :
    constantCoeff (substPS (pos i) (denE S pos a i)) ≠ 0 := by
  unfold denE
  rw [map_prod, map_prod, Finset.prod_ne_zero_iff]
  intro i' hi'
  rw [substPS_X_sub_C_pow, map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero]
  apply pow_ne_zero
  rw [sub_ne_zero]
  intro h
  exact (Finset.ne_of_mem_erase hi') (hinj (Finset.mem_of_mem_erase hi') hi h.symm)

theorem X_pow_dvd_substPS_denE (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) {i i' : ι}
    (hi : i ∈ S) (hne : i' ≠ i) :
    (X : PowerSeries ℚ) ^ a i ∣ substPS (pos i) (denE S pos a i') := by
  unfold denE
  rw [map_prod]
  simp only [substPS_X_sub_C_pow]
  have hmem : i ∈ S.erase i' := Finset.mem_erase.2 ⟨hne.symm, hi⟩
  have := Finset.dvd_prod_of_mem
    (fun j : ι => (C (pos i - pos j) + X : PowerSeries ℚ) ^ a j) hmem
  simp only [sub_self, map_zero, zero_add] at this
  exact this

/-- Local divisibility: `(t - pos i)^{a i} ∣ N - pfSum`. -/
theorem pf_local (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (N : Polynomial ℚ)
    (hinj : Set.InjOn pos S) {i : ι} (hi : i ∈ S) :
    (Polynomial.X - Polynomial.C (pos i)) ^ a i ∣ N - pfSum S pos a N := by
  set P := N - pfSum S pos a N with hP
  set V := substPS (pos i) (denE S pos a i) with hV
  have hV0 : constantCoeff V ≠ 0 := constantCoeff_substPS_denE S pos a hinj hi
  set T : PowerSeries ℚ := ∑ l ∈ Icc 1 (a i), C (coeff (a i - l) (tay S pos a N i)) *
    X ^ (a i - l) with hT
  set Er : PowerSeries ℚ := ∑ i' ∈ S.erase i, ∑ l ∈ Icc 1 (a i'),
    C (coeff (a i' - l) (tay S pos a N i')) * (C (pos i - pos i') + X) ^ (a i' - l) *
      substPS (pos i) (denE S pos a i') with hEr
  have hN : substPS (pos i) N = tay S pos a N i * V := by
    unfold tay
    rw [← hV, mul_assoc, PowerSeries.inv_mul_cancel _ hV0, mul_one]
  have hPF : substPS (pos i) (pfSum S pos a N) = T * V + Er := by
    unfold pfSum
    rw [map_sum, ← Finset.add_sum_erase _ _ hi]
    congr 1
    · rw [map_sum, hT, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, map_mul, substPS_C, substPS_X_sub_C_pow, sub_self, map_zero, zero_add, ← hV]
    · rw [hEr]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, map_mul, substPS_C, substPS_X_sub_C_pow]
  have hTdvd : (X : PowerSeries ℚ) ^ a i ∣ tay S pos a N i - T := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hT, map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (a i - m)]
    · rw [ite_eq_left (by omega), Nat.sub_sub_self (by omega), sub_self]
    · intro l hl hne
      rw [Finset.mem_Icc] at hl
      rw [ite_eq_right (by omega)]
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_Icc]; omega
  have hErdvd : (X : PowerSeries ℚ) ^ a i ∣ Er := by
    rw [hEr]
    refine Finset.dvd_sum fun i' hi' => Finset.dvd_sum fun l _ => ?_
    exact Dvd.dvd.mul_left (X_pow_dvd_substPS_denE S pos a hi (Finset.ne_of_mem_erase hi')) _
  have key : (X : PowerSeries ℚ) ^ a i ∣ substPS (pos i) P := by
    rw [hP, map_sub, hN, hPF]
    have : tay S pos a N i * V - (T * V + Er) = (tay S pos a N i - T) * V - Er := by ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left hTdvd V) hErdvd
  -- back to polynomials
  set Q := P.comp (Polynomial.X - Polynomial.C (-pos i)) with hQ
  have hQdvd : Polynomial.X ^ a i ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    have h1 := key
    rw [← neg_neg (pos i), ← coe_comp_eq_substPS, ← hQ, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 m hm
    rwa [Polynomial.coeff_coe] at h2
  obtain ⟨R, hR⟩ := hQdvd
  have hPQ : P = Q.comp (Polynomial.X - Polynomial.C (pos i)) := by
    rw [hQ, Polynomial.comp_assoc]
    simp
  refine ⟨R.comp (Polynomial.X - Polynomial.C (pos i)), ?_⟩
  rw [hPQ, hR, Polynomial.mul_comp, Polynomial.X_pow_comp]

/-- Partial fractions: `∏_i (t - pos i)^{a i} ∣ N - pfSum`. -/
theorem pf_dvd (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (N : Polynomial ℚ)
    (hinj : Set.InjOn pos S) : den S pos a ∣ N - pfSum S pos a N := by
  unfold den
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    have hne : pos i - pos j ≠ 0 := sub_ne_zero.2 fun h => hij (hinj hi hj h)
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.2 hne)).pow
  · intro i hi
    exact pf_local S pos a N hinj hi

/-! ### Degrees and reflections -/

theorem natDegree_X_sub_C_pow_le (y : ℚ) (m : ℕ) :
    ((Polynomial.X - Polynomial.C y) ^ m).natDegree ≤ m := by
  rw [(Polynomial.monic_X_sub_C y).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

omit [DecidableEq ι] in
theorem monic_den (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) : (den S pos a).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => (Polynomial.monic_X_sub_C _).pow _

theorem natDegree_denE (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (i : ι) :
    (denE S pos a i).natDegree = ∑ i' ∈ S.erase i, a i' := by
  unfold denE
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i' _ => (Polynomial.monic_X_sub_C _).pow _]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

omit [DecidableEq ι] in
theorem natDegree_den (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) :
    (den S pos a).natDegree = ∑ i ∈ S, a i := by
  unfold den
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i' _ => (Polynomial.monic_X_sub_C _).pow _]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

theorem natDegree_pfSum_le (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (N : Polynomial ℚ) :
    (pfSum S pos a N).natDegree ≤ (∑ i ∈ S, a i) - 1 := by
  unfold pfSum
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
  rw [Finset.mem_Icc] at hl
  have hsum : ∑ i' ∈ S.erase i, a i' + a i = ∑ i ∈ S, a i := Finset.sum_erase_add _ _ hi
  have h1 := Polynomial.natDegree_mul_le (p := Polynomial.C (coeff (a i - l) (tay S pos a N i)) *
    (Polynomial.X - Polynomial.C (pos i)) ^ (a i - l)) (q := denE S pos a i)
  have h2 := Polynomial.natDegree_mul_le (p := Polynomial.C (coeff (a i - l) (tay S pos a N i)))
    (q := (Polynomial.X - Polynomial.C (pos i)) ^ (a i - l))
  rw [Polynomial.natDegree_C, zero_add] at h2
  have h3 := natDegree_X_sub_C_pow_le (pos i) (a i - l)
  rw [natDegree_denE] at h1
  omega

/-- `reflect (M + k) f = X^k · reflect M f` when `deg f ≤ M`. -/
theorem reflect_add_X_pow (f : Polynomial ℚ) (M k : ℕ) (hf : f.natDegree ≤ M) :
    Polynomial.reflect (M + k) f = Polynomial.X ^ k * Polynomial.reflect M f := by
  ext n
  rw [Polynomial.coeff_reflect, Polynomial.coeff_X_pow_mul']
  by_cases h1 : n ≤ M + k
  · rw [Polynomial.revAt_le h1]
    split_ifs with h2
    · rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega : n - k ≤ M)]
      congr 1
      omega
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · have h2 : f.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h3 : f.coeff (n - k) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.revAt_eq_self_of_lt (by omega), ite_eq_left (by omega), Polynomial.coeff_reflect,
      Polynomial.revAt_eq_self_of_lt (by omega), h2, h3]

theorem reflect_X_sub_C (y : ℚ) :
    Polynomial.reflect 1 (Polynomial.X - Polynomial.C y) = 1 - Polynomial.C y * Polynomial.X := by
  rw [Polynomial.reflect_sub, Polynomial.reflect_one_X, Polynomial.reflect_C, pow_one]

theorem reflect_X_sub_C_pow (y : ℚ) (m : ℕ) :
    Polynomial.reflect m ((Polynomial.X - Polynomial.C y) ^ m) =
      (1 - Polynomial.C y * Polynomial.X) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.reflect_mul _ _ (natDegree_X_sub_C_pow_le y m)
      (by rw [Polynomial.natDegree_X_sub_C]), ih, reflect_X_sub_C, pow_succ]

theorem reflect_prod {κ : Type*} (s : Finset κ) (f : κ → Polynomial ℚ) (d : κ → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    Polynomial.reflect (∑ i ∈ s, d i) (∏ i ∈ s, f i) = ∏ i ∈ s, Polynomial.reflect (d i) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, Finset.prod_insert hx]
    have hrest : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
      (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Polynomial.reflect_mul _ _ (hf x (Finset.mem_insert_self x s)) hrest,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem reflect_sum {κ : Type*} (s : Finset κ) (f : κ → Polynomial ℚ) (M : ℕ) :
    Polynomial.reflect M (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect M (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Polynomial.reflect_add, ih]

omit [DecidableEq ι] in
theorem reflect_den (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) :
    Polynomial.reflect (∑ i ∈ S, a i) (den S pos a) =
      ∏ i ∈ S, (1 - Polynomial.C (pos i) * Polynomial.X) ^ a i := by
  unfold den
  rw [reflect_prod _ _ _ fun i _ => natDegree_X_sub_C_pow_le _ _]
  exact Finset.prod_congr rfl fun i _ => reflect_X_sub_C_pow _ _

theorem reflect_denE (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (i : ι) :
    Polynomial.reflect (∑ i' ∈ S.erase i, a i') (denE S pos a i) =
      ∏ i' ∈ S.erase i, (1 - Polynomial.C (pos i') * Polynomial.X) ^ a i' := by
  unfold denE
  rw [reflect_prod _ _ _ fun i _ => natDegree_X_sub_C_pow_le _ _]
  exact Finset.prod_congr rfl fun i _ => reflect_X_sub_C_pow _ _

theorem constantCoeff_one_sub_pow (y : ℚ) (m : ℕ) :
    constantCoeff ((1 - C y * X : PowerSeries ℚ) ^ m) = 1 := by
  simp

omit [DecidableEq ι] in
theorem constantCoeff_drev (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) :
    constantCoeff (drev S pos a) = 1 := by
  unfold drev
  rw [map_prod]
  exact Finset.prod_eq_one fun i _ => constantCoeff_one_sub_pow _ _

/-- The residue theorem at infinity, in partial-fraction form. -/
theorem grt (S : Finset ι) (pos : ι → ℚ) (a : ι → ℕ) (N : Polynomial ℚ)
    (hinj : Set.InjOn pos S) (ha : ∀ i ∈ S, 1 ≤ a i) :
    ∑ i ∈ S, coeff (a i - 1) (tay S pos a N i) =
      coeffZ ((N.reverse : PowerSeries ℚ) * (drev S pos a)⁻¹)
        ((N.natDegree : ℤ) - ((∑ i ∈ S, a i : ℕ) : ℤ) + 1) := by
  classical
  obtain ⟨Q, hQ⟩ := pf_dvd S pos a N hinj
  set d := N.natDegree with hd
  set A := ∑ i ∈ S, a i with hA
  set c : ι → ℕ → ℚ := fun i l => coeff (a i - l) (tay S pos a N i) with hc
  have hQdeg : Q.natDegree ≤ d := by
    rcases eq_or_ne Q 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; exact Nat.zero_le _
    · have h1 := (monic_den S pos a).natDegree_mul' h0
      rw [← hQ, natDegree_den] at h1
      have h2 := Polynomial.natDegree_sub_le N (pfSum S pos a N)
      have h3 := natDegree_pfSum_le S pos a N
      rw [h1] at h2
      have := le_max_iff.1 h2
      omega
  have hNeq : N = den S pos a * Q + pfSum S pos a N := by rw [← hQ]; ring
  -- reflect everything at degree `A + d`
  have hRN : Polynomial.reflect (A + d) N = Polynomial.X ^ A * N.reverse := by
    rw [add_comm, reflect_add_X_pow N d A le_rfl]
    rfl
  have hRQ : Polynomial.reflect (A + d) (den S pos a * Q) =
      (∏ i ∈ S, (1 - Polynomial.C (pos i) * Polynomial.X) ^ a i) * Polynomial.reflect d Q := by
    rw [Polynomial.reflect_mul _ _ (by rw [natDegree_den]) hQdeg, reflect_den]
  have hRterm : ∀ i ∈ S, ∀ l ∈ Icc 1 (a i),
      Polynomial.reflect (A + d) (Polynomial.C (c i l) *
        (Polynomial.X - Polynomial.C (pos i)) ^ (a i - l) * denE S pos a i) =
      Polynomial.C (c i l) * Polynomial.X ^ (d + l) *
        ((1 - Polynomial.C (pos i) * Polynomial.X) ^ (a i - l) *
          ∏ i' ∈ S.erase i, (1 - Polynomial.C (pos i') * Polynomial.X) ^ a i') := by
    intro i hi l hl
    rw [Finset.mem_Icc] at hl
    have hsum : ∑ i' ∈ S.erase i, a i' + a i = A := Finset.sum_erase_add _ _ hi
    have hdeg : ((Polynomial.X - Polynomial.C (pos i)) ^ (a i - l) * denE S pos a i).natDegree ≤
        (a i - l) + ∑ i' ∈ S.erase i, a i' :=
      Polynomial.natDegree_mul_le.trans (add_le_add (natDegree_X_sub_C_pow_le _ _)
        (natDegree_denE S pos a i).le)
    rw [mul_assoc, Polynomial.reflect_C_mul,
      show A + d = ((a i - l) + ∑ i' ∈ S.erase i, a i') + (d + l) by omega,
      reflect_add_X_pow _ _ _ hdeg,
      Polynomial.reflect_mul _ _ (natDegree_X_sub_C_pow_le _ _) (natDegree_denE S pos a i).le,
      reflect_X_sub_C_pow, reflect_denE]
    ring
  have hRP : Polynomial.reflect (A + d) (pfSum S pos a N) =
      ∑ i ∈ S, ∑ l ∈ Icc 1 (a i), Polynomial.C (c i l) * Polynomial.X ^ (d + l) *
        ((1 - Polynomial.C (pos i) * Polynomial.X) ^ (a i - l) *
          ∏ i' ∈ S.erase i, (1 - Polynomial.C (pos i') * Polynomial.X) ^ a i') := by
    unfold pfSum
    rw [reflect_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [reflect_sum]
    exact Finset.sum_congr rfl fun l hl => hRterm i hi l hl
  have hmain := congrArg (Polynomial.reflect (A + d)) hNeq
  rw [Polynomial.reflect_add, hRN, hRQ, hRP] at hmain
  -- to power series
  have hPS := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) hmain
  simp only [map_add, map_mul, map_sum, map_prod, map_pow, map_sub, map_one,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C] at hPS
  have hdrev : drev S pos a = ∏ i ∈ S, (1 - C (pos i) * X) ^ a i := rfl
  rw [← hdrev] at hPS
  have hd0 : constantCoeff (drev S pos a) ≠ 0 := by rw [constantCoeff_drev]; exact one_ne_zero
  have hterm : ∀ i ∈ S, ∀ l ∈ Icc 1 (a i),
      ((1 - C (pos i) * X) ^ (a i - l) * ∏ i' ∈ S.erase i, (1 - C (pos i') * X) ^ a i') *
        (drev S pos a)⁻¹ = ((1 - C (pos i) * X : PowerSeries ℚ) ^ l)⁻¹ := by
    intro i hi l hl
    rw [Finset.mem_Icc] at hl
    rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_one_sub_pow]; exact one_ne_zero)]
    have hsplit : drev S pos a = (1 - C (pos i) * X) ^ (a i - l) * (1 - C (pos i) * X) ^ l *
        ∏ i' ∈ S.erase i, (1 - C (pos i') * X) ^ a i' := by
      rw [← pow_add, Nat.sub_add_cancel hl.2, hdrev]
      exact (Finset.mul_prod_erase S (fun i => (1 - C (pos i) * X : PowerSeries ℚ) ^ a i) hi).symm
    calc (1 - C (pos i) * X) ^ (a i - l) * (∏ i' ∈ S.erase i, (1 - C (pos i') * X) ^ a i') *
          (drev S pos a)⁻¹ * (1 - C (pos i) * X) ^ l
        = drev S pos a * (drev S pos a)⁻¹ := by rw [hsplit]; ring
      _ = 1 := PowerSeries.mul_inv_cancel _ hd0
  have hkey : (X : PowerSeries ℚ) ^ A * ((N.reverse : PowerSeries ℚ) * (drev S pos a)⁻¹) =
      (Polynomial.reflect d Q : PowerSeries ℚ) + ∑ i ∈ S, ∑ l ∈ Icc 1 (a i),
        C (c i l) * X ^ (d + l) * ((1 - C (pos i) * X) ^ l)⁻¹ := by
    have h := congrArg (· * (drev S pos a)⁻¹) hPS
    rw [← mul_assoc, h, add_mul, mul_comm (drev S pos a), mul_assoc,
      PowerSeries.mul_inv_cancel _ hd0, mul_one, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [mul_assoc, hterm i hi l hl]
  have hcoef := congrArg (coeff (d + 1)) hkey
  rw [PowerSeries.coeff_X_pow_mul', map_add, Polynomial.coeff_coe, Polynomial.coeff_reflect,
    Polynomial.revAt_eq_self_of_lt (by omega),
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_add, map_sum] at hcoef
  have hinner : ∀ i ∈ S, ∑ l ∈ Icc 1 (a i),
      coeff (d + 1) (C (c i l) * X ^ (d + l) * ((1 - C (pos i) * X : PowerSeries ℚ) ^ l)⁻¹) =
        c i 1 := by
    intro i hi
    rw [Finset.sum_eq_single 1]
    · rw [mul_assoc, coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
        constantCoeff_one_sub_pow, inv_one, mul_one]
    · intro l hl hne
      rw [Finset.mem_Icc] at hl
      rw [mul_assoc, coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨le_rfl, ha i hi⟩) h
  have hsum : ∑ i ∈ S, ∑ l ∈ Icc 1 (a i), coeff (d + 1) (C (c i l) * X ^ (d + l) *
      ((1 - C (pos i) * X : PowerSeries ℚ) ^ l)⁻¹) = ∑ i ∈ S, coeff (a i - 1) (tay S pos a N i) :=
    Finset.sum_congr rfl hinner
  simp only [map_sum] at hcoef
  rw [hsum] at hcoef
  unfold coeffZ
  split_ifs with hz
  · rw [← hcoef, ite_eq_left (by omega), show d + 1 - A = ((d : ℤ) - (A : ℤ) + 1).toNat by omega]
  · rw [← hcoef, ite_eq_right (by omega)]

end Residue

/-! ## 6. The residue theorem for local types

`posSet τ` are the distinct item positions (doubled local coordinates), `netE τ w` the net exponent
at `w`; `poleSet τ` / `zeroSet τ` the positions with negative / positive net exponent and
`ord τ w = -netE τ w` the pole order.  Main result `grt_local`:
`∑_{w ∈ poleSet} [ε^{ord w - 1}] ((w/2 + ε)^m · taylorAt τ w) = [y^{E + m + 1}] rSer τ`
(the finite residues of `v^m RR(v)` sum to its residue at infinity). -/

section LocalGRT

/-- Distinct positions of the items. -/
def posSet (τ : LocalType) : Finset ℤ :=
  (τ.items.map Prod.fst).toFinset

/-- Positions with negative net exponent (the poles of `RR`). -/
def poleSet (τ : LocalType) : Finset ℤ :=
  (posSet τ).filter fun w => τ.netE w < 0

/-- Positions with positive net exponent (the zeros of `RR`). -/
def zeroSet (τ : LocalType) : Finset ℤ :=
  (posSet τ).filter fun w => 0 < τ.netE w

/-- The pole order `-netE τ w` (as a natural number). -/
def ord (τ : LocalType) (w : ℤ) : ℕ :=
  (-τ.netE w).toNat

theorem list_prod_filter_map {α M : Type*} [CommMonoid M] (L : List α) (P : α → Bool)
    (f : α → M) : ((L.filter P).map f).prod = (L.map fun x => if P x then f x else 1).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.filter_cons, List.map_cons, List.prod_cons]
    split_ifs with h
    · rw [List.map_cons, List.prod_cons, ih]
    · rw [one_mul, ih]

/-- The net exponent of `x :: L`. -/
theorem netE_cons (L : List (ℤ × ℤ)) (x : ℤ × ℤ) (p : ℤ) :
    (((x :: L).filter fun y => y.1 = p).map Prod.snd).sum =
      (if x.1 = p then x.2 else 0) + ((L.filter fun y => y.1 = p).map Prod.snd).sum := by
  by_cases h : x.1 = p
  · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ite_eq_left h]
  · rw [List.filter_cons_of_neg (by simpa using h), ite_eq_right h, zero_add]

/-- Grouping a product over items by position. -/
theorem list_prod_group {M : Type*} [CommMonoid M] (L : List (ℤ × ℤ)) (F : ℤ → ℤ → M)
    (h0 : ∀ p, F p 0 = 1) (hadd : ∀ p e₁ e₂, F p (e₁ + e₂) = F p e₁ * F p e₂)
    (T : Finset ℤ) (hT : ∀ x ∈ L, x.1 ∈ T) :
    (L.map fun x => F x.1 x.2).prod =
      ∏ p ∈ T, F p ((L.filter fun y => y.1 = p).map Prod.snd).sum := by
  induction L with
  | nil => simp [h0]
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ih fun y hy => hT y (List.mem_cons_of_mem _ hy)]
    simp only [netE_cons, hadd, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single x.1]
    · simp
    · intro p _ hp
      rw [ite_eq_right (Ne.symm hp), h0]
    · intro h
      exact absurd (hT x (List.mem_cons_self ..)) h

/-- Grouping a sum over items by position. -/
theorem list_sum_group (L : List (ℤ × ℤ)) (T : Finset ℤ) (hT : ∀ x ∈ L, x.1 ∈ T) :
    (L.map Prod.snd).sum = ∑ p ∈ T, ((L.filter fun y => y.1 = p).map Prod.snd).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, ih fun y hy => hT y (List.mem_cons_of_mem _ hy)]
    simp only [netE_cons, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single x.1]
    · simp
    · intro p _ hp
      rw [ite_eq_right (Ne.symm hp)]
    · intro h
      exact absurd (hT x (List.mem_cons_self ..)) h

theorem mem_posSet {τ : LocalType} {x : ℤ × ℤ} (hx : x ∈ τ.items) : x.1 ∈ posSet τ := by
  unfold posSet
  rw [List.mem_toFinset]
  exact List.mem_map.2 ⟨x, hx, rfl⟩

theorem netE_eq_zero_of_not_mem {τ : LocalType} {w : ℤ} (hw : w ∉ posSet τ) : τ.netE w = 0 := by
  unfold LocalType.netE
  rw [List.filter_eq_nil_iff.2]
  · simp
  · intro x hx
    simp only [decide_eq_true_eq]
    intro h
    exact hw (h ▸ mem_posSet hx)

theorem E_eq_sum (τ : LocalType) : τ.E = ∑ p ∈ posSet τ, τ.netE p :=
  list_sum_group τ.items (posSet τ) fun _ hx => mem_posSet hx

theorem prod_ite_eq_erase {M : Type*} [CommMonoid M] (T : Finset ℤ) (w : ℤ) (f : ℤ → M) :
    ∏ p ∈ T, (if p = w then 1 else f p) = ∏ p ∈ T.erase w, f p := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
  congr 1
  ext p
  simp [and_comm]

/-- `taylorAt` as a product over the other positions. -/
theorem taylorAt_eq_prod (τ : LocalType) (w : ℤ) :
    taylorAt τ w = ∏ p ∈ (posSet τ).erase w, lin (((w : ℚ) - p) / 2) (τ.netE p) := by
  unfold taylorAt
  rw [list_prod_filter_map]
  have hF : ∀ x : ℤ × ℤ, (if decide (x.1 ≠ w) then C ((((w : ℚ) - x.1) / 2) ^ x.2) *
      bser (2 / ((w : ℚ) - x.1)) x.2 else 1) =
      (fun p e => if p = w then (1 : PowerSeries ℚ) else lin (((w : ℚ) - p) / 2) e) x.1 x.2 := by
    intro x
    by_cases h : x.1 = w
    · simp [h]
    · simp only [h, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false]
      unfold lin
      rw [inv_div]
  rw [List.map_congr_left fun x _ => hF x]
  rw [list_prod_group τ.items (fun p e => if p = w then (1 : PowerSeries ℚ) else
      lin (((w : ℚ) - p) / 2) e) (fun p => by simp [lin_zero])
    (fun p e₁ e₂ => by
      by_cases h : p = w
      · simp [h]
      · simp only [h, ite_false]
        exact lin_add (div_ne_zero (sub_ne_zero.2 (by exact_mod_cast Ne.symm h)) two_ne_zero) _ _)
    (posSet τ) fun _ hx => mem_posSet hx]
  exact prod_ite_eq_erase _ w _

/-- `rSer` as a product over the positions. -/
theorem rSer_eq_prod (τ : LocalType) :
    rSer τ = ∏ p ∈ posSet τ, bser (-(p : ℚ) / 2) (τ.netE p) := by
  unfold rSer
  exact list_prod_group τ.items (fun p e => bser (-(p : ℚ) / 2) e) (fun p => bser_zero _)
    (fun p e₁ e₂ => bser_add _ _ _) (posSet τ) fun _ hx => mem_posSet hx

/-- Splitting a product over the positions into zeros, poles and the rest. -/
theorem prod_posSet_split {M : Type*} [CommMonoid M] (τ : LocalType) (T : Finset ℤ)
    (_hT : T ⊆ posSet τ) (g : ℤ → M) (hg : ∀ p ∈ T, τ.netE p = 0 → g p = 1) :
    ∏ p ∈ T, g p = (∏ p ∈ T.filter (fun p => 0 < τ.netE p), g p) *
      ∏ p ∈ T.filter (fun p => τ.netE p < 0), g p := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun p => 0 < τ.netE p)]
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not (T.filter fun p => ¬ 0 < τ.netE p)
    (fun p => τ.netE p < 0), Finset.filter_filter, Finset.filter_filter]
  have h1 : (T.filter fun p => ¬ 0 < τ.netE p ∧ τ.netE p < 0) =
      T.filter fun p => τ.netE p < 0 := by
    ext p; simp only [Finset.mem_filter]; constructor
    · rintro ⟨h, -, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨h, by omega, h2⟩
  rw [h1, Finset.prod_eq_one (s := T.filter fun p => ¬ 0 < τ.netE p ∧ ¬ τ.netE p < 0), mul_one]
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hg p hp.1 (by omega)

theorem prod_inv_distrib' {κ : Type*} (s : Finset κ) (φ : κ → PowerSeries ℚ) :
    (∏ j ∈ s, φ j)⁻¹ = ∏ j ∈ s, (φ j)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, PowerSeries.mul_inv_rev, ih, mul_comm]

/-- Splitting a sum over the positions into zeros, poles and the rest. -/
theorem sum_posSet_split (τ : LocalType) (T : Finset ℤ) (g : ℤ → ℤ)
    (hg : ∀ p ∈ T, τ.netE p = 0 → g p = 0) :
    ∑ p ∈ T, g p = (∑ p ∈ T.filter (fun p => 0 < τ.netE p), g p) +
      ∑ p ∈ T.filter (fun p => τ.netE p < 0), g p := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun p => 0 < τ.netE p)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (T.filter fun p => ¬ 0 < τ.netE p)
    (fun p => τ.netE p < 0), Finset.filter_filter, Finset.filter_filter]
  have h1 : (T.filter fun p => ¬ 0 < τ.netE p ∧ τ.netE p < 0) =
      T.filter fun p => τ.netE p < 0 := by
    ext p; simp only [Finset.mem_filter]; constructor
    · rintro ⟨h, -, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨h, by omega, h2⟩
  rw [h1, Finset.sum_eq_zero (s := T.filter fun p => ¬ 0 < τ.netE p ∧ ¬ τ.netE p < 0), add_zero]
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hg p hp.1 (by omega)

theorem reverse_one' : (1 : Polynomial ℚ).reverse = 1 := by
  rw [← Polynomial.C_1, Polynomial.reverse_C]

theorem reverse_X_sub_C (y : ℚ) :
    (Polynomial.X - Polynomial.C y).reverse = 1 - Polynomial.C y * Polynomial.X := by
  unfold Polynomial.reverse
  rw [Polynomial.natDegree_X_sub_C, reflect_X_sub_C]

theorem reverse_prod_X_sub_C {κ : Type*} (s : Finset κ) (y : κ → ℚ) (k : κ → ℕ) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (y i)) ^ k i).reverse =
      ∏ i ∈ s, (1 - Polynomial.C (y i) * Polynomial.X) ^ k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reverse_one']
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.reverse_mul_of_domain, ih]
    congr 1
    induction k a with
    | zero => simp [reverse_one']
    | succ m ihm => rw [pow_succ, Polynomial.reverse_mul_of_domain, ihm, reverse_X_sub_C, pow_succ]

theorem coe_prod_one_sub {κ : Type*} (s : Finset κ) (y : κ → ℚ) (k : κ → ℕ) :
    ((∏ i ∈ s, (1 - Polynomial.C (y i) * Polynomial.X) ^ k i : Polynomial ℚ) : PowerSeries ℚ) =
      ∏ i ∈ s, (1 - C (y i) * X) ^ k i := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

theorem zeroSet_netE {τ : LocalType} {z : ℤ} (hz : z ∈ zeroSet τ) : 0 < τ.netE z := by
  unfold zeroSet at hz
  exact (Finset.mem_filter.1 hz).2

theorem poleSet_netE {τ : LocalType} {w : ℤ} (hw : w ∈ poleSet τ) : τ.netE w < 0 := by
  unfold poleSet at hw
  exact (Finset.mem_filter.1 hw).2

theorem netE_of_poleSet {τ : LocalType} {w : ℤ} (hw : w ∈ poleSet τ) :
    τ.netE w = -((ord τ w : ℕ) : ℤ) := by
  have := poleSet_netE hw
  unfold ord
  omega

/-- **Residue theorem for a local type**: the residues of `v^m RR(v)` at its poles add up to the
coefficient `[y^{E + m + 1}] r(y)` of the expansion at infinity. -/
theorem grt_local (τ : LocalType) (m : ℕ) :
    ∑ w ∈ poleSet τ, coeff (ord τ w - 1) ((C ((w : ℚ) / 2) + X) ^ m * taylorAt τ w) =
      coeffZ (rSer τ) (τ.E + m + 1) := by
  classical
  set S := poleSet τ with hS
  set Z := zeroSet τ with hZ
  set pos : ℤ → ℚ := fun w => (w : ℚ) / 2 with hpos
  set N : Polynomial ℚ := Polynomial.X ^ m *
    ∏ z ∈ Z, (Polynomial.X - Polynomial.C (pos z)) ^ (τ.netE z).toNat with hN
  have hinj : Set.InjOn pos S := by
    intro x _ y _ h
    simp only [hpos] at h
    have : (x : ℚ) = y := by linarith
    exact_mod_cast this
  have ha : ∀ w ∈ S, 1 ≤ ord τ w := by
    intro w hw
    have := poleSet_netE hw
    unfold ord
    omega
  -- the two filters of `(posSet τ).erase w`
  have hsplitZ : ∀ w ∈ S, ((posSet τ).erase w).filter (fun p => 0 < τ.netE p) = Z := by
    intro w hw
    have hw' := poleSet_netE hw
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, hZ, zeroSet]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, h1⟩, h2⟩
      rintro rfl; omega
  have hsplitS : ∀ w ∈ S, ((posSet τ).erase w).filter (fun p => τ.netE p < 0) = S.erase w := by
    intro w _
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, hS, poleSet]
    tauto
  have hne : ∀ w ∈ S, ∀ p, w ≠ p → (((w : ℚ) - p) / 2) ≠ 0 := by
    intro w _ p h
    exact div_ne_zero (sub_ne_zero.2 (by exact_mod_cast h)) two_ne_zero
  have htay : ∀ w ∈ S, tay S pos (ord τ) N w = (C ((w : ℚ) / 2) + X) ^ m * taylorAt τ w := by
    intro w hw
    unfold tay denE
    rw [taylorAt_eq_prod, prod_posSet_split τ _ (Finset.erase_subset _ _) _ (fun p _ hp => by
      rw [hp, lin_zero]), hsplitZ w hw, hsplitS w hw]
    rw [hN, map_mul, map_pow, substPS_X, map_prod, map_prod]
    simp only [substPS_X_sub_C_pow]
    rw [prod_inv_distrib', mul_assoc]
    congr 2
    · refine Finset.prod_congr rfl fun z hz => ?_
      have hz' := zeroSet_netE hz
      have hwz : w ≠ z := by
        rintro rfl
        have := poleSet_netE hw
        omega
      have : τ.netE z = ((τ.netE z).toNat : ℤ) := by omega
      rw [this, lin_nat (hne w hw z hwz), Int.toNat_natCast]
      simp only [hpos]
      congr 2
      ring
    · refine Finset.prod_congr rfl fun s hs => ?_
      have hs' := Finset.mem_erase.1 hs
      rw [netE_of_poleSet hs'.2, lin_neg_nat (hne w hw s (Ne.symm hs'.1))]
      simp only [hpos]
      congr 3
      ring
  have hG := grt S pos (ord τ) N hinj ha
  have hN_rev : (N.reverse : PowerSeries ℚ) = ∏ z ∈ Z, (1 - C (pos z) * X) ^ (τ.netE z).toNat := by
    rw [hN, Polynomial.reverse_X_pow_mul, reverse_prod_X_sub_C, coe_prod_one_sub]
  have hrSer : rSer τ = (N.reverse : PowerSeries ℚ) * (drev S pos (ord τ))⁻¹ := by
    rw [rSer_eq_prod, prod_posSet_split τ _ subset_rfl _ (fun p _ hp => by rw [hp, bser_zero])]
    rw [hN_rev, drev, prod_inv_distrib']
    have hZf : (posSet τ).filter (fun p => 0 < τ.netE p) = Z := rfl
    have hSf : (posSet τ).filter (fun p => τ.netE p < 0) = S := rfl
    rw [hZf, hSf]
    congr 1
    · refine Finset.prod_congr rfl fun z hz => ?_
      have hz' := zeroSet_netE hz
      have : τ.netE z = ((τ.netE z).toNat : ℤ) := by omega
      rw [this, bser_nat, Int.toNat_natCast]
      simp only [hpos]
      congr 1
      rw [neg_div, map_neg]
      ring
    · refine Finset.prod_congr rfl fun s hs => ?_
      rw [netE_of_poleSet hs, bser_neg_nat]
      simp only [hpos]
      congr 2
      rw [neg_div, map_neg]
      ring
  have hdeg : (N.natDegree : ℤ) - ((∑ i ∈ S, ord τ i : ℕ) : ℤ) + 1 = τ.E + m + 1 := by
    have hmon : (∏ z ∈ Z, (Polynomial.X - Polynomial.C (pos z)) ^ (τ.netE z).toNat).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun z _ => (Polynomial.monic_X_sub_C _).pow _
    have hN1 : N.natDegree = m + ∑ z ∈ Z, (τ.netE z).toNat := by
      rw [hN, ((Polynomial.monic_X).pow m).natDegree_mul hmon, Polynomial.natDegree_X_pow,
        Polynomial.natDegree_prod_of_monic _ _ fun z _ => (Polynomial.monic_X_sub_C _).pow _]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    have hE : τ.E = ∑ z ∈ Z, τ.netE z + ∑ s ∈ S, τ.netE s := by
      rw [E_eq_sum, sum_posSet_split τ _ _ (fun p _ hp => hp)]
      rfl
    rw [hN1, hE]
    push_cast
    have h1 : ∑ z ∈ Z, (((τ.netE z).toNat : ℕ) : ℤ) = ∑ z ∈ Z, τ.netE z :=
      Finset.sum_congr rfl fun z hz => by have := zeroSet_netE hz; omega
    have h2 : ∑ s ∈ S, ((ord τ s : ℕ) : ℤ) = -∑ s ∈ S, τ.netE s := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s hs => by rw [netE_of_poleSet hs]; ring
    rw [h1, h2]
    ring
  calc ∑ w ∈ S, coeff (ord τ w - 1) ((C ((w : ℚ) / 2) + X) ^ m * taylorAt τ w)
      = ∑ w ∈ S, coeff (ord τ w - 1) (tay S pos (ord τ) N w) :=
        Finset.sum_congr rfl fun w hw => by rw [htay w hw]
    _ = coeffZ (rSer τ) (τ.E + m + 1) := by rw [hG, hrSer, hdeg]

end LocalGRT

/-! ## 7. Adding the kernel pole to a local type -/

section KerType

/-- The local type with the kernel pole `v^{-j}` added (the item `(0, -j)`). -/
def kerType (τ : LocalType) (j : ℕ) : LocalType :=
  ⟨τ.items ++ [(0, -(j : ℤ))], τ.pairs⟩

theorem kerType_E (τ : LocalType) (j : ℕ) : (kerType τ j).E = τ.E - j := by
  simp [kerType, LocalType.E, sub_eq_add_neg]

theorem kerType_netE (τ : LocalType) (j : ℕ) (w : ℤ) :
    (kerType τ j).netE w = τ.netE w - (if w = 0 then (j : ℤ) else 0) := by
  unfold kerType LocalType.netE
  rw [List.filter_append, List.map_append, List.sum_append]
  by_cases h : w = 0
  · subst h; simp [sub_eq_add_neg]
  · have h' : ¬ (0 : ℤ) = w := fun h0 => h h0.symm
    simp [h, h']

theorem kerType_rSer (τ : LocalType) (j : ℕ) : rSer (kerType τ j) = rSer τ := by
  unfold rSer kerType
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  have : bser (-((0 : ℤ) : ℚ) / 2) (-(j : ℤ)) = 1 := by
    ext i
    rw [coeff_bser, coeff_one]
    rcases i with _ | i
    · simp [gchoose_zero_right]
    · simp
  rw [this, mul_one]

theorem kerType_taylorAt (τ : LocalType) (j : ℕ) (w : ℤ) :
    taylorAt (kerType τ j) w =
      taylorAt τ w * (if w = 0 then 1 else lin ((w : ℚ) / 2) (-(j : ℤ))) := by
  unfold taylorAt kerType
  simp only [List.filter_append, List.map_append, List.prod_append]
  congr 1
  by_cases h : w = 0
  · subst h; simp
  · have h' : (0 : ℤ) ≠ w := fun h0 => h h0.symm
    simp only [List.filter_cons, ne_eq, h', not_false_eq_true, decide_true, ite_true,
      List.filter_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h,
      ite_false]
    unfold lin
    push_cast
    rw [sub_zero, inv_div]

theorem kerType_posSet (τ : LocalType) (j : ℕ) :
    posSet (kerType τ j) = insert 0 (posSet τ) := by
  unfold posSet kerType
  ext w
  simp

theorem kerType_poleSet (τ : LocalType) (j : ℕ) (hj : 1 ≤ j) (h0 : τ.netE 0 ≤ 0) :
    poleSet (kerType τ j) = insert 0 (poleSet τ) := by
  unfold poleSet
  rw [kerType_posSet]
  ext w
  simp only [Finset.mem_filter, Finset.mem_insert, kerType_netE]
  by_cases h : w = 0
  · subst h; simp; omega
  · simp [h]

theorem kerType_ord (τ : LocalType) (j : ℕ) {w : ℤ} (hw : w ≠ 0) :
    ord (kerType τ j) w = ord τ w := by
  unfold ord
  rw [kerType_netE, ite_eq_right hw, sub_zero]

theorem kerType_ord0 (τ : LocalType) (j : ℕ) (h0 : τ.netE 0 ≤ 0) :
    ord (kerType τ j) 0 = ord τ 0 + j := by
  unfold ord
  rw [kerType_netE, ite_eq_left rfl]
  omega

end KerType

/-! ## 8. The local model of a class: dictionary

For `τ = localModel u q k₀`: the class poles `k = k₀ + J q ≤ n` (`clsJ`) sit at the positions
`-2J`, which are exactly `poleSet τ` (`poleSet_eq`), with pole order `ord = a_k - ctr` (`ord_pole`;
`ctr = 1` only at the centre `k = n/2` when the δ-zero is in the disc).  The outer factor `Û`
(`Onum / Oden`: the factors of `R_n` whose zero or pole is outside the disc, and the constant `2`)
gives the per-pole factorisation (`Gser_factor`, Lemma 4.1 at `-k`):
`G_k(ε) = q^{E + ord} ε^{ctr} Û(-k + ε) τ_k(ε/q)`. -/

section Model

variable (u q k₀ : ℕ)

/-- The δ-zero `-n/2` lies in the disc of `-k₀` (the test used by `localModel`). -/
abbrev inD : Prop := (2 * (k₀ : ℤ) - 40 * u) % q = 0

/-- The numerator zero `-1/2 - c` lies in the disc of `-k₀`. -/
abbrev inZ (c : ℕ) : Prop := (2 * (c : ℤ) + 1 - 2 * k₀) % q = 0

/-- The class poles `k = k₀ + J q ≤ n`, indexed by `J`. -/
def clsJ : Finset ℕ :=
  (range (40 * u / q + 1)).filter fun J => k₀ + J * q ≤ 40 * u

/-- `1` when the δ-zero sits on the pole `k₀ + J q` (the centre `n/2`), else `0`. -/
def ctr (J : ℕ) : ℕ :=
  if inD u q k₀ ∧ k₀ + J * q = 20 * u then 1 else 0

/-- The numerator of the outer factor `Û`: `2`, the δ-factor if outside the disc, and the
numerator factors `t + 1/2 + c` outside the disc. -/
def Onum : Polynomial ℚ :=
  Polynomial.C 2 * (if inD u q k₀ then 1 else Polynomial.X + Polynomial.C ((20 * u : ℕ) : ℚ)) *
    ∏ m : Fin 6, ∏ c ∈ (block u m).filter (fun c => ¬ inZ q k₀ c),
      (Polynomial.X + Polynomial.C (1 / 2 + (c : ℚ)))

/-- The denominator of the outer factor: the poles outside the class. -/
def Oden : Polynomial ℚ :=
  ∏ j ∈ (range (40 * u + 1)).filter (fun j => j % q ≠ k₀),
    (Polynomial.X + Polynomial.C (j : ℚ)) ^ apole u j

/-- The Taylor series of the outer factor `Û` at `t = y`. -/
def Uhat (y : ℚ) : PowerSeries ℚ :=
  substPS y (Onum u q k₀) * (substPS y (Oden u q k₀))⁻¹

end Model

/-! ### List helpers -/

theorem sum_filterMap_range {α M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → Option α)
    (F : α → M) :
    (((List.range N).filterMap f).map F).sum = ∑ J ∈ range N, (f J).elim 0 F := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    congr 1
    cases h : f N <;> simp [h]

theorem prod_filterMap_range {α M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → Option α)
    (F : α → M) :
    (((List.range N).filterMap f).map F).prod = ∏ J ∈ range N, (f J).elim 1 F := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filterMap_append, List.map_append, List.prod_append, ih,
      Finset.prod_range_succ]
    congr 1
    cases h : f N <;> simp [h]

theorem sum_flatMap_range {α M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → List α)
    (F : α → M) :
    (((List.range N).flatMap g).map F).sum = ∑ J ∈ range N, ((g J).map F).sum := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp

theorem flatMap_singleton_eq_map {α β : Type*} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, ih]; rfl

/-- The coerced range `↑(List.range N) : List ℤ` used by `localModel`. -/
theorem bind_range_cast (N : ℕ) :
    (List.range N >>= fun a => (pure (a : ℤ) : List ℤ)) = (List.range N).map (fun a : ℕ => (a : ℤ)) :=
  flatMap_singleton_eq_map _ _

/-- The net exponent at `w` of a list, as a sum. -/
theorem nE_eq_sum (L : List (ℤ × ℤ)) (w : ℤ) :
    ((L.filter fun y => y.1 = w).map Prod.snd).sum =
      (L.map fun y => if y.1 = w then y.2 else 0).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [netE_cons, ih, List.map_cons, List.sum_cons]

theorem nE_append (L₁ L₂ : List (ℤ × ℤ)) (w : ℤ) :
    (((L₁ ++ L₂).filter fun y => y.1 = w).map Prod.snd).sum =
      ((L₁.filter fun y => y.1 = w).map Prod.snd).sum +
        ((L₂.filter fun y => y.1 = w).map Prod.snd).sum := by
  rw [List.filter_append, List.map_append, List.sum_append]

theorem nE_nonneg (L : List (ℤ × ℤ)) (hL : ∀ x ∈ L, 0 ≤ x.2) (w : ℤ) :
    0 ≤ ((L.filter fun y => y.1 = w).map Prod.snd).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact hL y (List.mem_of_mem_filter hy)

/-! ### The three parts of `localModel` -/

section ModelParts

variable (u q k₀ : ℕ)

/-- The pole items. -/
def PLf : ℕ → Option (ℤ × ℤ) := fun j =>
  if k₀ + j * q ≤ 40 * u then some (-(2 * (j : ℤ)), -((apole u (k₀ + j * q) : ℕ) : ℤ))
  else none

/-- The zero items (the index `t` is an integer, as in `localModel`). -/
def ZLf : ℤ → Option (ℤ × ℤ) := fun t =>
  if 0 ≤ (k₀ : ℤ) + t * q - (q + 1) / 2 ∧ (k₀ : ℤ) + t * q - (q + 1) / 2 < 40 * u ∧
      mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat ≠ 0 then
    some (-(2 * t - 1), (mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat : ℤ))
  else none

/-- The list of zero items. -/
def ZLl : List (ℤ × ℤ) :=
  ((List.range (40 * u / q + 2)).map (fun a : ℕ => (a : ℤ))).filterMap (ZLf u q k₀)

/-- The δ item. -/
def DLl : List (ℤ × ℤ) :=
  if inD u q k₀ then [((2 * (k₀ : ℤ) - 40 * u) / q, 1)] else []

theorem items_eq : (localModel u q k₀).items =
    (List.range (40 * u / q + 1)).filterMap (PLf u q k₀) ++ ZLl u q k₀ ++ DLl u q k₀ := by
  unfold localModel ZLl
  rw [← bind_range_cast]
  rfl

theorem netE_split (w : ℤ) : (localModel u q k₀).netE w =
    ((((List.range (40 * u / q + 1)).filterMap (PLf u q k₀)).filter fun y => y.1 = w).map
        Prod.snd).sum +
      (((ZLl u q k₀).filter fun y => y.1 = w).map
        Prod.snd).sum +
      (((DLl u q k₀).filter fun y => y.1 = w).map Prod.snd).sum := by
  unfold LocalType.netE
  rw [items_eq, nE_append, nE_append]

theorem ZL_nonneg : ∀ x ∈ ZLl u q k₀, 0 ≤ x.2 := by
  intro x hx
  obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 hx
  unfold ZLf at ht
  split_ifs at ht
  cases ht
  exact Nat.cast_nonneg _

theorem DL_nonneg : ∀ x ∈ DLl u q k₀, 0 ≤ x.2 := by
  intro x hx
  unfold DLl at hx
  split_ifs at hx
  · rw [List.mem_singleton] at hx; rw [hx]; norm_num
  · exact absurd hx (List.not_mem_nil)

theorem ZL_odd : ∀ x ∈ ZLl u q k₀, x.1 % 2 = 1 := by
  intro x hx
  obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 hx
  unfold ZLf at ht
  split_ifs at ht
  cases ht
  omega

theorem nE_PL (w : ℤ) :
    ((((List.range (40 * u / q + 1)).filterMap (PLf u q k₀)).filter fun y => y.1 = w).map
        Prod.snd).sum =
      ∑ J ∈ clsJ u q k₀, if -(2 * (J : ℤ)) = w then -((apole u (k₀ + J * q) : ℕ) : ℤ) else 0 := by
  rw [nE_eq_sum, sum_filterMap_range]
  unfold clsJ PLf
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun J _ => ?_
  split_ifs <;> simp_all

end ModelParts

section Dict

variable (u q k₀ : ℕ)

theorem mem_clsJ {J : ℕ} (hq : 0 < q) : J ∈ clsJ u q k₀ ↔ k₀ + J * q ≤ 40 * u := by
  unfold clsJ
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have : J ≤ 40 * u / q := (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega

theorem sum_cls {M : Type*} [AddCommMonoid M] (hq : 0 < q) (hk₀ : k₀ < q) (G : ℕ → M) :
    ∑ k ∈ (range (40 * u + 1)).filter (fun k => k % q = k₀), G k =
      ∑ J ∈ clsJ u q k₀, G (k₀ + J * q) := by
  refine Finset.sum_nbij' (fun k => k / q) (fun J => k₀ + J * q) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [mem_clsJ u q k₀ hq]
    have := Nat.mod_add_div k q
    rw [hk.2] at this
    rw [mul_comm] at this
    omega
  · intro J hJ
    rw [mem_clsJ u q k₀ hq] at hJ
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk₀]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have := Nat.mod_add_div k q
    rw [hk.2, mul_comm] at this
    omega
  · intro J _
    rw [Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hk₀, zero_add]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have := Nat.mod_add_div k q
    rw [hk.2, mul_comm] at this
    rw [this]

theorem prod_cls {M : Type*} [CommMonoid M] (hq : 0 < q) (hk₀ : k₀ < q) (G : ℕ → M) :
    ∏ k ∈ (range (40 * u + 1)).filter (fun k => k % q = k₀), G k =
      ∏ J ∈ clsJ u q k₀, G (k₀ + J * q) := by
  refine Finset.prod_nbij' (fun k => k / q) (fun J => k₀ + J * q) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [mem_clsJ u q k₀ hq]
    have := Nat.mod_add_div k q
    rw [hk.2, mul_comm] at this
    omega
  · intro J hJ
    rw [mem_clsJ u q k₀ hq] at hJ
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk₀]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have := Nat.mod_add_div k q
    rw [hk.2, mul_comm] at this
    omega
  · intro J _
    rw [Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hk₀, zero_add]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have := Nat.mod_add_div k q
    rw [hk.2, mul_comm] at this
    rw [this]

theorem nE_DL (hq : 0 < q) (J : ℕ) :
    (((DLl u q k₀).filter fun y => y.1 = -(2 * (J : ℤ))).map Prod.snd).sum = (ctr u q k₀ J : ℤ) := by
  unfold DLl ctr
  by_cases hD : inD u q k₀
  · have hdvd : (q : ℤ) ∣ 2 * (k₀ : ℤ) - 40 * u := Int.dvd_of_emod_eq_zero hD
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have hiff : (2 * (k₀ : ℤ) - 40 * u) / q = -(2 * (J : ℤ)) ↔ k₀ + J * q = 20 * u := by
      rw [Int.ediv_eq_iff_eq_mul_left hq0 hdvd]
      constructor
      · intro h
        have : ((k₀ + J * q : ℕ) : ℤ) = 20 * u := by push_cast; linarith
        exact_mod_cast this
      · intro h
        have : ((k₀ + J * q : ℕ) : ℤ) = ((20 * u : ℕ) : ℤ) := by rw [h]
        push_cast at this
        linarith
    rw [ite_eq_left hD]
    by_cases hc : k₀ + J * q = 20 * u
    · rw [ite_eq_left ⟨hD, hc⟩, List.filter_cons_of_pos (by simpa using hiff.2 hc)]
      simp
    · rw [ite_eq_right (fun h => hc h.2), List.filter_cons_of_neg (by simpa using fun h => hc (hiff.1 h))]
      simp
  · rw [ite_eq_right hD, ite_eq_right (fun h => hD h.1)]
    simp

theorem netE_pole (hq : 0 < q) (_hk₀ : k₀ < q) {J : ℕ} (hJ : k₀ + J * q ≤ 40 * u) :
    (localModel u q k₀).netE (-(2 * (J : ℤ))) =
      -((apole u (k₀ + J * q) : ℕ) : ℤ) + (ctr u q k₀ J : ℤ) := by
  rw [netE_split, nE_PL, nE_DL u q k₀ hq J]
  have hZ : (((ZLl u q k₀).filter
      fun y => y.1 = -(2 * (J : ℤ))).map Prod.snd).sum = 0 := by
    rw [List.filter_eq_nil_iff.2]
    · simp
    · intro x hx
      have := ZL_odd u q k₀ x hx
      simp only [decide_eq_true_eq]
      omega
  rw [hZ, add_zero]
  congr 1
  rw [Finset.sum_eq_single J]
  · simp
  · intro J' _ hJ'
    rw [ite_eq_right (by omega)]
  · intro h
    exact absurd ((mem_clsJ u q k₀ hq).2 hJ) h

theorem apole_centre (hk : 20 * u ≤ 40 * u) : apole u (20 * u) = 4 := by
  unfold apole
  split_ifs <;> omega

theorem ord_pole (hq : 0 < q) (hk₀ : k₀ < q) {J : ℕ} (hJ : k₀ + J * q ≤ 40 * u) :
    ord (localModel u q k₀) (-(2 * (J : ℤ))) + ctr u q k₀ J = apole u (k₀ + J * q) := by
  unfold ord
  rw [netE_pole u q k₀ hq hk₀ hJ]
  have h1 := apole_pos u (k₀ + J * q)
  have h2 : ctr u q k₀ J ≤ 1 := by unfold ctr; split_ifs <;> omega
  omega

theorem ord_pole_pos (hq : 0 < q) (hk₀ : k₀ < q) {J : ℕ} (hJ : k₀ + J * q ≤ 40 * u) :
    1 ≤ ord (localModel u q k₀) (-(2 * (J : ℤ))) := by
  have h := ord_pole u q k₀ hq hk₀ hJ
  have h1 := apole_pos u (k₀ + J * q)
  unfold ctr at h
  split_ifs at h with hc
  · rw [hc.2, apole_centre u (by omega)] at h
    omega
  · omega

theorem PL_mem (hq : 0 < q) {J : ℕ} (hJ : k₀ + J * q ≤ 40 * u) :
    (-(2 * (J : ℤ)), -((apole u (k₀ + J * q) : ℕ) : ℤ)) ∈ (localModel u q k₀).items := by
  rw [items_eq]
  apply List.mem_append_left
  apply List.mem_append_left
  rw [List.mem_filterMap]
  refine ⟨J, List.mem_range.2 ?_, ?_⟩
  · have := (mem_clsJ u q k₀ hq).2 hJ
    unfold clsJ at this
    exact Finset.mem_range.1 (Finset.mem_filter.1 this).1
  · simp [PLf, hJ]

theorem poleSet_eq (hq : 0 < q) (hk₀ : k₀ < q) :
    poleSet (localModel u q k₀) = (clsJ u q k₀).image fun J : ℕ => -(2 * (J : ℤ)) := by
  ext w
  simp only [poleSet, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hw, hneg⟩
    by_contra hno
    push Not at hno
    have hPL : ((((List.range (40 * u / q + 1)).filterMap (PLf u q k₀)).filter
        fun y => y.1 = w).map Prod.snd).sum = 0 := by
      rw [nE_PL]
      refine Finset.sum_eq_zero fun J hJ => ?_
      rw [ite_eq_right (hno J hJ)]
    have := netE_split u q k₀ w
    rw [hPL, zero_add] at this
    have h1 := nE_nonneg _ (ZL_nonneg u q k₀) w
    have h2 := nE_nonneg _ (DL_nonneg u q k₀) w
    omega
  · rintro ⟨J, hJ, rfl⟩
    rw [mem_clsJ u q k₀ hq] at hJ
    refine ⟨mem_posSet (PL_mem u q k₀ hq hJ), ?_⟩
    rw [netE_pole u q k₀ hq hk₀ hJ]
    have h := ord_pole_pos u q k₀ hq hk₀ hJ
    have h2 := ord_pole u q k₀ hq hk₀ hJ
    omega

theorem netE_zero_of_gt (hq : 0 < q) (_hk₀ : k₀ < q) (hn : 40 * u < k₀) :
    (localModel u q k₀).netE 0 = 0 := by
  have h0 := nE_DL u q k₀ hq 0
  simp only [Nat.cast_zero, mul_zero, neg_zero] at h0
  rw [netE_split, nE_PL, h0]
  have hZ : (((ZLl u q k₀).filter
      fun y => y.1 = 0).map Prod.snd).sum = 0 := by
    rw [List.filter_eq_nil_iff.2]
    · simp
    · intro x hx
      have := ZL_odd u q k₀ x hx
      simp only [decide_eq_true_eq]
      omega
  rw [hZ, add_zero]
  have hc : ctr u q k₀ 0 = 0 := by
    unfold ctr
    rw [ite_eq_right (fun h => by have := h.2; omega)]
  rw [hc, Finset.sum_eq_zero]
  · simp
  · intro J hJ
    rw [mem_clsJ u q k₀ hq] at hJ
    rw [ite_eq_right]
    intro h
    have : J = 0 := by omega
    subst this
    omega

theorem netE_zero_nonpos (hq : 0 < q) (hk₀ : k₀ < q) : (localModel u q k₀).netE 0 ≤ 0 := by
  by_cases h : k₀ ≤ 40 * u
  · have h0 : k₀ + 0 * q ≤ 40 * u := by omega
    have := netE_pole u q k₀ hq hk₀ h0
    simp only [Nat.cast_zero, mul_zero, neg_zero] at this
    rw [this]
    have h1 := ord_pole_pos u q k₀ hq hk₀ h0
    have h2 := ord_pole u q k₀ hq hk₀ h0
    simp only [Nat.cast_zero, mul_zero, neg_zero] at h1 h2
    unfold ord at h1 h2
    rw [this] at h1 h2
    omega
  · rw [netE_zero_of_gt u q k₀ hq hk₀ (by omega)]


theorem pairs_eq : (localModel u q k₀).pairs = (List.range (40 * u / q + 1)).flatMap (fun j =>
      if k₀ + j * q ≤ 40 * u ∧ (k₀ : ℤ) + j * q - 20 * u ≠ 0 then
        ((List.range (((k₀ : ℤ) + j * q - 20 * u).natAbs / q + 1)).map
            (fun a : ℕ => (a : ℤ))).filterMap fun t : ℤ =>
          if ((2 * t + 1) * q : ℤ) < 2 * |(k₀ : ℤ) + j * q - 20 * u| then
            some (-(2 * (j : ℤ)),
              -(2 * (j : ℤ)) + ((k₀ : ℤ) + j * q - 20 * u).sign * (2 * t + 1),
              ((k₀ : ℤ) + j * q - 20 * u).sign)
          else none
      else []) := by
  unfold localModel
  simp only [bind_range_cast]

theorem pairs_sum {M : Type*} [AddCommMonoid M] (hq : 0 < q) (F : ℤ × ℤ × ℤ → M) :
    ((localModel u q k₀).pairs.map F).sum = ∑ J ∈ clsJ u q k₀,
      ∑ t ∈ range (((k₀ : ℤ) + J * q - 20 * u).natAbs / q + 1),
        if ((2 * t + 1) * q : ℤ) < 2 * |(k₀ : ℤ) + J * q - 20 * u| then
          F (-(2 * (J : ℤ)), -(2 * (J : ℤ)) + ((k₀ : ℤ) + J * q - 20 * u).sign * (2 * t + 1),
            ((k₀ : ℤ) + J * q - 20 * u).sign) else 0 := by
  rw [pairs_eq, sum_flatMap_range]
  unfold clsJ
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun J _ => ?_
  by_cases h1 : k₀ + J * q ≤ 40 * u
  · rw [ite_eq_left h1]
    by_cases h2 : (k₀ : ℤ) + J * q - 20 * u = 0
    · rw [ite_eq_right (fun h => h.2 h2)]
      simp only [List.map_nil, List.sum_nil]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [ite_eq_right]
      rw [h2, abs_zero, mul_zero, not_lt]
      positivity
    · rw [ite_eq_left ⟨h1, h2⟩, List.filterMap_map, sum_filterMap_range]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Function.comp_apply]
      split_ifs <;> simp
  · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]
    simp

theorem pairs_mem (hq : 0 < q) {pr : ℤ × ℤ × ℤ} (hpr : pr ∈ (localModel u q k₀).pairs) :
    ∃ J : ℕ, J ∈ clsJ u q k₀ ∧ ∃ t : ℕ,
      ((2 * (t : ℤ) + 1) * q : ℤ) < 2 * |(k₀ : ℤ) + (J : ℤ) * q - 20 * u| ∧
      pr = (-(2 * (J : ℤ)), -(2 * (J : ℤ)) + ((k₀ : ℤ) + (J : ℤ) * q - 20 * u).sign * (2 * t + 1),
        ((k₀ : ℤ) + (J : ℤ) * q - 20 * u).sign) := by
  rw [pairs_eq, List.mem_flatMap] at hpr
  obtain ⟨J, -, hmem⟩ := hpr
  split_ifs at hmem with h
  · rw [List.filterMap_map, List.mem_filterMap] at hmem
    obtain ⟨t, -, ht⟩ := hmem
    simp only [Function.comp_apply] at ht
    split_ifs at ht with h2
    refine ⟨J, (mem_clsJ u q k₀ hq).2 h.1, t, h2, (Option.some.inj ht).symm⟩
  · simp at hmem

end Dict

/-- `oddBetween d` as the image of `range |d|`. -/
theorem oddBetween_eq (d : ℤ) :
    oddBetween d = (range d.natAbs).image (fun l : ℕ => d.sign * (2 * (l : ℤ) + 1)) := by
  unfold oddBetween
  rcases lt_trichotomy d 0 with h | rfl | h
  · rw [ite_eq_right (by omega), Int.sign_eq_neg_one_of_neg h, show (-d).toNat = d.natAbs by omega]
    congr 1
    funext l
    ring
  · simp
  · rw [ite_eq_left h.le, Int.sign_eq_one_of_pos h, show d.toNat = d.natAbs by omega]
    congr 1
    funext l
    ring

/-- If `q = 2r+1` divides the odd number `2l+1`, the cofactor is odd: `2l+1 = q (2t+1)`. -/
theorem odd_cofactor {r l : ℕ} (h : ((2 * r + 1 : ℕ) : ℤ) ∣ 2 * (l : ℤ) + 1) :
    ∃ t : ℕ, 2 * l + 1 = (2 * r + 1) * (2 * t + 1) := by
  obtain ⟨m, hm⟩ := h
  have hm0 : 0 ≤ m := by
    by_contra hneg
    have h1 : ((2 * r + 1 : ℕ) : ℤ) * m < 0 := mul_neg_of_pos_of_neg (by positivity) (by omega)
    omega
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' := ⟨m.toNat, by omega⟩
  have hm' : 2 * l + 1 = (2 * r + 1) * m' := by exact_mod_cast hm
  have hodd : m' % 2 = 1 := by
    by_contra hev
    have h2 : m' = 2 * (m' / 2) := by omega
    rw [h2] at hm'
    have h3 : (2 * l + 1) % 2 = ((2 * r + 1) * (2 * (m' / 2))) % 2 := by rw [hm']
    simp [Nat.mul_mod, Nat.add_mod] at h3
  refine ⟨m' / 2, ?_⟩
  rw [hm']
  congr 1
  omega

theorem sum_oddBetween_dvd {M : Type*} [AddCommMonoid M] (q : ℕ) (hq : Odd q) (d : ℤ)
    (G : ℤ → M) :
    ∑ o ∈ (oddBetween d).filter (fun o => (q : ℤ) ∣ o), G o =
      ∑ t ∈ range (d.natAbs / q + 1),
        if ((2 * t + 1) * q : ℤ) < 2 * |d| then G (d.sign * (2 * t + 1) * q) else 0 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [oddBetween]
  obtain ⟨r, rfl⟩ := hq
  have hsg : d.sign = 1 ∨ d.sign = -1 := by
    rcases lt_or_gt_of_ne hd with h | h
    · exact Or.inr (Int.sign_eq_neg_one_of_neg h)
    · exact Or.inl (Int.sign_eq_one_of_pos h)
  have hdvd : ∀ z : ℤ, ((2 * r + 1 : ℕ) : ℤ) ∣ d.sign * z ↔ ((2 * r + 1 : ℕ) : ℤ) ∣ z := by
    intro z
    rcases hsg with h | h <;> rw [h] <;> simp
  have habs : |d| = (d.natAbs : ℤ) := Int.abs_eq_natAbs d
  have hinj : Function.Injective (fun l : ℕ => d.sign * (2 * (l : ℤ) + 1)) := by
    intro x y h
    simp only at h
    rcases hsg with hs | hs <;> rw [hs] at h <;> omega
  -- the map `t ↦ l = t q + r` (so `2l + 1 = (2t+1) q`)
  have hmul : ∀ t : ℕ, 2 * (t * (2 * r + 1) + r) + 1 = (2 * t + 1) * (2 * r + 1) := by
    intro t; ring
  rw [oddBetween_eq, Finset.filter_image, Finset.sum_image (fun x _ y _ h => hinj h),
    ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun t => t * (2 * r + 1) + r) (fun l => (2 * l + 1) / (2 * r + 1) / 2)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    have e : ((2 * (t * (2 * r + 1) + r) + 1 : ℕ) : ℤ) = (2 * t + 1) * ((2 * r + 1 : ℕ) : ℤ) := by
      rw [hmul]; push_cast; ring
    refine ⟨?_, ?_⟩
    · have h2 := ht.2
      rw [habs, ← e] at h2
      omega
    · rw [hdvd]
      exact ⟨2 * t + 1, by push_cast; ring⟩
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
    obtain ⟨hl1, hl2⟩ := hl
    rw [hdvd] at hl2
    obtain ⟨t, ht⟩ := odd_cofactor hl2
    rw [ht, Nat.mul_div_cancel_left _ (by omega), show (2 * t + 1) / 2 = t by omega]
    have e := hmul t
    have hlP : t * (2 * r + 1) + r = l := by nlinarith
    refine ⟨?_, ?_⟩
    · have h1 : t * (2 * r + 1) ≤ d.natAbs := by omega
      have := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * r + 1)).2 h1
      omega
    · rw [habs]
      have e2 : ((2 * t + 1 : ℕ) : ℤ) * ((2 * r + 1 : ℕ) : ℤ) = ((2 * l + 1 : ℕ) : ℤ) := by
        rw [ht]; push_cast; ring
      push_cast at e2 ⊢
      have : (l : ℤ) < d.natAbs := by exact_mod_cast hl1
      linarith
  · intro t _
    rw [hmul t, Nat.mul_div_cancel _ (by omega)]
    omega
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl
    obtain ⟨_, hl2⟩ := hl
    rw [hdvd] at hl2
    obtain ⟨t, ht⟩ := odd_cofactor hl2
    rw [ht, Nat.mul_div_cancel_left _ (by omega), show (2 * t + 1) / 2 = t by omega]
    have e := hmul t
    nlinarith
  · intro t _
    congr 1
    push_cast
    ring

/-! ## 9. Lemma 4.2: `q`-integrality of the local data

For `q > 2x + 2` (`80u + 2q < q²`) every item position of `localModel u q k₀` differs from a pole
position `-2J` (a class pole, or `J = 0`) by an integer prime to `q` (`items_sep`), so every factor
`lin ((w - p)/2) e` of `taylorAt` is `q`-integral; the same holds for the extra kernel item and for
the factor `(b - ε)^{-5}` of `gSer` (`2t + 1 < q`). -/

section Integrality

variable {u q k₀ : ℕ}


/-- `taylorAt` as a list product of `lin` factors. -/
theorem taylorAt_eq_list (τ : LocalType) (w : ℤ) :
    taylorAt τ w =
      (τ.items.map fun x => if x.1 = w then (1 : PowerSeries ℚ) else
        lin (((w : ℚ) - x.1) / 2) x.2).prod := by
  unfold taylorAt
  rw [list_prod_filter_map]
  congr 1
  apply List.map_congr_left
  intro x _
  by_cases h : x.1 = w
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false]
    unfold lin
    rw [inv_div]

theorem PSV_taylorAt_of {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (τ : LocalType) (w : ℤ)
    (h : ∀ x ∈ τ.items, x.1 ≠ w → ¬ (q : ℤ) ∣ (w - x.1)) : PSV q 0 (taylorAt τ w) := by
  rw [taylorAt_eq_list]
  apply PSV.list_prod
  intro f hf
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
  split_ifs with hxw
  · exact PSV.one
  · apply PSV_lin
    have := unit_half hq2 (h x hx hxw)
    push_cast at this
    exact this

/-- All item positions differ from a pole position `-2J` (`k = k₀ + J q ≤ max(n, q-1)`) by an
integer prime to `q` (proof Lemma 4.2). -/
theorem items_sep {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (hsq : 80 * u + 2 * q < q ^ 2) {J : ℕ} (hJ : k₀ + J * q ≤ 40 * u ∨ J = 0) :
    ∀ x ∈ (localModel u q k₀).items, x.1 ≠ -(2 * (J : ℤ)) →
      ¬ (q : ℤ) ∣ (-(2 * (J : ℤ)) - x.1) := by
  have hq0 : 0 < q := hq.pos
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  -- `k = k₀ + J q` is at most `max(n, q - 1)`
  have hk : (k₀ : ℤ) + J * q ≤ 40 * u ∨ (k₀ : ℤ) + J * q ≤ q - 1 := by
    rcases hJ with h | h
    · left; exact_mod_cast h
    · right; subst h; push_cast; omega
  have hn : (80 * u : ℤ) < (q : ℤ) ^ 2 := by exact_mod_cast (by omega : 80 * u < q ^ 2)
  have hq2' : (2 * (q : ℤ)) < (q : ℤ) ^ 2 := by exact_mod_cast (by omega : 2 * q < q ^ 2)
  have hJ0 : (0 : ℤ) ≤ J := by positivity
  have hk0 : (0 : ℤ) ≤ (k₀ : ℤ) + J * q := by positivity
  have hk2 : 2 * ((k₀ : ℤ) + J * q) < (q : ℤ) ^ 2 := by
    rcases hk with h | h <;> linarith
  intro x hx hxw
  apply not_dvd_of_small (by omega)
  rw [items_eq, List.mem_append, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · -- a pole `-2J'`
    obtain ⟨J', -, hJ'⟩ := List.mem_filterMap.1 hx
    unfold PLf at hJ'
    split_ifs at hJ' with hle
    cases hJ'
    have hle' : (k₀ : ℤ) + J' * q ≤ 40 * u := by exact_mod_cast hle
    have hJ'0 : (0 : ℤ) ≤ (k₀ : ℤ) + J' * q := by positivity
    have e : (q : ℤ) * |(-(2 * (J : ℤ)) - -(2 * (J' : ℤ)))| =
        |2 * (((k₀ : ℤ) + J' * q) - ((k₀ : ℤ) + J * q))| := by
      rw [← abs_of_nonneg (by positivity : (0 : ℤ) ≤ q), ← abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q)]
      congr 1
      ring
    rw [e, abs_lt]
    constructor <;> linarith
  · -- a zero `-(2t - 1)`
    unfold ZLl at hx
    rw [List.filterMap_map, List.mem_filterMap] at hx
    obtain ⟨t, -, ht⟩ := hx
    simp only [Function.comp_apply] at ht
    unfold ZLf at ht
    split_ifs at ht with hc
    cases ht
    obtain ⟨r, hr⟩ := hq.odd_of_ne_two hq2
    have hqr : ((q : ℤ) + 1) / 2 = r + 1 := by rw [hr]; push_cast; omega
    rw [hqr] at hc
    obtain ⟨hc1, hc2, -⟩ := hc
    have e : (q : ℤ) * |(-(2 * (J : ℤ)) - -(2 * (t : ℤ) - 1))| =
        |2 * ((k₀ : ℤ) + t * q - (r + 1)) + 1 - 2 * ((k₀ : ℤ) + J * q)| := by
      rw [← abs_of_nonneg (by positivity : (0 : ℤ) ≤ q), ← abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q)]
      congr 1
      have : (q : ℤ) = 2 * r + 1 := by rw [hr]; push_cast; ring
      rw [this]
      ring
    rw [e, abs_lt]
    constructor <;> linarith
  · -- the δ-zero
    unfold DLl at hx
    split_ifs at hx with hD
    · rw [List.mem_singleton] at hx
      subst hx
      have hdvd : (q : ℤ) ∣ 2 * (k₀ : ℤ) - 40 * u := Int.dvd_of_emod_eq_zero hD
      obtain ⟨m, hm⟩ := hdvd
      have hq0' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hdiv : (2 * (k₀ : ℤ) - 40 * u) / q = m := by
        rw [hm, Int.mul_ediv_cancel_left _ hq0']
      simp only at hxw ⊢
      rw [hdiv] at hxw ⊢
      have e : (q : ℤ) * |(-(2 * (J : ℤ)) - m)| = |40 * u - 2 * ((k₀ : ℤ) + J * q)| := by
        rw [← abs_of_nonneg (by positivity : (0 : ℤ) ≤ q), ← abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q)]
        congr 1
        linear_combination hm
      rw [e, abs_lt]
      constructor <;> linarith
    · simp at hx

theorem PSV_taylorAt_model (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (hsq : 80 * u + 2 * q < q ^ 2) {J : ℕ} (hJ : k₀ + J * q ≤ 40 * u ∨ J = 0) :
    haveI : Fact q.Prime := ⟨hq⟩
    PSV q 0 (taylorAt (localModel u q k₀) (-(2 * (J : ℤ)))) := by
  have : Fact q.Prime := ⟨hq⟩
  exact PSV_taylorAt_of hq2 _ _ (items_sep hq hq2 hk₀ hsq hJ)

theorem PSV_taylorAt_ker (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (hsq : 80 * u + 2 * q < q ^ 2) (j : ℕ) {J : ℕ} (hJ : k₀ + J * q ≤ 40 * u ∨ J = 0) :
    haveI : Fact q.Prime := ⟨hq⟩
    PSV q 0 (taylorAt (kerType (localModel u q k₀) j) (-(2 * (J : ℤ)))) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [kerType_taylorAt]
  refine (PSV_taylorAt_model hq hq2 hk₀ hsq hJ).mul' (M' := 0) (N := 0) ?_ (by simp)
  split_ifs with h0
  · exact PSV.one
  · apply PSV_lin
    have hJ0 : J ≠ 0 := by rintro rfl; simp at h0
    have hJq : J * q ≤ 40 * u := by
      rcases hJ with h | h
      · omega
      · exact absurd h hJ0
    have hJlt : J < q := by
      by_contra hge
      push Not at hge
      have : q * q ≤ J * q := Nat.mul_le_mul_right q hge
      nlinarith
    have e : (((-(2 * (J : ℤ)) : ℤ) : ℚ) / 2) = ((-(J : ℤ) : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    apply unit_int
    intro hd
    have : (q : ℤ) ∣ (J : ℤ) := by
      have := dvd_neg.1 hd
      exact this
    have h2 : q ∣ J := by exact_mod_cast this
    have := Nat.le_of_dvd (by omega) h2
    omega

theorem PSV_gfac {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (wk we : ℤ)
    (h : ¬ (q : ℤ) ∣ (we - wk)) :
    PSV q 0 (C ((((we : ℚ) - wk) / 2) ^ (-5 : ℤ)) * bser (-2 / ((we : ℚ) - wk)) (-5)) := by
  have hβ : padicNorm q (((we - wk : ℤ) : ℚ) / 2) = 1 := unit_half hq2 h
  push_cast at hβ
  refine (PSV.ofC (valGe_of_unit (unit_zpow hβ _))).mul' (PSV_bser ?_ _) (by simp)
  have : (-2 / ((we : ℚ) - wk)) = -(((we : ℚ) - wk) / 2)⁻¹ := by rw [inv_div, neg_div]
  rw [this]
  exact valGe_neg (valGe_of_unit (unit_inv hβ))

theorem PSV_gSer_model (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (hsq : 80 * u + 2 * q < q ^ 2) {pr : ℤ × ℤ × ℤ} (hpr : pr ∈ (localModel u q k₀).pairs) :
    haveI : Fact q.Prime := ⟨hq⟩
    PSV q 0 (gSer (localModel u q k₀) pr.1 pr.2.1) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨J, hJ, t, ht, rfl⟩ := pairs_mem u q k₀ hq.pos hpr
  rw [mem_clsJ u q k₀ hq.pos] at hJ
  have hJ' : (k₀ : ℤ) + J * q ≤ 40 * u := by exact_mod_cast hJ
  have hk0 : (0 : ℤ) ≤ (k₀ : ℤ) + J * q := by positivity
  set d : ℤ := (k₀ : ℤ) + (J : ℤ) * q - 20 * u with hd
  have hdn : |d| ≤ 20 * u := abs_le.2 ⟨by omega, by omega⟩
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, abs_zero, mul_zero] at ht
    have : (0 : ℤ) ≤ (2 * (t : ℤ) + 1) * q := by positivity
    omega
  have hlt : 2 * (t : ℤ) + 1 < q := by
    have h1 : (2 * (t : ℤ) + 1) * q < q * q := by
      have : (80 * u : ℤ) < (q : ℤ) ^ 2 := by exact_mod_cast (by omega : 80 * u < q ^ 2)
      nlinarith
    exact lt_of_mul_lt_mul_right h1 (by positivity)
  have hsg : d.sign = 1 ∨ d.sign = -1 := by
    rcases lt_or_gt_of_ne hd0 with h | h
    · exact Or.inr (Int.sign_eq_neg_one_of_neg h)
    · exact Or.inl (Int.sign_eq_one_of_pos h)
  have hnd : ¬ (q : ℤ) ∣ ((-(2 * (J : ℤ)) + d.sign * (2 * t + 1)) - -(2 * (J : ℤ))) := by
    rw [show ((-(2 * (J : ℤ)) + d.sign * (2 * t + 1)) - -(2 * (J : ℤ))) =
      d.sign * (2 * t + 1) by ring]
    intro hdvd
    have h2 : (q : ℤ) ∣ 2 * (t : ℤ) + 1 := by
      rcases hsg with h | h
      · rw [h, one_mul] at hdvd; exact hdvd
      · rw [h, neg_one_mul, dvd_neg] at hdvd; exact hdvd
    have := Int.le_of_dvd (by positivity) h2
    omega
  unfold gSer
  exact (PSV_taylorAt_model hq hq2 hk₀ hsq (Or.inl hJ)).mul' (PSV_gfac hq2 _ _ hnd) (by simp)

end Integrality

/-! ## 10. Truncation of the outer factor at the centre of the disc

`Û = Onum / Oden` is `q`-integral at every point `-k₀ - J q` of the disc (`PSV_Uhat`), with unit
denominator (`constantCoeff_substPS_Oden`).  With `T(t) = ∑_{m<M} F_m (t + k₀)^m` the Taylor
truncation of `Û` at `-k₀`, `Onum - T·Oden = (t + k₀)^M S(t + k₀)` with `S` `q`-integral, hence
`rescale q (Û(-k₀ - Jq + ε)) ≡ ∑_{m<M} F_m q^m (ε - J)^m (mod q^M)` coefficientwise
(`trunc_exists`). -/

section Truncation

variable {u q k₀ : ℕ}


theorem unit_prod {q : ℕ} [Fact q.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, padicNorm q (f i) = 1) : padicNorm q (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unit_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `substPS y (P.comp (X + C c)) = substPS (y + c) P`. -/
theorem substPS_comp_X_add_C (y c : ℚ) (P : Polynomial ℚ) :
    substPS y (P.comp (Polynomial.X + Polynomial.C c)) = substPS (y + c) P := by
  have h : (substPS y).comp (Polynomial.compRingHom (Polynomial.X + Polynomial.C c)) =
      substPS (y + c) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [substPS]
    · simp only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.X_comp]
      rw [substPS_X_add_C, substPS_X]
  exact RingHom.congr_fun h P

/-- `j ≢ k₀ (mod q)` gives a `q`-unit `j - k₀ - J q`. -/
theorem unit_out_pole {q k₀ : ℕ} [Fact q.Prime] (hk₀ : k₀ < q) {j : ℕ} (hj : j % q ≠ k₀)
    (J : ℕ) : padicNorm q (-((k₀ + J * q : ℕ) : ℚ) + j) = 1 := by
  have e : (-((k₀ + J * q : ℕ) : ℚ) + j) = (((j : ℤ) - k₀ - J * q : ℤ) : ℚ) := by push_cast; ring
  rw [e]
  apply unit_int
  intro hdvd
  apply hj
  have h1 : (q : ℤ) ∣ (j : ℤ) - k₀ := by
    have : (j : ℤ) - k₀ = ((j : ℤ) - k₀ - J * q) + J * q := by ring
    rw [this]
    exact dvd_add hdvd (dvd_mul_left _ _)
  have h2 : k₀ ≡ j [MOD q] := Nat.modEq_iff_dvd.2 h1
  unfold Nat.ModEq at h2
  rw [← h2, Nat.mod_eq_of_lt hk₀]

theorem PSV_Oden {u q k₀ : ℕ} [Fact q.Prime] (z : ℤ) :
    PSV q 0 (substPS (z : ℚ) (Oden u q k₀)) := by
  unfold Oden
  rw [map_prod]
  refine PSV.prod _ _ fun j _ => ?_
  rw [map_pow, substPS_X_add_C]
  refine PSV.pow ((PSV.ofC ?_).add PSV.ofX) _
  have : ((z : ℚ) + j) = ((z + j : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact valGe_int _

theorem constantCoeff_substPS_Oden {u q k₀ : ℕ} [Fact q.Prime] (hk₀ : k₀ < q) (J : ℕ) :
    padicNorm q (constantCoeff (substPS (-((k₀ + J * q : ℕ) : ℚ)) (Oden u q k₀))) = 1 := by
  unfold Oden
  rw [map_prod, map_prod]
  apply unit_prod
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [map_pow, map_pow, substPS_X_add_C, map_add, constantCoeff_C, constantCoeff_X, add_zero]
  exact unit_zpow (unit_out_pole hk₀ hj.2 J) _ |>.symm.trans (by rw [zpow_natCast]) |>.symm

theorem PSV_Oden_inv {u q k₀ : ℕ} [Fact q.Prime] (hk₀ : k₀ < q) (J : ℕ) :
    PSV q 0 (substPS (-((k₀ + J * q : ℕ) : ℚ)) (Oden u q k₀))⁻¹ := by
  apply PSV.inv _ (constantCoeff_substPS_Oden hk₀ J)
  have := PSV_Oden (u := u) (q := q) (k₀ := k₀) (-((k₀ + J * q : ℕ) : ℤ))
  push_cast at this ⊢
  exact this

theorem PSV_Onum {u q k₀ : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (z : ℤ) :
    PSV q 0 (substPS (z : ℚ) (Onum u q k₀)) := by
  unfold Onum
  rw [map_mul, map_mul, map_prod, substPS_C]
  have h1 : PSV q 0 (C (2 : ℚ)) := PSV.ofC (by simpa using valGe_int (q := q) 2)
  have h2 : PSV q 0 (substPS (z : ℚ)
      (if inD u q k₀ then 1 else Polynomial.X + Polynomial.C ((20 * u : ℕ) : ℚ))) := by
    split_ifs
    · rw [map_one]; exact PSV.one
    · rw [substPS_X_add_C]
      refine (PSV.ofC ?_).add PSV.ofX
      have : ((z : ℚ) + ((20 * u : ℕ) : ℚ)) = ((z + 20 * u : ℤ) : ℚ) := by push_cast; ring
      rw [this]; exact valGe_int _
  refine (h1.mul' h2 (N := 0) (by simp)).mul' (M' := 0) (N := 0) ?_ (by simp)
  · refine PSV.prod _ _ fun m _ => ?_
    rw [map_prod]
    refine PSV.prod _ _ fun c _ => ?_
    rw [substPS_X_add_C]
    refine (PSV.ofC ?_).add PSV.ofX
    have : ((z : ℚ) + (1 / 2 + (c : ℚ))) = ((2 * z + 2 * c + 1 : ℤ) : ℚ) / 2 := by
      push_cast; ring
    rw [this]
    exact valGe_half hq2 _

theorem PSV_Uhat {u q k₀ : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hk₀ : k₀ < q) (J : ℕ) :
    PSV q 0 (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ))) := by
  unfold Uhat
  refine (?_ : PSV q 0 _).mul' (PSV_Oden_inv hk₀ J) (by simp)
  have := PSV_Onum (u := u) (k₀ := k₀) hq2 (-((k₀ + J * q : ℕ) : ℤ))
  push_cast at this ⊢
  exact this

theorem rescale_C_add_X_pow (q a : ℚ) (m : ℕ) :
    rescale q ((C (q * a) + X : PowerSeries ℚ) ^ m) = C (q ^ m) * (C a + X) ^ m := by
  rw [map_pow, map_add, rescale_C', rescale_X, map_pow, ← mul_pow]
  congr 1
  rw [map_mul]
  ring

/-- **Truncation at the centre of the disc** (general form).  Let `A, B ∈ ℚ[t]` with
`A(-k₀+ε)/B(-k₀+ε)` `q`-integral and `B(-k₀ - Jq + ε)` `q`-integral with unit constant term at
every point of the disc.  With `F_m = [ε^m] (A/B)(-k₀+ε)`, at every `J`,
`rescale q ((A/B)(-k₀ - Jq + ε)) ≡ ∑_{m<M} F_m q^m (ε - J)^m (mod q^M)` coefficientwise.
(For `FarPart7`: take `A/B = Û · g_{j,ξ}`.) -/
theorem trunc_general {q k₀ : ℕ} [hqF : Fact q.Prime] (A B : Polynomial ℚ) (M : ℕ)
    (hF : PSV q 0 (substPS (-(k₀ : ℚ)) A * (substPS (-(k₀ : ℚ)) B)⁻¹))
    (hBu : ∀ J : ℕ, padicNorm q (constantCoeff (substPS (-((k₀ + J * q : ℕ) : ℚ)) B)) = 1)
    (hBJ : ∀ J : ℕ, PSV q 0 (substPS (-((k₀ + J * q : ℕ) : ℚ)) B)) :
    ∃ F : ℕ → ℚ, ∀ J : ℕ,
      PSV q M (rescale (q : ℚ) (substPS (-((k₀ + J * q : ℕ) : ℚ)) A *
          (substPS (-((k₀ + J * q : ℕ) : ℚ)) B)⁻¹) -
        ∑ m ∈ range M, C (F m * (q : ℚ) ^ m) * (C (-(J : ℚ)) + X) ^ m) := by
  have hq := hqF.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set Fs : PowerSeries ℚ := substPS (-(k₀ : ℚ)) A * (substPS (-(k₀ : ℚ)) B)⁻¹ with hFs
  set T : Polynomial ℚ := ∑ m ∈ range M, Polynomial.C (coeff m Fs) *
    (Polynomial.X + Polynomial.C (k₀ : ℚ)) ^ m with hT
  set P : Polynomial ℚ := A - T * B with hP
  have hcast0 : (-((k₀ + 0 * q : ℕ) : ℚ)) = -(k₀ : ℚ) := by simp
  have hB0 : constantCoeff (substPS (-(k₀ : ℚ)) B) ≠ 0 := by
    have := hBu 0
    rw [hcast0] at this
    exact unit_ne_zero this
  -- at the centre: `substPS (-k₀) T` is the truncation of `Fs`
  have hT0 : substPS (-(k₀ : ℚ)) T = ∑ m ∈ range M, C (coeff m Fs) * X ^ m := by
    rw [hT, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, substPS_C, map_pow, substPS_X_add_C, neg_add_cancel, map_zero, zero_add]
  have hP0 : substPS (-(k₀ : ℚ)) P =
      (Fs - ∑ m ∈ range M, C (coeff m Fs) * X ^ m) * substPS (-(k₀ : ℚ)) B := by
    rw [hP, map_sub, map_mul, hT0, sub_mul]
    congr 1
    rw [hFs, mul_assoc, PowerSeries.inv_mul_cancel _ hB0, mul_one]
  -- low coefficients vanish, the others are `q`-integral
  have hlow : ∀ i < M, coeff i (substPS (-(k₀ : ℚ)) P) = 0 := by
    intro i hi
    rw [hP0, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp1 : p.1 < M := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      omega
    rw [map_sub, map_sum]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single p.1 (fun b _ hb => ite_eq_right (Ne.symm hb))
      (fun h => absurd (Finset.mem_range.2 hp1) h), ite_eq_left rfl, sub_self, zero_mul]
  have hPint : PSV q 0 (substPS (-(k₀ : ℚ)) P) := by
    rw [hP0]
    have hT' : PSV q 0 (∑ m ∈ range M, C (coeff m Fs) * X ^ m) := by
      refine PSV.sum _ _ fun m _ => ?_
      have := (PSV.ofC (hF m)).mul' (PSV.pow (PSV.ofX (q := q)) m) (N := 0) (by simp)
      exact this
    have hB' : PSV q 0 (substPS (-(k₀ : ℚ)) B) := by
      have := hBJ 0
      rw [hcast0] at this
      exact this
    exact (hF.sub hT').mul' hB' (by simp)
  -- `P = (t + k₀)^M · S(t + k₀)` with `S` `q`-integral
  set Q := P.comp (Polynomial.X - Polynomial.C (k₀ : ℚ)) with hQ
  have hQc : ∀ i, Q.coeff i = coeff i (substPS (-(k₀ : ℚ)) P) := by
    intro i
    rw [← Polynomial.coeff_coe, hQ, coe_comp_eq_substPS]
  obtain ⟨S, hS⟩ : Polynomial.X ^ M ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [hQc]
    exact hlow d hd
  have hSint : ∀ i, ValGe q 0 (S.coeff i) := by
    intro i
    have := hQc (i + M)
    rw [hS, Polynomial.coeff_X_pow_mul] at this
    rw [this]
    exact hPint _
  have hPS : P = (Polynomial.X + Polynomial.C (k₀ : ℚ)) ^ M *
      S.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)) := by
    have h1 : P = Q.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)) := by
      rw [hQ, Polynomial.comp_assoc]
      simp
    rw [h1, hS, Polynomial.mul_comp, Polynomial.X_pow_comp]
  clear_value Fs
  refine ⟨fun m => coeff m Fs, fun J => ?_⟩
  set y : ℚ := -((k₀ + J * q : ℕ) : ℚ) with hy
  have hyk : y + k₀ = (q : ℚ) * (-(J : ℚ)) := by rw [hy]; push_cast; ring
  have hBy : constantCoeff (substPS y B) ≠ 0 := unit_ne_zero (hBu J)
  -- the difference `(A/B)(y) - T(y) = P(y)/B(y)`
  have hdiff : substPS y A * (substPS y B)⁻¹ - substPS y T =
      (C (y + k₀) + X) ^ M * substPS (y + k₀) S * (substPS y B)⁻¹ := by
    have hPy : substPS y P = (C (y + k₀) + X) ^ M * substPS (y + k₀) S := by
      rw [hPS, map_mul, map_pow, substPS_X_add_C, substPS_comp_X_add_C]
    rw [← hPy, hP, map_sub, map_mul, sub_mul, mul_assoc (substPS y T),
      PowerSeries.mul_inv_cancel _ hBy, mul_one]
  have hTy : rescale (q : ℚ) (substPS y T) =
      ∑ m ∈ range M, C (coeff m Fs * (q : ℚ) ^ m) * (C (-(J : ℚ)) + X) ^ m := by
    rw [hT, map_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, substPS_C, map_mul, rescale_C', map_pow, substPS_X_add_C, hyk,
      rescale_C_add_X_pow, map_mul]
    ring
  rw [← hTy, ← map_sub, hdiff, map_mul, map_mul, hyk, rescale_C_add_X_pow]
  have h1 : PSV q M (C ((q : ℚ) ^ M) * (C (-(J : ℚ)) + X) ^ M) := by
    have hc : ValGe q (M : ℤ) ((q : ℚ) ^ M) := by rw [← zpow_natCast]; exact valGe_qzpow _
    have hp : PSV q 0 ((C (-(J : ℚ)) + X) ^ M) :=
      PSV.pow ((PSV.ofC (by simpa using valGe_int (q := q) (-(J : ℤ)))).add PSV.ofX) M
    have := PSV.C_mul hc hp
    simpa using this
  have h2 : PSV q 0 (rescale (q : ℚ) (substPS ((q : ℚ) * (-(J : ℚ))) S)) := by
    refine PSV.resc (PSV_substPS ?_ S hSint) (valGe_nat q)
    have : ((q : ℚ) * (-(J : ℚ))) = ((-(q * J : ℤ)) : ℚ) := by push_cast; ring
    rw [this]; exact valGe_int _
  have h3 : PSV q 0 (rescale (q : ℚ) (substPS y B)⁻¹) :=
    PSV.resc (PSV.inv (hBJ J) (hBu J)) (valGe_nat q)
  exact (h1.mul' h2 (N := (M : ℤ)) (by simp)).mul' h3 (N := (M : ℤ)) (by simp)

/-- **Truncation of `Û`** (the case `A/B = Onum/Oden`). -/
theorem trunc_exists (u q k₀ : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (M : ℕ) :
    haveI : Fact q.Prime := ⟨hq⟩
    ∃ F : ℕ → ℚ, ∀ J : ℕ,
      PSV q M (rescale (q : ℚ) (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ))) -
        ∑ m ∈ range M, C (F m * (q : ℚ) ^ m) * (C (-(J : ℚ)) + X) ^ m) := by
  have : Fact q.Prime := ⟨hq⟩
  have hF : PSV q 0 (substPS (-(k₀ : ℚ)) (Onum u q k₀) * (substPS (-(k₀ : ℚ)) (Oden u q k₀))⁻¹) := by
    have := PSV_Uhat (u := u) hq2 hk₀ 0
    simp only [zero_mul, add_zero] at this
    exact this
  have hBJ : ∀ J : ℕ, PSV q 0 (substPS (-((k₀ + J * q : ℕ) : ℚ)) (Oden u q k₀)) := by
    intro J
    have := PSV_Oden (u := u) (q := q) (k₀ := k₀) (-((k₀ + J * q : ℕ) : ℤ))
    push_cast at this ⊢
    exact this
  exact trunc_general (Onum u q k₀) (Oden u q k₀) M hF (fun J => constantCoeff_substPS_Oden hk₀ J)
    hBJ



end Truncation

/-! ## 11. The per-pole factorisation (proof Lemma 4.1)

Step A (`Gser_split`, `Rser_split`): split the linear factors of `G_k(ε) = ε^{a_k} R_n(-k + ε)` into
the outer factor `Û(-k + ε) = Uhat` and the in-disc factors `Inum · Iden⁻¹` (δ-zero if `inD`,
zeros `-1/2 - c` with `inZ c`, the other class poles).  Step B (`in_part`): the in-disc factors
equal `q^{E - netE w} ε^{ctr} τ_k(ε/q)`, item list by item list: poles (`PL_part`, via
`prod_cls_erase`), zeros (`ZL_part`, via the reindexing `prod_ZL_reindex` `t ↦ c_t` and the
multiplicity regrouping `prod_block_regroup`), δ (`DL_part`, the centre case gives `ε^{ctr}`);
the powers of `q` come out of `rescale_taylorAt`. -/

section FactorAux

variable {u q k₀ : ℕ}

/-- Regrouping the numerator blocks by multiplicity: `∏_m ∏_{c ∈ C_m, P c} f c = ∏_{c, P c} f c ^ μ(c)`. -/
theorem prod_block_regroup {M : Type*} [CommMonoid M] (u : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (f : ℕ → M) :
    ∏ m : Fin 6, ∏ c ∈ (block u m).filter P, f c =
      ∏ c ∈ (range (40 * u)).filter P, f c ^ mu u c := by
  have h1 : ∀ m : Fin 6, ∏ c ∈ (block u m).filter P, f c =
      ∏ c ∈ (range (40 * u)).filter P, (if c ∈ block u m then f c else 1) := by
    intro m
    rw [← Finset.prod_filter]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, block, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h3⟩, h1, h2⟩
    · rintro ⟨⟨-, h3⟩, h1, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [Finset.prod_congr rfl fun m _ => h1 m, Finset.prod_comm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rfl

/-- An in-disc zero `c` (`q ∣ 2c + 1 - 2k₀`, `q = 2r + 1`) has `c + r + 1 - k₀ ∈ qℕ`. -/
theorem zero_index {q k₀ r c : ℕ} (hqr : q = 2 * r + 1) (hk₀ : k₀ < q)
    (hZ : (2 * (c : ℤ) + 1 - 2 * k₀) % q = 0) : k₀ ≤ c + r + 1 ∧ q ∣ c + r + 1 - k₀ := by
  have hdvd : (q : ℤ) ∣ 2 * (c : ℤ) + 1 - 2 * k₀ := Int.dvd_of_emod_eq_zero hZ
  obtain ⟨s, hs⟩ := hdvd
  have hqz : (q : ℤ) = 2 * r + 1 := by rw [hqr]; push_cast; ring
  have hX : (c : ℤ) + r + 1 - k₀ = q * ((r + 1) * (s + 1) - ((c : ℤ) + r + 1 - k₀)) := by
    rw [hqz] at hs ⊢; linear_combination (r + 1) * hs
  set t : ℤ := (r + 1) * (s + 1) - ((c : ℤ) + r + 1 - k₀) with ht
  have hk₀' : (k₀ : ℤ) < q := by exact_mod_cast hk₀
  have hk : (k₀ : ℤ) ≤ c + r + 1 := by
    by_contra hneg
    push Not at hneg
    have htneg : t < 0 := by
      by_contra h
      push Not at h
      have : (0 : ℤ) ≤ q * t := mul_nonneg (by positivity) h
      linarith
    have : (q : ℤ) * t ≤ -q := by nlinarith
    omega
  have ht0 : 0 ≤ t := by
    by_contra h
    push Not at h
    have : (q : ℤ) * t < 0 := mul_neg_of_pos_of_neg (by rw [hqz]; positivity) h
    linarith
  refine ⟨by exact_mod_cast hk, t.toNat, ?_⟩
  have hk' : k₀ ≤ c + r + 1 := by exact_mod_cast hk
  have : ((c + r + 1 - k₀ : ℕ) : ℤ) = ((q * t.toNat : ℕ) : ℤ) := by
    push_cast [hk', Int.toNat_of_nonneg ht0]
    linarith
  exact_mod_cast this

/-- The zero items of `localModel` are the in-disc numerator zeros `c` with `μ(c) ≠ 0`:
reindexing `t ↦ c_t = k₀ + t q - (q+1)/2`. -/
theorem prod_ZL_reindex {M : Type*} [CommMonoid M] (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (f : ℕ → M) :
    ∏ t ∈ range (40 * u / q + 2),
        (if 0 ≤ (k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2 ∧ (k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2 < 40 * u ∧
            mu u ((k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2).toNat ≠ 0 then
          f ((k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2).toNat else 1) =
      ∏ c ∈ (range (40 * u)).filter (fun c => inZ q k₀ c ∧ mu u c ≠ 0), f c := by
  obtain ⟨r, hr⟩ := hq.odd_of_ne_two hq2
  have hqr : ((q : ℤ) + 1) / 2 = r + 1 := by rw [hr]; push_cast; omega
  have hq0 : 0 < q := hq.pos
  simp only [hqr]
  rw [← Finset.prod_filter]
  -- the inverse map and its properties
  have hinv : ∀ c : ℕ, inZ q k₀ c →
      ((k₀ : ℤ) + (((c + r + 1 - k₀) / q : ℕ) : ℤ) * q - (r + 1)) = c ∧
        (c + r + 1 - k₀) / q * q = c + r + 1 - k₀ ∧ k₀ ≤ c + r + 1 := by
    intro c hZ
    obtain ⟨hk, hd⟩ := zero_index hr hk₀ hZ
    have h1 := Nat.div_mul_cancel hd
    refine ⟨?_, h1, hk⟩
    generalize (c + r + 1 - k₀) / q = t at h1 ⊢
    have h2 : ((t * q : ℕ) : ℤ) = ((c + r + 1 - k₀ : ℕ) : ℤ) := by rw [h1]
    push_cast [hk] at h2
    linarith
  refine Finset.prod_nbij' (fun t => ((k₀ : ℤ) + (t : ℤ) * q - (r + 1)).toNat)
    (fun c => (c + r + 1 - k₀) / q) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    obtain ⟨-, h1, h2, h3⟩ := ht
    refine ⟨by omega, ?_, h3⟩
    -- `2 c_t + 1 - 2 k₀ = q (2t - 1)`
    change (2 * (((k₀ : ℤ) + (t : ℤ) * q - (r + 1)).toNat : ℤ) + 1 - 2 * k₀) % q = 0
    rw [Int.toNat_of_nonneg h1]
    have : 2 * ((k₀ : ℤ) + (t : ℤ) * q - (r + 1)) + 1 - 2 * k₀ = (q : ℤ) * (2 * t - 1) := by
      have : (q : ℤ) = 2 * r + 1 := by rw [hr]; push_cast; ring
      rw [this]; ring
    rw [this, Int.mul_emod_right]
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
    obtain ⟨hcn, hZ, hmu⟩ := hc
    obtain ⟨hct, hmul, hk⟩ := hinv c hZ
    refine ⟨?_, ?_⟩
    · -- `t < n/q + 2`
      have h1 : (c + r + 1 - k₀) / q * q < 40 * u + q := by
        rw [hmul]; rw [hr]; omega
      have h2 := Nat.lt_div_mul_add (a := 40 * u) hq0
      have h3 : (c + r + 1 - k₀) / q * q < (40 * u / q + 2) * q := by nlinarith
      exact lt_of_mul_lt_mul_right h3 (Nat.zero_le _)
    · rw [hct]
      simp only [Int.toNat_natCast]
      exact ⟨by positivity, by exact_mod_cast hcn, hmu⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨-, h1, -, -⟩ := ht
    have h3 : k₀ ≤ ((k₀ : ℤ) + (t : ℤ) * q - (r + 1)).toNat + r + 1 := by
      have : (0 : ℤ) ≤ (t : ℤ) * q := by positivity
      omega
    have e2 : ((k₀ : ℤ) + (t : ℤ) * q - (r + 1)).toNat + r + 1 - k₀ = t * q := by
      have : ((((k₀ : ℤ) + (t : ℤ) * q - (r + 1)).toNat + r + 1 - k₀ : ℕ) : ℤ) =
          ((t * q : ℕ) : ℤ) := by
        push_cast [h3, Int.toNat_of_nonneg h1]; ring
      exact_mod_cast this
    rw [e2, Nat.mul_div_cancel _ hq0]
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    obtain ⟨-, hZ, -⟩ := hc
    obtain ⟨hct, -, -⟩ := hinv c hZ
    rw [hct, Int.toNat_natCast]
  · intro t _
    rfl
/-- The in-disc numerator factors (δ-zero and zeros `-1/2 - c`) at `t = y + ε`. -/
def Inum (u q k₀ : ℕ) (y : ℚ) : PowerSeries ℚ :=
  (if inD u q k₀ then C (y + ((20 * u : ℕ) : ℚ)) + X else 1) *
    ∏ m : Fin 6, ∏ c ∈ (block u m).filter (fun c => inZ q k₀ c), (C (y + (1 / 2 + (c : ℚ))) + X)

/-- The class poles other than `k`, at `t = y + ε`. -/
def Iden (u q k₀ : ℕ) (y : ℚ) (k : ℕ) : PowerSeries ℚ :=
  ∏ j ∈ ((range (40 * u + 1)).filter (fun j => j % q = k₀)).erase k,
    (C (y + (j : ℚ)) + X) ^ apole u j

theorem substPS_Onum (y : ℚ) : substPS y (Onum u q k₀) =
    C 2 * (if inD u q k₀ then 1 else C (y + ((20 * u : ℕ) : ℚ)) + X) *
      ∏ m : Fin 6, ∏ c ∈ (block u m).filter (fun c => ¬ inZ q k₀ c),
        (C (y + (1 / 2 + (c : ℚ))) + X) := by
  unfold Onum
  rw [map_mul, map_mul, substPS_C, map_prod]
  congr 1
  · congr 1
    split_ifs
    · exact map_one _
    · exact substPS_X_add_C _ _
  · refine Finset.prod_congr rfl fun m _ => ?_
    rw [map_prod]
    exact Finset.prod_congr rfl fun c _ => substPS_X_add_C _ _

theorem substPS_Oden (y : ℚ) : substPS y (Oden u q k₀) =
    ∏ j ∈ (range (40 * u + 1)).filter (fun j => j % q ≠ k₀), (C (y + (j : ℚ)) + X) ^ apole u j := by
  unfold Oden
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_pow, substPS_X_add_C]

/-- `numSer` split into the in-disc and the outer numerator factors. -/
theorem numSer_split (y : ℚ) : numSer u y =
    (∏ m : Fin 6, ∏ c ∈ (block u m).filter (fun c => inZ q k₀ c), (C (y + (1 / 2 + (c : ℚ))) + X)) *
      ∏ m : Fin 6, ∏ c ∈ (block u m).filter (fun c => ¬ inZ q k₀ c),
        (C (y + (1 / 2 + (c : ℚ))) + X) := by
  unfold numSer
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact Finset.prod_congr rfl fun c _ => by rw [add_assoc]

/-- The δ-factor `(2t + n)` at `t = y + ε`, split according to `inD`. -/
theorem delta_split (y : ℚ) :
    (C (2 * y + ((40 * u : ℕ) : ℚ)) + C 2 * X : PowerSeries ℚ) =
      C 2 * (if inD u q k₀ then C (y + ((20 * u : ℕ) : ℚ)) + X else 1) *
        (if inD u q k₀ then 1 else C (y + ((20 * u : ℕ) : ℚ)) + X) := by
  have h : (C (2 * y + ((40 * u : ℕ) : ℚ)) + C 2 * X : PowerSeries ℚ) =
      C 2 * (C (y + ((20 * u : ℕ) : ℚ)) + X) := by
    rw [mul_add, ← map_mul]
    congr 2
    push_cast; ring
  rw [h]
  split_ifs <;> ring

/-- **Step A** (Lemma 4.1 at a class pole): `G_k = Û(-k+ε) · (in-disc factors)`. -/
theorem Gser_split {k : ℕ} (hk : k % q = k₀) :
    Gser u k = Uhat u q k₀ (-(k : ℚ)) * (Inum u q k₀ (-(k : ℚ)) * (Iden u q k₀ (-(k : ℚ)) k)⁻¹) := by
  have hden : ∏ j ∈ (range (40 * u + 1)).erase k, (C ((j : ℚ) - k) + X) ^ apole u j =
      Iden u q k₀ (-(k : ℚ)) k * substPS (-(k : ℚ)) (Oden u q k₀) := by
    rw [substPS_Oden, Iden,
      ← Finset.prod_filter_mul_prod_filter_not ((range (40 * u + 1)).erase k) (fun j => j % q = k₀),
      Finset.filter_erase]
    congr 1
    · exact Finset.prod_congr rfl fun j _ => by congr 3; ring
    · have : ((range (40 * u + 1)).erase k).filter (fun j => ¬ j % q = k₀) =
          (range (40 * u + 1)).filter (fun j => j % q ≠ k₀) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, h3⟩
        · rintro ⟨h2, h3⟩; exact ⟨⟨fun h => h3 (h ▸ hk), h2⟩, h3⟩
      rw [this]
      exact Finset.prod_congr rfl fun j _ => by congr 3; ring
  have hlin : (C (((40 * u : ℕ) : ℚ) - 2 * k) + C 2 * X : PowerSeries ℚ) =
      C (2 * (-(k : ℚ)) + ((40 * u : ℕ) : ℚ)) + C 2 * X := by
    congr 2; ring
  unfold Gser
  rw [hden, hlin, delta_split (u := u) (q := q) (k₀ := k₀), numSer_split (q := q) (k₀ := k₀),
    PowerSeries.mul_inv_rev, Uhat, substPS_Onum, Inum]
  ring

/-- **Step A** at `-k₀` when `k₀ > n` (no pole of the class): `R_n(-k₀+ε) = Û(-k₀+ε) · Inum`. -/
theorem Rser_split (hk₀ : k₀ < q) (hn : 40 * u < k₀) :
    Rser u (-(k₀ : ℚ)) = Uhat u q k₀ (-(k₀ : ℚ)) * Inum u q k₀ (-(k₀ : ℚ)) := by
  have hden : ∏ j ∈ range (40 * u + 1), (C (-(k₀ : ℚ) + j) + X) ^ apole u j =
      substPS (-(k₀ : ℚ)) (Oden u q k₀) := by
    rw [substPS_Oden]
    have : (range (40 * u + 1)).filter (fun j => j % q ≠ k₀) = range (40 * u + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
      intro hj
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [this]
  unfold Rser
  rw [hden, delta_split (u := u) (q := q) (k₀ := k₀), numSer_split (q := q) (k₀ := k₀), Uhat,
    substPS_Onum, Inum]
  ring

theorem prod_ite_eq_erase' {α M : Type*} [DecidableEq α] [CommMonoid M] (T : Finset α) (w : α)
    (f : α → M) : ∏ p ∈ T, (if p = w then 1 else f p) = ∏ p ∈ T.erase w, f p := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
  congr 1
  ext p
  simp [and_comm]

theorem list_sum_sub_ite (L : List (ℤ × ℤ)) (w : ℤ) :
    (L.map Prod.snd).sum - (L.map fun x => if x.1 = w then x.2 else 0).sum =
      (L.map fun x => if x.1 = w then (0 : ℤ) else x.2).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    split_ifs <;> ring

theorem list_rescale_lin {q : ℚ} (hq : q ≠ 0) (w : ℤ) (L : List (ℤ × ℤ)) :
    (L.map fun x => rescale q⁻¹
        (if x.1 = w then (1 : PowerSeries ℚ) else lin (((w : ℚ) - x.1) / 2) x.2)).prod =
      C (q ^ (-(L.map fun x => if x.1 = w then (0 : ℤ) else x.2).sum)) *
        (L.map fun x => if x.1 = w then (1 : PowerSeries ℚ) else
          lin (q * (((w : ℚ) - x.1) / 2)) x.2).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih]
    by_cases h : x.1 = w
    · simp only [h, ite_true, map_one, one_mul, zero_add]
    · simp only [h, ite_false]
      rw [rescale_lin (inv_ne_zero hq), inv_zpow', div_inv_eq_mul,
        mul_comm (((w : ℚ) - x.1) / 2) q, neg_add, zpow_add₀ hq, map_mul]
      ring

/-- `q^{E - netE w} · rescale q⁻¹ (taylorAt τ w)` is the product of the factors
`((w - p) q/2 + ε)^e` over the items not at `w`. -/
theorem rescale_taylorAt {q : ℚ} (hq : q ≠ 0) (τ : LocalType) (w : ℤ) :
    C (q ^ (τ.E - τ.netE w)) * rescale q⁻¹ (taylorAt τ w) =
      (τ.items.map fun x => if x.1 = w then (1 : PowerSeries ℚ) else
        lin (q * (((w : ℚ) - x.1) / 2)) x.2).prod := by
  rw [taylorAt_eq_list, map_list_prod, List.map_map]
  have hs : τ.E - τ.netE w = (τ.items.map fun x => if x.1 = w then (0 : ℤ) else x.2).sum := by
    unfold LocalType.E LocalType.netE
    rw [nE_eq_sum, list_sum_sub_ite]
  have e : (⇑(rescale q⁻¹) ∘ fun x : ℤ × ℤ => if x.1 = w then (1 : PowerSeries ℚ) else
      lin (((w : ℚ) - x.1) / 2) x.2) = fun x => rescale q⁻¹
        (if x.1 = w then (1 : PowerSeries ℚ) else lin (((w : ℚ) - x.1) / 2) x.2) := rfl
  rw [e, list_rescale_lin hq, hs, ← mul_assoc, ← map_mul, ← zpow_add₀ hq, add_neg_cancel,
    zpow_zero, map_one, one_mul]

theorem prod_cls_erase {M : Type*} [CommMonoid M] (hq : 0 < q) (hk₀ : k₀ < q) (J : ℕ)
    (G : ℕ → M) :
    ∏ j ∈ ((range (40 * u + 1)).filter (fun j => j % q = k₀)).erase (k₀ + J * q), G j =
      ∏ J' ∈ (clsJ u q k₀).erase J, G (k₀ + J' * q) := by
  rw [← prod_ite_eq_erase', prod_cls u q k₀ hq hk₀, ← prod_ite_eq_erase']
  refine Finset.prod_congr rfl fun J' _ => ?_
  by_cases h : J' = J
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Nat.eq_of_mul_eq_mul_right hq (by omega)))]

theorem PL_part (hq : 0 < q) (hk₀ : k₀ < q) (J : ℕ) :
    (((List.range (40 * u / q + 1)).filterMap (PLf u q k₀)).map fun x =>
        if x.1 = -(2 * (J : ℤ)) then (1 : PowerSeries ℚ) else
          lin ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - x.1) / 2)) x.2).prod =
      (Iden u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) (k₀ + J * q))⁻¹ := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [prod_filterMap_range]
  have h1 : ∏ J' ∈ range (40 * u / q + 1), (PLf u q k₀ J').elim 1 (fun x =>
      if x.1 = -(2 * (J : ℤ)) then (1 : PowerSeries ℚ) else
        lin ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - x.1) / 2)) x.2) =
      ∏ J' ∈ clsJ u q k₀, (if J' = J then (1 : PowerSeries ℚ) else
        ((C ((q : ℚ) * ((J' : ℚ) - J)) + X) ^ apole u (k₀ + J' * q))⁻¹) := by
    unfold clsJ
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun J' _ => ?_
    unfold PLf
    by_cases hc : k₀ + J' * q ≤ 40 * u
    · rw [ite_eq_left hc, ite_eq_left hc]
      simp only [Option.elim]
      by_cases h2 : J' = J
      · subst h2; simp
      · have h3 : ¬ (-(2 * (J' : ℤ)) = -(2 * (J : ℤ))) := by omega
        rw [ite_eq_right h3, ite_eq_right h2]
        rw [show ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - ((-(2 * (J' : ℤ)) : ℤ) : ℚ)) / 2)) =
          (q : ℚ) * ((J' : ℚ) - J) by push_cast; ring]
        rw [lin_neg_nat (mul_ne_zero hq0 (sub_ne_zero.2 (by exact_mod_cast h2)))]
    · rw [ite_eq_right hc, ite_eq_right hc]
      rfl
  rw [h1, prod_ite_eq_erase', Iden, prod_inv_distrib', prod_cls_erase hq hk₀ J]
  refine Finset.prod_congr rfl fun J' _ => ?_
  congr 3
  push_cast
  ring

theorem ZL_part (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (J : ℕ) :
    ((ZLl u q k₀).map fun x => if x.1 = -(2 * (J : ℤ)) then (1 : PowerSeries ℚ) else
        lin ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - x.1) / 2)) x.2).prod =
      ∏ m : Fin 6, ∏ c ∈ (block u m).filter (fun c => inZ q k₀ c),
        (C (-((k₀ + J * q : ℕ) : ℚ) + (1 / 2 + (c : ℚ))) + X) := by
  obtain ⟨r, hr⟩ := hq.odd_of_ne_two hq2
  have hqr : ((q : ℤ) + 1) / 2 = r + 1 := by rw [hr]; push_cast; omega
  have hqQ : (q : ℚ) = 2 * r + 1 := by rw [hr]; push_cast; ring
  unfold ZLl
  rw [List.filterMap_map, prod_filterMap_range]
  have hterm : ∀ t ∈ range (40 * u / q + 2),
      ((ZLf u q k₀ ∘ fun a : ℕ => (a : ℤ)) t).elim 1 (fun x =>
        if x.1 = -(2 * (J : ℤ)) then (1 : PowerSeries ℚ) else
          lin ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - x.1) / 2)) x.2) =
      (if 0 ≤ (k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2 ∧ (k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2 < 40 * u ∧
            mu u ((k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2).toNat ≠ 0 then
          (C (-((k₀ + J * q : ℕ) : ℚ) + (1 / 2 +
            ((((k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2).toNat : ℕ) : ℚ))) + X) ^
              mu u ((k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2).toNat else 1) := by
    intro t _
    simp only [Function.comp_apply]
    unfold ZLf
    split_ifs with hc
    · simp only [Option.elim]
      rw [ite_eq_right (by omega)]
      have hct : (((((k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2).toNat : ℕ) : ℚ)) =
          (k₀ : ℚ) + t * q - (r + 1) := by
        rw [hqr] at hc ⊢
        have := Int.toNat_of_nonneg hc.1
        have h2 : (((((k₀ : ℤ) + (t : ℤ) * q - (r + 1)).toNat : ℕ) : ℤ) : ℚ) =
            (((k₀ : ℤ) + (t : ℤ) * q - (r + 1) : ℤ) : ℚ) := by rw [this]
        push_cast at h2
        exact h2
      have hβ : ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - ((-(2 * (t : ℤ) - 1) : ℤ) : ℚ)) / 2)) =
          -((k₀ + J * q : ℕ) : ℚ) + (1 / 2 + ((((k₀ : ℤ) + (t : ℤ) * q - (q + 1) / 2).toNat : ℕ) : ℚ)) := by
        rw [hct]; push_cast; rw [hqQ]; ring
      have hβ0 : ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - ((-(2 * (t : ℤ) - 1) : ℤ) : ℚ)) / 2)) ≠ 0 := by
        apply mul_ne_zero (by exact_mod_cast hq.ne_zero)
        apply div_ne_zero _ two_ne_zero
        have : (-(2 * (J : ℤ)) - (-(2 * (t : ℤ) - 1)) : ℤ) ≠ 0 := by omega
        exact_mod_cast this
      rw [lin_nat hβ0, hβ]
    · rfl
  rw [Finset.prod_congr rfl hterm,
    prod_ZL_reindex hq hq2 hk₀ (fun c => (C (-((k₀ + J * q : ℕ) : ℚ) + (1 / 2 + (c : ℚ))) + X) ^ mu u c),
    prod_block_regroup, ← Finset.filter_filter]
  apply Finset.prod_filter_of_ne
  intro c _ hne h0
  apply hne
  rw [h0, pow_zero]

theorem DL_part (hq : 0 < q) (J : ℕ) :
    X ^ ctr u q k₀ J * ((DLl u q k₀).map fun x => if x.1 = -(2 * (J : ℤ)) then (1 : PowerSeries ℚ) else
        lin ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - x.1) / 2)) x.2).prod =
      (if inD u q k₀ then C (-((k₀ + J * q : ℕ) : ℚ) + ((20 * u : ℕ) : ℚ)) + X else 1) := by
  unfold DLl ctr
  by_cases hD : inD u q k₀
  · have hdvd : (q : ℤ) ∣ 2 * (k₀ : ℤ) - 40 * u := Int.dvd_of_emod_eq_zero hD
    obtain ⟨m, hm⟩ := hdvd
    have hq0' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have hdiv : (2 * (k₀ : ℤ) - 40 * u) / q = m := by rw [hm, Int.mul_ediv_cancel_left _ hq0']
    rw [ite_eq_left hD, ite_eq_left hD, hdiv]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    by_cases hc : k₀ + J * q = 20 * u
    · have hmJ : m = -(2 * (J : ℤ)) := by
        have h1 : ((k₀ + J * q : ℕ) : ℤ) = ((20 * u : ℕ) : ℤ) := by rw [hc]
        push_cast at h1
        have h2 : (q : ℤ) * m = q * (-(2 * J)) := by linarith
        exact mul_left_cancel₀ hq0' h2
      rw [ite_eq_left ⟨hD, hc⟩, ite_eq_left hmJ, pow_one, mul_one]
      have : (-((k₀ + J * q : ℕ) : ℚ) + ((20 * u : ℕ) : ℚ)) = 0 := by
        rw [hc]; ring
      rw [this, map_zero, zero_add]
    · have hmJ : m ≠ -(2 * (J : ℤ)) := by
        intro h
        apply hc
        rw [h] at hm
        have : ((k₀ + J * q : ℕ) : ℤ) = ((20 * u : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast this
      rw [ite_eq_right (fun h => hc h.2), ite_eq_right hmJ, pow_zero, one_mul]
      have hβ : ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - (m : ℚ)) / 2)) =
          -((k₀ + J * q : ℕ) : ℚ) + ((20 * u : ℕ) : ℚ) := by
        have hmQ : (q : ℚ) * m = 2 * k₀ - 40 * u := by exact_mod_cast hm.symm
        push_cast
        linear_combination (-1 / 2 : ℚ) * hmQ
      have hβ0 : ((q : ℚ) * ((((-(2 * (J : ℤ)) : ℤ) : ℚ) - (m : ℚ)) / 2)) ≠ 0 := by
        apply mul_ne_zero (by exact_mod_cast hq.ne')
        apply div_ne_zero _ two_ne_zero
        have : ((-(2 * (J : ℤ))) - m : ℤ) ≠ 0 := sub_ne_zero.2 (Ne.symm hmJ)
        exact_mod_cast this
      rw [lin_one hβ0, hβ]
  · rw [ite_eq_right hD, ite_eq_right (fun h => hD h.1), ite_eq_right hD]
    simp

/-- **Step B**: the in-disc factors are the rescaled local model. -/
theorem in_part (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (J : ℕ) :
    Inum u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) * (Iden u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) (k₀ + J * q))⁻¹ =
      C ((q : ℚ) ^ ((localModel u q k₀).E - (localModel u q k₀).netE (-(2 * (J : ℤ))))) *
        (X ^ ctr u q k₀ J * rescale ((q : ℚ)⁻¹) (taylorAt (localModel u q k₀) (-(2 * (J : ℤ))))) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [mul_left_comm, rescale_taylorAt hq0, items_eq, List.map_append, List.map_append,
    List.prod_append, List.prod_append, PL_part hq.pos hk₀ J, ZL_part hq hq2 hk₀ J]
  have hDL := DL_part (u := u) (k₀ := k₀) hq.pos J
  unfold Inum
  rw [← hDL]
  ring

theorem Gser_factor_aux (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) {J : ℕ}
    (hJ : k₀ + J * q ≤ 40 * u) :
    Gser u (k₀ + J * q) =
      C ((q : ℚ) ^ ((localModel u q k₀).E + ord (localModel u q k₀) (-(2 * (J : ℤ))))) *
        (X ^ ctr u q k₀ J * (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) *
          rescale ((q : ℚ)⁻¹) (taylorAt (localModel u q k₀) (-(2 * (J : ℤ)))))) := by
  have hk : (k₀ + J * q) % q = k₀ := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk₀]
  rw [Gser_split hk, in_part hq hq2 hk₀ J]
  have hE : (localModel u q k₀).E - (localModel u q k₀).netE (-(2 * (J : ℤ))) =
      (localModel u q k₀).E + ord (localModel u q k₀) (-(2 * (J : ℤ))) := by
    have h1 := netE_pole u q k₀ hq.pos hk₀ hJ
    have h2 := ord_pole u q k₀ hq.pos hk₀ hJ
    unfold ord at h2 ⊢
    omega
  rw [hE]
  ring

theorem Rser_factor_aux (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (hn : 40 * u < k₀) :
    Rser u (-(k₀ : ℚ)) = C ((q : ℚ) ^ (localModel u q k₀).E) *
      (Uhat u q k₀ (-(k₀ : ℚ)) * rescale ((q : ℚ)⁻¹) (taylorAt (localModel u q k₀) 0)) := by
  rw [Rser_split hk₀ hn]
  have h := in_part (u := u) hq hq2 hk₀ 0
  have hI : Iden u q k₀ (-((k₀ + 0 * q : ℕ) : ℚ)) (k₀ + 0 * q) = 1 := by
    unfold Iden
    apply Finset.prod_eq_one
    intro j hj
    exfalso
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨-, hj1, hj2⟩ := hj
    rw [Nat.mod_eq_of_lt (by omega)] at hj2
    omega
  have hc : ctr u q k₀ 0 = 0 := by
    unfold ctr
    rw [ite_eq_right (fun h => by have := h.2; omega)]
  rw [hI, inv_one, mul_one, hc, pow_zero, one_mul] at h
  simp only [zero_mul, add_zero, Nat.cast_zero, mul_zero, neg_zero] at h
  rw [h, netE_zero_of_gt u q k₀ hq.pos hk₀ hn, sub_zero]
  ring

end FactorAux

section Factor

variable (u q k₀ : ℕ)

/-- **Per-pole factorisation** (proof Lemma 4.1 at the pole `-k`, `k = k₀ + J q ≤ n`):
`G_k(ε) = q^{E + ord} ε^{ctr} Û(-k + ε) τ_k(ε/q)`, with `τ_k = taylorAt τ (-2J)` and
`Û = Uhat` (the factors of `R_n` outside the disc, `q`-integral: `PSV_Uhat`). -/
theorem Gser_factor (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) {J : ℕ}
    (hJ : k₀ + J * q ≤ 40 * u) :
    Gser u (k₀ + J * q) =
      C ((q : ℚ) ^ ((localModel u q k₀).E + ord (localModel u q k₀) (-(2 * (J : ℤ))))) *
        (X ^ ctr u q k₀ J * (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) *
          rescale ((q : ℚ)⁻¹) (taylorAt (localModel u q k₀) (-(2 * (J : ℤ)))))) :=
  Gser_factor_aux hq hq2 hk₀ hJ

/-- The same at `-k₀` when `k₀ > n` (the class has no pole): `R_n(-k₀ + ε) = q^E Û RR(ε/q)`. -/
theorem Rser_factor (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) (hn : 40 * u < k₀) :
    Rser u (-(k₀ : ℚ)) = C ((q : ℚ) ^ (localModel u q k₀).E) *
      (Uhat u q k₀ (-(k₀ : ℚ)) * rescale ((q : ℚ)⁻¹) (taylorAt (localModel u q k₀) 0)) :=
  Rser_factor_aux hq hq2 hk₀ hn

end Factor

/-! ## 12. Residue tools (shared with `PerPole7`, `FarPart7`)

`ResF τ Φ = ∑_{w ∈ poleSet τ} [ε^{ord w - 1}] (Φ_w · taylorAt τ w)` is the sum of the residues of
`Φ(v) RR(v)` over the poles of a local type, for a family `Φ` of Taylor series at the local points
(`ResF_add`, `ResF_sum`: linearity; with `grt_local` it is evaluated on polynomials).
`Ufam u q k₀ w = rescale q (Û(-k₀ + q w/2))` is the family of the outer factor.  The per-pole
identity `coeff_Gser_mul`:
`[ε^{a_k - 1 + n}] (G_k(ε) · q^s S(ε/q)) = q^{E + 1 + s - n} [ε^{ord - 1 + n}] (Ũ_w · taylorAt · S)`,
and `coeff_Gser_mul_eq_sum`: `[ε^{a_k - 1}] (G_k S) = ∑_{i ≤ 4} r_{i,k} [ε^{i-1}] S`.
Binomial coefficients at negative integers: `gchoose_neg` (`= negChoose`), `coeff_lin_neg`,
`coeff_inv_pow`. -/

section ResidueTools

theorem gchoose_succ_right (e : ℤ) (r : ℕ) :
    gchoose e (r + 1) = gchoose e r * ((e : ℚ) - r) / (r + 1) := by
  unfold gchoose
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  have hf : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  push_cast
  field_simp

/-- `C(-j, r) = (-1)^r C(r + j - 1, r)` for `j ≥ 1`. -/
theorem gchoose_neg (j : ℕ) (hj : 1 ≤ j) (r : ℕ) : gchoose (-(j : ℤ)) r = negChoose j r := by
  induction r with
  | zero => simp [gchoose, negChoose]
  | succ r ih =>
    rw [gchoose_succ_right, ih]
    unfold negChoose
    have hN := Nat.add_one_mul_choose_eq (r + j - 1) r
    rw [show r + j - 1 + 1 = r + j by omega] at hN
    rw [show r + 1 + j - 1 = r + j by omega, pow_succ]
    have hr : ((r : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((r + j - 1).choose r : ℚ) * ((r : ℚ) + j) / ((r : ℚ) + 1) =
        ((r + j).choose (r + 1) : ℚ) := by
      rw [div_eq_iff hr]
      have := congrArg (fun x : ℕ => (x : ℚ)) hN
      push_cast at this
      linarith
    rw [← h2]
    push_cast
    ring

theorem coeff_sum_C_mul (s : Finset ℕ) (a : ℕ → ℚ) (Φ : ℕ → PowerSeries ℚ) (g : PowerSeries ℚ)
    (n : ℕ) : coeff n ((∑ m ∈ s, C (a m) * Φ m) * g) = ∑ m ∈ s, a m * coeff n (Φ m * g) := by
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, coeff_C_mul]

theorem coeff_C_add_X_pow (v : ℚ) (m l : ℕ) :
    coeff l ((C v + X : PowerSeries ℚ) ^ m) = (m.choose l : ℚ) * v ^ (m - l) := by
  have h : ((C v + X : PowerSeries ℚ) ^ m) = (((Polynomial.X + Polynomial.C v) ^ m :
      Polynomial ℚ) : PowerSeries ℚ) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, add_comm]
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_X_add_C_pow, mul_comm]

theorem coeff_mul_rescale_inv {q : ℚ} (hq : q ≠ 0) (f g : PowerSeries ℚ) (n : ℕ) :
    coeff n (f * rescale q⁻¹ g) = (q ^ n)⁻¹ * coeff n (rescale q f * g) := by
  have h : f * rescale q⁻¹ g = rescale q⁻¹ (rescale q f * g) := by
    rw [map_mul, rescale_rescale, mul_inv_cancel₀ hq, rescale_one, RingHom.id_apply]
  rw [h, coeff_rescale, inv_pow]

theorem coeff_lin_neg (z : ℚ) (_hz : z ≠ 0) (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : 1 ≤ i) :
    coeff (i - 1) (lin z (-(j : ℤ))) = negChoose j (i - 1) * (z⁻¹) ^ (i + j - 1) := by
  unfold lin
  rw [coeff_C_mul, coeff_bser, gchoose_neg j hj, zpow_neg, zpow_natCast, ← inv_pow]
  rw [show i + j - 1 = j + (i - 1) by omega, pow_add]
  ring

theorem coeff_inv_pow (z : ℚ) (hz : z ≠ 0) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    coeff (j - 1) (((C z + X : PowerSeries ℚ) ^ i)⁻¹) = negChoose i (j - 1) * (z⁻¹) ^ (i + j - 1) := by
  rw [← lin_neg_nat hz, coeff_lin_neg z hz i hi j hj, add_comm i j]

/-- The residue functional `∑_{w ∈ poleSet} [ε^{ord-1}] (Φ_w · taylorAt)`. -/
def ResF (τ : LocalType) (Φ : ℤ → PowerSeries ℚ) : ℚ :=
  ∑ w ∈ poleSet τ, coeff (ord τ w - 1) (Φ w * taylorAt τ w)

theorem ResF_add (τ : LocalType) (Φ₁ Φ₂ : ℤ → PowerSeries ℚ) :
    ResF τ (fun w => Φ₁ w + Φ₂ w) = ResF τ Φ₁ + ResF τ Φ₂ := by
  unfold ResF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [add_mul, map_add]

theorem ResF_sum (τ : LocalType) (s : Finset ℕ) (a : ℕ → ℚ) (Φ : ℕ → ℤ → PowerSeries ℚ) :
    ResF τ (fun w => ∑ m ∈ s, C (a m) * Φ m w) = ∑ m ∈ s, a m * ResF τ (Φ m) := by
  unfold ResF
  simp only [coeff_sum_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `Ũ_w = rescale q (Û(-k₀ + q w/2))`: the Taylor series of `Û(-k₀ + q v)` at `v = w/2`. -/
def Ufam (u q k₀ : ℕ) (w : ℤ) : PowerSeries ℚ :=
  rescale (q : ℚ) (Uhat u q k₀ (-(k₀ : ℚ) + (q : ℚ) * ((w : ℚ) / 2)))

theorem Ufam_pole (u q k₀ J : ℕ) :
    Ufam u q k₀ (-(2 * (J : ℤ))) = rescale (q : ℚ) (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ))) := by
  unfold Ufam
  congr 2
  push_cast
  ring

theorem Ufam_zero (u q k₀ : ℕ) :
    Ufam u q k₀ 0 = rescale (q : ℚ) (Uhat u q k₀ (-(k₀ : ℚ))) := by
  unfold Ufam
  congr 2
  push_cast
  ring

/-- The core per-pole identity (from `Gser_factor`). -/
theorem coeff_Gser_mul {u q k₀ : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q) {J : ℕ}
    (hJ : k₀ + J * q ≤ 40 * u) (n : ℕ) (s : ℤ) (S : PowerSeries ℚ) :
    coeff (apole u (k₀ + J * q) - 1 + n)
        (Gser u (k₀ + J * q) * (C ((q : ℚ) ^ s) * rescale ((q : ℚ)⁻¹) S)) =
      (q : ℚ) ^ ((localModel u q k₀).E + 1 + s - n) *
        coeff (ord (localModel u q k₀) (-(2 * (J : ℤ))) - 1 + n)
          (Ufam u q k₀ (-(2 * (J : ℤ))) * (taylorAt (localModel u q k₀) (-(2 * (J : ℤ))) * S)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hab := ord_pole u q k₀ hq.pos hk₀ hJ
  have ha := ord_pole_pos u q k₀ hq.pos hk₀ hJ
  rw [Gser_factor u q k₀ hq hq2 hk₀ hJ, ← hab]
  have e1 : C ((q : ℚ) ^ ((localModel u q k₀).E + (ord (localModel u q k₀) (-(2 * (J : ℤ))) : ℤ))) *
      (X ^ ctr u q k₀ J * (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) *
        rescale (q : ℚ)⁻¹ (taylorAt (localModel u q k₀) (-(2 * (J : ℤ)))))) *
      (C ((q : ℚ) ^ s) * rescale (q : ℚ)⁻¹ S) =
      C ((q : ℚ) ^ ((localModel u q k₀).E + (ord (localModel u q k₀) (-(2 * (J : ℤ))) : ℤ)) *
        (q : ℚ) ^ s) * (X ^ ctr u q k₀ J * (Uhat u q k₀ (-((k₀ + J * q : ℕ) : ℚ)) *
        rescale (q : ℚ)⁻¹ (taylorAt (localModel u q k₀) (-(2 * (J : ℤ))) * S))) := by
    rw [map_mul (rescale _), map_mul C]
    ring
  rw [e1, coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
    show ord (localModel u q k₀) (-(2 * (J : ℤ))) + ctr u q k₀ J - 1 + n - ctr u q k₀ J =
      ord (localModel u q k₀) (-(2 * (J : ℤ))) - 1 + n by omega,
    coeff_mul_rescale_inv hq0, ← Ufam_pole, ← mul_assoc]
  congr 1
  rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
  congr 1
  omega

/-- `[ε^{a_k - 1}] (G_k S) = ∑_i r_{i,k} [ε^{i-1}] S`. -/
theorem coeff_Gser_mul_eq_sum (u k : ℕ) (hk : k ≤ 40 * u) (S : PowerSeries ℚ) :
    coeff (apole u k - 1) (Gser u k * S) = ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i k * coeff (i - 1) S := by
  have ha := apole_pos u k
  have ha4 := apole_le u k
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one,
    Nat.sub_add_cancel ha]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl ha4)]
  · refine Finset.sum_nbij' (fun l => apole u k - l) (fun i => apole u k - i) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_range] at hl
      simp only [Finset.mem_Icc]
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      simp only [Finset.mem_range]
      omega
    · intro l hl
      simp only [Finset.mem_range] at hl
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      omega
    · intro l hl
      simp only [Finset.mem_range] at hl
      unfold rcoef
      rw [ite_eq_left ⟨by omega, by omega, hk⟩, show apole u k - (apole u k - l) = l by omega,
        show apole u k - l - 1 = apole u k - 1 - l by omega]
  · intro i hi hni
    simp only [Finset.mem_Icc] at hi hni
    unfold rcoef
    rw [ite_eq_right (by omega), zero_mul]

end ResidueTools

end LE7

end Zeta2.Z7

end
