module

public import Zeta2Lean.Pair.Statements
public import Zeta2Lean.Pair.Proofs.NonvanishingLS

@[expose] public section

/-!
# GAP 3 (nonvanishing): `S_n ≠ 0` infinitely often along configuration E

*In this repository.* This file is the pair repository's (https://github.com/gmDevi/zeta2-7-9-lean),
unchanged apart from this paragraph and the module-system header.
The `ζ₂(7)` proof (`Zeta2Lean/Z7/Proofs/AuxPrime7.lean`) uses its `q`-integral subring and
residue calculus (namespace `Zeta2.Pair.NVq`).
Its references to documents, scripts and pair files that are not included here (such as
`BLUEPRINT_PAIR.md`, `docs/proof.md`, `python/pair_mirror.py` or `Pair/Main.lean`) are to
that repository.

gap: 'nonvanishing'.

**Status: proved** (complete, kernel-checked; `#print axioms Nonvanishing_proof` gives
`[propext, Classical.choice, Quot.sound]`).  Of the seven hypotheses of `Nonvanishing_proof` only
`Stmt_L1` (through `Nonvanishing_of_LaiSprang`) and `Stmt_CoeffVanish` (the parity relation
`r_{i,n-k} = (-1)^{i+1} r_{i,k}`) are used; the others belong to the fixed signature.

**Task.** Prove `Stmt_Nonvanishing configE`: if `ζ₂(7)` and `ζ₂(9)` are both rational, then for
infinitely many `m` every limit `I` of the Riemann sums of `integrand (40m) (m · hE)` is non-zero.

**Route** (`docs/proof.md` §7, Theorem A, in the form written there: the exact parity relation
(3.2) replaces the root trick of the original nonvanishing track).  We prove the arithmetic
Lai–Sprang condition `LaiSprangCond_proof : Stmt_CoeffVanish → Stmt_LaiSprangCond configE` and
conclude with `Nonvanishing_of_LaiSprang`.  Given `B`, take the `m` with `q := 40m - 1` prime and
`q > max(B, 10⁹)` (Dirichlet, `frequently_prime_forty_mul_sub_one_gt`).  Then (`n = 40m = q + 1`)
`v_q(ρ₀) = -9`, `v_q(Z₇) ≥ -3`, `v_q(Z₉) ≥ -1`.  The bound `q > 10⁹` replaces the conditions
`q ≥ 79`, `q ≠ 91079` of Theorem A: it makes the constants `20`, `168`, `20720700` and
`743204640 = 2⁵·3·5·17·91079` units mod `q`.

**Informal proof as formalized** (namespace `NVq`; `Z_(q)` = `Zq q`, the rationals with `q ∤ den`;
`G_k = Gser`, `r_{i,k} = [ε^{6-i}] G_k`).
1. *Every pole* (`good_all`): `q^{6-i} r_{i,k} ∈ Z_(q)`, i.e. `G_k(q ε)` has `q`-integral
   coefficients.
   * Middle poles `2 ≤ k ≤ n - 2` (`Gser_mem_mid`): every pole value `j - k` is non-zero and has
     `|j - k| < q`, and the numerator factors `ε + u - k + 1/2` are `q`-integral (`q` odd).
   * Singular poles `k ∈ {0, 1}` (`Gser_sing`): each of the six numerator blocks contains the
     factor `ε + q/2` (`u = n/2 - 1 + k`), and the pole product contains `(ε + q)^6`
     (`j = k + q`).  So `G_k = Q · Γ_k` with `Q = ((ε + q/2)/(ε + q))^6` and `Γ_k = Gam m q k`
     `q`-integral (`Gam_mem`), and `Γ₀(0)` is a `q`-unit (`gam00_unit`).  Moreover
     `Q(q ε) = 2^{-6} Q̂`, `Q̂ = ((1 + 2ε)/(1 + ε))^6` (`rescale_Qser`).
   * Top poles `k ∈ {n - 1, n}`: reflect with `Stmt_CoeffVanish.symm`.
2. *`A_k^{(s)}`* (`Ahalf_split`): the only non-integral term of `∑_{l<k} (l + 1/2)^{-s}` is
   `l = n/2 - 1`, where `l + 1/2 = q/2`.  So `A_k^{(s)} = A + [k ≥ n/2] (2/q)^s` with `A ∈ Z_(q)`.
3. *Residue of `q⁹ ρ₀`* (`rho0_res`).  Poles `k ≤ n - 2` contribute `0 mod q` (`Tterm_low`).
   For `n/2 ≤ k ≤ n - 2` this uses the two numerator factors `ε - q/2` of the blocks
   `h = m, 2m` (`Gser_mid2`), so `q² ∣ [ε^μ] G_k(q ε)` (`ghat_mid2`).  At the top pole `n - k'`
   (`k' ∈ {0, 1}`), the parity relation and the universal identity
   `∑_{i=1}^{6} (i)₄ (-2)^{i+4} [ε^{6-i}](2^{-6} Q̂ Γ) = -168 Γ₁ + 168 Γ₂ - 108 Γ₃ + 48 Γ₄ - 12 Γ₅`
   (`Lam_hat`; `β₀ = 0`, `β₁ = -168`) give the residue `168 γ_{k',1}` (`Tterm_top`).  Hence
   `q⁹ ρ₀ ≡ -168 (γ_{1,1} + γ_{0,1}) (mod q)`, with `γ_{k,λ} = [ε^λ] Γ_k`.
4. *The two singular poles* (`gam_id`, `gam_id_int`).  Telescoping the numerator blocks
   (`block_id`) and the pole products (`pole_id`) gives the exact identity `Γ₁ · A = Γ₀ · B`, with
   `A = (n + 2ε) ∏_m (2n + 2h_m - 1 + 2ε) (ε - 1)^6` and
   `B = (n - 2 + 2ε) ∏_m (-2h_m - 1 + 2ε) (ε + n)^6` (integer coefficients).  Modulo `q`
   (`n ≡ 1`, `40 m ≡ 1`; `field_facts`, `zmod_facts`) we get `b₀ = -a₀`, `a₀ = 20720700/20⁶ ≠ 0`
   and `a₁ + b₁ = 743204640/20⁶ ≠ 0`.  Coefficient `0` gives `γ_{1,0} ≡ -γ_{0,0}`, and
   coefficient `1` gives `(γ_{1,1} + γ_{0,1}) a₀ ≡ γ_{0,0} (a₁ + b₁)`.  So
   `γ_{1,1} + γ_{0,1} ≡ γ_{0,0} K`, `K = 12386744/345345`, a unit (`field_final`, `res_ne_zero`).
5. *Conclusion.*  `q⁹ ρ₀` is a `q`-unit, so `ρ₀ ≠ 0` and `v_q(ρ₀) = -9` (`rho0_val`).  Step 1
   summed over `k` gives `q^{6-i} c_i ∈ Z_(q)` (`csum_mem`), so `v_q(Z₇) ≥ -3 > -9` and
   `v_q(Z₉) ≥ -1 > -9` (`val_lt`).

**Numerical check.** `python/pair_mirror.py`, sections "GAP data" (`S!=0`) and
"Stmt_LaiSprangCond"; `python/pair_audit_independent.py`, section E
(`(v_q ρ₀, v_q Z₇, v_q Z₉) = (-9, -2, 0)` at `n = 80, 240, 360`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

namespace NVq

/-! ### `q`-integral rationals -/

variable {q : ℕ} [hqP : Fact q.Prime]

/-- The `q`-integral rationals (`q ∤ den`), a subring of `ℚ`. -/
def Zq (q : ℕ) [Fact q.Prime] : Subring ℚ where
  carrier := {x | ¬ q ∣ x.den}
  mul_mem' {a b} ha hb h := by
    rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).1 (h.trans (Rat.mul_den_dvd a b)) with h' | h'
    · exact ha h'
    · exact hb h'
  one_mem' := by
    change ¬ q ∣ (1 : ℚ).den
    rw [Rat.den_one]
    exact (Fact.out : q.Prime).not_dvd_one
  add_mem' {a b} ha hb h := by
    rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).1 (h.trans (Rat.add_den_dvd a b)) with h' | h'
    · exact ha h'
    · exact hb h'
  zero_mem' := by
    change ¬ q ∣ (0 : ℚ).den
    rw [Rat.den_zero]
    exact (Fact.out : q.Prime).not_dvd_one
  neg_mem' {a} ha := by
    change ¬ q ∣ (-a).den
    rw [Rat.den_neg_eq_den]
    exact ha

theorem mem_Zq {x : ℚ} : x ∈ Zq q ↔ ¬ q ∣ x.den := Iff.rfl

theorem Zq_int (z : ℤ) : (z : ℚ) ∈ Zq q := intCast_mem _ z

theorem Zq_nat (k : ℕ) : (k : ℚ) ∈ Zq q := natCast_mem _ k

theorem Zq_inv_int {z : ℤ} (hz : ¬ (q : ℤ) ∣ z) : (z : ℚ)⁻¹ ∈ Zq q := by
  rw [mem_Zq, Rat.inv_intCast_den]
  split_ifs with h0
  · exact (Fact.out : q.Prime).not_dvd_one
  · intro h
    exact hz (Int.natCast_dvd.2 h)

theorem Zq_div_int (a : ℤ) {b : ℤ} (hb : ¬ (q : ℤ) ∣ b) : (a : ℚ) / b ∈ Zq q := by
  rw [div_eq_mul_inv]
  exact mul_mem (Zq_int a) (Zq_inv_int hb)

/-! ### Residues modulo `q` -/

theorem den_cast_ne {x : ℚ} (hx : x ∈ Zq q) : ((x.den : ℕ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hx

theorem res_add {x y : ℚ} (hx : x ∈ Zq q) (hy : y ∈ Zq q) :
    ((x + y : ℚ) : ZMod q) = (x : ZMod q) + (y : ZMod q) :=
  Rat.cast_add_of_ne_zero (den_cast_ne hx) (den_cast_ne hy)

theorem res_sub {x y : ℚ} (hx : x ∈ Zq q) (hy : y ∈ Zq q) :
    ((x - y : ℚ) : ZMod q) = (x : ZMod q) - (y : ZMod q) :=
  Rat.cast_sub_of_ne_zero (den_cast_ne hx) (den_cast_ne hy)

theorem res_mul {x y : ℚ} (hx : x ∈ Zq q) (hy : y ∈ Zq q) :
    ((x * y : ℚ) : ZMod q) = (x : ZMod q) * (y : ZMod q) :=
  Rat.cast_mul_of_ne_zero (den_cast_ne hx) (den_cast_ne hy)

theorem res_pow {x : ℚ} (hx : x ∈ Zq q) (k : ℕ) : ((x ^ k : ℚ) : ZMod q) = (x : ZMod q) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, res_mul (pow_mem hx k) hx, ih, pow_succ]

theorem res_int (z : ℤ) : (((z : ℚ)) : ZMod q) = (z : ZMod q) := Rat.cast_intCast z

theorem res_inv_int {z : ℤ} (hz : ¬ (q : ℤ) ∣ z) :
    ((((z : ℚ))⁻¹ : ℚ) : ZMod q) = (z : ZMod q)⁻¹ := by
  have hne : (((z : ℚ).num : ℤ) : ZMod q) ≠ 0 := by
    rw [Rat.num_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hz
  rw [Rat.cast_inv_of_ne_zero hne, Rat.cast_intCast]

theorem res_div_int (a : ℤ) {b : ℤ} (hb : ¬ (q : ℤ) ∣ b) :
    ((((a : ℚ) / b) : ℚ) : ZMod q) = (a : ZMod q) / (b : ZMod q) := by
  rw [div_eq_mul_inv, res_mul (Zq_int a) (Zq_inv_int hb), res_int, res_inv_int hb, div_eq_mul_inv]

theorem res_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ∈ Zq q) :
    ((∑ i ∈ s, f i : ℚ) : ZMod q) = ∑ i ∈ s, (f i : ZMod q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : f a ∈ Zq q := hf a (mem_insert_self a s)
    have h2 : ∀ i ∈ s, f i ∈ Zq q := fun i hi => hf i (mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, res_add h1 (sum_mem h2), ih h2]

/-- `x` is `q`-integral with residue `r`. -/
def HasRes (q : ℕ) [Fact q.Prime] (x : ℚ) (r : ZMod q) : Prop :=
  x ∈ Zq q ∧ (x : ZMod q) = r

theorem HasRes.add {x y : ℚ} {r s : ZMod q} (hx : HasRes q x r) (hy : HasRes q y s) :
    HasRes q (x + y) (r + s) :=
  ⟨add_mem hx.1 hy.1, by rw [res_add hx.1 hy.1, hx.2, hy.2]⟩

theorem HasRes.sub {x y : ℚ} {r s : ZMod q} (hx : HasRes q x r) (hy : HasRes q y s) :
    HasRes q (x - y) (r - s) :=
  ⟨sub_mem hx.1 hy.1, by rw [res_sub hx.1 hy.1, hx.2, hy.2]⟩

theorem HasRes.mul {x y : ℚ} {r s : ZMod q} (hx : HasRes q x r) (hy : HasRes q y s) :
    HasRes q (x * y) (r * s) :=
  ⟨mul_mem hx.1 hy.1, by rw [res_mul hx.1 hy.1, hx.2, hy.2]⟩

theorem HasRes.neg {x : ℚ} {r : ZMod q} (hx : HasRes q x r) : HasRes q (-x) (-r) :=
  ⟨neg_mem hx.1, by rw [Rat.cast_neg, hx.2]; rfl⟩

theorem HasRes.of_mem {x : ℚ} (hx : x ∈ Zq q) : HasRes q x (x : ZMod q) := ⟨hx, rfl⟩

theorem HasRes.int (z : ℤ) : HasRes q (z : ℚ) (z : ZMod q) := ⟨Zq_int z, res_int z⟩

theorem HasRes.nat (k : ℕ) : HasRes q (k : ℚ) (k : ZMod q) :=
  ⟨Zq_nat k, Rat.cast_natCast k⟩

theorem HasRes.congr {x y : ℚ} {r s : ZMod q} (hx : HasRes q x r) (hxy : x = y) (hrs : r = s) :
    HasRes q y s := hxy ▸ hrs ▸ hx

theorem HasRes.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (r : ι → ZMod q)
    (hf : ∀ i ∈ s, HasRes q (f i) (r i)) : HasRes q (∑ i ∈ s, f i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨zero_mem _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

/-- `q · z` has residue `0` for `q`-integral `z`. -/
theorem HasRes.q_mul {z : ℚ} (hz : z ∈ Zq q) : HasRes q ((q : ℚ) * z) 0 := by
  have := (HasRes.nat (q := q) q).mul (HasRes.of_mem hz)
  rwa [ZMod.natCast_self, zero_mul] at this

/-! ### Units and `q`-adic valuations -/

theorem num_not_dvd {x : ℚ} (hr : (x : ZMod q) ≠ 0) : ¬ (q : ℤ) ∣ x.num := by
  intro h
  apply hr
  rw [Rat.cast_def, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h, zero_div]

theorem Zq_inv_of_res {x : ℚ} (hr : (x : ZMod q) ≠ 0) : x⁻¹ ∈ Zq q := by
  have hx : x⁻¹ = ((x.den : ℤ) : ℚ) / ((x.num : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [inv_div]
    push_cast
    rfl
  rw [hx]
  exact Zq_div_int _ (num_not_dvd hr)

theorem pv_nonneg {x : ℚ} (hx : x ∈ Zq q) : 0 ≤ padicValRat q x := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hx]
  simp

theorem pv_eq_zero {x : ℚ} (hx : x ∈ Zq q) (hr : (x : ZMod q) ≠ 0) : padicValRat q x = 0 := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hx,
    padicValInt.eq_zero_of_not_dvd (num_not_dvd hr)]
  simp

/-! ### Power series with `q`-integral coefficients -/

/-- Power series over `ℚ` with `q`-integral coefficients. -/
def ZqPS (q : ℕ) [Fact q.Prime] : Subring (PowerSeries ℚ) :=
  (PowerSeries.map (Zq q).subtype).range

theorem mem_ZqPS {F : PowerSeries ℚ} : F ∈ ZqPS q ↔ ∀ j, coeff j F ∈ Zq q := by
  constructor
  · rintro ⟨F', rfl⟩ j
    rw [coeff_map]
    exact (coeff j F').2
  · intro h
    refine ⟨PowerSeries.mk fun j => ⟨coeff j F, h j⟩, ?_⟩
    ext j
    simp [coeff_map]

theorem C_mem {a : ℚ} (ha : a ∈ Zq q) : C a ∈ ZqPS q := by
  rw [mem_ZqPS]
  intro j
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem X_mem : (X : PowerSeries ℚ) ∈ ZqPS q := by
  rw [mem_ZqPS]
  intro j
  rw [coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem inv_mem {F : PowerSeries ℚ} (hF : F ∈ ZqPS q) (h0 : constantCoeff F ≠ 0)
    (h0' : (constantCoeff F)⁻¹ ∈ Zq q) : F⁻¹ ∈ ZqPS q := by
  obtain ⟨G, rfl⟩ := hF
  have hc : ((constantCoeff G : Zq q) : ℚ) = constantCoeff (PowerSeries.map (Zq q).subtype G) := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    rfl
  let u : (Zq q)ˣ :=
    { val := constantCoeff G
      inv := ⟨(constantCoeff (PowerSeries.map (Zq q).subtype G))⁻¹, h0'⟩
      val_inv := Subtype.ext (by
        change ((constantCoeff G : Zq q) : ℚ) * _ = 1
        rw [hc, mul_inv_cancel₀ h0])
      inv_val := Subtype.ext (by
        change _ * ((constantCoeff G : Zq q) : ℚ) = 1
        rw [hc, inv_mul_cancel₀ h0]) }
  refine ⟨invOfUnit G u, ?_⟩
  rw [eq_comm, PowerSeries.inv_eq_iff_mul_eq_one h0, ← map_mul, invOfUnit_mul G u rfl, map_one]

theorem rescale_mem {a : ℚ} (ha : a ∈ Zq q) {F : PowerSeries ℚ} (hF : F ∈ ZqPS q) :
    rescale a F ∈ ZqPS q := by
  rw [mem_ZqPS] at hF ⊢
  intro j
  rw [coeff_rescale]
  exact mul_mem (pow_mem ha j) (hF j)

theorem rescale_C' (a r : ℚ) : rescale a (C r) = C r := by
  ext j
  rw [coeff_rescale, coeff_C]
  split_ifs with hj
  · subst hj
    simp
  · simp

theorem rescale_inv' (a : ℚ) (φ : PowerSeries ℚ) : rescale a φ⁻¹ = (rescale a φ)⁻¹ := by
  have hc : constantCoeff (rescale a φ) = constantCoeff φ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
  by_cases hφ : constantCoeff φ = 0
  · rw [PowerSeries.inv_eq_zero.mpr hφ, map_zero, PowerSeries.inv_eq_zero.mpr (hc.trans hφ)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (hc ▸ hφ), ← map_mul, PowerSeries.inv_mul_cancel φ hφ,
      map_one]

theorem lin_mem {a b : ℚ} (ha : a ∈ Zq q) (hb : b ∈ Zq q) : (C a + C b * X) ∈ ZqPS q :=
  add_mem (C_mem ha) (mul_mem (C_mem hb) X_mem)

theorem lin1_mem {a : ℚ} (ha : a ∈ Zq q) : (C a + X) ∈ ZqPS q :=
  add_mem (C_mem ha) X_mem

theorem constantCoeff_lin1 (a : ℚ) : constantCoeff (C a + X) = a := by simp

/-- A bounded odd integer other than `±q` is prime to `q`. -/
theorem not_dvd_odd {w : ℤ} (h1 : -(3 * (q : ℤ)) < 2 * w + 1) (h2 : 2 * w + 1 < 3 * q)
    (h3 : 2 * w + 1 ≠ q) (h4 : 2 * w + 1 ≠ -q) : ¬ (q : ℤ) ∣ 2 * w + 1 := by
  rintro ⟨t, ht⟩
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have ht1 : -3 < t := by nlinarith
  have ht2 : t < 3 := by nlinarith
  interval_cases t <;> omega

omit hqP in
/-- A non-zero integer of absolute value `< q` is prime to `q`. -/
theorem not_dvd_small {z : ℤ} (h0 : z ≠ 0) (h1 : -(q : ℤ) < z) (h2 : z < q) : ¬ (q : ℤ) ∣ z := by
  intro hd
  exact h0 (Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨h1, h2⟩))

theorem half_mem (hq2 : q ≠ 2) : (1 / 2 : ℚ) ∈ Zq q := by
  have : (1 / 2 : ℚ) = ((1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by norm_num
  rw [this]
  refine Zq_div_int 1 ?_
  intro h
  have h2 : (q : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
  have hq1 : 2 ≤ q := (Fact.out : q.Prime).two_le
  omega

/-- `(∏_{j ∈ S} (C(j - k) + X)^6)⁻¹` is `q`-integral when all `j - k` are prime to `q`. -/
theorem pole_inv_mem (S : Finset ℕ) (k : ℕ) (hS : ∀ j ∈ S, ¬ (q : ℤ) ∣ ((j : ℤ) - k)) :
    (∏ j ∈ S, (C ((j : ℚ) - k) + X) ^ 6)⁻¹ ∈ ZqPS q := by
  have hcast : ∀ j : ℕ, ((j : ℚ) - k) = (((j : ℤ) - k : ℤ) : ℚ) := fun j => by push_cast; ring
  have hne : ∀ j ∈ S, ((j : ℚ) - k) ≠ 0 := by
    intro j hj h0
    apply hS j hj
    have : ((j : ℤ) - k : ℤ) = 0 := by exact_mod_cast (hcast j).symm.trans h0
    rw [this]
    exact dvd_zero _
  refine inv_mem (prod_mem fun j _ => pow_mem (lin1_mem (sub_mem (Zq_nat j) (Zq_nat k))) 6) ?_ ?_
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    rw [map_pow, constantCoeff_lin1]
    exact pow_ne_zero _ (hne j hj)
  · rw [map_prod, ← Finset.prod_inv_distrib]
    refine prod_mem fun j hj => ?_
    rw [map_pow, constantCoeff_lin1, ← inv_pow, hcast j]
    exact pow_mem (Zq_inv_int (hS j hj)) 6

/-! ### Configuration E: `n = 40 m`, `h = m · hE`, `q = n - 1` -/

/-- The shift vector of configuration E at step `m`. -/
def hm (m : ℕ) : Fin 6 → ℤ := fun i => (m : ℤ) * hE i

theorem configE_h_eq (m : ℕ) : configE.h m = hm m := rfl

theorem hE_bounds (i : Fin 6) : -17 ≤ hE i ∧ hE i ≤ 6 := by
  fin_cases i <;> simp [hE]

theorem hm_bounds (m : ℕ) (i : Fin 6) : -17 * (m : ℤ) ≤ hm m i ∧ hm m i ≤ 6 * m := by
  have := hE_bounds i
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  unfold hm
  constructor <;> nlinarith

theorem hm_one (m : ℕ) : hm m 1 = m := by simp [hm, hE]

theorem hm_two (m : ℕ) : hm m 2 = 2 * m := by simp [hm, hE]; ring

theorem mem_offsets {n : ℕ} {c u : ℤ} : u ∈ offsets n c ↔ -c ≤ u ∧ u < n + c := by
  rw [offsets, Finset.mem_Ico]

section cfg

variable {m : ℕ}

theorem numfac_mem (hq2 : q ≠ 2) (k : ℕ) (u : ℤ) :
    (-(k : ℚ) + 1 / 2 + (u : ℚ)) ∈ Zq q :=
  add_mem (add_mem (neg_mem (Zq_nat k)) (half_mem hq2)) (Zq_int u)

theorem numSer_mem (hq2 : q ≠ 2) (n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) :
    numSer n h (-(k : ℚ)) ∈ ZqPS q :=
  prod_mem fun _ _ => prod_mem fun u _ => lin1_mem (numfac_mem hq2 k u)

theorem linG_mem (n k : ℕ) : (C ((n : ℚ) - 2 * k) + C 2 * X) ∈ ZqPS q := by
  refine lin_mem (sub_mem (Zq_nat n) (mul_mem ?_ (Zq_nat k))) ?_ <;>
    exact_mod_cast Zq_nat 2

/-- Middle poles: `G_k` itself is `q`-integral for `2 ≤ k ≤ n - 2` (`n = q + 1`). -/
theorem Gser_mem_mid (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k : ℕ} (hk2 : 2 ≤ k)
    (hkn : k + 2 ≤ 40 * m) : Gser (40 * m) (hm m) k ∈ ZqPS q := by
  unfold Gser
  refine mul_mem (mul_mem (linG_mem _ _) (numSer_mem hq2 _ _ _)) (pole_inv_mem _ _ ?_)
  intro j hj
  have hj' := Finset.mem_erase.1 hj
  have hjn : j < 40 * m + 1 := Finset.mem_range.1 hj'.2
  have hjk : j ≠ k := hj'.1
  refine not_dvd_small ?_ ?_ ?_ <;> omega

theorem rescale_lin1 (a b : ℚ) : rescale b (C a + X) = C a + C b * X := by
  rw [map_add, rescale_C', rescale_X]

theorem lin1_q (a b : ℚ) (hb : b ≠ 0) : C a + C b * X = C b * (C (a / b) + X) := by
  rw [mul_add, ← map_mul, mul_div_cancel₀ a hb]

omit hqP in
theorem q_cast (hqm : q + 1 = 40 * m) : (q : ℚ) = 40 * m - 1 := by
  have : ((q + 1 : ℕ) : ℚ) = ((40 * m : ℕ) : ℚ) := by rw [hqm]
  push_cast at this
  linarith

theorem m_pos (hqm : q + 1 = 40 * m) : 1 ≤ m := by
  have := (Fact.out : q.Prime).two_le
  omega

/-- Middle poles `n/2 ≤ k ≤ n - 2`: two numerator factors `ε - q/2` (blocks `1`, `2`). -/
theorem Gser_mid2 (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k : ℕ} (hk1 : 20 * m ≤ k)
    (hkn : k + 2 ≤ 40 * m) :
    ∃ F ∈ ZqPS q, Gser (40 * m) (hm m) k = (C (-(q : ℚ) / 2) + X) ^ 2 * F := by
  set g : ℤ → PowerSeries ℚ := fun u => C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X with hg
  set u0 : ℤ := (k : ℤ) - 20 * m with hu0
  have hf : g u0 = C (-(q : ℚ) / 2) + X := by
    simp only [hg, hu0]
    congr 2
    rw [q_cast hqm]
    push_cast
    ring1
  have hmem1 : u0 ∈ offsets (40 * m) (hm m 1) := by
    rw [mem_offsets, hm_one]
    push_cast
    omega
  have hmem2 : u0 ∈ offsets (40 * m) (hm m 2) := by
    rw [mem_offsets, hm_two]
    push_cast
    omega
  have hB1 : ∏ u ∈ offsets (40 * m) (hm m 1), g u =
      (C (-(q : ℚ) / 2) + X) * ∏ u ∈ (offsets (40 * m) (hm m 1)).erase u0, g u := by
    rw [← hf, Finset.mul_prod_erase _ _ hmem1]
  have hB2 : ∏ u ∈ offsets (40 * m) (hm m 2), g u =
      (C (-(q : ℚ) / 2) + X) * ∏ u ∈ (offsets (40 * m) (hm m 2)).erase u0, g u := by
    rw [← hf, Finset.mul_prod_erase _ _ hmem2]
  have hBmem : ∀ (i : Fin 6) (s : Finset ℤ), ∏ u ∈ s, g u ∈ ZqPS q :=
    fun _ s => prod_mem fun u _ => lin1_mem (numfac_mem hq2 k u)
  have hpole : (∏ j ∈ (range (40 * m + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹ ∈ ZqPS q := by
    refine pole_inv_mem _ _ ?_
    intro j hj
    have hj' := Finset.mem_erase.1 hj
    have hjn : j < 40 * m + 1 := Finset.mem_range.1 hj'.2
    have hjk : j ≠ k := hj'.1
    refine not_dvd_small ?_ ?_ ?_ <;> omega
  refine ⟨(C (((40 * m : ℕ) : ℚ) - 2 * k) + C 2 * X) *
      ((∏ u ∈ offsets (40 * m) (hm m 0), g u) * (∏ u ∈ (offsets (40 * m) (hm m 1)).erase u0, g u) *
        (∏ u ∈ (offsets (40 * m) (hm m 2)).erase u0, g u) * (∏ u ∈ offsets (40 * m) (hm m 3), g u) *
        (∏ u ∈ offsets (40 * m) (hm m 4), g u) * (∏ u ∈ offsets (40 * m) (hm m 5), g u)) *
      (∏ j ∈ (range (40 * m + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹, ?_, ?_⟩
  · refine mul_mem (mul_mem (linG_mem _ _) ?_) hpole
    refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact hBmem 0 _
  · unfold Gser numSer
    rw [Fin.prod_univ_six]
    change (C (((40 * m : ℕ) : ℚ) - 2 * k) + C 2 * X) *
        ((∏ u ∈ offsets (40 * m) (hm m 0), g u) * (∏ u ∈ offsets (40 * m) (hm m 1), g u) *
          (∏ u ∈ offsets (40 * m) (hm m 2), g u) * (∏ u ∈ offsets (40 * m) (hm m 3), g u) *
          (∏ u ∈ offsets (40 * m) (hm m 4), g u) * (∏ u ∈ offsets (40 * m) (hm m 5), g u)) *
        (∏ j ∈ (range (40 * m + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹ = _
    rw [hB1, hB2]
    ring1

/-- The coefficients of `G_k(q ε)` are divisible by `q²` for middle poles `n/2 ≤ k ≤ n - 2`. -/
theorem ghat_mid2 (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k : ℕ} (hk1 : 20 * m ≤ k)
    (hkn : k + 2 ≤ 40 * m) (μ : ℕ) :
    ∃ z ∈ Zq q, coeff μ (rescale (q : ℚ) (Gser (40 * m) (hm m) k)) = (q : ℚ) ^ 2 * z := by
  obtain ⟨F, hF, hG⟩ := Gser_mid2 hq2 hqm hk1 hkn
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hr : rescale (q : ℚ) (Gser (40 * m) (hm m) k) =
      C ((q : ℚ) ^ 2) * ((C (-(q : ℚ) / 2 / q) + X) ^ 2 * rescale (q : ℚ) F) := by
    rw [hG, map_mul, map_pow, rescale_lin1, lin1_q _ _ hq0, mul_pow, map_pow]
    ring1
  refine ⟨coeff μ ((C (-(q : ℚ) / 2 / q) + X) ^ 2 * rescale (q : ℚ) F), ?_, ?_⟩
  · have h1 : (-(q : ℚ) / 2 / q) ∈ Zq q := by
      rw [show (-(q : ℚ) / 2 / q) = -(1 / 2) by field_simp]
      exact neg_mem (half_mem hq2)
    exact (mem_ZqPS.1 (mul_mem (pow_mem (lin1_mem h1) 2) (rescale_mem (Zq_nat q) hF))) μ
  · rw [hr, coeff_C_mul]

/-! ### The singular poles `k ∈ {0, 1}`: `G_k = Q · Γ_k` -/

/-- Numerator of `Γ_k`: the six factors `ε + q/2` removed. -/
def Nprime (m k : ℕ) : PowerSeries ℚ :=
  ∏ i : Fin 6, ∏ u ∈ (offsets (40 * m) (hm m i)).erase (20 * (m : ℤ) - 1 + k),
    (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X)

/-- Pole product of `Γ_k`: the factor `(ε + q)^6` removed. -/
def Pprime (m q k : ℕ) : PowerSeries ℚ :=
  ∏ j ∈ ((range (40 * m + 1)).erase k).erase (k + q), (C ((j : ℚ) - k) + X) ^ 6

/-- `Γ_k = G_k / Q`, a power series with `q`-integral coefficients and unit constant term. -/
def Gam (m q k : ℕ) : PowerSeries ℚ :=
  (C (((40 * m : ℕ) : ℚ) - 2 * k) + C 2 * X) * Nprime m k * (Pprime m q k)⁻¹

/-- `Q(ε) = ((ε + q/2) / (ε + q))^6`. -/
def Qser (q : ℕ) : PowerSeries ℚ :=
  (C ((q : ℚ) / 2) + X) ^ 6 * ((C (q : ℚ) + X) ^ 6)⁻¹

theorem u0_mem (hqm : q + 1 = 40 * m) {k : ℕ} (hk : k ≤ 1) (i : Fin 6) :
    20 * (m : ℤ) - 1 + k ∈ offsets (40 * m) (hm m i) := by
  have hb := hm_bounds m i
  have hm1 := m_pos hqm
  rw [mem_offsets]
  push_cast
  constructor <;> omega

theorem Gser_sing (hqm : q + 1 = 40 * m) {k : ℕ} (hk : k ≤ 1) :
    Gser (40 * m) (hm m) k = Qser q * Gam m q k := by
  set g : ℤ → PowerSeries ℚ := fun u => C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X with hg
  have hf : g (20 * (m : ℤ) - 1 + k) = C ((q : ℚ) / 2) + X := by
    simp only [hg]
    congr 2
    rw [q_cast hqm]
    push_cast
    ring1
  have hB : ∀ i : Fin 6, ∏ u ∈ offsets (40 * m) (hm m i), g u =
      (C ((q : ℚ) / 2) + X) *
        ∏ u ∈ (offsets (40 * m) (hm m i)).erase (20 * (m : ℤ) - 1 + k), g u := by
    intro i
    rw [← hf, Finset.mul_prod_erase _ _ (u0_mem hqm hk i)]
  have hnum : numSer (40 * m) (hm m) (-(k : ℚ)) = (C ((q : ℚ) / 2) + X) ^ 6 * Nprime m k := by
    unfold numSer Nprime
    change ∏ i : Fin 6, ∏ u ∈ offsets (40 * m) (hm m i), g u = _
    rw [Finset.prod_congr rfl (fun i _ => hB i), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hmemP : k + q ∈ (range (40 * m + 1)).erase k := by
    rw [Finset.mem_erase, Finset.mem_range]
    have := (Fact.out : q.Prime).pos
    omega
  have hpole : ∏ j ∈ (range (40 * m + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6 =
      (C (q : ℚ) + X) ^ 6 * Pprime m q k := by
    unfold Pprime
    rw [← Finset.mul_prod_erase _ _ hmemP]
    congr 3
    push_cast
    rw [add_sub_cancel_left]
  unfold Gser Gam Qser
  rw [hnum, hpole, PowerSeries.mul_inv_rev]
  ring

end cfg

/-! ### The universal local factor: `Q(q ε) = 2^{-6} ((1 + 2ε)/(1 + ε))^6` -/

/-- `((1 + 2ε)/(1 + ε))^6`. -/
def Qhat : PowerSeries ℚ := (1 + 2 * X) ^ 6 * ((1 + X) ^ 6)⁻¹

/-- Its Taylor polynomial of degree `5`: `1 + 6ε + 9ε² - 4ε³ - 6ε⁴ + 12ε⁵`. -/
def Pp : PowerSeries ℚ :=
  C 1 + C 6 * X ^ 1 + C 9 * X ^ 2 + C (-4) * X ^ 3 + C (-6) * X ^ 4 + C 12 * X ^ 5

/-- `((1+2ε)^6 - Pp (1+ε)^6) / ε^6`. -/
def Sp : PowerSeries ℚ :=
  C (-10) + C (-60) * X + C (-135) * X ^ 2 + C (-140) * X ^ 3 + C (-66) * X ^ 4 + C (-12) * X ^ 5

theorem poly_id : (1 + 2 * X : PowerSeries ℚ) ^ 6 = Pp * (1 + X) ^ 6 + X ^ 6 * Sp := by
  simp only [Pp, Sp, map_one, map_neg, map_ofNat]
  ring1

theorem Qhat_eq : Qhat = Pp + X ^ 6 * (Sp * ((1 + X) ^ 6)⁻¹) := by
  have h1 : constantCoeff ((1 + X : PowerSeries ℚ) ^ 6) ≠ 0 := by simp
  unfold Qhat
  rw [poly_id]
  calc (Pp * (1 + X) ^ 6 + X ^ 6 * Sp) * ((1 + X) ^ 6)⁻¹
      = Pp * ((1 + X) ^ 6 * ((1 + X) ^ 6)⁻¹) + X ^ 6 * (Sp * ((1 + X) ^ 6)⁻¹) := by ring
    _ = Pp + X ^ 6 * (Sp * ((1 + X) ^ 6)⁻¹) := by rw [PowerSeries.mul_inv_cancel _ h1, mul_one]

theorem coeff_Qhat_mul (Γ : PowerSeries ℚ) {μ : ℕ} (hμ : μ < 6) :
    coeff μ (Qhat * Γ) = coeff μ (Pp * Γ) := by
  rw [Qhat_eq, add_mul, map_add, mul_assoc, coeff_X_pow_mul']
  simp only [show ¬ (6 ≤ μ) by omega, ite_false, add_zero]

theorem coeff_Pp_mul (Γ : PowerSeries ℚ) (μ : ℕ) :
    coeff μ (Pp * Γ) = coeff μ Γ + 6 * (if 1 ≤ μ then coeff (μ - 1) Γ else 0) +
      9 * (if 2 ≤ μ then coeff (μ - 2) Γ else 0) + (-4) * (if 3 ≤ μ then coeff (μ - 3) Γ else 0) +
      (-6) * (if 4 ≤ μ then coeff (μ - 4) Γ else 0) +
      12 * (if 5 ≤ μ then coeff (μ - 5) Γ else 0) := by
  simp only [Pp, add_mul, map_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul', map_one, one_mul]

theorem sum_Icc16 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Icc (1 : ℕ) 6, f i = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  rw [show Icc (1 : ℕ) 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- The universal identity behind `β₀ = 0`, `β₁ = -168`:
`∑_{i=1}^{6} (i)₄ (-2)^{i+4} [ε^{6-i}] (2^{-6} Qhat Γ)`
`= -168 Γ₁ + 168 Γ₂ - 108 Γ₃ + 48 Γ₄ - 12 Γ₅` (`Γ_λ = [ε^λ] Γ`; no `Γ₀` term). -/
theorem Lam_hat (Γ : PowerSeries ℚ) :
    ∑ i ∈ Icc (1 : ℕ) 6, ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * (-2 : ℚ) ^ (i + 4) *
        coeff (6 - i) (C (1 / 64) * Qhat * Γ) =
      -168 * coeff 1 Γ + 168 * coeff 2 Γ - 108 * coeff 3 Γ + 48 * coeff 4 Γ - 12 * coeff 5 Γ := by
  have h : ∀ μ < 6, coeff μ (C (1 / 64) * Qhat * Γ) = 1 / 64 * coeff μ (Pp * Γ) := by
    intro μ hμ
    rw [mul_assoc, coeff_C_mul, coeff_Qhat_mul Γ hμ]
  rw [sum_Icc16, h (6 - 1) (by norm_num), h (6 - 2) (by norm_num), h (6 - 3) (by norm_num),
    h (6 - 4) (by norm_num), h (6 - 5) (by norm_num), h (6 - 6) (by norm_num)]
  simp only [coeff_Pp_mul]
  norm_num
  ring

omit hqP in
theorem rescale_Qser (hq0 : (q : ℚ) ≠ 0) : rescale (q : ℚ) (Qser q) = C (1 / 64) * Qhat := by
  have e1 : C ((q : ℚ) / 2) + C (q : ℚ) * X = C ((q : ℚ) / 2) * (1 + 2 * X) := by
    rw [mul_add, mul_one, ← mul_assoc, show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm,
      ← map_mul]
    congr 3
    ring
  have e2 : C (q : ℚ) + C (q : ℚ) * X = C (q : ℚ) * (1 + X) := by rw [mul_add, mul_one]
  unfold Qser Qhat
  rw [map_mul, map_pow, rescale_inv', map_pow, rescale_lin1, rescale_lin1, e1, e2, mul_pow, mul_pow,
    PowerSeries.mul_inv_rev, ← map_pow, ← map_pow, PowerSeries.C_inv]
  have hc : ((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ 6)⁻¹ = 1 / 64 := by
    field_simp
    ring
  calc C (((q : ℚ) / 2) ^ 6) * (1 + 2 * X) ^ 6 * (((1 + X) ^ 6)⁻¹ * C (((q : ℚ) ^ 6)⁻¹))
      = C (((q : ℚ) / 2) ^ 6 * ((q : ℚ) ^ 6)⁻¹) * ((1 + 2 * X) ^ 6 * ((1 + X) ^ 6)⁻¹) := by
        rw [map_mul]
        ring
    _ = C (1 / 64) * ((1 + 2 * X) ^ 6 * ((1 + X) ^ 6)⁻¹) := by rw [hc]

theorem two_mem_PS : (2 : PowerSeries ℚ) ∈ ZqPS q := by
  rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm]
  exact C_mem (by exact_mod_cast Zq_nat 2)

theorem Qhat_mem : Qhat ∈ ZqPS q := by
  unfold Qhat
  refine mul_mem (pow_mem (add_mem (one_mem _) (mul_mem two_mem_PS X_mem)) 6) ?_
  refine inv_mem (pow_mem (add_mem (one_mem _) X_mem) 6) (by simp) (by simp)

/-! ### Units -/

/-- `x` is a `q`-adic unit. -/
def IsU (q : ℕ) [Fact q.Prime] (x : ℚ) : Prop := x ∈ Zq q ∧ (x : ZMod q) ≠ 0

theorem IsU.mul {x y : ℚ} (hx : IsU q x) (hy : IsU q y) : IsU q (x * y) :=
  ⟨mul_mem hx.1 hy.1, by rw [res_mul hx.1 hy.1]; exact mul_ne_zero hx.2 hy.2⟩

theorem IsU.pow {x : ℚ} (hx : IsU q x) (k : ℕ) : IsU q (x ^ k) :=
  ⟨pow_mem hx.1 k, by rw [res_pow hx.1]; exact pow_ne_zero _ hx.2⟩

theorem IsU.ne_zero {x : ℚ} (hx : IsU q x) : x ≠ 0 := by
  rintro rfl
  exact hx.2 (by simp)

theorem IsU.inv {x : ℚ} (hx : IsU q x) : IsU q x⁻¹ := by
  refine ⟨Zq_inv_of_res hx.2, ?_⟩
  intro h
  have := res_mul hx.1 (Zq_inv_of_res hx.2)
  rw [mul_inv_cancel₀ hx.ne_zero, h, mul_zero, Rat.cast_one] at this
  exact one_ne_zero this

theorem IsU.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, IsU q (f i)) :
    IsU q (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨one_mem _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem IsU.int {z : ℤ} (hz : ¬ (q : ℤ) ∣ z) : IsU q (z : ℚ) :=
  ⟨Zq_int z, by rw [res_int, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hz⟩

theorem IsU.div_int {a b : ℤ} (ha : ¬ (q : ℤ) ∣ a) (hb : ¬ (q : ℤ) ∣ b) : IsU q ((a : ℚ) / b) := by
  rw [div_eq_mul_inv]
  exact (IsU.int ha).mul (IsU.int hb).inv

/-- An integer in `(-q, 2q)` other than `0, q` is prime to `q`. -/
theorem not_dvd_two {z : ℤ} (h0 : z ≠ 0) (hq' : z ≠ q) (h1 : -(q : ℤ) < z) (h2 : z < 2 * q) :
    ¬ (q : ℤ) ∣ z := by
  rintro ⟨t, ht⟩
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have ht1 : -1 < t := by nlinarith
  have ht2 : t < 2 := by nlinarith
  interval_cases t <;> simp_all

section sing

variable {m : ℕ}

theorem Gam_mem (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k : ℕ} (hk : k ≤ 1) :
    Gam m q k ∈ ZqPS q := by
  unfold Gam Nprime Pprime
  refine mul_mem (mul_mem (linG_mem _ _) ?_) (pole_inv_mem _ _ ?_)
  · exact prod_mem fun _ _ => prod_mem fun u _ => lin1_mem (numfac_mem hq2 k u)
  · intro j hj
    have hj1 := Finset.mem_erase.1 hj
    have hj2 := Finset.mem_erase.1 hj1.2
    have hjn : j < 40 * m + 1 := Finset.mem_range.1 hj2.2
    refine not_dvd_two ?_ ?_ ?_ ?_ <;> omega

/-- `γ_{0,0} = Γ_0(0)` is a `q`-adic unit. -/
theorem gam00_unit (hqm : q + 1 = 40 * m) : IsU q (coeff 0 (Gam m q 0)) := by
  have hm1 := m_pos hqm
  rw [coeff_zero_eq_constantCoeff_apply]
  unfold Gam Nprime Pprime
  simp only [map_mul, map_prod, map_pow, constantCoeff_inv, map_add, constantCoeff_C,
    constantCoeff_X, add_zero, mul_zero, Nat.cast_zero, sub_zero, neg_zero, zero_add]
  refine IsU.mul (IsU.mul ?_ ?_) (IsU.inv ?_)
  · have : ((40 * m : ℕ) : ℚ) = (((q + 1 : ℕ) : ℤ) : ℚ) := by rw [hqm]; push_cast; ring
    rw [this]
    refine IsU.int (not_dvd_two ?_ ?_ ?_ ?_) <;> push_cast <;> omega
  · refine IsU.prod _ _ fun i _ => IsU.prod _ _ fun u hu => ?_
    have hu1 := Finset.mem_erase.1 hu
    have hu2 := mem_offsets.1 hu1.2
    have hb := hm_bounds m i
    have e : (1 / 2 + (u : ℚ)) = ((2 * u + 1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
      push_cast
      ring
    rw [e]
    refine IsU.div_int ?_ ?_
    · refine not_dvd_odd ?_ ?_ ?_ ?_ <;> omega
    · intro h
      have := Int.le_of_dvd (by norm_num) h
      have := (Fact.out : q.Prime).two_le
      omega
  · refine IsU.prod _ _ fun j hj => IsU.pow ?_ 6
    have hj1 := Finset.mem_erase.1 hj
    have hj2 := Finset.mem_erase.1 hj1.2
    have hjn : j < 40 * m + 1 := Finset.mem_range.1 hj2.2
    have e : (j : ℚ) = ((j : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    refine IsU.int (not_dvd_two ?_ ?_ ?_ ?_) <;> omega

theorem rescale_Gser_sing (hqm : q + 1 = 40 * m) {k : ℕ} (hk : k ≤ 1) :
    rescale (q : ℚ) (Gser (40 * m) (hm m) k) = C (1 / 64) * Qhat * rescale (q : ℚ) (Gam m q k) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  rw [Gser_sing hqm hk, map_mul, rescale_Qser hq0]

theorem ghat_sing_mem (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k : ℕ} (hk : k ≤ 1) (μ : ℕ) :
    coeff μ (rescale (q : ℚ) (Gser (40 * m) (hm m) k)) ∈ Zq q := by
  rw [rescale_Gser_sing hqm hk]
  have h64 : (1 / 64 : ℚ) ∈ Zq q := by
    rw [show (1 / 64 : ℚ) = (1 / 2) ^ 6 by norm_num]
    exact pow_mem (half_mem hq2) 6
  exact mem_ZqPS.1 (mul_mem (mul_mem (C_mem h64) Qhat_mem)
    (rescale_mem (Zq_nat q) (Gam_mem hq2 hqm hk))) μ

/-- The `Λ`-functional at a singular pole: `β₀ = 0`, `β₁ = -168`. -/
theorem Lam_sing (hqm : q + 1 = 40 * m) {k : ℕ} (hk : k ≤ 1) :
    ∑ i ∈ Icc (1 : ℕ) 6, ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * (-2 : ℚ) ^ (i + 4) *
        coeff (6 - i) (rescale (q : ℚ) (Gser (40 * m) (hm m) k)) =
      -168 * (q * coeff 1 (Gam m q k)) + 168 * (q ^ 2 * coeff 2 (Gam m q k)) -
        108 * (q ^ 3 * coeff 3 (Gam m q k)) + 48 * (q ^ 4 * coeff 4 (Gam m q k)) -
        12 * (q ^ 5 * coeff 5 (Gam m q k)) := by
  rw [rescale_Gser_sing hqm hk, Lam_hat]
  simp only [coeff_rescale, pow_one]

end sing

/-! ### `A_k^{(s)}`: the only non-integral term is `ℓ* = n/2 - 1`, with `ℓ* + 1/2 = q/2` -/

theorem Ahalf_split {m : ℕ} (hqm : q + 1 = 40 * m) {k : ℕ} (hk : k ≤ q + 1)
    (s : ℕ) : ∃ A ∈ Zq q, Ahalf k s = A + (if 20 * m ≤ k then (2 / (q : ℚ)) ^ s else 0) := by
  have hm1 := m_pos hqm
  have hterm : ∀ l ∈ range k, l ≠ 20 * m - 1 → (((l : ℚ) + 1 / 2)⁻¹) ^ s ∈ Zq q := by
    intro l hl hne
    have hlk := Finset.mem_range.1 hl
    refine pow_mem ?_ s
    have e : ((l : ℚ) + 1 / 2)⁻¹ = ((2 : ℤ) : ℚ) / ((2 * (l : ℤ) + 1 : ℤ) : ℚ) := by
      have : (2 * (l : ℚ) + 1) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    rw [e]
    refine Zq_div_int 2 (not_dvd_odd ?_ ?_ ?_ ?_) <;> omega
  by_cases h : 20 * m ≤ k
  · have hl0 : 20 * m - 1 ∈ range k := Finset.mem_range.2 (by omega)
    refine ⟨∑ l ∈ (range k).erase (20 * m - 1), (((l : ℚ) + 1 / 2)⁻¹) ^ s,
      sum_mem fun l hl => hterm l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl), ?_⟩
    rw [ite_eq_left h, Ahalf, ← Finset.sum_erase_add _ _ hl0]
    congr 2
    rw [q_cast hqm, Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  · refine ⟨Ahalf k s, sum_mem fun l hl => hterm l hl ?_, by rw [ite_eq_right h, add_zero]⟩
    have := Finset.mem_range.1 hl
    omega

/-! ### Coefficient bounds for all poles -/

theorem rcoef_eq {n : ℕ} {h : Fin 6 → ℤ} {i k : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) (hk : k ≤ n) :
    rcoef n h i k = coeff (6 - i) (Gser n h k) := by
  simp [rcoef, hi1, hi6, hk]

omit hqP in
theorem qpow_rcoef {n : ℕ} {h : Fin 6 → ℤ} {i k : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) (hk : k ≤ n) :
    (q : ℚ) ^ (6 - i) * rcoef n h i k = coeff (6 - i) (rescale (q : ℚ) (Gser n h k)) := by
  rw [rcoef_eq hi1 hi6 hk, coeff_rescale]

theorem admissible_hm (m : ℕ) : Admissible (40 * m) (hm m) := admissible_E m

theorem rcoef_symm (hV : Stmt_CoeffVanish) (m : ℕ) {i k : ℕ} (hk : k ≤ 40 * m) :
    rcoef (40 * m) (hm m) i (40 * m - k) = (-1) ^ (i + 1) * rcoef (40 * m) (hm m) i k :=
  hV.symm (40 * m) (hm m) (admissible_hm m) i k hk

/-- `q^{6-i} r_{i,k}` is `q`-integral for every pole `k`. -/
theorem good_all (hV : Stmt_CoeffVanish) {m : ℕ} (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k : ℕ}
    (hk : k ≤ 40 * m) {i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) :
    (q : ℚ) ^ (6 - i) * rcoef (40 * m) (hm m) i k ∈ Zq q := by
  have hsing : ∀ k' ≤ 1, (q : ℚ) ^ (6 - i) * rcoef (40 * m) (hm m) i k' ∈ Zq q := by
    intro k' hk'
    rw [qpow_rcoef hi1 hi6 (by omega)]
    exact ghat_sing_mem hq2 hqm hk' _
  by_cases h1 : k ≤ 1
  · exact hsing k h1
  by_cases h2 : k + 2 ≤ 40 * m
  · rw [qpow_rcoef hi1 hi6 hk]
    exact mem_ZqPS.1 (rescale_mem (Zq_nat q) (Gser_mem_mid hq2 hqm (by omega) h2)) _
  · -- `k ∈ {n - 1, n}`: reflect to `n - k ∈ {1, 0}`
    have hk' : 40 * m - k ≤ 1 := by omega
    have hs := rcoef_symm hV m (i := i) (k := 40 * m - k) (by omega)
    rw [show 40 * m - (40 * m - k) = k by omega] at hs
    rw [hs, mul_left_comm]
    exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (hsing _ hk')

/-! ### The residue of `q⁹ ρ₀` -/

/-- The `(i, k)` term of `-q⁹ ρ₀`. -/
def Tterm (m q k i : ℕ) : ℚ :=
  (q : ℚ) ^ 9 * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef (40 * m) (hm m) i k *
    Ahalf k (i + 4))

omit hqP in
theorem alg_I1 {i : ℕ} (hi6 : i ≤ 6) (P r A : ℚ) :
    (q : ℚ) ^ 9 * (P * r * A) = q * (q ^ (2 + i) * P * ((q : ℚ) ^ (6 - i) * r) * A) := by
  have : (q : ℚ) ^ 9 = q * (q ^ (2 + i) * q ^ (6 - i)) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  rw [this]
  ring

theorem alg_I2 {i : ℕ} (hi6 : i ≤ 6) (P r z : ℚ) (hr : (q : ℚ) ^ (6 - i) * r = q ^ 2 * z) :
    (q : ℚ) ^ 9 * (P * r * (2 / (q : ℚ)) ^ (i + 4)) = q * (P * 2 ^ (i + 4) * z) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have h9 : (q : ℚ) ^ 9 * r = q ^ (i + 4) * (q * z) := by
    calc (q : ℚ) ^ 9 * r = q ^ (3 + i) * ((q : ℚ) ^ (6 - i) * r) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega
      _ = q ^ (3 + i) * (q ^ 2 * z) := by rw [hr]
      _ = q ^ (i + 4) * (q * z) := by ring
  have hpow : (q : ℚ) ^ (i + 4) ≠ 0 := pow_ne_zero _ hq0
  calc (q : ℚ) ^ 9 * (P * r * (2 / (q : ℚ)) ^ (i + 4))
      = P * 2 ^ (i + 4) * ((q : ℚ) ^ 9 * r) / q ^ (i + 4) := by rw [div_pow]; ring
    _ = P * 2 ^ (i + 4) * (q ^ (i + 4) * (q * z)) / q ^ (i + 4) := by rw [h9]
    _ = q * (P * 2 ^ (i + 4) * z) := by field_simp

theorem alg_I3 {i : ℕ} (hi6 : i ≤ 6) (P r : ℚ) :
    (q : ℚ) ^ 9 * (P * ((-1) ^ (i + 1) * r) * (2 / (q : ℚ)) ^ (i + 4)) =
      -(1 / (q : ℚ)) * (P * (-2 : ℚ) ^ (i + 4) * ((q : ℚ) ^ (6 - i) * r)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have h10 : (q : ℚ) ^ (i + 4) * q ^ (6 - i) = q ^ 9 * q := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hq9 : (q : ℚ) ^ 9 / q ^ (i + 4) = q ^ (6 - i) / q := by
    rw [div_eq_div_iff (pow_ne_zero _ hq0) hq0]
    linear_combination -h10
  have hm2 : (-2 : ℚ) ^ (i + 4) = (-1) ^ (i + 4) * 2 ^ (i + 4) := by
    rw [← mul_pow]
    norm_num
  have hs : (-1 : ℚ) ^ (i + 4) = -(-1) ^ (i + 1) := by
    rw [pow_add, pow_add]
    norm_num
  calc (q : ℚ) ^ 9 * (P * ((-1) ^ (i + 1) * r) * (2 / (q : ℚ)) ^ (i + 4))
      = P * (-1) ^ (i + 1) * r * 2 ^ (i + 4) * ((q : ℚ) ^ 9 / q ^ (i + 4)) := by
        rw [div_pow]
        ring
    _ = P * (-1) ^ (i + 1) * r * 2 ^ (i + 4) * ((q : ℚ) ^ (6 - i) / q) := by rw [hq9]
    _ = -(1 / (q : ℚ)) * (P * (-2 : ℚ) ^ (i + 4) * ((q : ℚ) ^ (6 - i) * r)) := by
        rw [hm2, hs]
        ring

theorem two_mem : (2 : ℚ) ∈ Zq q := by exact_mod_cast Zq_nat 2

section rhoRes

variable {m : ℕ}

/-- Low and middle poles `k ≤ n - 2` contribute `0` modulo `q`. -/
theorem Tterm_low (hV : Stmt_CoeffVanish) (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k : ℕ}
    (hk : k < q) {i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) : HasRes q (Tterm m q k i) 0 := by
  obtain ⟨A, hA, hAeq⟩ := Ahalf_split hqm (k := k) (by omega) (i + 4)
  have hg := good_all hV hq2 hqm (k := k) (by omega) hi1 hi6
  have hP : ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) ∈ Zq q := by
    have : ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) =
        ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by
      push_cast
      ring
    rw [this]
    exact Zq_nat _
  have hlow : ∀ B ∈ Zq q, HasRes q ((q : ℚ) ^ 9 * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) *
      rcoef (40 * m) (hm m) i k * B)) 0 := by
    intro B hB
    rw [alg_I1 hi6]
    exact HasRes.q_mul (mul_mem (mul_mem (mul_mem (pow_mem (Zq_nat q) _) hP) hg) hB)
  unfold Tterm
  rw [hAeq]
  split_ifs with h20
  · obtain ⟨z, hz, hze⟩ := ghat_mid2 hq2 hqm h20 (by omega) (6 - i)
    have hr : (q : ℚ) ^ (6 - i) * rcoef (40 * m) (hm m) i k = q ^ 2 * z := by
      rw [qpow_rcoef hi1 hi6 (by omega), hze]
    have e : (q : ℚ) ^ 9 * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef (40 * m) (hm m) i k *
        (A + (2 / (q : ℚ)) ^ (i + 4))) =
        (q : ℚ) ^ 9 * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef (40 * m) (hm m) i k * A) +
        (q : ℚ) ^ 9 * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef (40 * m) (hm m) i k *
          (2 / (q : ℚ)) ^ (i + 4)) := by ring
    rw [e, alg_I2 hi6 _ _ _ hr]
    have h2 : HasRes q ((q : ℚ) * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * 2 ^ (i + 4) * z)) 0 :=
      HasRes.q_mul (mul_mem (mul_mem hP (pow_mem two_mem _)) hz)
    have := (hlow A hA).add h2
    rwa [add_zero] at this
  · rw [add_zero]
    exact hlow A hA

/-- The two top poles `k = n - k'` (`k' ∈ {0, 1}`) contribute `168 γ_{k',1}` modulo `q`. -/
theorem Tterm_top (hV : Stmt_CoeffVanish) (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {k' : ℕ}
    (hk' : k' ≤ 1) :
    HasRes q (∑ i ∈ Icc (1 : ℕ) 6, Tterm m q (40 * m - k') i)
      (168 * ((coeff 1 (Gam m q k') : ℚ) : ZMod q)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hm1 := m_pos hqm
  have hsplit : ∀ i : ℕ, ∃ A ∈ Zq q, Ahalf (40 * m - k') (i + 4) =
      A + (if 20 * m ≤ 40 * m - k' then (2 / (q : ℚ)) ^ (i + 4) else 0) :=
    fun i => Ahalf_split hqm (k := 40 * m - k') (by omega) (i + 4)
  choose A hA hAeq using hsplit
  set P : ℕ → ℚ := fun i => (i : ℚ) * (i + 1) * (i + 2) * (i + 3) with hPdef
  have hP : ∀ i, P i ∈ Zq q := by
    intro i
    have : P i = ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by
      simp only [hPdef]
      push_cast
      ring
    rw [this]
    exact Zq_nat _
  -- split each term into the integral part and the `(2/q)^{i+4}` part
  have hsum : ∑ i ∈ Icc (1 : ℕ) 6, Tterm m q (40 * m - k') i =
      ∑ i ∈ Icc (1 : ℕ) 6, (q : ℚ) ^ 9 * (P i * rcoef (40 * m) (hm m) i (40 * m - k') * A i) +
      ∑ i ∈ Icc (1 : ℕ) 6, (q : ℚ) ^ 9 * (P i * ((-1) ^ (i + 1) * rcoef (40 * m) (hm m) i k') *
        (2 / (q : ℚ)) ^ (i + 4)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold Tterm
    rw [hAeq i, ite_eq_left (by omega), rcoef_symm hV m (i := i) (k := k') (by omega)]
    ring
  -- the `(2/q)^{i+4}` part is `-(1/q) Λ̂`
  have hsum2 : ∑ i ∈ Icc (1 : ℕ) 6, (q : ℚ) ^ 9 * (P i * ((-1) ^ (i + 1) *
      rcoef (40 * m) (hm m) i k') * (2 / (q : ℚ)) ^ (i + 4)) =
      -(1 / (q : ℚ)) * ∑ i ∈ Icc (1 : ℕ) 6, ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) *
        (-2 : ℚ) ^ (i + 4) * coeff (6 - i) (rescale (q : ℚ) (Gser (40 * m) (hm m) k')) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    rw [← qpow_rcoef hi'.1 hi'.2 (by omega), alg_I3 hi'.2]
  rw [hsum, hsum2, Lam_sing hqm hk']
  -- the integral part
  have h1 : HasRes q (∑ i ∈ Icc (1 : ℕ) 6,
      (q : ℚ) ^ 9 * (P i * rcoef (40 * m) (hm m) i (40 * m - k') * A i))
      (∑ i ∈ Icc (1 : ℕ) 6, 0) := by
    refine HasRes.sum _ _ _ fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    rw [alg_I1 hi'.2]
    exact HasRes.q_mul (mul_mem (mul_mem (mul_mem (pow_mem (Zq_nat q) _) (hP i))
      (good_all hV hq2 hqm (by omega) hi'.1 hi'.2)) (hA i))
  have hγ : ∀ b, coeff b (Gam m q k') ∈ Zq q := mem_ZqPS.1 (Gam_mem hq2 hqm hk')
  have h2 : HasRes q (168 * coeff 1 (Gam m q k') + (q : ℚ) * (-168 * coeff 2 (Gam m q k') +
      108 * (q * coeff 3 (Gam m q k')) - 48 * (q ^ 2 * coeff 4 (Gam m q k')) +
      12 * (q ^ 3 * coeff 5 (Gam m q k')))) (168 * ((coeff 1 (Gam m q k') : ℚ) : ZMod q) + 0) := by
    refine HasRes.add ?_ (HasRes.q_mul ?_)
    · have := (HasRes.nat (q := q) 168).mul (HasRes.of_mem (hγ 1))
      simpa using this
    · refine add_mem (sub_mem (add_mem (mul_mem ?_ (hγ 2)) ?_) ?_) ?_
      · exact neg_mem (by exact_mod_cast Zq_nat 168)
      · exact mul_mem (by exact_mod_cast Zq_nat 108) (mul_mem (Zq_nat q) (hγ 3))
      · exact mul_mem (by exact_mod_cast Zq_nat 48) (mul_mem (pow_mem (Zq_nat q) 2) (hγ 4))
      · exact mul_mem (by exact_mod_cast Zq_nat 12) (mul_mem (pow_mem (Zq_nat q) 3) (hγ 5))
  have := h1.add h2
  refine this.congr ?_ (by simp)
  field_simp
  ring

/-- The residue of `q⁹ ρ₀`: `-168 (γ_{1,1} + γ_{0,1})`. -/
theorem rho0_res (hV : Stmt_CoeffVanish) (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) :
    HasRes q ((q : ℚ) ^ 9 * rho0 (40 * m) (hm m))
      (-(0 + 168 * ((coeff 1 (Gam m q 1) : ℚ) : ZMod q) +
        168 * ((coeff 1 (Gam m q 0) : ℚ) : ZMod q))) := by
  have e1 : (q : ℚ) ^ 9 * rho0 (40 * m) (hm m) =
      -(∑ k ∈ range (40 * m + 1), ∑ i ∈ Icc (1 : ℕ) 6, Tterm m q k i) := by
    unfold rho0 genRho0 Tterm
    rw [mul_neg, Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have e2 : 40 * m + 1 = q + 1 + 1 := by omega
  rw [e1, e2, Finset.sum_range_succ, Finset.sum_range_succ]
  refine HasRes.neg (HasRes.add (HasRes.add ?_ ?_) ?_)
  · have := HasRes.sum (range q) (fun k => ∑ i ∈ Icc (1 : ℕ) 6, Tterm m q k i) (fun _ => 0)
      fun k hk => by
        have := HasRes.sum (Icc (1 : ℕ) 6) (fun i => Tterm m q k i) (fun _ => (0 : ZMod q))
          fun i hi => Tterm_low hV hq2 hqm (Finset.mem_range.1 hk) (Finset.mem_Icc.1 hi).1
            (Finset.mem_Icc.1 hi).2
        simpa using this
    simpa using this
  · have := Tterm_top hV hq2 hqm (k' := 1) le_rfl
    rwa [show 40 * m - 1 = q by omega] at this
  · have := Tterm_top hV hq2 hqm (k' := 0) (by norm_num)
    rwa [show 40 * m - 0 = q + 1 by omega] at this

end rhoRes

/-! ### The two singular poles: `Γ₁ · A = Γ₀ · B` -/

theorem telescope {M : Type*} [CommMonoid M] (f : ℤ → M) {a b : ℤ} (hab : a ≤ b) :
    (∏ u ∈ Ico a b, f (u - 1)) * f (b - 1) = (∏ u ∈ Ico a b, f u) * f (a - 1) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
    have hI : Ico a (b + 1) = insert b (Ico a b) := by
      ext u
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hb : b ∉ Ico a b := by simp
    rw [hI, Finset.prod_insert hb, Finset.prod_insert hb, add_sub_cancel_right]
    calc f (b - 1) * (∏ u ∈ Ico a b, f (u - 1)) * f b
        = ((∏ u ∈ Ico a b, f (u - 1)) * f (b - 1)) * f b := by
          rw [mul_comm (f (b - 1)) (∏ u ∈ Ico a b, f (u - 1))]
      _ = ((∏ u ∈ Ico a b, f u) * f (a - 1)) * f b := by rw [ih]
      _ = f b * (∏ u ∈ Ico a b, f u) * f (a - 1) := by
          rw [mul_right_comm, mul_comm (∏ u ∈ Ico a b, f u) (f b)]

theorem lin1_ne_zero (a : ℚ) : (C a + X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp at this

section blocks

variable {m : ℕ}

/-- One numerator block: `N'_1 · (ε + n + c - 1/2) = N'_0 · (ε - c - 1/2)`. -/
theorem block_id (hqm : q + 1 = 40 * m) (i : Fin 6) :
    (∏ u ∈ (offsets (40 * m) (hm m i)).erase (20 * (m : ℤ) - 1 + ((1 : ℕ) : ℤ)),
        (C (-((1 : ℕ) : ℚ) + 1 / 2 + (u : ℚ)) + X)) *
      (C (((40 * m : ℕ) : ℚ) + (hm m i : ℚ) - 1 / 2) + X) =
    (∏ u ∈ (offsets (40 * m) (hm m i)).erase (20 * (m : ℤ) - 1 + ((0 : ℕ) : ℤ)),
        (C (-((0 : ℕ) : ℚ) + 1 / 2 + (u : ℚ)) + X)) *
      (C (-(hm m i : ℚ) - 1 / 2) + X) := by
  set f : ℤ → PowerSeries ℚ := fun w => C ((w : ℚ) + 1 / 2) + X with hf
  set c := hm m i with hc
  have hb := hm_bounds m i
  have h1 : ∏ u ∈ (offsets (40 * m) c).erase (20 * (m : ℤ) - 1 + ((1 : ℕ) : ℤ)),
      (C (-((1 : ℕ) : ℚ) + 1 / 2 + (u : ℚ)) + X) =
      ∏ u ∈ (offsets (40 * m) c).erase (20 * (m : ℤ) - 1 + ((1 : ℕ) : ℤ)), f (u - 1) := by
    refine Finset.prod_congr rfl fun u _ => ?_
    simp only [hf]
    congr 2
    push_cast
    ring
  have h0 : ∏ u ∈ (offsets (40 * m) c).erase (20 * (m : ℤ) - 1 + ((0 : ℕ) : ℤ)),
      (C (-((0 : ℕ) : ℚ) + 1 / 2 + (u : ℚ)) + X) =
      ∏ u ∈ (offsets (40 * m) c).erase (20 * (m : ℤ) - 1 + ((0 : ℕ) : ℤ)), f u := by
    refine Finset.prod_congr rfl fun u _ => ?_
    simp only [hf]
    congr 2
    push_cast
    ring
  have hfb : C (((40 * m : ℕ) : ℚ) + (c : ℚ) - 1 / 2) + X = f (40 * m + c - 1) := by
    simp only [hf]
    congr 2
    push_cast
    ring
  have hfa : C (-(c : ℚ) - 1 / 2) + X = f (-c - 1) := by
    simp only [hf]
    congr 2
    push_cast
    ring
  have hmem1 := u0_mem hqm (k := 1) le_rfl i
  have hmem0 := u0_mem hqm (k := 0) (by norm_num) i
  rw [← hc] at hmem1 hmem0
  have hp1 : f (20 * (m : ℤ) - 1) *
      ∏ u ∈ (offsets (40 * m) c).erase (20 * (m : ℤ) - 1 + ((1 : ℕ) : ℤ)), f (u - 1) =
      ∏ u ∈ offsets (40 * m) c, f (u - 1) := by
    have := Finset.mul_prod_erase (offsets (40 * m) c) (fun u => f (u - 1)) hmem1
    simpa using this
  have hp0 : f (20 * (m : ℤ) - 1) *
      ∏ u ∈ (offsets (40 * m) c).erase (20 * (m : ℤ) - 1 + ((0 : ℕ) : ℤ)), f u =
      ∏ u ∈ offsets (40 * m) c, f u := by
    have := Finset.mul_prod_erase (offsets (40 * m) c) f hmem0
    simpa using this
  have htel := telescope f (a := -c) (b := 40 * m + c) (by omega)
  rw [h1, h0, hfb, hfa]
  refine mul_left_cancel₀ (lin1_ne_zero ((((20 * (m : ℤ) - 1 : ℤ)) : ℚ) + 1 / 2)) ?_
  change f (20 * (m : ℤ) - 1) * _ = f (20 * (m : ℤ) - 1) * _
  rw [← mul_assoc, ← mul_assoc, hp1, hp0]
  unfold offsets
  exact htel

/-- The numerators: `N'_1 · ∏(ε + n + h_i - 1/2) = N'_0 · ∏(ε - h_i - 1/2)`. -/
theorem num_id (hqm : q + 1 = 40 * m) :
    Nprime m 1 * ∏ i : Fin 6, (C (((40 * m : ℕ) : ℚ) + (hm m i : ℚ) - 1 / 2) + X) =
    Nprime m 0 * ∏ i : Fin 6, (C (-(hm m i : ℚ) - 1 / 2) + X) := by
  unfold Nprime
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => block_id hqm i

theorem Pprime_cc_ne (m q k : ℕ) : constantCoeff (Pprime m q k) ≠ 0 := by
  unfold Pprime
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  rw [map_pow, constantCoeff_lin1]
  refine pow_ne_zero _ (sub_ne_zero.2 ?_)
  have := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
  exact_mod_cast this

/-- The pole products: `P'_0 · (ε - 1)^6 = P'_1 · (ε + n)^6`. -/
theorem pole_id (hqm : q + 1 = 40 * m) :
    Pprime m q 0 * (C (-1 : ℚ) + X) ^ 6 = Pprime m q 1 * (C (((40 * m : ℕ) : ℚ)) + X) ^ 6 := by
  set G : ℚ → PowerSeries ℚ := fun t => (C t + X) ^ 6 with hG
  have hq1 := (Fact.out : q.Prime).one_lt
  have hGne : ∀ t, G t ≠ 0 := fun t => pow_ne_zero _ (lin1_ne_zero t)
  have hP0 : Pprime m q 0 = ∏ j ∈ ((range (40 * m + 1)).erase 0).erase q, G (j : ℚ) := by
    unfold Pprime
    simp only [hG, Nat.cast_zero, sub_zero, zero_add]
  have hP1 : Pprime m q 1 = ∏ j ∈ ((range (40 * m + 1)).erase 1).erase (1 + q),
      G ((j : ℚ) - 1) := by
    unfold Pprime
    simp only [hG, Nat.cast_one]
  have hq_mem0 : q ∈ (range (40 * m + 1)).erase 0 := by
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have hq_mem1 : 1 + q ∈ (range (40 * m + 1)).erase 1 := by
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have p1 : G q * Pprime m q 0 = ∏ j ∈ (range (40 * m + 1)).erase 0, G (j : ℚ) := by
    rw [hP0, Finset.mul_prod_erase _ (fun j : ℕ => G (j : ℚ)) hq_mem0]
  have p2 : G 0 * ∏ j ∈ (range (40 * m + 1)).erase 0, G (j : ℚ) =
      ∏ j ∈ range (40 * m + 1), G (j : ℚ) := by
    have := Finset.mul_prod_erase (range (40 * m + 1)) (fun j : ℕ => G (j : ℚ))
      (Finset.mem_range.2 (by omega : 0 < 40 * m + 1))
    simpa using this
  have p3 : G q * Pprime m q 1 = ∏ j ∈ (range (40 * m + 1)).erase 1, G ((j : ℚ) - 1) := by
    rw [hP1]
    have := Finset.mul_prod_erase ((range (40 * m + 1)).erase 1) (fun j : ℕ => G ((j : ℚ) - 1))
      hq_mem1
    rw [← this, show (((1 + q : ℕ) : ℚ) - 1) = (q : ℚ) by push_cast; ring]
  have p4 : G 0 * ∏ j ∈ (range (40 * m + 1)).erase 1, G ((j : ℚ) - 1) =
      ∏ j ∈ range (40 * m + 1), G ((j : ℚ) - 1) := by
    have := Finset.mul_prod_erase (range (40 * m + 1)) (fun j : ℕ => G ((j : ℚ) - 1))
      (Finset.mem_range.2 (by omega : 1 < 40 * m + 1))
    simpa using this
  have p5 : ∏ j ∈ range (40 * m + 1), G ((j : ℚ) - 1) =
      (∏ j ∈ range (40 * m), G (j : ℚ)) * G (-1) := by
    rw [Finset.prod_range_succ']
    have e1 : ∀ j ∈ range (40 * m), G (((j + 1 : ℕ) : ℚ) - 1) = G (j : ℚ) := fun j _ => by
      rw [Nat.cast_succ, add_sub_cancel_right]
    rw [Finset.prod_congr rfl e1, Nat.cast_zero, zero_sub]
  have p6 : ∏ j ∈ range (40 * m + 1), G (j : ℚ) = (∏ j ∈ range (40 * m), G (j : ℚ)) *
      G ((40 * m : ℕ) : ℚ) := Finset.prod_range_succ _ _
  have key : (G q * G 0) * (Pprime m q 0 * G (-1)) =
      (G q * G 0) * (Pprime m q 1 * G ((40 * m : ℕ) : ℚ)) := by
    calc (G q * G 0) * (Pprime m q 0 * G (-1))
        = G 0 * (G q * Pprime m q 0) * G (-1) := by ring
      _ = (∏ j ∈ range (40 * m), G (j : ℚ)) * G ((40 * m : ℕ) : ℚ) * G (-1) := by
          rw [p1, p2, p6]
      _ = (∏ j ∈ range (40 * m + 1), G ((j : ℚ) - 1)) * G ((40 * m : ℕ) : ℚ) := by
          rw [p5]
          ring
      _ = G 0 * (G q * Pprime m q 1) * G ((40 * m : ℕ) : ℚ) := by rw [p3, p4]
      _ = (G q * G 0) * (Pprime m q 1 * G ((40 * m : ℕ) : ℚ)) := by ring
  exact mul_left_cancel₀ (mul_ne_zero (hGne _) (hGne _)) key

/-- `Γ₁ · A = Γ₀ · B` (half-integer form). -/
theorem gam_id (hqm : q + 1 = 40 * m) :
    Gam m q 1 * ((C (((40 * m : ℕ) : ℚ) - 2 * ((0 : ℕ) : ℚ)) + C 2 * X) *
      (∏ i : Fin 6, (C (((40 * m : ℕ) : ℚ) + (hm m i : ℚ) - 1 / 2) + X)) * (C (-1 : ℚ) + X) ^ 6) =
    Gam m q 0 * ((C (((40 * m : ℕ) : ℚ) - 2 * ((1 : ℕ) : ℚ)) + C 2 * X) *
      (∏ i : Fin 6, (C (-(hm m i : ℚ) - 1 / 2) + X)) * (C (((40 * m : ℕ) : ℚ)) + X) ^ 6) := by
  have hP := pole_id (q := q) hqm (m := m)
  have hc0 := Pprime_cc_ne m q 0
  have hc1 := Pprime_cc_ne m q 1
  have hinv : (Pprime m q 1)⁻¹ * (C (-1 : ℚ) + X) ^ 6 =
      (Pprime m q 0)⁻¹ * (C (((40 * m : ℕ) : ℚ)) + X) ^ 6 := by
    calc (Pprime m q 1)⁻¹ * (C (-1 : ℚ) + X) ^ 6
        = (Pprime m q 1)⁻¹ * (Pprime m q 0)⁻¹ * (Pprime m q 0 * (C (-1 : ℚ) + X) ^ 6) *
            1 := by rw [mul_one, ← mul_assoc, mul_assoc _ (Pprime m q 0)⁻¹,
              PowerSeries.inv_mul_cancel _ hc0, mul_one]
      _ = (Pprime m q 0)⁻¹ * (C (((40 * m : ℕ) : ℚ)) + X) ^ 6 *
            ((Pprime m q 1)⁻¹ * Pprime m q 1) := by rw [hP]; ring
      _ = (Pprime m q 0)⁻¹ * (C (((40 * m : ℕ) : ℚ)) + X) ^ 6 := by
            rw [PowerSeries.inv_mul_cancel _ hc1, mul_one]
  have hN := num_id (q := q) hqm (m := m)
  unfold Gam
  calc (C (((40 * m : ℕ) : ℚ) - 2 * ((1 : ℕ) : ℚ)) + C 2 * X) * Nprime m 1 * (Pprime m q 1)⁻¹ *
        ((C (((40 * m : ℕ) : ℚ) - 2 * ((0 : ℕ) : ℚ)) + C 2 * X) *
          (∏ i : Fin 6, (C (((40 * m : ℕ) : ℚ) + (hm m i : ℚ) - 1 / 2) + X)) * (C (-1 : ℚ) + X) ^ 6)
      = (C (((40 * m : ℕ) : ℚ) - 2 * ((1 : ℕ) : ℚ)) + C 2 * X) *
          (C (((40 * m : ℕ) : ℚ) - 2 * ((0 : ℕ) : ℚ)) + C 2 * X) *
          (Nprime m 1 * ∏ i : Fin 6, (C (((40 * m : ℕ) : ℚ) + (hm m i : ℚ) - 1 / 2) + X)) *
          ((Pprime m q 1)⁻¹ * (C (-1 : ℚ) + X) ^ 6) := by ring
    _ = (C (((40 * m : ℕ) : ℚ) - 2 * ((1 : ℕ) : ℚ)) + C 2 * X) *
          (C (((40 * m : ℕ) : ℚ) - 2 * ((0 : ℕ) : ℚ)) + C 2 * X) *
          (Nprime m 0 * ∏ i : Fin 6, (C (-(hm m i : ℚ) - 1 / 2) + X)) *
          ((Pprime m q 0)⁻¹ * (C (((40 * m : ℕ) : ℚ)) + X) ^ 6) := by rw [hN, hinv]
    _ = _ := by ring

end blocks

/-! ### Jets (coefficients `0` and `1`) of the explicit factors, over any commutative ring -/

section jets

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `a + b ε`. -/
def linS (a b : R) : PowerSeries R := C a + C b * X

/-- `A(ε) = (n + 2ε) ∏_i (2n + 2h_i - 1 + 2ε) (ε - 1)^6` (integer coefficients). -/
def AserR (N : R) (H : Fin 6 → R) : PowerSeries R :=
  linS N 2 * (∏ i, linS (2 * N + 2 * H i - 1) 2) * (linS (-1) 1) ^ 6

/-- `B(ε) = (n - 2 + 2ε) ∏_i (-2h_i - 1 + 2ε) (ε + n)^6` (integer coefficients). -/
def BserR (N : R) (H : Fin 6 → R) : PowerSeries R :=
  linS (N - 2) 2 * (∏ i, linS (-2 * H i - 1) 2) * (linS N 1) ^ 6

omit [CommRing S] in
theorem map_linS [CommRing S] (φ : R →+* S) (a b : R) :
    PowerSeries.map φ (linS a b) = linS (φ a) (φ b) := by
  simp [linS]

theorem map_AserR (φ : R →+* S) (N : R) (H : Fin 6 → R) :
    PowerSeries.map φ (AserR N H) = AserR (φ N) (fun i => φ (H i)) := by
  simp only [AserR, map_mul, map_prod, map_pow, map_linS, map_sub, map_add, map_neg, map_one,
    map_ofNat]

theorem map_BserR (φ : R →+* S) (N : R) (H : Fin 6 → R) :
    PowerSeries.map φ (BserR N H) = BserR (φ N) (fun i => φ (H i)) := by
  simp only [BserR, map_mul, map_prod, map_pow, map_linS, map_sub, map_neg, map_one,
    map_ofNat]

omit [CommRing S] in
theorem coeff0_mul' (F G : PowerSeries R) : coeff 0 (F * G) = coeff 0 F * coeff 0 G := by
  simp only [coeff_zero_eq_constantCoeff_apply, map_mul]

omit [CommRing S] in
theorem coeff1_mul' (F G : PowerSeries R) :
    coeff 1 (F * G) = coeff 0 F * coeff 1 G + coeff 1 F * coeff 0 G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

omit [CommRing S] in
theorem coeff0_linS (a b : R) : coeff 0 (linS a b) = a := by simp [linS]

omit [CommRing S] in
theorem coeff1_linS (a b : R) : coeff 1 (linS a b) = b := by simp [linS]

omit [CommRing S] in
theorem coeff0_pow' (F : PowerSeries R) (k : ℕ) : coeff 0 (F ^ k) = (coeff 0 F) ^ k := by
  simp only [coeff_zero_eq_constantCoeff_apply, map_pow]

omit [CommRing S] in
theorem coeff1_pow6 (F : PowerSeries R) : coeff 1 (F ^ 6) = 6 * (coeff 0 F) ^ 5 * coeff 1 F := by
  simp only [pow_succ, pow_zero, one_mul, coeff1_mul', coeff0_mul']
  ring

end jets

section final

variable {m : ℕ}

/-- `A`, `B` over `ℚ` are `64` times the half-integer factors of `gam_id`. -/
theorem gam_id_int (hqm : q + 1 = 40 * m) :
    Gam m q 1 * AserR ((40 * (m : ℤ) : ℤ) : ℚ) (fun i => ((hm m i : ℤ) : ℚ)) =
    Gam m q 0 * BserR ((40 * (m : ℤ) : ℤ) : ℚ) (fun i => ((hm m i : ℤ) : ℚ)) := by
  have h := gam_id (q := q) hqm (m := m)
  have e2 : ∀ a : ℚ, linS (2 * a - 1) (2 : ℚ) = C 2 * (C (a - 1 / 2) + X) := by
    intro a
    rw [linS, mul_add, ← map_mul]
    congr 2
    ring
  have hA : AserR ((40 * (m : ℤ) : ℤ) : ℚ) (fun i => ((hm m i : ℤ) : ℚ)) =
      C 64 * ((C (((40 * m : ℕ) : ℚ) - 2 * ((0 : ℕ) : ℚ)) + C 2 * X) *
        (∏ i : Fin 6, (C (((40 * m : ℕ) : ℚ) + (hm m i : ℚ) - 1 / 2) + X)) *
          (C (-1 : ℚ) + X) ^ 6) := by
    unfold AserR
    have e3 : ∀ i : Fin 6,
        linS (2 * (((40 * (m : ℤ) : ℤ)) : ℚ) + 2 * ((hm m i : ℤ) : ℚ) - 1) (2 : ℚ) =
          C 2 * (C (((40 * m : ℕ) : ℚ) + (hm m i : ℚ) - 1 / 2) + X) := by
      intro i
      rw [show 2 * (((40 * (m : ℤ) : ℤ)) : ℚ) + 2 * ((hm m i : ℤ) : ℚ) - 1 =
        2 * (((40 * m : ℕ) : ℚ) + (hm m i : ℚ)) - 1 by push_cast; ring, e2]
    rw [Finset.prod_congr rfl fun i _ => e3 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← map_pow]
    simp only [linS]
    rw [show ((2 : ℚ) ^ 6) = 64 by norm_num, show ((((40 * (m : ℤ) : ℤ)) : ℚ)) =
      ((40 * m : ℕ) : ℚ) - 2 * ((0 : ℕ) : ℚ) by push_cast; ring, map_one, one_mul]
    ring
  have hB : BserR ((40 * (m : ℤ) : ℤ) : ℚ) (fun i => ((hm m i : ℤ) : ℚ)) =
      C 64 * ((C (((40 * m : ℕ) : ℚ) - 2 * ((1 : ℕ) : ℚ)) + C 2 * X) *
        (∏ i : Fin 6, (C (-(hm m i : ℚ) - 1 / 2) + X)) * (C (((40 * m : ℕ) : ℚ)) + X) ^ 6) := by
    unfold BserR
    have e3 : ∀ i : Fin 6, linS (-2 * ((hm m i : ℤ) : ℚ) - 1) (2 : ℚ) =
        C 2 * (C (-(hm m i : ℚ) - 1 / 2) + X) := by
      intro i
      rw [show -2 * ((hm m i : ℤ) : ℚ) - 1 = 2 * (-(hm m i : ℚ)) - 1 by ring, e2]
    rw [Finset.prod_congr rfl fun i _ => e3 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← map_pow]
    simp only [linS]
    rw [show ((2 : ℚ) ^ 6) = 64 by norm_num, show ((((40 * (m : ℤ) : ℤ)) : ℚ)) - 2 =
      ((40 * m : ℕ) : ℚ) - 2 * ((1 : ℕ) : ℚ) by push_cast; ring,
      show ((((40 * (m : ℤ) : ℤ)) : ℚ)) = ((40 * m : ℕ) : ℚ) by push_cast; ring, map_one, one_mul]
    ring
  rw [hA, hB]
  linear_combination (C 64 : PowerSeries ℚ) * h

/-- Coefficients of `A` over `ℚ` are the images of those over `ℤ`, and their residues are the
coefficients over `ZMod q`. -/
theorem coeff_AserR_res (N : ℤ) (H : Fin 6 → ℤ) (j : ℕ) :
    HasRes q (coeff j (AserR (N : ℚ) (fun i => (H i : ℚ))))
      (coeff j (AserR (N : ZMod q) (fun i => (H i : ZMod q)))) := by
  have e1 : AserR (N : ℚ) (fun i => (H i : ℚ)) =
      PowerSeries.map (Int.castRingHom ℚ) (AserR N H) := by
    rw [map_AserR]
    rfl
  have e2 : AserR (N : ZMod q) (fun i => (H i : ZMod q)) =
      PowerSeries.map (Int.castRingHom (ZMod q)) (AserR N H) := by
    rw [map_AserR]
    rfl
  rw [e1, e2, coeff_map, coeff_map]
  exact HasRes.int _

theorem coeff_BserR_res (N : ℤ) (H : Fin 6 → ℤ) (j : ℕ) :
    HasRes q (coeff j (BserR (N : ℚ) (fun i => (H i : ℚ))))
      (coeff j (BserR (N : ZMod q) (fun i => (H i : ZMod q)))) := by
  have e1 : BserR (N : ℚ) (fun i => (H i : ℚ)) =
      PowerSeries.map (Int.castRingHom ℚ) (BserR N H) := by
    rw [map_BserR]
    rfl
  have e2 : BserR (N : ZMod q) (fun i => (H i : ZMod q)) =
      PowerSeries.map (Int.castRingHom (ZMod q)) (BserR N H) := by
    rw [map_BserR]
    rfl
  rw [e1, e2, coeff_map, coeff_map]
  exact HasRes.int _

theorem zmod_ne_zero_of_lt {c : ℕ} (hc0 : 0 < c) (hcq : c < q) : (c : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd hc0 h) (not_le.2 hcq)

/-- The arithmetic modulo `q`, over any field in which `40 M = 1` (and a few constants are
non-zero): `b₀ = -a₀`, `a₀ = 20720700 / 20⁶ ≠ 0`, `a₁ + b₁ = 743204640 / 20⁶ ≠ 0`. -/
theorem field_facts {K : Type*} [Field K] (M : K) (h40 : (40 : K) * M = 1) (h20 : (20 : K) ≠ 0)
    (hA0 : (20720700 : K) ≠ 0) (hA1 : (743204640 : K) ≠ 0) :
    coeff 0 (BserR (1 : K) (fun i => M * ((hE i : ℤ) : K))) =
      -coeff 0 (AserR (1 : K) (fun i => M * ((hE i : ℤ) : K))) ∧
    coeff 0 (AserR (1 : K) (fun i => M * ((hE i : ℤ) : K))) ≠ 0 ∧
    coeff 1 (AserR (1 : K) (fun i => M * ((hE i : ℤ) : K))) +
      coeff 1 (BserR (1 : K) (fun i => M * ((hE i : ℤ) : K))) ≠ 0 := by
  have h40ne : (40 : K) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h40
    exact zero_ne_one h40
  have hM : M = 40⁻¹ := eq_inv_of_mul_eq_one_right h40
  have hE0 : hE 0 = -17 := rfl
  have hE1 : hE 1 = 1 := rfl
  have hE2 : hE 2 = 2 := rfl
  have hE3 : hE 3 = 3 := rfl
  have hE4 : hE 4 = 5 := rfl
  have hE5 : hE 5 = 6 := rfl
  simp only [AserR, BserR, Fin.prod_univ_six, coeff1_mul', coeff0_mul', coeff0_linS, coeff1_linS,
    coeff1_pow6, coeff0_pow', hE0, hE1, hE2, hE3, hE4, hE5]
  push_cast
  refine ⟨by ring, ?_, ?_⟩
  · refine ne_of_eq_of_ne (b := 20720700 / 20 ^ 6) ?_ (div_ne_zero hA0 (pow_ne_zero _ h20))
    rw [hM]
    field_simp
    ring
  · refine ne_of_eq_of_ne (b := 743204640 / 20 ^ 6) ?_ (div_ne_zero hA1 (pow_ne_zero _ h20))
    rw [hM]
    field_simp
    ring

/-- The arithmetic modulo `q`: `b₀ = -a₀`, `a₀ ≠ 0`, `a₁ + b₁ ≠ 0`. -/
theorem zmod_facts (hqm : q + 1 = 40 * m) (hbig : 1000000000 < q) :
    coeff 0 (BserR ((40 * (m : ℤ) : ℤ) : ZMod q) (fun i => ((hm m i : ℤ) : ZMod q))) =
      -coeff 0 (AserR ((40 * (m : ℤ) : ℤ) : ZMod q) (fun i => ((hm m i : ℤ) : ZMod q))) ∧
    coeff 0 (AserR ((40 * (m : ℤ) : ℤ) : ZMod q) (fun i => ((hm m i : ℤ) : ZMod q))) ≠ 0 ∧
    coeff 1 (AserR ((40 * (m : ℤ) : ℤ) : ZMod q) (fun i => ((hm m i : ℤ) : ZMod q))) +
      coeff 1 (BserR ((40 * (m : ℤ) : ℤ) : ZMod q) (fun i => ((hm m i : ℤ) : ZMod q))) ≠ 0 := by
  set M : ZMod q := (m : ZMod q) with hMdef
  have h40 : (40 : ZMod q) * M = 1 := by
    have : ((q + 1 : ℕ) : ZMod q) = ((40 * m : ℕ) : ZMod q) := by rw [hqm]
    push_cast at this
    rw [ZMod.natCast_self, zero_add] at this
    rw [hMdef, ← this]
  have h20 : (20 : ZMod q) ≠ 0 := by
    exact_mod_cast zmod_ne_zero_of_lt (q := q) (c := 20) (by norm_num) (by omega)
  have hA0 : (20720700 : ZMod q) ≠ 0 := by
    exact_mod_cast zmod_ne_zero_of_lt (q := q) (c := 20720700) (by norm_num) (by omega)
  have hA1 : (743204640 : ZMod q) ≠ 0 := by
    exact_mod_cast zmod_ne_zero_of_lt (q := q) (c := 743204640) (by norm_num) (by omega)
  have hN : (((40 * (m : ℤ) : ℤ)) : ZMod q) = 1 := by push_cast; rw [← hMdef, h40]
  have hH : ∀ i : Fin 6, ((hm m i : ℤ) : ZMod q) = M * ((hE i : ℤ) : ZMod q) := by
    intro i
    simp [hm, hMdef]
  simp only [hN, hH]
  exact field_facts M h40 h20 hA0 hA1

/-- The final linear algebra modulo `q` (over any field). -/
theorem field_final {K : Type*} [Field K] {g00 g01 g10 g11 a0 a1 b0 b1 : K}
    (r0 : g10 * a0 = g00 * b0) (r1 : g10 * a1 + g11 * a0 = g00 * b1 + g01 * b0)
    (hb0 : b0 = -a0) (ha0 : a0 ≠ 0) (hab : a1 + b1 ≠ 0) (hg : g00 ≠ 0) (h168 : (168 : K) ≠ 0) :
    -(0 + 168 * g11 + 168 * g01) ≠ 0 := by
  have hg10 : g10 = -g00 := by
    have h1 : (g10 + g00) * a0 = 0 := by
      rw [hb0] at r0
      linear_combination r0
    have h2 := (mul_eq_zero.1 h1).resolve_right ha0
    linear_combination h2
  have key : (g01 + g11) * a0 = g00 * (a1 + b1) := by
    rw [hb0, hg10] at r1
    linear_combination r1
  intro h
  have h3 : g01 + g11 = 0 := by
    have : 168 * (g01 + g11) = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left h168
  rw [h3, zero_mul] at key
  exact mul_ne_zero hg hab key.symm

/-- The residue of `q⁹ ρ₀` is non-zero. -/
theorem res_ne_zero (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m)
    (hbig : 1000000000 < q) :
    -(0 + 168 * ((coeff 1 (Gam m q 1) : ℚ) : ZMod q) + 168 * ((coeff 1 (Gam m q 0) : ℚ) : ZMod q))
      ≠ 0 := by
  have hid := gam_id_int (q := q) hqm (m := m)
  have e0 := congrArg (coeff 0) hid
  have e1 := congrArg (coeff 1) hid
  rw [coeff0_mul', coeff0_mul'] at e0
  rw [coeff1_mul', coeff1_mul'] at e1
  have hγ : ∀ {k : ℕ}, k ≤ 1 → ∀ b, HasRes q (coeff b (Gam m q k))
      ((coeff b (Gam m q k) : ℚ) : ZMod q) :=
    fun hk b => HasRes.of_mem (mem_ZqPS.1 (Gam_mem hq2 hqm hk) b)
  have hA := fun j => coeff_AserR_res (q := q) (40 * (m : ℤ)) (hm m) j
  have hB := fun j => coeff_BserR_res (q := q) (40 * (m : ℤ)) (hm m) j
  have r0 := ((hγ (k := 1) le_rfl 0).mul (hA 0))
  rw [e0] at r0
  have r0' := r0.2.symm.trans ((hγ (k := 0) (by norm_num) 0).mul (hB 0)).2
  have r1 := ((hγ (k := 1) le_rfl 0).mul (hA 1)).add ((hγ (k := 1) le_rfl 1).mul (hA 0))
  rw [e1] at r1
  have r1' := r1.2.symm.trans
    (((hγ (k := 0) (by norm_num) 0).mul (hB 1)).add ((hγ (k := 0) (by norm_num) 1).mul (hB 0))).2
  obtain ⟨hb0, ha0, hab⟩ := zmod_facts (q := q) hqm hbig
  have hg : ((coeff 0 (Gam m q 0) : ℚ) : ZMod q) ≠ 0 := (gam00_unit hqm).2
  have h168 : (168 : ZMod q) ≠ 0 := by
    exact_mod_cast zmod_ne_zero_of_lt (q := q) (c := 168) (by norm_num) (by omega)
  exact field_final r0' r1' hb0 ha0 hab hg h168

/-- `v_q(ρ₀) = -9`. -/
theorem rho0_val (hV : Stmt_CoeffVanish) (hqm : q + 1 = 40 * m) (hbig : 1000000000 < q) :
    rho0 (40 * m) (hm m) ≠ 0 ∧ padicValRat q (rho0 (40 * m) (hm m)) = -9 := by
  have hq2 : q ≠ 2 := by omega
  have hr := rho0_res hV hq2 hqm (m := m)
  have hne := res_ne_zero hq2 hqm hbig
  rw [← hr.2] at hne
  have hρ : rho0 (40 * m) (hm m) ≠ 0 := by
    intro h
    rw [h, mul_zero, Rat.cast_zero] at hne
    exact hne rfl
  refine ⟨hρ, ?_⟩
  have h0 := pv_eq_zero hr.1 hne
  have hq0 : ((q : ℚ) ^ 9) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
  rw [padicValRat.mul hq0 hρ, padicValRat.pow, padicValRat.self (Fact.out : q.Prime).one_lt] at h0
  push_cast at h0
  linarith

theorem csum_mem (hV : Stmt_CoeffVanish) (hq2 : q ≠ 2) (hqm : q + 1 = 40 * m) {i : ℕ}
    (hi1 : 1 ≤ i) (hi6 : i ≤ 6) : (q : ℚ) ^ (6 - i) * csum (40 * m) (hm m) i ∈ Zq q := by
  unfold csum genCsum
  rw [Finset.mul_sum]
  exact sum_mem fun k hk => good_all hV hq2 hqm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hi1 hi6

/-- `v_q(ρ₀) < v_q(Z)` for a `ζ`-coefficient `Z = c · c_i` with `q^e Z` integral, `e < 9`. -/
theorem val_lt {Z ρ : ℚ} {e : ℕ} (he : e < 9) (hZ : (q : ℚ) ^ e * Z ∈ Zq q)
    (hρ : padicValRat q ρ = -9) : Z = 0 ∨ padicValRat q ρ < padicValRat q Z := by
  by_cases h : Z = 0
  · exact Or.inl h
  right
  have h0 := pv_nonneg hZ
  have hq0 : ((q : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
  rw [padicValRat.mul hq0 h, padicValRat.pow, padicValRat.self (Fact.out : q.Prime).one_lt] at h0
  rw [hρ]
  have : (e : ℤ) < 9 := by exact_mod_cast he
  linarith

end final

end NVq

open NVq in
/-- **The Lai–Sprang condition for configuration E**, with the prime `q = n - 1 = 40 m - 1`
(taken `> max(B, 10⁹)`): `v_q(ρ₀) = -9`, `v_q(Z₇) ≥ -3`, `v_q(Z₉) ≥ -1`. -/
theorem LaiSprangCond_proof (hV : Stmt_CoeffVanish) : Stmt_LaiSprangCond configE := by
  intro B
  refine (frequently_prime_forty_mul_sub_one_gt (max B 1000000000)).mono ?_
  rintro m ⟨hp, hlt⟩
  have : Fact (40 * m - 1).Prime := ⟨hp⟩
  have hqm : 40 * m - 1 + 1 = 40 * m := by
    have := hp.two_le
    omega
  have hbig : 1000000000 < 40 * m - 1 := lt_of_le_of_lt (le_max_right _ _) hlt
  have hq2 : 40 * m - 1 ≠ 2 := by omega
  obtain ⟨hne, hv⟩ := rho0_val hV hqm hbig
  refine ⟨40 * m - 1, hp, lt_of_le_of_lt (le_max_left _ _) hlt, hne, ?_, ?_⟩
  · have h7 : ((40 * m - 1 : ℕ) : ℚ) ^ 3 * Z7 (40 * m) (hm m) ∈ Zq (40 * m - 1) := by
      unfold Z7
      rw [mul_left_comm]
      exact mul_mem (by exact_mod_cast Zq_nat 46080) (csum_mem hV hq2 hqm (i := 3) (by norm_num)
        (by norm_num))
    exact val_lt (by norm_num) h7 hv
  · have h9 : ((40 * m - 1 : ℕ) : ℚ) ^ 1 * Z9 (40 * m) (hm m) ∈ Zq (40 * m - 1) := by
      unfold Z9
      rw [mul_left_comm]
      exact mul_mem (by exact_mod_cast Zq_nat 860160) (csum_mem hV hq2 hqm (i := 5) (by norm_num)
        (by norm_num))
    exact val_lt (by norm_num) h9 hv

-- The signature is fixed by the blueprint; only `hL1` and `hV` are needed.
set_option linter.unusedVariables false in
/-- **GAP 3**: `S_n ≠ 0` infinitely often along configuration E (via the Lai–Sprang condition at
`q = n - 1`). -/
theorem Nonvanishing_proof (hL1 : Stmt_L1) (hIT : Stmt_IntegrandTaylor) (hD : Stmt_Delta)
    (hDF : Stmt_DeltaFun) (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hCI : Stmt_CrudeInt) :
    Stmt_Nonvanishing configE :=
  Nonvanishing_of_LaiSprang configE hL1 (LaiSprangCond_proof hV)

end Zeta2.Pair

end
