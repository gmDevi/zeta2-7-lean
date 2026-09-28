module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Theorem K: the per-prime exponent bound from class certificates (proof §4.4–4.6)

gap: 'denominators' (combination).  Difficulty 3.

**Task.** Prove `Stmt_ThmK7` from `Stmt_ClassLemma7`, `Stmt_KernelIdentity7`, `Stmt_FarPart7`,
`Stmt_PerPole7` and `Stmt_Emin7`: for a prime `q ≥ 29` with `q² > 2n + 3q`, a kernel
`κ = c₀ + c y^j` (`1 ≤ j ≤ 4`, `q`-integral coefficients, `c ≠ 0 → j - 4 ≥ T`) and `T ≤ 0`, if every
class satisfies `LevGe … (T + 5)` and `PoleLevGe … T`, then `e_q(n) ≤ -T`.

**Informal proof** (proof Theorems 4.6 and K).
1. *Splitting* (elementary identities, prove them here):
   `rho u = -rhoP u` (`AhalfZ d s = sgn(d) ∑_{o ∈ oddBetween d} (2/o)^s`) and
   `rhoP u = ∑_{k₀ < q} classBad u q k₀ + goodPart u q` (split `oddBetween` by `q ∣ o`, and
   `range (40u+1)` by `k % q`).
2. *Bad part* `B = ∑_ξ β_ξ = ∑_ξ [β_ξ - 24 q^{-5} kerRes_ξ] - 24 q^{-5} c q^j ∑_ξ farRes_ξ`
   (`Stmt_KernelIdentity7`).  Each bracket has `v_q ≥ T` (`Stmt_ClassLemma7`, `P = T + 5`); each
   far term has `v_q ≥ j - 4 ≥ T` (`Stmt_FarPart7`; its hypothesis `j + 1 ≤ q + E_ξ` holds since
   `E_ξ ≥ -10` (`Stmt_Emin7`) and `q ≥ 29 ≥ j + 11`), or vanishes when `c = 0`.
3. *Good part*: `X(k, o/2)` with `q ∤ o` is a `ℤ_(q)`-combination of the `r_{i,k}`
   (`(i)₄ ∈ {24, 120, 360, 840}` and `2/o` are `q`-units for `q ≥ 11`), and `v_q(r_{i,k}) ≥ T` by
   `Stmt_PerPole7` (the pole `k` is the local point `-2⌊k/q⌋` of the class `k mod q`, and
   `PoleLevGe` covers it: `localModel` contains the item `(-2⌊k/q⌋, -a_k)`).
4. `c₃ = ∑_k r_{3,k}` has `v_q ≥ T`, and `Z = 46080 c₃`.  So `v_q(ρ), v_q(Z) ≥ T`, i.e.
   `padicValNat q (den) ≤ -T` for both, and `eq7 u q ≤ -T`.

**Lean hints.** `ValGe` is `padicNorm q x ≤ q^{-L}`: use `padicNorm.nonarchimedean`,
`padicNorm.mul`, `padicNorm.sum_le` (ultrametric sums), and for the conclusion
`padicNorm.eq_zpow_of_nonzero`, `padicValRat.of_nat`, `Rat.den`/`padicValNat` via
`padicValRat_of_nat`-style lemmas (the pair's `pn_*` helpers in `Denominators.lean`).

**Numerical check.** `python/z7_mirror.py`, section "ThmK7" (the hypotheses at the row kernels, and
`eq7 ≤ -T` against the true exponents, at `n = 200` and sampled primes of `n = 960`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

namespace ThmK7

/-! ### Elementary identities: `rho = -rhoP = -(∑ classBad + goodPart)` -/

/-- `AhalfZ d s = sgn(d) ∑_{o ∈ oddBetween d} (2/o)^s`. -/
theorem AhalfZ_eq (d : ℤ) (s : ℕ) :
    AhalfZ d s = ((d.sign : ℤ) : ℚ) * ∑ o ∈ oddBetween d, ((2 : ℚ) / o) ^ s := by
  unfold AhalfZ oddBetween
  by_cases hd : 0 ≤ d
  · simp only [hd, ↓reduceIte]
    rcases hd.lt_or_eq with hd | hd
    · rw [Int.sign_eq_one_of_pos hd, Finset.sum_image (by intro a _ b _ h; simpa using h)]
      push_cast
      rw [one_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [show (l : ℚ) + 1 / 2 = (2 * l + 1) / 2 by ring, inv_div]
    · subst hd
      simp
  · simp only [hd, ↓reduceIte]
    have hd' : d < 0 := lt_of_not_ge hd
    rw [Int.sign_eq_neg_one_of_neg hd', Finset.sum_image (by intro a _ b _ h; simpa using h)]
    have hIcc : Icc 1 (-d).toNat = Ico 1 ((-d).toNat + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    push_cast
    rw [neg_one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [show (1 : ℚ) / 2 - (1 + l) = -(2 * l + 1) / 2 by ring, inv_div]

/-- `rho u = -rhoP u`. -/
theorem rho_eq (u : ℕ) : rho u = -rhoP u := by
  unfold rho genRhoZ rhoP Xk
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [AhalfZ_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  ring

/-- `rhoP u = ∑_{k₀ < q} classBad u q k₀ + goodPart u q`. -/
theorem rhoP_split (u q : ℕ) (hq : 0 < q) :
    rhoP u = ∑ k₀ ∈ range q, classBad u q k₀ + goodPart u q := by
  unfold rhoP classBad goodPart
  rw [Finset.sum_fiberwise_of_maps_to (g := fun k => k % q)
    (fun k _ => Finset.mem_range.2 (Nat.mod_lt k hq)), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_add, Finset.sum_filter_add_sum_filter_not]

/-- The pole `-k` is the item `(-2⌊k/q⌋, -a_k)` of the local model of the class `k mod q`. -/
theorem pole_mem (u q k : ℕ) (hk : k ≤ 40 * u) :
    (-(2 * ((k / q : ℕ) : ℤ)), -((apole u k : ℕ) : ℤ)) ∈ (localModel u q (k % q)).items := by
  unfold localModel
  apply List.mem_append_left
  apply List.mem_append_left
  rw [List.mem_filterMap]
  refine ⟨k / q, List.mem_range.2 ?_, ?_⟩
  · have := Nat.div_le_div_right (c := q) hk
    omega
  · simp [Nat.mod_add_div', hk]

/-! ### `ValGe` calculus -/

variable {q : ℕ} [hqF : Fact q.Prime]

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

theorem valGe_pow {x : ℚ} (h : ValGe q 0 x) (n : ℕ) : ValGe q 0 (x ^ n) := by
  induction n with
  | zero => simpa using valGe_int (q := q) 1
  | succ n ih => rw [pow_succ]; exact valGe_mul ih h (by simp)

theorem valGe_poch (i : ℕ) : ValGe q 0 ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) := by
  have e : ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) =
      (((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℤ) : ℚ) := by push_cast; ring
  rw [e]
  exact valGe_int _

theorem valGe_two_div (hq3 : 3 ≤ q) {o : ℤ} (ho : ¬ (q : ℤ) ∣ o) : ValGe q 0 ((2 : ℚ) / o) := by
  have h2 : padicNorm q ((2 : ℤ) : ℚ) = 1 := by
    rw [padicNorm.int_eq_one_iff]
    intro h
    have : q ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have ho' : padicNorm q (o : ℚ) = 1 := (padicNorm.int_eq_one_iff o).2 ho
  unfold ValGe
  rw [padicNorm.div]
  push_cast at h2
  rw [h2, ho']
  simp

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
    unfold ValGe at h
    rw [padicNorm.eq_zpow_of_nonzero hx] at h
    have := (zpow_le_zpow_iff_right₀ q_gt_one).mp h
    omega
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    simp
    omega

end ThmK7

open ThmK7 in
theorem ThmK7_proof (hC : Stmt_ClassLemma7) (hK : Stmt_KernelIdentity7) (hF : Stmt_FarPart7)
    (hP : Stmt_PerPole7) (hE : Stmt_Emin7) : Stmt_ThmK7 := by
  intro u q c0 c j T hq hq29 hsq hT hj1 hj4 hc0 hc hcj hLev hPole
  have : Fact q.Prime := ⟨hq⟩
  have hq5 : 5 ≤ q := by omega
  have hsq2 : 80 * u + 2 * q < q ^ 2 := by omega
  -- per-pole bounds `v_q(r_{i,k}) ≥ T`
  have hr : ∀ i k, k ≤ 40 * u → ValGe q T (rcoef u i k) := by
    intro i k hk
    exact hP u q k T hq hq5 hsq2 hk
      (hPole (k % q) (Nat.mod_lt k hq.pos) _ (pole_mem u q k hk)) i
  have hr' : ∀ i, ∀ k ∈ range (40 * u + 1), ValGe q T (rcoef u i k) := fun i k hk =>
    hr i k (by rw [Finset.mem_range] at hk; omega)
  -- `Z = 46080 c₃`
  have hZ : ValGe q T (Zc u) := by
    unfold Zc csum genCsum
    have h46 : ((46080 : ℚ)) = ((46080 : ℤ) : ℚ) := by norm_num
    rw [h46]
    exact valGe_mul (valGe_int _) (valGe_sum _ _ (hr' 3)) (by simp)
  -- the good part
  have hG : ValGe q T (goodPart u q) := by
    unfold goodPart
    apply valGe_sum
    intro k hk
    have hk' : k ≤ 40 * u := by rw [Finset.mem_range] at hk; omega
    refine valGe_mul (valGe_int _) ?_ (zero_add T)
    apply valGe_sum
    intro o ho
    rw [Finset.mem_filter] at ho
    unfold Xk
    apply valGe_sum
    intro i _
    exact valGe_mul (valGe_mul (valGe_poch i) (hr i k hk') (zero_add T))
      (valGe_pow (valGe_two_div (by omega) ho.2) _) (add_zero T)
  -- the bad part, through the kernel identity
  have hB : ValGe q T (∑ k₀ ∈ range q, classBad u q k₀) := by
    have hKI := hK u q c0 c j hq.one_lt.le hj1
    have hker : ∑ k₀ ∈ range q, kerRes u q k₀ c0 j c =
        -∑ k₀ ∈ range q, c * (q : ℚ) ^ j * farRes u q k₀ j := by
      rw [Finset.sum_add_distrib] at hKI
      linarith
    have key : ∑ k₀ ∈ range q, classBad u q k₀ =
        ∑ k₀ ∈ range q, (classBad u q k₀ - 24 * ((q : ℚ) ^ 5)⁻¹ * kerRes u q k₀ c0 j c) -
          ∑ k₀ ∈ range q, 24 * ((q : ℚ) ^ 5)⁻¹ * (c * (q : ℚ) ^ j * farRes u q k₀ j) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hker]
      ring
    rw [key]
    apply valGe_sub
    · apply valGe_sum
      intro k₀ hk₀
      have hk₀' := Finset.mem_range.1 hk₀
      have := hC u q k₀ c0 c j (T + 5) hq hq5 hsq2 hk₀' hj1 hc0 hc (hLev k₀ hk₀')
      simpa using this
    · apply valGe_sum
      intro k₀ hk₀
      have hk₀' := Finset.mem_range.1 hk₀
      by_cases hcz : c = 0
      · subst hcz
        simp only [zero_mul, mul_zero]
        exact valGe_zero _
      · have hEm := hE u q k₀ hq hq5 hk₀'
        have hjT := hcj hcz
        exact valGe_mono (hF u q k₀ j c hq hq5 hsq2 hk₀' hj1 hc (by omega)) (by omega)
  have hrho : ValGe q T (rho u) := by
    rw [rho_eq, rhoP_split u q hq.pos]
    exact valGe_neg (valGe_add hB hG)
  unfold eq7
  rw [Nat.cast_max]
  exact max_le (den_le hT hrho) (den_le hT hZ)

end Zeta2.Z7

end
