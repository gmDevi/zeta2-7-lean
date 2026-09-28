module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Theorem G: growth of `ρ` and `Z` (proof §5)

gap: 'growth' (assembly of the growth lemmas).  Difficulty 3.

**Task.** Prove `Stmt_Growth7 g7` from `Stmt_MaxU7 g7` and `Stmt_ResidueBound7`: for every
`ε > 0`, eventually `|ρ|, |Z| ≤ e^{(0.71 + ε) 40u}`.

**Informal proof.**
* `|ρ| = |∑_{i ≤ 4, k ≤ n} (i)₄ r_{i,k} AhalfZ (k - 20u) (i+4)| ≤ ∑ 840 |r_{i,k}| · |AhalfZ|`, and
  `|AhalfZ d s| ≤ ∑_{l ≥ 0} (l + 1/2)^{-s} ≤ 2^s · 2` for `s ≥ 5`
  (`∑_{h} |h|^{-s} ≤ 2^s (1 - 2^{-s}) ζ(s)` over distinct half-integers of one sign).  So
  `|ρ| ≤ 4 · 840 · 2^9 · (n+1) · max_{i,k} |r_{i,k}|`, and `|Z| = 46080 |∑_k r_{3,k}| ≤
  46080 (n+1) max_k |r_{3,k}|` (the research proof has the constants `21514` and `5760`).
* `Stmt_ResidueBound7` and `U(k/n) ≤ 0.71` (`Stmt_MaxU7`, `k/n ∈ [0,1]`) give
  `max |r_{i,k}| ≤ C (u+1)^B e^{0.71 · 40u}`.
* So `|ρ|, |Z| ≤ C' (u+1)^{B+1} e^{0.71 · 40u} ≤ e^{(0.71 + ε) 40u}` for large `u`
  (`(u+1)^{B+1} C' ≤ e^{40 ε u}` eventually: `tendsto_pow_mul_exp_neg_atTop_nhds_zero`).

**Lean hints.** `abs_sum_le_sum_abs`, `Finset.sum_le_card_nsmul`; for the `AhalfZ` bound a crude
estimate suffices: `|AhalfZ d s| ≤ ∑_{l < |d|} (2/(2l+1))^s ≤ 2^s ∑_{l} 1/(2l+1)^2 ≤ 2^s · 2`
(`s ≥ 5`, or even `|AhalfZ d s| ≤ |d| 2^s ≤ n 2^s`, which only costs a polynomial factor).

**Numerical check.** `python/z7_mirror.py`, section "Growth7" (`log max(|ρ|,|Z|)/n`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

namespace Growth7Aux

/-- Crude bound on the centred `A`-sums: every term is `h^{-s}` with `|h| ≥ 1/2`. -/
theorem abs_AhalfZ_le (d : ℤ) (s : ℕ) : |AhalfZ d s| ≤ |(d : ℚ)| * 2 ^ s := by
  have key : ∀ x : ℚ, 1 / 2 ≤ |x| → |x⁻¹ ^ s| ≤ 2 ^ s := by
    intro x hx
    rw [abs_pow, abs_inv]
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  unfold AhalfZ
  split_ifs with hd
  · calc |∑ l ∈ range d.toNat, (((l : ℚ) + 1 / 2)⁻¹) ^ s|
        ≤ ∑ l ∈ range d.toNat, |(((l : ℚ) + 1 / 2)⁻¹) ^ s| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ range d.toNat, (2 : ℚ) ^ s := by
          refine sum_le_sum fun l _ => key _ ?_
          rw [abs_of_pos (by positivity)]
          linarith [(Nat.cast_nonneg l : (0 : ℚ) ≤ l)]
      _ = |(d : ℚ)| * 2 ^ s := by
          rw [sum_const, card_range, nsmul_eq_mul, abs_of_nonneg (by exact_mod_cast hd)]
          congr 1
          have h := Int.toNat_of_nonneg hd
          have h2 : (((d.toNat : ℕ) : ℤ) : ℚ) = ((d : ℤ) : ℚ) := by rw [h]
          push_cast at h2
          exact h2
  · rw [abs_neg]
    calc |∑ l ∈ Icc 1 (-d).toNat, (((1 : ℚ) / 2 - l)⁻¹) ^ s|
        ≤ ∑ l ∈ Icc 1 (-d).toNat, |(((1 : ℚ) / 2 - l)⁻¹) ^ s| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ Icc 1 (-d).toNat, (2 : ℚ) ^ s := by
          refine sum_le_sum fun l hl => key _ ?_
          have hl1 : (1 : ℚ) ≤ l := by exact_mod_cast (mem_Icc.1 hl).1
          rw [abs_of_neg (by linarith)]
          linarith
      _ = |(d : ℚ)| * 2 ^ s := by
          have hd' : (d : ℚ) < 0 := by exact_mod_cast not_le.1 hd
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, abs_of_neg hd']
          congr 1
          have h := Int.toNat_of_nonneg (show 0 ≤ -d by omega)
          have h2 : ((((-d).toNat : ℕ) : ℤ) : ℚ) = ((-d : ℤ) : ℚ) := by rw [h]
          push_cast at h2
          exact h2

/-- Polynomials are eventually dominated by `exp(δ u)`. -/
theorem eventually_poly_le_exp (A : ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℕ in atTop, A * (u : ℝ) ^ N ≤ Real.exp (δ * u) := by
  have hA1 : 0 < |A| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop N hδ).def (c := 1 / (|A| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (Real.exp_pos _)] at hm
  have hmN : 0 ≤ (m : ℝ) ^ N := by positivity
  calc A * (m : ℝ) ^ N ≤ (|A| + 1) * (m : ℝ) ^ N := by
        gcongr; linarith [le_abs_self A]
    _ ≤ (|A| + 1) * (1 / (|A| + 1) * Real.exp (δ * m)) := by gcongr
    _ = Real.exp (δ * m) := by field_simp

end Growth7Aux

open Growth7Aux in
theorem Growth7_proof (hU : Stmt_MaxU7 g7) (hR : Stmt_ResidueBound7) : Stmt_Growth7 g7 := by
  obtain ⟨C, B, hRb⟩ := hR
  -- uniform residue bound
  have hr : ∀ u : ℕ, 1 ≤ u → ∀ i k : ℕ, k ≤ 40 * u →
      |(rcoef u i k : ℝ)| ≤ |C| * ((u : ℝ) + 1) ^ B * Real.exp (g7 * (40 * u)) := by
    intro u hu i k hk
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hu' : (0 : ℝ) < 40 * u := by linarith
    have hκ0 : 0 ≤ (k : ℝ) / (40 * u) := by positivity
    have hκ1 : (k : ℝ) / (40 * u) ≤ 1 := by
      rw [div_le_one hu']; exact_mod_cast hk
    have hUk := hU _ hκ0 hκ1
    have he : Real.exp (40 * u * Upot ((k : ℝ) / (40 * u))) ≤ Real.exp (g7 * (40 * u)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hUk hu'.le
      linarith
    calc |(rcoef u i k : ℝ)|
        ≤ C * ((u : ℝ) + 1) ^ B * Real.exp (40 * u * Upot ((k : ℝ) / (40 * u))) := hRb u i k hu hk
      _ ≤ |C| * ((u : ℝ) + 1) ^ B * Real.exp (g7 * (40 * u)) := by
          gcongr; exact le_abs_self C
  intro ε hε
  have hδ : 0 < 40 * ε := by positivity
  set A1 : ℝ := 4 * 840 * 256 * 1681 * 2 ^ B * |C| with hA1
  set A2 : ℝ := 46080 * 41 * 2 ^ B * |C| with hA2
  have hA1n : 0 ≤ A1 := by positivity
  have hA2n : 0 ≤ A2 := by positivity
  filter_upwards [eventually_poly_le_exp (A1 + A2) (B + 2) hδ, eventually_ge_atTop 1]
    with u hpoly hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  set E := Real.exp (g7 * (40 * u)) with hE
  set M := |C| * ((u : ℝ) + 1) ^ B * E with hM
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  have hMn : 0 ≤ M := by positivity
  have hfin : (A1 + A2) * (u : ℝ) ^ (B + 2) * E ≤ Real.exp ((g7 + ε) * (40 * u)) := by
    calc (A1 + A2) * (u : ℝ) ^ (B + 2) * E ≤ Real.exp (40 * ε * u) * E := by gcongr
      _ = Real.exp ((g7 + ε) * (40 * u)) := by
          rw [hE, ← Real.exp_add]; congr 1; ring
  have hpow : ((u : ℝ) + 1) ^ B ≤ 2 ^ B * (u : ℝ) ^ B := by
    rw [← mul_pow]; gcongr; linarith
  have hlin : 40 * (u : ℝ) + 1 ≤ 41 * u := by linarith
  have hsq : (u : ℝ) ≤ (u : ℝ) ^ 2 := by nlinarith
  constructor
  · -- `ρ`
    have hbound : |(rho u : ℝ)| ≤ 4 * ((40 * (u : ℝ) + 1) * (840 * M * ((40 * u + 1) * 256))) := by
      rw [rho, genRhoZ, Rat.cast_neg, abs_neg, Rat.cast_sum]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ i ∈ Icc 1 4, ∑ k ∈ range (40 * u + 1), 840 * M * ((40 * (u : ℝ) + 1) * 256) := by
            refine sum_le_sum fun i hi => ?_
            rw [Rat.cast_sum]
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
            have hi4 : i ≤ 4 := (mem_Icc.1 hi).2
            have hk' : k ≤ 40 * u := Nat.lt_succ_iff.1 (mem_range.1 hk)
            have h1 : |(((i : ℚ) * (i + 1) * (i + 2) * (i + 3) : ℚ) : ℝ)| ≤ 840 := by
              have hq : |((i : ℚ) * (i + 1) * (i + 2) * (i + 3))| ≤ 840 := by
                have hi4' : (i : ℚ) ≤ 4 := by exact_mod_cast hi4
                rw [abs_of_nonneg (by positivity)]
                calc (i : ℚ) * (i + 1) * (i + 2) * (i + 3) ≤ 4 * (4 + 1) * (4 + 2) * (4 + 3) := by
                      gcongr
                  _ = 840 := by norm_num
              exact_mod_cast hq
            have h2 := hr u hu i k hk'
            have h3 : |((AhalfZ ((k : ℤ) - ((20 * u : ℕ) : ℤ)) (i + 4) : ℚ) : ℝ)| ≤
                (40 * (u : ℝ) + 1) * 256 := by
              have hq : |AhalfZ ((k : ℤ) - ((20 * u : ℕ) : ℤ)) (i + 4)| ≤ (40 * (u : ℚ) + 1) * 256 := by
                refine (abs_AhalfZ_le _ _).trans ?_
                have hd : |(((k : ℤ) - ((20 * u : ℕ) : ℤ) : ℤ) : ℚ)| ≤ 40 * (u : ℚ) + 1 := by
                  have hkq : (k : ℚ) ≤ 40 * u := by exact_mod_cast hk'
                  push_cast
                  rw [abs_le]
                  constructor <;> nlinarith [(Nat.cast_nonneg k : (0 : ℚ) ≤ k),
                    (Nat.cast_nonneg u : (0 : ℚ) ≤ u)]
                have hp : (2 : ℚ) ^ (i + 4) ≤ 256 := by
                  calc (2 : ℚ) ^ (i + 4) ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) (by omega)
                    _ = 256 := by norm_num
                exact mul_le_mul hd hp (by positivity) (by positivity)
              exact_mod_cast hq
            rw [Rat.cast_mul, Rat.cast_mul, abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3 (abs_nonneg _)
              (by positivity)
        _ = 4 * ((40 * (u : ℝ) + 1) * (840 * M * ((40 * u + 1) * 256))) := by
            simp only [sum_const, card_range, Nat.card_Icc, nsmul_eq_mul]
            push_cast
            ring
    refine hbound.trans (le_trans ?_ hfin)
    calc 4 * ((40 * (u : ℝ) + 1) * (840 * M * ((40 * u + 1) * 256)))
        = (4 * 840 * 256 * |C|) * ((40 * (u : ℝ) + 1) ^ 2 * ((u : ℝ) + 1) ^ B) * E := by
          rw [hM]; ring
      _ ≤ (4 * 840 * 256 * |C|) * ((41 * (u : ℝ)) ^ 2 * (2 ^ B * (u : ℝ) ^ B)) * E := by
          gcongr
      _ = A1 * (u : ℝ) ^ (B + 2) * E := by rw [hA1]; ring
      _ ≤ (A1 + A2) * (u : ℝ) ^ (B + 2) * E := by gcongr; linarith
  · -- `Z`
    have hbound : |(Zc u : ℝ)| ≤ 46080 * ((40 * (u : ℝ) + 1) * M) := by
      rw [Zc, csum, genCsum, Rat.cast_mul, Rat.cast_sum, abs_mul]
      have h0 : |((46080 : ℚ) : ℝ)| = 46080 := by norm_num
      rw [h0]
      gcongr
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ range (40 * u + 1), |((rcoef u 3 k : ℚ) : ℝ)|
          ≤ ∑ k ∈ range (40 * u + 1), M :=
            sum_le_sum fun k hk => hr u hu 3 k (Nat.lt_succ_iff.1 (mem_range.1 hk))
        _ = (40 * (u : ℝ) + 1) * M := by
            rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    refine hbound.trans (le_trans ?_ hfin)
    have hlin2 : 40 * (u : ℝ) + 1 ≤ 41 * (u : ℝ) ^ 2 := by nlinarith
    calc 46080 * ((40 * (u : ℝ) + 1) * M)
        = (46080 * |C|) * ((40 * (u : ℝ) + 1) * ((u : ℝ) + 1) ^ B) * E := by rw [hM]; ring
      _ ≤ (46080 * |C|) * ((41 * (u : ℝ) ^ 2) * (2 ^ B * (u : ℝ) ^ B)) * E := by gcongr
      _ = A2 * (u : ℝ) ^ (B + 2) * E := by rw [hA2]; ring
      _ ≤ (A1 + A2) * (u : ℝ) ^ (B + 2) * E := by gcongr; linarith

end Zeta2.Z7

end
