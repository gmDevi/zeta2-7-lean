module

public import Zeta2Lean.Z7.Proofs.LocalExpansion7

@[expose] public section

/-!
# Lemma 4.7: per-pole bounds for the good part and `c₃`

gap: 'denominators'.  Difficulty 4.

**Statement** (`Stmt_PerPole7`, from `Stmt_PF7`): for a prime `q ≥ 5`, `q > 2x + 2` (i.e.
`80u + 2q < q²`), a pole `k ≤ n` in the class `k₀ = k mod q` (local point `v_k = -⌊k/q⌋`, doubled
`w = -2⌊k/q⌋`) with net local order `a = -netE w` and Taylor series
`τ_k(u) = u^a RR_ξ(v_k + u) = taylorAt τ w`: if `τ_l = 0` for `E + a - T < l ≤ a - 1`
(`PoleLevAt`), then `v_q(r_{i,k}) ≥ T` for every `i`.

**Informal proof** (proof Lemma 4.7).  Expand around the centre `t_k = -k` exactly as in the class
lemma: `R_n(t_k + qw) = q^E Û(t_k + qw) w^{-a} τ_k(w)` with `Û(t_k + qw) = ∑_m F'_m q^m w^m`,
`F'_m ∈ ℤ_(q)`.  The coefficient of `(t - t_k)^{-i} = (qw)^{-i}` is
`r_{i,k} = q^{E+i} ∑_{l + m = a - i} F'_m q^m τ_l`; each term has valuation `≥ E + a - l`, and the
terms with `l > E + a - T` vanish.  (For `i > a` both sides are `0`: `r_{4, n/2} = 0` at the
centre, where `a = 3`.)  All `τ_l` are `q`-integral for `q > 2x + 2` (Lemma 4.2).

## Lean proof (exact algebra, no `q`-adic analysis)

Write `k = k₀ + J q` (`k₀ = k % q`, `J = k / q`), `τ = localModel u q k₀`, `w = -2J`,
`ord = -netE w` (the net pole order, `LE7.ord`), `ctr ∈ {0, 1}` (`1` only at the centre `n/2` when
the δ-zero is in the disc), so `a_k = ord + ctr` (`LE7.ord_pole`, `LE7.netE_pole`).

1. `r_{i,k} = [ε^{a_k - i}] G_k` (`rcoef`; it is `0` unless `1 ≤ i ≤ a_k`).
2. Per-pole factorisation `LE7.Gser_factor` (Lemma 4.1 at `-k`):
   `G_k(ε) = q^{E + ord} ε^{ctr} Û(-k + ε) τ_k(ε/q)`.  So `[ε^{a_k - i}] G_k = 0` if
   `a_k - i < ctr` (this is `r_{4,n/2} = 0`), and otherwise, with `N = a_k - i - ctr = ord - i`,
   `r_{i,k} = q^{E + ord} q^{-N} ∑_{m + l = N} q^m [ε^m]Û(-k+ε) · τ_l`
   (`LE7.coeff_mul_rescale_inv`).
3. `[ε^m]Û(-k+ε)` is `q`-integral (`LE7.PSV_Uhat`), `τ_l` is `q`-integral
   (`LE7.PSV_taylorAt_model`, Lemma 4.2, needs `80u + 2q < q²`); the term has valuation
   `≥ E + ord - N + m = E + ord - l`.
   Since `l ≤ N ≤ ord - 1`, `PoleLevAt` gives `τ_l = 0` unless `l ≤ E + ord - T`.

`Stmt_PF7` is not needed: `LE7.Gser_factor` is proved from the definitions directly.

**Numerical check.** `python/z7_mirror.py`, section "local models" (`PoleLevGe` against the
research engine's `LG`), and section "ThmK7" (per-pole levels versus the true valuations);
`python/z7_audit.py` (`PerPole7`, 8 values of `n`, the bound is attained).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Z7

namespace PP7

/-- `v_q(q^N) ≥ N` for a natural exponent. -/
theorem valGe_qpow {q : ℕ} [Fact q.Prime] (N : ℕ) : ValGe q (N : ℤ) ((q : ℚ) ^ N) := by
  rw [← zpow_natCast]
  exact LE7.valGe_qzpow _

/-- `v_q(q^{-N}) ≥ -N` for a natural exponent. -/
theorem valGe_inv_qpow {q : ℕ} [Fact q.Prime] (N : ℕ) :
    ValGe q (-(N : ℤ)) (((q : ℚ) ^ N)⁻¹) := by
  rw [← zpow_natCast, ← zpow_neg]
  exact LE7.valGe_qzpow _

/-- **Lemma 4.7 at the pole `k = k₀ + J q`** (`J = ⌊k/q⌋`, local position `w = -2J`). -/
theorem perPole {u q k₀ J : ℕ} (T : ℤ) (hq : q.Prime) (hq2 : q ≠ 2) (hk₀ : k₀ < q)
    (hsq : 80 * u + 2 * q < q ^ 2) (hJ : k₀ + J * q ≤ 40 * u)
    (hlev : PoleLevAt (localModel u q k₀) (-(2 * (J : ℤ))) T) (i : ℕ) :
    ValGe q T (rcoef u i (k₀ + J * q)) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hab := LE7.ord_pole u q k₀ hq.pos hk₀ hJ
  have hnet := LE7.netE_pole u q k₀ hq.pos hk₀ hJ
  have hU := LE7.PSV_Uhat (u := u) hq2 hk₀ J
  have hτ := LE7.PSV_taylorAt_model hq hq2 hk₀ hsq (Or.inl hJ)
  unfold PoleLevAt at hlev
  unfold rcoef
  split_ifs with hi
  swap
  · exact LE7.valGe_zero T
  obtain ⟨hi1, hia, -⟩ := hi
  rw [LE7.Gser_factor u q k₀ hq hq2 hk₀ hJ, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hc
  swap
  · rw [mul_zero]
    exact LE7.valGe_zero T
  rw [LE7.coeff_mul_rescale_inv hq0, coeff_mul, Finset.mul_sum, Finset.mul_sum]
  apply LE7.valGe_sum
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_rescale]
  by_cases hl : coeff p.2 (taylorAt (localModel u q k₀) (-(2 * (J : ℤ)))) = 0
  · rw [hl, mul_zero, mul_zero, mul_zero]
    exact LE7.valGe_zero T
  have hlT : ((p.2 : ℕ) : ℤ) ≤
      (localModel u q k₀).E - (localModel u q k₀).netE (-(2 * (J : ℤ))) - T := by
    by_contra h
    push Not at h
    exact hl (hlev p.2 (by unfold LE7.ord at hab; omega) h)
  refine LE7.valGe_mono (LE7.valGe_mul (LE7.valGe_qzpow _) (LE7.valGe_mul (valGe_inv_qpow _)
    (LE7.valGe_mul (LE7.valGe_mul (valGe_qpow p.1) (hU p.1) rfl) (hτ p.2) rfl) rfl) rfl) ?_
  unfold LE7.ord at hab ⊢
  omega

end PP7

theorem PerPole7_proof (_hPF : Stmt_PF7) : Stmt_PerPole7 := by
  intro u q k T hq hq5 hsq hk hlev i
  have hk₀ : k % q < q := Nat.mod_lt _ hq.pos
  have hkJ : k % q + k / q * q = k := by
    have := Nat.mod_add_div k q
    rw [mul_comm] at this
    exact this
  have hJ : k % q + k / q * q ≤ 40 * u := by rw [hkJ]; exact hk
  have h := PP7.perPole T hq (by omega) hk₀ hsq hJ hlev i
  rw [hkJ] at h
  exact h

end Zeta2.Z7

end
