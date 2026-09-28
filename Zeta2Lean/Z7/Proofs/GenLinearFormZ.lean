module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# The generic centred linear form (proof Lemma L before any vanishing)

gap: '' (routine, adapted).  **Proved** (architect, 2026-09-26).

**Task.** Prove `Stmt_GenLinearFormZ` from `Stmt_JConv`, `Stmt_Translation` (shared) and
`Stmt_TranslationNeg`: for every `a, n, m` and `r : ℕ → ℕ → ℚ`, the Riemann sums of
`genIntegrandZ a n m r x = ∑_{i ≤ a, k ≤ n} (i)₃ r_{i,k} (x + k - m + 1/2)^{-(i+3)}` converge to
`genRhoZ a n m r + ∑_{i=1}^{a} (i)₃ c_i J_{i+3}`.  Pure linearity; nothing about cand3 is used.

**Proof** (as `Zeta2Lean/Pair/Proofs/GenLinearForm.lean`, with a sign split).
In `ℚ_[2]`, the summand is `w_{i,k} · halfPowZ (i+3) (x + k - m)`, `w_{i,k} = (i)₃ r_{i,k}`.
For each `(i, k)` (`gz_term`), with `s = i + 3`:
* `k ≥ m`: `halfPowZ s (x + k - m) = halfPow s (x + (k - m))` and `Stmt_Translation s (k - m)`
  gives the limit `J_s - s ∑_{l < k-m} halfPow (s+1) l = J_s - s · AhalfZ (k - m) (s+1)`;
* `k < m`: `Stmt_TranslationNeg s (m - k)` gives `J_s + s ∑_{l=1}^{m-k} halfPowZ (s+1) (-l)
  = J_s - s · AhalfZ (k - m) (s+1)`.
Linearity (`HasVolkenborn.const_mul`, `HasVolkenborn.sum` twice) and `(i)₃ (i+3) = (i)₄` give the
claimed value.

**Numerical check.** `python/z7_mirror.py`, section "TranslationNeg / GenLinearFormZ / L7".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

/-- `halfPowZ s z` is the cast of the rational `(z + 1/2)^{-s}`. -/
private theorem gz_halfPowZ_eq_cast (s : ℕ) (z : ℤ) :
    halfPowZ s z = (((((z : ℚ) + 1 / 2)⁻¹) ^ s : ℚ) : ℚ_[2]) := by
  simp [halfPowZ, one_div]

/-- On natural numbers `halfPowZ` is `halfPow`. -/
private theorem gz_halfPowZ_natCast (s x : ℕ) : halfPowZ s (x : ℤ) = halfPow s x := by
  simp [halfPowZ, halfPow]

/-- One term: `∫ (t + 1/2 + k - m)^{-s} dt = J_s - s · AhalfZ (k - m) (s+1)`, both signs. -/
private theorem gz_term (hJ : Stmt_JConv) (hT : Stmt_Translation) (hN : Stmt_TranslationNeg)
    (s k m : ℕ) :
    HasVolkenborn (fun x : ℕ => halfPowZ s ((x : ℤ) + k - m))
      (J s - (s : ℚ_[2]) * ((AhalfZ ((k : ℤ) - m) (s + 1) : ℚ) : ℚ_[2])) := by
  rcases le_or_gt m k with hkm | hkm
  · -- a non-negative shift `d = k - m`
    have h1 := hT s (k - m) (J s) (hJ s)
    have e1 : (fun x : ℕ => halfPowZ s ((x : ℤ) + k - m)) = fun x => halfPow s (x + (k - m)) := by
      funext x
      rw [← gz_halfPowZ_natCast]
      congr 1
      push_cast [Nat.cast_sub hkm]
      ring
    have e2 : ((AhalfZ ((k : ℤ) - m) (s + 1) : ℚ) : ℚ_[2]) =
        ∑ l ∈ range (k - m), halfPow (s + 1) l := by
      have hd : (0 : ℤ) ≤ (k : ℤ) - m := by omega
      have ht : ((k : ℤ) - m).toNat = k - m := by omega
      rw [AhalfZ, ite_eq_left_of_eq_true _ _ (eq_true hd), ht, Rat.cast_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [halfPow_eq_cast]
    rw [e1, e2]
    exact h1
  · -- a negative shift `-e`, `e = m - k ≥ 1`
    have h1 := hN s (m - k) (J s) (hJ s)
    have e1 : (fun x : ℕ => halfPowZ s ((x : ℤ) + k - m)) =
        fun x : ℕ => halfPowZ s ((x : ℤ) - ((m - k : ℕ) : ℤ)) := by
      funext x
      congr 1
      push_cast [Nat.cast_sub hkm.le]
      ring
    have e2 : J s - (s : ℚ_[2]) * ((AhalfZ ((k : ℤ) - m) (s + 1) : ℚ) : ℚ_[2]) =
        J s + (s : ℚ_[2]) * ∑ l ∈ Icc 1 (m - k), halfPowZ (s + 1) (-(l : ℤ)) := by
      have hd : ¬ (0 : ℤ) ≤ (k : ℤ) - m := by omega
      have ht : (-((k : ℤ) - m)).toNat = m - k := by omega
      rw [AhalfZ, ite_eq_right_of_eq_false _ _ (eq_false hd), ht, Rat.cast_neg, Rat.cast_sum,
        mul_neg,
        sub_neg_eq_add]
      congr 2
      refine sum_congr rfl fun l _ => ?_
      rw [gz_halfPowZ_eq_cast]
      congr 3
      push_cast
      ring
    rw [e1, e2]
    exact h1

/-- The generic integrand, cast to `ℚ_[2]`, in `halfPowZ` form. -/
private theorem gz_integrand_cast (a n m : ℕ) (r : ℕ → ℕ → ℚ) (x : ℕ) :
    ((genIntegrandZ a n m r x : ℚ) : ℚ_[2]) =
      ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
        ((((i : ℚ) * (i + 1) * (i + 2)) * r i k : ℚ) : ℚ_[2]) *
          halfPowZ (i + 3) ((x : ℤ) + k - m) := by
  simp only [genIntegrandZ, Rat.cast_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
  rw [gz_halfPowZ_eq_cast, Rat.cast_mul]

theorem GenLinearFormZ_proof (hJ : Stmt_JConv) (hT : Stmt_Translation)
    (hN : Stmt_TranslationNeg) : Stmt_GenLinearFormZ := by
  intro a n m r
  -- `w i k = (i)₃ r_{i,k}` in `ℚ_[2]`
  set w : ℕ → ℕ → ℚ_[2] := fun i k =>
    ((((i : ℚ) * (i + 1) * (i + 2)) * r i k : ℚ) : ℚ_[2]) with hw
  -- linearity + translation: the Riemann sums converge termwise
  have key : HasVolkenborn
      (fun x : ℕ => ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1), w i k * halfPowZ (i + 3) ((x : ℤ) + k - m))
      (∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
        w i k * (J (i + 3) - ((i + 3 : ℕ) : ℚ_[2]) *
          ((AhalfZ ((k : ℤ) - m) (i + 3 + 1) : ℚ) : ℚ_[2]))) := by
    refine HasVolkenborn.sum _ (fun i _ => ?_)
    refine HasVolkenborn.sum _ (fun k _ => ?_)
    exact (gz_term hJ hT hN (i + 3) k m).const_mul (w i k)
  have e1 : (fun x => ((genIntegrandZ a n m r x : ℚ) : ℚ_[2])) =
      fun x : ℕ => ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
        w i k * halfPowZ (i + 3) ((x : ℤ) + k - m) := by
    funext x
    exact gz_integrand_cast a n m r x
  -- the translation terms assemble to `genRhoZ` (`(i)₃ (i+3) = (i)₄`)
  have hrho : (genRhoZ a n m r : ℚ_[2]) = -∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
      w i k * (((i + 3 : ℕ) : ℚ_[2]) * ((AhalfZ ((k : ℤ) - m) (i + 3 + 1) : ℚ) : ℚ_[2])) := by
    simp only [genRhoZ, hw]
    push_cast
    congr 1
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun k _ => ?_))
    ring
  -- the `J`-terms assemble to `(i)₃ c_i J_{i+3}`
  have hcs : ∀ i, ∑ k ∈ range (n + 1), w i k =
      ((i : ℚ_[2]) * (i + 1) * (i + 2)) * (genCsum n r i : ℚ_[2]) := by
    intro i
    simp only [hw, genCsum]
    push_cast
    rw [Finset.mul_sum]
  have e2 : ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
        w i k * (J (i + 3) - ((i + 3 : ℕ) : ℚ_[2]) *
          ((AhalfZ ((k : ℤ) - m) (i + 3 + 1) : ℚ) : ℚ_[2])) =
      (genRhoZ a n m r : ℚ_[2]) +
        ∑ i ∈ Icc 1 a, ((i : ℚ_[2]) * (i + 1) * (i + 2)) * (genCsum n r i : ℚ_[2]) * J (i + 3) := by
    rw [hrho]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcs]
    ring
  rw [e1]
  rwa [e2] at key

end Zeta2.Z7

end
