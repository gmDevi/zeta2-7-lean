module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Lemma 4.4: the kernel identity (sum of all residues vanishes)

gap: 'denominators'.  **Proved** (architect, 2026-09-26).

**Task.** Prove `Stmt_KernelIdentity7` from `Stmt_CoeffVanish7`: for `q ≥ 1`, `j ≥ 1`,
`∑_{k₀ < q} (kerRes u q k₀ c₀ j c + c q^j farRes u q k₀ j) = 0`.

**Informal proof.** This is `∑_ξ ∮_{D_ξ} R_n Ψ dt = 0` for `Ψ = c₀ + c q^j ∑_{i<q} (t+i)^{-j}`: the
sum of all residues of a rational function of degree `≤ -3 ≤ -2`.  With the explicit residues of
`kerRes`/`farRes` it becomes elementary:
* the `c₀` part is `c₀ ∑_{k ≤ n} r_{1,k} = c₀ c₁ = 0` (`Stmt_CoeffVanish7.c1`; every `k ≤ n` lies in
  exactly one class `k mod q`: `ki_fib`);
* the `c q^j` part, collected per pole `k` and per `i`: the class of `k` contributes
  `∑_{i' < q, i' ≠ k} C(-j, i-1) (i' - k)^{-(i+j-1)}` (the term `i' = k₀` from `kerRes`, the others
  from `farRes`; if `k = k₀ < q` both give `i' ≠ k₀`), and the kernel poles of all the other
  classes contribute `∑_{k₀ < q, k₀ ≠ k} C(-i, j-1) (k - k₀)^{-(i+j-1)}` (`ki_swap`); termwise,
  `C(-j, i-1) z^{-(i+j-1)} + C(-i, j-1) (-z)^{-(i+j-1)} = 0` (`ki_pair`: the residues of
  `(t+a)^{-i}(t+b)^{-j}` at `-a` and `-b` cancel).

**Numerical check.** `python/z7_mirror.py`, section "ClassLemma7 / KernelIdentity7 / FarPart7"
(exact `0` at `n = 80, 200`, several `q, j, c₀, c`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

/-- The residue identity: for `i, j ≥ 1` and any `z`,
`C(-j, i-1) z^{-(i+j-1)} + C(-i, j-1) (-z)^{-(i+j-1)} = 0`. -/
private theorem ki_pair (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (z : ℚ) :
    negChoose j (i - 1) * (z⁻¹) ^ (i + j - 1) +
      negChoose i (j - 1) * ((-z)⁻¹) ^ (i + j - 1) = 0 := by
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  have e1 : a + (b + 1) - 1 = a + b := by omega
  have e2 : b + (a + 1) - 1 = a + b := by omega
  have e3 : a + 1 + (b + 1) - 1 = a + b + 1 := by omega
  have e4 : a + 1 - 1 = a := by omega
  have e5 : b + 1 - 1 = b := by omega
  simp only [negChoose, e1, e2, e3, e4, e5]
  rw [← Nat.choose_symm_add, inv_neg, neg_pow (z⁻¹) (a + b + 1)]
  have h : ((-1 : ℚ) ^ b) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hp : (-1 : ℚ) ^ (a + b + 1) = (-1) ^ a * (-1) ^ b * (-1) := by
    rw [pow_succ, pow_add]
  rw [hp]
  linear_combination (-((a + b).choose a : ℚ) * (z⁻¹) ^ (a + b + 1) * (-1) ^ a) * h

/-- Summing over the fibres of `k ↦ k mod q`. -/
private theorem ki_fib (n q : ℕ) (hq : 1 ≤ q) (f : ℕ → ℕ → ℚ) :
    ∑ k₀ ∈ range q, ∑ k ∈ (range (n + 1)).filter (fun k => k % q = k₀), f k₀ k =
      ∑ k ∈ range (n + 1), f (k % q) k := by
  have h1 : ∀ k₀ ∈ range q, ∑ k ∈ (range (n + 1)).filter (fun k => k % q = k₀), f k₀ k =
      ∑ k ∈ (range (n + 1)).filter (fun k => k % q = k₀), f (k % q) k := by
    intro k₀ _
    refine sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]
  rw [sum_congr rfl h1]
  exact Finset.sum_fiberwise_of_maps_to (fun k _ => mem_range.2 (Nat.mod_lt _ (by omega)))
    (fun k => f (k % q) k)

/-- Swapping a double sum with the diagonal removed. -/
private theorem ki_swap (n q : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ k₀ ∈ range q, ∑ k ∈ (range (n + 1)).erase k₀, f k₀ k =
      ∑ k ∈ range (n + 1), ∑ k₀ ∈ (range q).erase k, f k₀ k := by
  simp only [← Finset.filter_ne', Finset.sum_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun k₀ _ => ?_
  by_cases h : k = k₀
  · subst h; simp
  · simp [h, Ne.symm h]

theorem KernelIdentity7_proof (hV : Stmt_CoeffVanish7) : Stmt_KernelIdentity7 := by
  intro u q c0 c j hq hj
  set n := 40 * u with hn
  -- the pieces of `kerRes` and `farRes`
  set S1 : ℕ → ℚ := fun k₀ => ∑ k ∈ (range (n + 1)).filter (fun k => k % q = k₀), rcoef u 1 k
    with hS1
  set G : ℕ → ℕ → ℚ := fun k₀ k =>
    (if k ≠ k₀ then ∑ i ∈ Icc (1 : ℕ) 4,
        rcoef u i k * negChoose j (i - 1) * (((k₀ : ℚ) - k)⁻¹) ^ (i + j - 1) else 0) +
      ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i k * ∑ i' ∈ (range q).erase k₀,
        negChoose j (i - 1) * (((i' : ℚ) - k)⁻¹) ^ (i + j - 1) with hG
  set H : ℕ → ℕ → ℚ := fun k₀ k => ∑ i ∈ Icc (1 : ℕ) 4,
      rcoef u i k * negChoose i (j - 1) * (((k : ℚ) - k₀)⁻¹) ^ (i + j - 1) with hH
  have hsplit : ∀ k₀, kerRes u q k₀ c0 j c + c * (q : ℚ) ^ j * farRes u q k₀ j =
      c0 * S1 k₀ + c * (q : ℚ) ^ j *
        (∑ k ∈ (range (n + 1)).filter (fun k => k % q = k₀), G k₀ k +
          ∑ k ∈ (range (n + 1)).erase k₀, H k₀ k) := by
    intro k₀
    have hfilt : ((range (n + 1)).filter (fun k => k % q = k₀ ∧ k ≠ k₀)) =
        ((range (n + 1)).filter (fun k => k % q = k₀)).filter (fun k => k ≠ k₀) := by
      rw [Finset.filter_filter]
    simp only [kerRes, farRes, hS1, hG, hH, ← hn, hfilt, Finset.sum_filter,
      Finset.sum_add_distrib]
    ring
  rw [sum_congr rfl fun k₀ _ => hsplit k₀, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_add_distrib, ki_fib n q hq G, ki_swap n q H]
  -- `c₀`-part: `∑_k r_{1,k} = c₁ = 0`
  have hS1sum : ∑ k₀ ∈ range q, S1 k₀ = 0 := by
    have := ki_fib n q hq (fun _ k => rcoef u 1 k)
    rw [hS1]
    simp only
    rw [this]
    exact hV.c1 u
  -- the `c`-part cancels pole by pole
  have hGk : ∀ k ∈ range (n + 1), G (k % q) k = ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i k *
      ∑ i' ∈ (range q).erase k, negChoose j (i - 1) * (((i' : ℚ) - k)⁻¹) ^ (i + j - 1) := by
    intro k _
    rcases lt_or_ge k q with hkq | hkq
    · have hm : k % q = k := Nat.mod_eq_of_lt hkq
      simp only [hG, hm, ne_eq, not_true_eq_false, ite_false, zero_add]
    · have hm : k % q ≠ k := by
        have := Nat.mod_lt k (by omega : 0 < q)
        omega
      have hmem : k % q ∈ range q := mem_range.2 (Nat.mod_lt _ (by omega))
      have hk : k ∉ range q := by simp; omega
      simp only [hG, Ne.symm hm, ne_eq, not_false_eq_true, ite_true,
        Finset.erase_eq_of_notMem hk]
      rw [← Finset.sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← Finset.add_sum_erase _ _ hmem]
      ring
  have hHk : ∀ k, ∑ k₀ ∈ (range q).erase k, H k₀ k = ∑ i ∈ Icc (1 : ℕ) 4, rcoef u i k *
      ∑ i' ∈ (range q).erase k, negChoose i (j - 1) * (((k : ℚ) - i')⁻¹) ^ (i + j - 1) := by
    intro k
    simp only [hH, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => ?_
    ring
  have hc : ∑ k ∈ range (n + 1), G (k % q) k +
      ∑ k ∈ range (n + 1), ∑ k₀ ∈ (range q).erase k, H k₀ k = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hGk k hk, hHk k, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    rw [Finset.sum_eq_zero fun i' _ => ?_, mul_zero]
    have := ki_pair i j hi1 hj ((i' : ℚ) - k)
    rw [show -((i' : ℚ) - k) = (k : ℚ) - i' by ring] at this
    exact this
  rw [hS1sum, hc]
  ring

end Zeta2.Z7

end
