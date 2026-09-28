module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# Lemma 4.8(1): every class has `E_ξ ≥ -10`

gap: 'denominators'.  Difficulty 3.  No dependencies.

**Task.** Prove `Stmt_Emin7`: for a prime `q ≥ 5` and `k₀ < q`, `(localModel u q k₀).E ≥ -10`.

**Informal proof** (proof Lemma 4.8(1)).  `E = ∑_{zeros} μ - ∑_{poles} a + [δ]`.
* Block `m` contributes at least `⌊L_m/q⌋ > L_m/q - 1` zeros to the class: the values
  `2(c - k₀) + 1`, `c ∈ C_m`, are `L_m` consecutive odd numbers, and every `q` consecutive odd
  numbers contain exactly one multiple of `q` (`q` odd).  (A multiple `2(c - k₀) + 1 = sq` is the
  zero item at `w = -s` of `localModel`, counted once per block containing `c`, i.e. with
  multiplicity `μ(c)`.)
* The level set `I_ℓ = {k : a_k ≥ ℓ}` (an interval of `|I_ℓ| = 40u+1, 36u+1, 32u+1, 28u+1`
  integers) contributes fewer than `|I_ℓ|/q + 1` poles; `∑_ℓ #(I_ℓ ∩ class) = ∑_{k ∈ class} a_k`.
* `∑_m L_m = 136 u` and `∑_ℓ |I_ℓ| = 136 u + 4` give `E > -10 - 4/q`, so `E ≥ -10`.

**Lean hints.** Rewrite `E` as (zero count) − (pole-order sum) + δ from the three `filterMap`
blocks of `localModel` (`List.sum_append`, `List.filterMap` sums); the counts of multiples of `q`
in arithmetic progressions: the pair's `card_odd_dvd`, `cntQ_ge` (`Denominators.lean`),
`Nat.count_modEq_card`, `Nat.Ioc_filter_dvd_card_eq_div`.

**Numerical check.** `python/z7_mirror.py`, section "BigPrimes7 / SmallPrimes7 / Emin7" (all
classes of all primes `5 ≤ q ≤ n` at `n = 40 … 480`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

namespace Emin7Aux

lemma sum_filterMap_range (n : ℕ) (g : ℕ → Option (ℤ × ℤ)) :
    (((List.range n).filterMap g).map Prod.snd).sum =
      ∑ i ∈ range n, ((g i).map Prod.snd).getD 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    cases h : g n <;> simp [h]

lemma sum_filterMap_range_int (n : ℕ) (g : ℤ → Option (ℤ × ℤ)) :
    (((do let a ← List.range n; pure (a : ℤ) : List ℤ).filterMap g).map Prod.snd).sum =
      ∑ i ∈ range n, ((g i).map Prod.snd).getD 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    cases h : g n <;> simp [List.range_succ, h]

lemma getD_ite (c : Prop) [Decidable c] (p : ℤ × ℤ) :
    ((if c then some p else none : Option (ℤ × ℤ)).map Prod.snd).getD 0 =
      if c then p.2 else 0 := by
  split_ifs <;> rfl

/-- Upper count: indices `j` with `k₀ + j q ∈ [A, B]` number at most `(B - A)/q + 1`. -/
lemma card_mul_le (S : Finset ℕ) (q k₀ A B : ℕ) (hAB : A ≤ B)
    (hS : ∀ j ∈ S, A ≤ k₀ + j * q ∧ k₀ + j * q ≤ B) :
    (S.card : ℤ) * q ≤ (B : ℤ) - A + q := by
  rcases S.eq_empty_or_nonempty with hE | hne
  · subst hE; simp; omega
  · have ha := hS _ (S.min'_mem hne)
    have hb := hS _ (S.max'_mem hne)
    have hsub : S ⊆ Icc (S.min' hne) (S.max' hne) := fun x hx =>
      mem_Icc.2 ⟨S.min'_le x hx, S.le_max' x hx⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hab : S.min' hne ≤ S.max' hne := S.min'_le _ (S.max'_mem hne)
    have h1 : (S.card : ℤ) ≤ ((S.max' hne : ℕ) : ℤ) + 1 - (S.min' hne : ℕ) := by omega
    have ha' : (A : ℤ) ≤ k₀ + ((S.min' hne : ℕ) : ℤ) * q := by exact_mod_cast ha.1
    have hb' : (k₀ : ℤ) + ((S.max' hne : ℕ) : ℤ) * q ≤ B := by exact_mod_cast hb.2
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hq0]

/-- Lower count: indices `t < M` with `k₀ + t q ∈ [A + h, B + h)` number at least
`(B - A)/q - 1`. -/
lemma card_mul_ge (q k₀ h A B M : ℕ) (hq : 0 < q) (hk : k₀ < q)
    (hM : B + h ≤ M * q) :
    (B : ℤ) - A - q ≤
      (((range M).filter fun t => A + h ≤ k₀ + t * q ∧ k₀ + t * q < B + h).card : ℤ) * q := by
  obtain ⟨t0, e1, e2⟩ : ∃ t0, A + h ≤ k₀ + t0 * q ∧ k₀ + t0 * q < A + h + q := by
    refine ⟨(A + h + q - 1 - k₀) / q, ?_, ?_⟩
    · have := Nat.lt_div_mul_add (a := A + h + q - 1 - k₀) hq
      omega
    · have := Nat.div_mul_le_self (A + h + q - 1 - k₀) q
      omega
  have e3 : (B - A) / q * q ≤ B - A := Nat.div_mul_le_self _ _
  have e4 : B - A < (B - A) / q * q + q := Nat.lt_div_mul_add hq
  have hsub : (range ((B - A) / q)).map (addLeftEmbedding t0) ⊆
      (range M).filter fun t => A + h ≤ k₀ + t * q ∧ k₀ + t * q < B + h := by
    intro x hx
    simp only [Finset.mem_map, mem_range, addLeftEmbedding_apply] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hiq : (i + 1) * q ≤ (B - A) / q * q := Nat.mul_le_mul_right _ hi
    have hexp : (t0 + i) * q = t0 * q + i * q := add_mul _ _ _
    have hexp2 : (i + 1) * q = i * q + q := by ring
    simp only [mem_filter, mem_range]
    refine ⟨?_, by omega, by omega⟩
    by_contra hc
    have := Nat.mul_le_mul_right q (not_lt.mp hc)
    omega
  have hc := card_le_card hsub
  rw [card_map, card_range] at hc
  have e4' : (((B - A : ℕ)) : ℤ) < (((B - A) / q : ℕ) : ℤ) * q + q := by exact_mod_cast e4
  have e5 : (B : ℤ) - A ≤ ((B - A : ℕ) : ℤ) := by omega
  have e6 : (((B - A) / q : ℕ) : ℤ) * q ≤
      (((range M).filter fun t => A + h ≤ k₀ + t * q ∧ k₀ + t * q < B + h).card : ℤ) * q := by
    exact_mod_cast Nat.mul_le_mul_right q hc
  linarith

/-- The pole part: `q · (-∑ a_k) ≥ -(136 u + 4 q)`. -/
lemma pole_bound (u q k₀ : ℕ) (_hq : 0 < q) :
    -((136 * u + 4 * q : ℕ) : ℤ) ≤ (q : ℤ) *
      ∑ x ∈ range (40 * u / q + 1),
        (if k₀ + x * q ≤ 40 * u then -((apole u (k₀ + x * q) : ℕ) : ℤ) else 0) := by
  have hterm : ∀ x : ℕ,
      (if k₀ + x * q ≤ 40 * u then -((apole u (k₀ + x * q) : ℕ) : ℤ) else 0) =
        -∑ l ∈ range 4, (if 2 * (l * u) ≤ k₀ + x * q ∧ k₀ + x * q + 2 * (l * u) ≤ 40 * u
          then (1 : ℤ) else 0) := by
    intro x
    generalize k₀ + x * q = k
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, apole]
    split_ifs <;> omega
  rw [sum_congr rfl (fun x _ => hterm x), sum_neg_distrib, sum_comm]
  simp only [sum_boole]
  have hc : ∀ l ∈ range 4,
      ((((range (40 * u / q + 1)).filter fun x =>
          2 * (l * u) ≤ k₀ + x * q ∧ k₀ + x * q + 2 * (l * u) ≤ 40 * u).card : ℕ) : ℤ) * q ≤
        40 * u - 4 * ((l : ℤ) * u) + q := by
    intro l hl
    have hl4 : l * u ≤ 3 * u := Nat.mul_le_mul_right _ (by simp at hl; omega)
    have := card_mul_le ((range (40 * u / q + 1)).filter fun x =>
        2 * (l * u) ≤ k₀ + x * q ∧ k₀ + x * q + 2 * (l * u) ≤ 40 * u) q k₀ (2 * (l * u))
      (40 * u - 2 * (l * u)) (by omega) (by intro j hj; simp only [mem_filter] at hj; omega)
    have hcast : ((40 * u - 2 * (l * u) : ℕ) : ℤ) = 40 * u - 2 * ((l : ℤ) * u) := by
      have : ((l * u : ℕ) : ℤ) = (l : ℤ) * u := by push_cast; ring
      omega
    rw [hcast] at this
    push_cast at this
    linarith
  have hs : (∑ l ∈ range 4, ((((range (40 * u / q + 1)).filter fun x =>
          2 * (l * u) ≤ k₀ + x * q ∧ k₀ + x * q + 2 * (l * u) ≤ 40 * u).card : ℕ) : ℤ)) * q ≤
        136 * u + 4 * q := by
    rw [sum_mul]
    refine (sum_le_sum hc).trans (le_of_eq ?_)
    simp [sum_range_succ]
    ring
  push_cast
  nlinarith

/-- The zero part: `q · (∑ μ) ≥ 136 u - 6 q`. -/
lemma zero_bound (u q k₀ : ℕ) (hq5 : 5 ≤ q) (hk : k₀ < q) :
    (136 * u : ℤ) - 6 * q ≤ (q : ℤ) *
      ∑ x ∈ range (40 * u / q + 2),
        (if 0 ≤ (k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2 ∧
            (k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2 < 40 * (u : ℤ) ∧
            mu u ((k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2).toNat ≠ 0 then
          ((mu u ((k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2).toNat : ℕ) : ℤ) else 0) := by
  set h := (q + 1) / 2 with hhdef
  have hh : ((q : ℤ) + 1) / 2 = (h : ℤ) := by omega
  have hq : 0 < q := by omega
  have heta : ∀ m, eta m ≤ 13 := by decide
  have hterm : ∀ x : ℕ,
      ∑ m : Fin 6, (if eta m * u + h ≤ k₀ + x * q ∧ k₀ + x * q < 40 * u - eta m * u + h
        then (1 : ℤ) else 0) ≤
      (if 0 ≤ (k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2 ∧
            (k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2 < 40 * (u : ℤ) ∧
            mu u ((k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2).toNat ≠ 0 then
          ((mu u ((k₀ : ℤ) + (x : ℤ) * q - ((q : ℤ) + 1) / 2).toNat : ℕ) : ℤ) else 0) := by
    intro x
    rw [hh]
    have hc : (k₀ : ℤ) + (x : ℤ) * q - h = ((k₀ + x * q : ℕ) : ℤ) - h := by push_cast; ring
    rw [hc]
    generalize k₀ + x * q = K
    rw [sum_boole]
    by_cases hK : h ≤ K ∧ K < 40 * u + h
    · have hf : (univ.filter fun m : Fin 6 =>
          eta m * u + h ≤ K ∧ K < 40 * u - eta m * u + h) =
          univ.filter fun m => ((K : ℤ) - h).toNat ∈ block u m := by
        ext m
        have := Nat.mul_le_mul_right u (heta m)
        simp only [mem_filter, mem_univ, true_and, block, mem_Ico]
        omega
      rw [hf]
      have hmu : (univ.filter fun m => ((K : ℤ) - h).toNat ∈ block u m).card =
          mu u ((K : ℤ) - h).toNat := rfl
      rw [hmu]
      split_ifs with hcond
      · exact le_refl _
      · have : mu u ((K : ℤ) - h).toNat = 0 := by
          by_contra hne
          exact hcond ⟨by omega, by omega, hne⟩
        rw [this]
        simp
    · have hf : (univ.filter fun m : Fin 6 =>
          eta m * u + h ≤ K ∧ K < 40 * u - eta m * u + h) = ∅ := by
        ext m
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        omega
      rw [hf, card_empty]
      split_ifs <;> simp
  have hper : ∀ m : Fin 6, (40 * (u : ℤ) - 2 * ((eta m : ℤ) * u) - q) ≤
      ((((range (40 * u / q + 2)).filter fun t =>
        eta m * u + h ≤ k₀ + t * q ∧ k₀ + t * q < 40 * u - eta m * u + h).card : ℕ) : ℤ) * q := by
    intro m
    have hM : 40 * u - eta m * u + h ≤ (40 * u / q + 2) * q := by
      have := Nat.lt_div_mul_add (a := 40 * u) hq
      rw [add_mul]
      omega
    have := card_mul_ge q k₀ h (eta m * u) (40 * u - eta m * u) (40 * u / q + 2) hq hk hM
    have he := Nat.mul_le_mul_right u (heta m)
    have hcast : ((40 * u - eta m * u : ℕ) : ℤ) = 40 * u - (eta m : ℤ) * u := by
      have : ((eta m * u : ℕ) : ℤ) = (eta m : ℤ) * u := by push_cast; ring
      omega
    rw [hcast] at this
    push_cast at this
    linarith
  have hsum : (136 * u : ℤ) - 6 * q ≤ ∑ m : Fin 6,
      ((((range (40 * u / q + 2)).filter fun t =>
        eta m * u + h ≤ k₀ + t * q ∧ k₀ + t * q < 40 * u - eta m * u + h).card : ℕ) : ℤ) * q := by
    refine le_trans (le_of_eq ?_) (sum_le_sum fun m _ => hper m)
    simp [Fin.sum_univ_six, eta]
    ring
  refine hsum.trans ?_
  have hq0 : (0 : ℤ) ≤ q := by positivity
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hterm x) hq0)
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_boole]
  ring

end Emin7Aux

open Emin7Aux in
theorem Emin7_proof : Stmt_Emin7 := by
  intro u q k₀ hq hq5 hk
  simp only [LocalType.E, localModel, List.map_append, List.sum_append]
  rw [sum_filterMap_range, sum_filterMap_range_int]
  simp only [getD_ite]
  refine le_trans ?_ (le_add_of_nonneg_right ?_)
  · have h1 := pole_bound u q k₀ (by omega)
    have h2 := zero_bound u q k₀ hq5 hk
    have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq5
    push_cast at h1
    nlinarith
  · split_ifs <;> simp

end Zeta2.Z7

end
