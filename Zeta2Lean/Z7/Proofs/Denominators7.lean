module

public import Zeta2Lean.Z7.Statements
public import Zeta2Lean.Pair.Proofs.Denominators

@[expose] public section

/-!
# Theorem A: the odd denominator is `≤ e^{(3.99 + ε) n}` (proof §4.9, PNT)

gap: 'denominators' (analytic part).  Difficulty 4.

**Status: proved** (complete, kernel-checked; `#print axioms Denominators7_proof` gives
`[propext, Classical.choice, Quot.sound]`).  Hypothesis: `Stmt_ExpBounds7` (all five fields are
used); PNT (`PNT_Stmt`, the hypothesis of `Stmt_Denominators7`) enters only through the pair's
`Pair.Den.theta_eventually`.

**Construction.** `D u := Dodd7 u = ∏_{q ≤ 40u odd prime} q^{eq7 u q}` (odd, `Dodd7_odd`),
`e u := e7 u = v₂(den ρ) + v₂(den Z)`.
* *Integrality (every `u`).* `den_dvd`: `den x ∣ 2^{e u} D u` for `x = ρ, Z`, prime by prime
  (`Nat.factorization_prime_le_iff_dvd`): at `2` by the choice of `e`; at an odd `p ≤ n` because
  `p^{eq7} ∣ D` and `v_p(den x) ≤ eq7 u p` (definition of `eq7`); at an odd `p > n` because
  `eq7 u p = 0` (`big`).  Then `int_of_den_dvd` (`x · den x = num x`).
* *Size.* `log D = ∑_{q ≤ n odd} eq7 u q · log q` (`log_Dodd7`), and `log_sum_bound7` splits the odd
  primes `q ≤ n = 40u` into four ranges:
  1. `q ≤ 1000` or `q² ≤ 2n + 3q` (`small`): `≤ 19 log(2n+1)` each, at most `1001 + √(5n)`
     primes: `≤ 38038 (√(2n) + 1) log(2n) = o(n)`;
  2. `q > 1000`, `q² > 2n + 3q`, `q ∣ u` (`crude`): `≤ 14 log q` each, total `≤ 14 log u`
     (`Nat.prod_primeFactors_dvd`);
  3. the same with `q ∤ u` and `140 q ≤ n` (`tail`): `≤ 10`, total `≤ 10 θ(n/140)`;
  4. the same with `n/q ∈ [1, 140)` (`rows`): `chain7_sum` over the 3409 rows of `denTable7`
     (they tile `[1, 140)`: `denTable7_chain`, `denTable7_rowOK`, `denTable7_length`, all
     `decide +kernel`) gives `≤ ∑_rows f (θ(n/a) - θ(n/b))`, and PNT on the `2 · 3409` end points
     gives `≤ n ∑_rows f (1/a - 1/b) + 28 · 3409 · δ n`.
  Primes `q > n` do not occur.  The constant: `table_integral`,
  `∑_rows f (1/a - 1/b) + 10/140 ≤ 3.99` (true value `3.9240891610`), from the kernel-checked
  fixed-point fact `denTable7_integral_fixed` (`Uterm7_ge`: `S f (1/a - 1/b) ≤ Uterm7`).
  With `δ = ε/400000` the total is `≤ (3.99 + ε/2) n` eventually.

**Reuse.** From `Zeta2Lean.Pair.Proofs.Denominators` (namespace `Zeta2.Pair.Den`, only
`PNT_Stmt`-dependent analytic lemmas): `oddPrimesLE`, `primesIoc`, `sum_primesIoc_split`,
`theta_nat_sub`, `interval_sum_le`, `theta_eventually`, `eventually_forall_list`, `list_sum_le`,
`list_sum_affine`, `list_sum_mul_left`, `small_term_eventually`.  All new helpers live in the
namespace `Zeta2.Z7.Den7`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

namespace Den7

/-! ### Kernel-checked facts about the table -/

/-- `chain7 A L B`: the rows of `L` tile `[A₁/A₂, B₁/B₂)` in order (exact endpoint pairs). -/
def chain7 : ℕ × ℕ → List DenRow → ℕ × ℕ → Bool
  | A, [], B => decide (A = B)
  | A, r :: L, B => decide (r.an = A.1) && decide (r.ad = A.2) && chain7 (r.bn, r.bd) L B

/-- Row checks: positive denominators, `1 ≤ a < b ≤ 140`, `f ≤ 14`. -/
def rowOK7 (r : DenRow) : Bool :=
  decide (0 < r.ad) && decide (0 < r.bd) && decide (r.an * r.bd < r.bn * r.ad) &&
    decide (r.ad ≤ r.an) && decide (r.bn ≤ 140 * r.bd) && decide (r.f ≤ 14)

theorem denTable7_chain : chain7 (1, 1) denTable7 (140, 1) = true := by decide +kernel

theorem denTable7_rowOK : denTable7.all rowOK7 = true := by decide +kernel

theorem denTable7_length : denTable7.length = 3409 := by decide +kernel

/-! ### Row facts -/

lemma rowOK7_spec (r : DenRow) (h : rowOK7 r = true) :
    0 < r.ad ∧ 0 < r.bd ∧ r.an * r.bd < r.bn * r.ad ∧ r.ad ≤ r.an ∧ r.bn ≤ 140 * r.bd ∧
      r.f ≤ 14 := by
  unfold rowOK7 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

lemma mem_rowOK7 {r : DenRow} (hr : r ∈ denTable7) : rowOK7 r = true :=
  List.all_eq_true.1 denTable7_rowOK r hr

lemma rowOK7_an_pos (r : DenRow) (h : rowOK7 r = true) : 0 < r.an := by
  obtain ⟨had, -, -, hda, -, -⟩ := rowOK7_spec r h
  omega

lemma rowOK7_bn_pos (r : DenRow) (h : rowOK7 r = true) : 0 < r.bn := by
  obtain ⟨-, -, hab, -, -, -⟩ := rowOK7_spec r h
  rcases Nat.eq_zero_or_pos r.bn with h0 | h0
  · rw [h0, zero_mul] at hab
    exact absurd hab (Nat.not_lt_zero _)
  · exact h0

lemma rowOK7_rat (r : DenRow) (h : rowOK7 r = true) :
    (1 : ℚ) ≤ r.a ∧ r.a < r.b ∧ r.b ≤ 140 := by
  obtain ⟨had, hbd, hab, hda, hb140, -⟩ := rowOK7_spec r h
  have had' : (0 : ℚ) < r.ad := by exact_mod_cast had
  have hbd' : (0 : ℚ) < r.bd := by exact_mod_cast hbd
  refine ⟨?_, ?_, ?_⟩
  · unfold DenRow.a
    rw [le_div_iff₀ had', one_mul]
    exact_mod_cast hda
  · unfold DenRow.a DenRow.b
    rw [div_lt_div_iff₀ had' hbd']
    exact_mod_cast hab
  · unfold DenRow.b
    rw [div_le_iff₀ hbd']
    exact_mod_cast hb140

lemma rowOK7_real (r : DenRow) (h : rowOK7 r = true) :
    (1 : ℝ) ≤ ((r.a : ℚ) : ℝ) ∧ ((r.a : ℚ) : ℝ) < ((r.b : ℚ) : ℝ) ∧ ((r.b : ℚ) : ℝ) ≤ 140 := by
  obtain ⟨h1, h2, h3⟩ := rowOK7_rat r h
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-! ### Chains of rows and sums over primes -/

lemma chain7_le : ∀ (L : List DenRow) (A B : ℕ × ℕ), chain7 A L B = true →
    (∀ r ∈ L, rowOK7 r = true) → 0 < A.2 →
      ((A.1 : ℚ) / A.2 ≤ (B.1 : ℚ) / B.2 ∧ 0 < B.2)
  | [], A, B, h, _, hA => by
    simp only [chain7, decide_eq_true_eq] at h
    subst h
    exact ⟨le_rfl, hA⟩
  | r :: L, A, B, h, hok, _ => by
    simp only [chain7, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpa, hqa⟩, hL⟩ := h
    have hr := hok r List.mem_cons_self
    obtain ⟨-, hbd, -, -, -, -⟩ := rowOK7_spec r hr
    obtain ⟨ih1, ih2⟩ := chain7_le L (r.bn, r.bd) B hL
      (fun c hc => hok c (List.mem_cons_of_mem _ hc)) hbd
    refine ⟨?_, ih2⟩
    have e : (A.1 : ℚ) / A.2 = r.a := by unfold DenRow.a; rw [hpa, hqa]
    rw [e]
    exact (rowOK7_rat r hr).2.1.le.trans ih1

/-- Summing a bounded function over the primes of a chain of rows. -/
lemma chain7_sum (y : ℝ) (hy : 0 ≤ y) (f : ℕ → ℝ) (w : DenRow → ℝ) :
    ∀ (L : List DenRow) (A B : ℕ × ℕ), chain7 A L B = true → (∀ r ∈ L, rowOK7 r = true) →
      0 < A.1 → 0 < A.2 →
      (∀ r ∈ L, ∀ q : ℕ, q.Prime → ((r.a : ℚ) : ℝ) ≤ y / q → y / q < ((r.b : ℚ) : ℝ) →
        f q ≤ w r) →
      (∀ r ∈ L, 0 ≤ w r) →
      ∑ q ∈ Pair.Den.primesIoc ⌊y / ((B.1 : ℝ) / B.2)⌋₊ ⌊y / ((A.1 : ℝ) / A.2)⌋₊,
          f q * Real.log q ≤
        (L.map fun r => w r * (Chebyshev.theta (y / ((r.a : ℚ) : ℝ)) -
          Chebyshev.theta (y / ((r.b : ℚ) : ℝ)))).sum
  | [], A, B, h, _, _, _, _, _ => by
    simp only [chain7, decide_eq_true_eq] at h
    subst h
    simp [Pair.Den.primesIoc]
  | r :: L, A, B, h, hok, hA1, hA2, hf, hw => by
    simp only [chain7, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpa, hqa⟩, hL⟩ := h
    have hr := hok r List.mem_cons_self
    obtain ⟨-, hbd, -, -, -, -⟩ := rowOK7_spec r hr
    have hok' : ∀ c ∈ L, rowOK7 c = true := fun c hc => hok c (List.mem_cons_of_mem _ hc)
    obtain ⟨hbB, -⟩ := chain7_le L (r.bn, r.bd) B hL hok' hbd
    have ih := chain7_sum y hy f w L (r.bn, r.bd) B hL hok' (rowOK7_bn_pos r hr) hbd
      (fun c hc => hf c (List.mem_cons_of_mem _ hc))
      (fun c hc => hw c (List.mem_cons_of_mem _ hc))
    have eA : ((A.1 : ℝ) / A.2) = ((r.a : ℚ) : ℝ) := by
      unfold DenRow.a
      rw [← hpa, ← hqa]
      push_cast
      rfl
    have eb : (((r.bn, r.bd) : ℕ × ℕ).1 : ℝ) / (((r.bn, r.bd) : ℕ × ℕ).2 : ℝ) =
        ((r.b : ℚ) : ℝ) := by
      unfold DenRow.b
      push_cast
      rfl
    rw [eb] at ih
    rw [eA]
    obtain ⟨h1a, habR, -⟩ := rowOK7_real r hr
    have haR : (0 : ℝ) < ((r.a : ℚ) : ℝ) := lt_of_lt_of_le one_pos h1a
    have hbR : (0 : ℝ) < ((r.b : ℚ) : ℝ) := haR.trans habR
    have hbBR : ((r.b : ℚ) : ℝ) ≤ (B.1 : ℝ) / B.2 := by
      have e : (r.b : ℚ) = ((r.bn, r.bd).1 : ℚ) / ((r.bn, r.bd).2 : ℚ) := rfl
      have h' : (r.b : ℚ) ≤ (B.1 : ℚ) / B.2 := by rw [e]; exact hbB
      have := (Rat.cast_le (K := ℝ)).2 h'
      push_cast at this
      exact this
    have i1 : ⌊y / ((B.1 : ℝ) / B.2)⌋₊ ≤ ⌊y / ((r.b : ℚ) : ℝ)⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hy hbR hbBR)
    have i2 : ⌊y / ((r.b : ℚ) : ℝ)⌋₊ ≤ ⌊y / ((r.a : ℚ) : ℝ)⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hy haR habR.le)
    rw [Pair.Den.sum_primesIoc_split _ _ _ i1 i2, List.map_cons, List.sum_cons]
    have hc := Pair.Den.interval_sum_le y ((r.a : ℚ) : ℝ) ((r.b : ℚ) : ℝ) (w r) hy haR habR.le
      f (fun q hq h1 h2 => hf r List.mem_cons_self q hq h1 h2)
    linarith

/-! ### The numerical constant `∑ f (1/a - 1/b) + 10/140 ≤ 3.99` -/

lemma ceil_div_ge (N d : ℕ) (hd : 0 < d) : (N : ℝ) / d ≤ (((N + d - 1) / d : ℕ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  have h := Nat.lt_div_mul_add (a := N + d - 1) hd
  have h2 : N ≤ (N + d - 1) / d * d := by omega
  exact_mod_cast h2

lemma floor_div_le (N d : ℕ) (hd : 0 < d) : (((N / d : ℕ)) : ℝ) ≤ (N : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast Nat.div_mul_le_self N d

lemma Uterm7_ge (r : DenRow) (h : rowOK7 r = true) :
    (Sfix7 : ℝ) * ((r.f : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))) ≤
      (Uterm7 r : ℝ) := by
  obtain ⟨had, hbd, -, -, -, -⟩ := rowOK7_spec r h
  have han := rowOK7_an_pos r h
  have hbn := rowOK7_bn_pos r h
  have hA := ceil_div_ge (Sfix7 * r.ad) r.an han
  have hB := floor_div_le (Sfix7 * r.bd) r.bn hbn
  unfold Uterm7
  set A := (Sfix7 * r.ad + r.an - 1) / r.an with hAdef
  set B := (Sfix7 * r.bd) / r.bn with hBdef
  have hsub : (A : ℝ) - B ≤ ((A - B : ℕ) : ℝ) := by
    rcases le_total B A with hBA | hAB
    · rw [Nat.cast_sub hBA]
    · rw [Nat.sub_eq_zero_of_le hAB, Nat.cast_zero]
      have : (A : ℝ) ≤ B := by exact_mod_cast hAB
      linarith
  have han' : (r.an : ℝ) ≠ 0 := by exact_mod_cast han.ne'
  have hbn' : (r.bn : ℝ) ≠ 0 := by exact_mod_cast hbn.ne'
  have had' : (r.ad : ℝ) ≠ 0 := by exact_mod_cast had.ne'
  have hbd' : (r.bd : ℝ) ≠ 0 := by exact_mod_cast hbd.ne'
  have ea : 1 / ((r.a : ℚ) : ℝ) = (r.ad : ℝ) / r.an := by
    unfold DenRow.a
    push_cast
    field_simp
  have eb : 1 / ((r.b : ℚ) : ℝ) = (r.bd : ℝ) / r.bn := by
    unfold DenRow.b
    push_cast
    field_simp
  have hf0 : (0 : ℝ) ≤ r.f := Nat.cast_nonneg _
  push_cast at hA hB
  rw [ea, eb, Nat.cast_mul]
  calc (Sfix7 : ℝ) * ((r.f : ℝ) * ((r.ad : ℝ) / r.an - (r.bd : ℝ) / r.bn))
      = (r.f : ℝ) * ((Sfix7 : ℝ) * r.ad / r.an - (Sfix7 : ℝ) * r.bd / r.bn) := by ring
    _ ≤ (r.f : ℝ) * ((A : ℝ) - B) := by
        apply mul_le_mul_of_nonneg_left _ hf0
        linarith
    _ ≤ (r.f : ℝ) * ((A - B : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hsub hf0

lemma list_sum_natCast {α : Type*} (L : List α) (f : α → ℕ) :
    (((L.map f).sum : ℕ) : ℝ) = (L.map fun a => (f a : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

/-- The exponent integral of the table plus the tail: `∑ f (1/a - 1/b) + 10/140 ≤ 3.99`. -/
theorem table_integral :
    (denTable7.map fun r => (r.f : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))).sum +
      10 / 140 ≤ 399 / 100 := by
  have hS : (0 : ℝ) < Sfix7 := by unfold Sfix7; norm_num
  set T := (denTable7.map Uterm7).sum with hT
  set Sig := (denTable7.map fun r => (r.f : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))).sum
    with hSig
  have h1 : (Sfix7 : ℝ) * Sig ≤ (T : ℝ) := by
    rw [hSig, hT, ← Pair.Den.list_sum_mul_left, list_sum_natCast]
    apply Pair.Den.list_sum_le
    intro r hr
    exact Uterm7_ge r (mem_rowOK7 hr)
  have h2 : (Sfix7 : ℝ) * (10 / 140) ≤ (((10 * Sfix7 + 139) / 140 : ℕ) : ℝ) := by
    have := ceil_div_ge (10 * Sfix7) 140 (by norm_num)
    have e : 10 * Sfix7 + 140 - 1 = 10 * Sfix7 + 139 := by omega
    rw [e] at this
    push_cast at this
    linarith
  have h3 := (Nat.cast_le (α := ℝ)).2 denTable7_integral_fixed
  rw [← hT, Nat.cast_add] at h3
  have h4 := floor_div_le (399 * Sfix7) 100 (by norm_num)
  push_cast at h4
  have h5 : (Sfix7 : ℝ) * (Sig + 10 / 140) ≤ (Sfix7 : ℝ) * (399 / 100) := by
    rw [mul_add]
    linarith
  exact le_of_mul_le_mul_left h5 hS

/-! ### The prime number theorem part -/

/-- The main analytic estimate: `∑_{q ≤ n odd} e_q log q ≤ (3.99 + ε) n` eventually. -/
theorem log_sum_bound7 (hPNT : PNT_Stmt) (hX : Stmt_ExpBounds7) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∑ q ∈ Pair.Den.oddPrimesLE (40 * u), (eq7 u q : ℝ) * Real.log q ≤
      (399 / 100 + ε) * (40 * u) := by
  set δ : ℝ := ε / 400000 with hδ
  have hδ0 : 0 < δ := by positivity
  have hPa : ∀ᶠ m : ℕ in atTop, ∀ r ∈ denTable7,
      |Chebyshev.theta (40 * m / ((r.a : ℚ) : ℝ)) - 40 * m / ((r.a : ℚ) : ℝ)| ≤
        δ * (40 * m / ((r.a : ℚ) : ℝ)) :=
    Pair.Den.eventually_forall_list denTable7 _ fun r hr =>
      Pair.Den.theta_eventually hPNT _
        (lt_of_lt_of_le one_pos (rowOK7_real r (mem_rowOK7 hr)).1) δ hδ0
  have hPb : ∀ᶠ m : ℕ in atTop, ∀ r ∈ denTable7,
      |Chebyshev.theta (40 * m / ((r.b : ℚ) : ℝ)) - 40 * m / ((r.b : ℚ) : ℝ)| ≤
        δ * (40 * m / ((r.b : ℚ) : ℝ)) :=
    Pair.Den.eventually_forall_list denTable7 _ fun r hr =>
      Pair.Den.theta_eventually hPNT _
        (by have := rowOK7_real r (mem_rowOK7 hr); linarith) δ hδ0
  have hP140 := Pair.Den.theta_eventually hPNT 140 (by norm_num) δ hδ0
  have hsm := Pair.Den.small_term_eventually (4 * 38052 / ε)
  filter_upwards [hPa, hPb, hP140, hsm, eventually_ge_atTop 1] with u hua hub hu140 husm hu1
  have hu0 : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hn0 : (0 : ℝ) ≤ 40 * (u : ℝ) := by positivity
  set X : ℝ := (Real.sqrt (2 * (40 * u : ℝ)) + 1) * Real.log (2 * (40 * u : ℝ)) with hXdef
  have hlog80 : 0 ≤ Real.log (2 * (40 * u : ℝ)) := Real.log_nonneg (by linarith)
  have hsq0 : 0 ≤ Real.sqrt (2 * (40 * u : ℝ)) := Real.sqrt_nonneg _
  have hX0 : Real.log (2 * (40 * u : ℝ)) ≤ X := by
    rw [hXdef]
    nlinarith
  -- the splitting of the odd primes `q ≤ n`
  set F : ℕ → ℝ := fun q => (eq7 u q : ℝ) * Real.log q with hF
  set S := Pair.Den.oddPrimesLE (40 * u) with hS
  set P : ℕ → Prop := fun q => 1000 < q ∧ 80 * u + 3 * q < q ^ 2 with hP
  have hsplit1 := Finset.sum_filter_add_sum_filter_not S P F
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (S.filter P) (fun q => q ∣ u) F
  have hsplit3 := Finset.sum_filter_add_sum_filter_not
    ((S.filter P).filter (fun q => ¬ q ∣ u)) (fun q => 140 * q ≤ 40 * u) F
  -- (1) small primes: `q ≤ 1000` or `q² ≤ 2n + 3q`
  have hSS : ∑ q ∈ S.filter (fun q => ¬ P q), F q ≤ 38038 * X := by
    have hL : Real.log ((80 * u + 1 : ℕ) : ℝ) ≤ 2 * Real.log (2 * (40 * u : ℝ)) := by
      have h1 : Real.log ((80 * u + 1 : ℕ) : ℝ) ≤ Real.log ((2 * (40 * u : ℝ)) ^ 2) := by
        apply Real.log_le_log (by positivity)
        push_cast
        nlinarith
      have h2 : Real.log ((2 * (40 * u : ℝ)) ^ 2) = 2 * Real.log (2 * (40 * u : ℝ)) := by
        rw [Real.log_pow]
        norm_num
      linarith
    have hterm : ∀ q ∈ S.filter (fun q => ¬ P q),
        F q ≤ 19 * Real.log ((80 * u + 1 : ℕ) : ℝ) := by
      intro q hq
      simp only [hS, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
      obtain ⟨⟨hqn, hqp, hq2⟩, -⟩ := hq
      have hE := hX.small u q hqp hq2
      have hpow : q ^ Nat.log q (80 * u + 1) ≤ 80 * u + 1 := Nat.pow_log_le_self q (by omega)
      have hlog2 : (Nat.log q (80 * u + 1) : ℝ) * Real.log q ≤
          Real.log ((80 * u + 1 : ℕ) : ℝ) := by
        rw [← Real.log_pow]
        apply Real.log_le_log (by have := hqp.pos; positivity)
        exact_mod_cast hpow
      simp only [hF]
      calc (eq7 u q : ℝ) * Real.log q ≤ ((19 * Nat.log q (80 * u + 1) : ℕ) : ℝ) * Real.log q := by
            apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg q)
            exact_mod_cast hE
        _ = 19 * ((Nat.log q (80 * u + 1) : ℝ) * Real.log q) := by push_cast; ring
        _ ≤ 19 * Real.log ((80 * u + 1 : ℕ) : ℝ) := by linarith
    have hcard : ((S.filter (fun q => ¬ P q)).card : ℝ) ≤
        1001 * (Real.sqrt (2 * (40 * u : ℝ)) + 1) := by
      have hsub : S.filter (fun q => ¬ P q) ⊆ range (1001 + Nat.sqrt (200 * u)) := by
        intro q hq
        simp only [hS, hP, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
        obtain ⟨⟨hqn, hqp, hq2⟩, hns⟩ := hq
        rw [mem_range]
        rcases le_or_gt q 1000 with h | h
        · omega
        · have hsq : q ^ 2 ≤ 80 * u + 3 * q := by
            by_contra hc
            exact hns ⟨h, by omega⟩
          have : q ≤ Nat.sqrt (200 * u) := by
            rw [Nat.le_sqrt']
            omega
          omega
      have h1 := Finset.card_le_card hsub
      rw [card_range] at h1
      have h2 : ((Nat.sqrt (200 * u) : ℕ) : ℝ) ≤ Real.sqrt ((200 * u : ℕ) : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      have h3 : Real.sqrt ((200 * u : ℕ) : ℝ) ≤ 2 * Real.sqrt (2 * (40 * u : ℝ)) := by
        have e : (2 * Real.sqrt (2 * (40 * u : ℝ))) ^ 2 = 4 * (2 * (40 * u : ℝ)) := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          norm_num
        calc Real.sqrt ((200 * u : ℕ) : ℝ)
            ≤ Real.sqrt ((2 * Real.sqrt (2 * (40 * u : ℝ))) ^ 2) := by
              apply Real.sqrt_le_sqrt
              rw [e]
              push_cast
              nlinarith
          _ = 2 * Real.sqrt (2 * (40 * u : ℝ)) := Real.sqrt_sq (by positivity)
      have h4 : ((S.filter (fun q => ¬ P q)).card : ℝ) ≤ 1001 + ((Nat.sqrt (200 * u) : ℕ) : ℝ) := by
        exact_mod_cast h1
      nlinarith
    calc ∑ q ∈ S.filter (fun q => ¬ P q), F q
        ≤ ∑ q ∈ S.filter (fun q => ¬ P q), 19 * Real.log ((80 * u + 1 : ℕ) : ℝ) :=
          Finset.sum_le_sum hterm
      _ = ((S.filter (fun q => ¬ P q)).card : ℝ) * (19 * Real.log ((80 * u + 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1001 * (Real.sqrt (2 * (40 * u : ℝ)) + 1)) *
            (19 * (2 * Real.log (2 * (40 * u : ℝ)))) := by
          apply mul_le_mul hcard (by linarith) (by positivity) (by positivity)
      _ = 38038 * X := by rw [hXdef]; ring
  -- (2) primes dividing `u` (crude bound `14`)
  have hSD : ∑ q ∈ (S.filter P).filter (fun q => q ∣ u), F q ≤ 14 * X := by
    have hterm : ∀ q ∈ (S.filter P).filter (fun q => q ∣ u), F q ≤ 14 * Real.log q := by
      intro q hq
      simp only [hS, hP, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
      obtain ⟨⟨⟨hqn, hqp, hq2⟩, hq1000, hsq⟩, -⟩ := hq
      have := hX.crude u q hqp (by omega) hsq
      simp only [hF]
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg q)
      exact_mod_cast this
    have hsub : (S.filter P).filter (fun q => q ∣ u) ⊆ u.primeFactors := by
      intro q hq
      simp only [hS, hP, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
      rw [Nat.mem_primeFactors]
      exact ⟨hq.1.1.2.1, hq.2, by omega⟩
    have hprod : Real.log (∏ q ∈ u.primeFactors, (q : ℝ)) ≤ Real.log u := by
      have hdvd := Nat.prod_primeFactors_dvd u
      have hle : ∏ q ∈ u.primeFactors, q ≤ u := Nat.le_of_dvd (by omega) hdvd
      have hpos : 0 < ∏ q ∈ u.primeFactors, q :=
        Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
      have hpos' := (Nat.cast_lt (α := ℝ)).2 hpos
      have hle' := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at hpos' hle'
      exact Real.log_le_log hpos' hle'
    have hlogu : Real.log u ≤ Real.log (2 * (40 * u : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    calc ∑ q ∈ (S.filter P).filter (fun q => q ∣ u), F q
        ≤ ∑ q ∈ (S.filter P).filter (fun q => q ∣ u), 14 * Real.log q := Finset.sum_le_sum hterm
      _ ≤ ∑ q ∈ u.primeFactors, 14 * Real.log q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro q _ _
          have := Real.log_natCast_nonneg q
          positivity
      _ = 14 * Real.log (∏ q ∈ u.primeFactors, (q : ℝ)) := by
          rw [← Finset.mul_sum, Real.log_prod]
          intro q hq
          have := (Nat.prime_of_mem_primeFactors hq).pos
          positivity
      _ ≤ 14 * X := by linarith
  -- (3) the tail `n/q ≥ 140`, `q ∤ u` (bound `10`)
  have hST : ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => 140 * q ≤ 40 * u),
      F q ≤ 10 * Chebyshev.theta ((40 * u : ℝ) / 140) := by
    have hth : Chebyshev.theta ((40 * u : ℝ) / 140) =
        ∑ p ∈ Pair.Den.primesIoc 0 (40 * u / 140), Real.log p := by
      rw [Chebyshev.theta_eq_theta_coe_floor]
      have hfl : ⌊(40 * u : ℝ) / 140⌋₊ = 40 * u / 140 := by
        rw [← Nat.floor_div_eq_div (K := ℝ) (40 * u) 140]
        push_cast
        ring_nf
      rw [hfl]
      have := Pair.Den.theta_nat_sub 0 (40 * u / 140) (Nat.zero_le _)
      simp only [CharP.cast_eq_zero, Chebyshev.theta_zero, sub_zero] at this
      exact this
    rw [hth, Finset.mul_sum]
    calc ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => 140 * q ≤ 40 * u), F q
        ≤ ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => 140 * q ≤ 40 * u),
            10 * Real.log q := by
          apply Finset.sum_le_sum
          intro q hq
          simp only [hS, hP, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
          obtain ⟨⟨⟨⟨hqn, hqp, hq2⟩, hq1000, hsq⟩, hdvd⟩, h140⟩ := hq
          have := hX.tail u q hqp hq1000 hdvd hsq (by omega)
          simp only [hF]
          apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg q)
          exact_mod_cast this
      _ ≤ ∑ p ∈ Pair.Den.primesIoc 0 (40 * u / 140), 10 * Real.log p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            simp only [hS, hP, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
            simp only [Pair.Den.primesIoc, mem_filter, mem_Ioc]
            obtain ⟨⟨⟨⟨hqn, hqp, hq2⟩, -, -⟩, -⟩, h140⟩ := hq
            exact ⟨⟨hqp.pos, by omega⟩, hqp⟩
          · intro p _ _
            have := Real.log_natCast_nonneg p
            positivity
  -- (4) the rows: `n/q ∈ [1, 140)`, `q ∤ u`
  set fR : ℕ → ℝ := fun q =>
    if 1000 < q ∧ 80 * u + 3 * q < q ^ 2 ∧ ¬ q ∣ u then (eq7 u q : ℝ) else 0 with hfR
  have hSR : ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => ¬ 140 * q ≤ 40 * u),
      F q ≤ (denTable7.map fun r => (r.f : ℝ) * (Chebyshev.theta ((40 * u : ℝ) / ((r.a : ℚ) : ℝ)) -
          Chebyshev.theta ((40 * u : ℝ) / ((r.b : ℚ) : ℝ)))).sum := by
    have hch := chain7_sum (40 * u : ℝ) hn0 fR (fun r => (r.f : ℝ)) denTable7 (1, 1) (140, 1)
      denTable7_chain (fun r hr => mem_rowOK7 hr) (by norm_num) (by norm_num)
      (by
        intro r hr q hq h1 h2
        simp only [hfR]
        split_ifs with hc
        · obtain ⟨hq1000, hsq, hdvd⟩ := hc
          have e : ((((40 * u : ℕ) : ℚ) / q : ℚ) : ℝ) = (40 * u : ℝ) / q := by push_cast; ring
          have h1' : r.a ≤ ((40 * u : ℕ) : ℚ) / q := by
            rw [← e] at h1
            exact_mod_cast h1
          have h2' : ((40 * u : ℕ) : ℚ) / q < r.b := by
            rw [← e] at h2
            exact_mod_cast h2
          exact_mod_cast hX.rows r hr u q hq hq1000 hdvd hsq h1' h2'
        · positivity)
      (fun r _ => Nat.cast_nonneg _)
    have e1 : ⌊(40 * u : ℝ) / ((((140, 1) : ℕ × ℕ).1 : ℝ) / (((140, 1) : ℕ × ℕ).2 : ℝ))⌋₊ =
        40 * u / 140 := by
      rw [← Nat.floor_div_eq_div (K := ℝ) (40 * u) 140]
      push_cast
      ring_nf
    have e2 : ⌊(40 * u : ℝ) / ((((1, 1) : ℕ × ℕ).1 : ℝ) / (((1, 1) : ℕ × ℕ).2 : ℝ))⌋₊ =
        40 * u := by
      have : (40 * u : ℝ) / ((((1, 1) : ℕ × ℕ).1 : ℝ) / (((1, 1) : ℕ × ℕ).2 : ℝ)) =
          ((40 * u : ℕ) : ℝ) := by push_cast; ring
      rw [this, Nat.floor_natCast]
    rw [e1, e2] at hch
    refine le_trans ?_ hch
    calc ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => ¬ 140 * q ≤ 40 * u), F q
        = ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => ¬ 140 * q ≤ 40 * u),
            fR q * Real.log q := by
          apply Finset.sum_congr rfl
          intro q hq
          simp only [hS, hP, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
          obtain ⟨⟨⟨⟨hqn, hqp, hq2⟩, hq1000, hsq⟩, hdvd⟩, h140⟩ := hq
          simp only [hF, hfR]
          split_ifs with hc
          · rfl
          · exact absurd ⟨hq1000, hsq, hdvd⟩ hc
      _ ≤ ∑ q ∈ Pair.Den.primesIoc (40 * u / 140) (40 * u), fR q * Real.log q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            simp only [hS, hP, mem_filter, Pair.Den.oddPrimesLE, mem_range] at hq
            simp only [Pair.Den.primesIoc, mem_filter, mem_Ioc]
            obtain ⟨⟨⟨⟨hqn, hqp, hq2⟩, -, -⟩, -⟩, h140⟩ := hq
            exact ⟨⟨by omega, by omega⟩, hqp⟩
          · intro q _ _
            have := Real.log_natCast_nonneg q
            have : 0 ≤ fR q := by
              simp only [hfR]
              split_ifs <;> positivity
            positivity
  -- PNT on each row
  have hrowPNT : ∀ r ∈ denTable7, (r.f : ℝ) * (Chebyshev.theta ((40 * u : ℝ) / ((r.a : ℚ) : ℝ)) -
      Chebyshev.theta ((40 * u : ℝ) / ((r.b : ℚ) : ℝ))) ≤
      (40 * u : ℝ) * ((r.f : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))) +
        28 * δ * (40 * u) := by
    intro r hr
    obtain ⟨h1a, hab, -⟩ := rowOK7_real r (mem_rowOK7 hr)
    have hf14 : (r.f : ℝ) ≤ 14 := by exact_mod_cast (rowOK7_spec r (mem_rowOK7 hr)).2.2.2.2.2
    have hf0 : (0 : ℝ) ≤ r.f := Nat.cast_nonneg _
    have hA := hua r hr
    have hB := hub r hr
    rw [abs_le] at hA hB
    have hna : (40 * u : ℝ) / ((r.a : ℚ) : ℝ) ≤ 40 * u := div_le_self hn0 h1a
    have hnb : (40 * u : ℝ) / ((r.b : ℚ) : ℝ) ≤ 40 * u := div_le_self hn0 (by linarith)
    have hna0 : 0 ≤ (40 * u : ℝ) / ((r.a : ℚ) : ℝ) := div_nonneg hn0 (by linarith)
    have hnb0 : 0 ≤ (40 * u : ℝ) / ((r.b : ℚ) : ℝ) := div_nonneg hn0 (by linarith)
    have hdiff : Chebyshev.theta ((40 * u : ℝ) / ((r.a : ℚ) : ℝ)) -
        Chebyshev.theta ((40 * u : ℝ) / ((r.b : ℚ) : ℝ)) ≤
        (40 * u : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ)) + 2 * δ * (40 * u) := by
      have e1 : (40 * u : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ)) =
          (40 * u : ℝ) / ((r.a : ℚ) : ℝ) - (40 * u : ℝ) / ((r.b : ℚ) : ℝ) := by ring
      rw [e1]
      have i1 : δ * ((40 * u : ℝ) / ((r.a : ℚ) : ℝ)) ≤ δ * (40 * u) :=
        mul_le_mul_of_nonneg_left hna hδ0.le
      have i2 : δ * ((40 * u : ℝ) / ((r.b : ℚ) : ℝ)) ≤ δ * (40 * u) :=
        mul_le_mul_of_nonneg_left hnb hδ0.le
      linarith
    have hpos : 0 ≤ 2 * δ * (40 * u : ℝ) := by positivity
    calc (r.f : ℝ) * (Chebyshev.theta ((40 * u : ℝ) / ((r.a : ℚ) : ℝ)) -
          Chebyshev.theta ((40 * u : ℝ) / ((r.b : ℚ) : ℝ)))
        ≤ (r.f : ℝ) * ((40 * u : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ)) +
            2 * δ * (40 * u)) := mul_le_mul_of_nonneg_left hdiff hf0
      _ = (40 * u : ℝ) * ((r.f : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))) +
            (r.f : ℝ) * (2 * δ * (40 * u)) := by ring
      _ ≤ (40 * u : ℝ) * ((r.f : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))) +
            28 * δ * (40 * u) := by
          have : (r.f : ℝ) * (2 * δ * (40 * u)) ≤ 14 * (2 * δ * (40 * u)) :=
            mul_le_mul_of_nonneg_right hf14 hpos
          linarith
  have hPNTsum : (denTable7.map fun r => (r.f : ℝ) *
      (Chebyshev.theta ((40 * u : ℝ) / ((r.a : ℚ) : ℝ)) -
        Chebyshev.theta ((40 * u : ℝ) / ((r.b : ℚ) : ℝ)))).sum ≤
      (40 * u : ℝ) * (denTable7.map fun r => (r.f : ℝ) *
        (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))).sum +
        28 * δ * (40 * u) * denTable7.length := by
    rw [← Pair.Den.list_sum_affine]
    exact Pair.Den.list_sum_le _ _ _ hrowPNT
  -- assemble
  have hT := table_integral
  set Sig := (denTable7.map fun r => (r.f : ℝ) * (1 / ((r.a : ℚ) : ℝ) - 1 / ((r.b : ℚ) : ℝ))).sum
    with hSig
  have hSign : (40 * u : ℝ) * Sig ≤ (40 * u : ℝ) * (399 / 100 - 10 / 140) :=
    mul_le_mul_of_nonneg_left (by linarith) hn0
  rw [denTable7_length] at hPNTsum
  rw [abs_le] at hu140
  have hsmall : 38052 * X ≤ ε / 4 * (40 * u) := by
    have h4 := mul_le_mul_of_nonneg_left husm (by positivity : (0 : ℝ) ≤ ε / 4)
    have e : ε / 4 * (4 * 38052 / ε * X) = 38052 * X := by
      field_simp
    rw [e] at h4
    exact h4
  have hδn : δ * (40 * u : ℝ) * (95452 + 10 / 140) ≤ ε / 4 * (40 * u) := by
    have : δ * (95452 + 10 / 140) ≤ ε / 4 := by
      rw [hδ]
      linarith
    nlinarith
  have htot : ∑ q ∈ S, F q = ∑ q ∈ S.filter (fun q => ¬ P q), F q +
      ∑ q ∈ (S.filter P).filter (fun q => q ∣ u), F q +
      ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => 140 * q ≤ 40 * u), F q +
      ∑ q ∈ ((S.filter P).filter (fun q => ¬ q ∣ u)).filter (fun q => ¬ 140 * q ≤ 40 * u),
        F q := by
    rw [← hsplit1, ← hsplit2, ← hsplit3]
    ring
  change ∑ q ∈ S, F q ≤ (399 / 100 + ε) * (40 * u)
  rw [htot]
  nlinarith

/-! ### The common denominator -/

/-- The odd part of the common denominator: `∏_{q ≤ n odd prime} q^{e_q}`. -/
def Dodd7 (u : ℕ) : ℕ :=
  ∏ q ∈ Pair.Den.oddPrimesLE (40 * u), q ^ eq7 u q

/-- The power of `2`: `v₂(den ρ) + v₂(den Z)`. -/
def e7 (u : ℕ) : ℕ :=
  padicValNat 2 (rho u).den + padicValNat 2 (Zc u).den

lemma Dodd7_pos (u : ℕ) : 0 < Dodd7 u := by
  unfold Dodd7
  apply Finset.prod_pos
  intro q hq
  simp only [Pair.Den.oddPrimesLE, mem_filter] at hq
  exact pow_pos hq.2.1.pos _

lemma Dodd7_odd (u : ℕ) : Odd (Dodd7 u) := by
  unfold Dodd7
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro q hq
  simp only [Pair.Den.oddPrimesLE, mem_filter] at hq
  exact (hq.2.1.odd_of_ne_two hq.2.2).pow

lemma pow_dvd_Dodd7 (hX : Stmt_ExpBounds7) (u p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ eq7 u p ∣ Dodd7 u := by
  by_cases hpn : p ≤ 40 * u
  · apply Finset.dvd_prod_of_mem (fun q => q ^ eq7 u q)
    simp only [Pair.Den.oddPrimesLE, mem_filter, mem_range]
    exact ⟨by omega, hp, hp2⟩
  · rw [hX.big u p hp hp2 (by omega), pow_zero]
    exact one_dvd _

lemma den_dvd (hX : Stmt_ExpBounds7) (u : ℕ) (x : ℚ) (hx2 : padicValNat 2 x.den ≤ e7 u)
    (hxq : ∀ p, p.Prime → p ≠ 2 → padicValNat p x.den ≤ eq7 u p) :
    x.den ∣ 2 ^ e7 u * Dodd7 u := by
  have hN : 2 ^ e7 u * Dodd7 u ≠ 0 := by
    have := Dodd7_pos u
    positivity
  rw [← Nat.factorization_prime_le_iff_dvd x.den_nz hN]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, ← padicValNat_dvd_iff_le hN]
  by_cases hp2 : p = 2
  · subst hp2
    exact (pow_dvd_pow 2 hx2).trans (dvd_mul_right _ _)
  · exact (pow_dvd_pow p (hxq p hp hp2)).trans
      ((pow_dvd_Dodd7 hX u p hp hp2).trans (dvd_mul_left _ _))

lemma int_of_den_dvd (x : ℚ) (N : ℕ) (h : x.den ∣ N) : ∃ z : ℤ, (N : ℚ) * x = z := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * x.num, ?_⟩
  rw [hc]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

lemma log_Dodd7 (u : ℕ) :
    Real.log (Dodd7 u : ℝ) = ∑ q ∈ Pair.Den.oddPrimesLE (40 * u), (eq7 u q : ℝ) * Real.log q := by
  unfold Dodd7
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro q _
    rw [Real.log_pow]
  · intro q hq
    simp only [Pair.Den.oddPrimesLE, mem_filter] at hq
    have : (0 : ℝ) < q := by exact_mod_cast hq.2.1.pos
    positivity

end Den7

open Den7 in
theorem Denominators7_proof (hX : Stmt_ExpBounds7) : Stmt_Denominators7 delta7 := by
  intro hPNT
  refine ⟨Dodd7, e7, Filter.Eventually.of_forall fun u => ?_, ?_⟩
  · refine ⟨Dodd7_odd u, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := int_of_den_dvd (rho u) _ (den_dvd hX u (rho u)
        (by unfold e7; exact Nat.le_add_right _ _)
        (fun p _ _ => by unfold eq7; exact le_max_left _ _))
      exact ⟨z, by rw [← hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := int_of_den_dvd (Zc u) _ (den_dvd hX u (Zc u)
        (by unfold e7; exact Nat.le_add_left _ _)
        (fun p _ _ => by unfold eq7; exact le_max_right _ _))
      exact ⟨z, by rw [← hz]; push_cast; ring⟩
  · intro ε hε
    filter_upwards [log_sum_bound7 hPNT hX ε hε] with u hu
    have hpos : (0 : ℝ) < (Dodd7 u : ℝ) := by exact_mod_cast Dodd7_pos u
    rw [← Real.exp_log hpos, log_Dodd7]
    apply Real.exp_le_exp.2
    unfold delta7
    exact hu

end Zeta2.Z7

end

