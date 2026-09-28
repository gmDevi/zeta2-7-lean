module

public import Zeta2Lean.Pair.Statements

@[expose] public section

/-!
# GAP 2 (denominators): a provable common denominator with small odd part

*In this repository.* This file is the pair repository's (https://github.com/gmDevi/zeta2-7-9-lean),
unchanged apart from this paragraph and the module-system header.
The `ζ₂(7)` proof (`Zeta2Lean/Z7/Proofs/Denominators7.lean`) uses its prime-sum lemmas
(namespace `Zeta2.Pair.Den`: `theta_tendsto`, `interval_sum_le`, `sum_primesIoc_split`, …).
Its references to documents, scripts and pair files that are not included here (such as
`BLUEPRINT_PAIR.md`, `docs/proof.md`, `python/pair_mirror.py` or `Pair/Main.lean`) are to
that repository.

gap: 'denominators'.

**Status: proved** (complete, kernel-checked; `#print axioms Denominators_proof` gives
`[propext, Classical.choice, Quot.sound]`).  Of the three hypotheses of `Denominators_proof` only
`Stmt_CrudeInt` is used (its field `forms` supplies the power of `2`); `Stmt_PF` and
`Stmt_CoeffVanish` belong to the fixed signature.  PNT (`PNT_Stmt`, the hypothesis of
`Stmt_Denominators`) enters only through `theta_tendsto`.

**Result.** Put `n = 40 m`, `h = m · hE`.  The common denominator
`D m := Dfull n h = 2^{v₂(Dcrude n)} · Dodd n h`, `Dodd n h = ∏_{q ≤ n odd prime} q^{Eexp n h q}`,
clears `ρ₀, Z₇, Z₉` for **every** `m` (`Dfull_clears`), and, assuming PNT, for every `ε > 0`
eventually `D m · ‖D m‖₂ = Dodd n h ≤ exp((8.97 + ε) n)` (`Dfull_mul_norm`, `log_sum_bound`,
`margin_T`), which gives the target `deltaE = 9`.

**Route.** The *residue level* of the verified informal proof (`docs/proof.md` §4.1–4.5, i.e.
Theorem D (a)–(c) and Theorem D∞ with the plain residue function `s(x) = min_y v(x, y)`; they are
Theorem 1 (a)–(c) and Theorem 2 of the denominators track that §4 summarises).  No second- or
third-order refinement is used: the residue level already gives `10 - R⁽⁰⁾ ≈ 8.91 < 9`.  The
exponent `Eexp n h q` is the first-order bound with valuations capped at `M = ⌊log_q 2n⌋`,
`max_k (10 M - W_k)`; for `q ≤ n < q²/2` (`M = 1`) it is the residue level `10 - min_k W_k` with
the level-one count `W_k = Wlev n h q k = v(n/q, k/q)` of `docs/proof.md` Lemma D3 (the
`δ`-factor `n - 2k` is not used), and for `q > n` it is `0`.

## Local part (every odd prime `q`)

* `Gser_PSB`, `rcoef_bound`: every linear factor of `G_k(ε) = ε⁶ R_n(-k+ε)` is controlled with the
  valuations capped at `M` (`2n < q^{M+1}`), so `‖r_{i,k}‖_q ≤ q^{-W_k} q^{M(6-i)}`, where
  `W_k = Wtot n h q M k = ∑_{e=1}^{M} Wlev n h (q^e) k` is the Legendre-type count
  (numerator factors divisible by `q^e` minus six times the pole factors).
* `rho_bound_gen`: `‖ρ₀‖_q, ‖Z₇‖_q, ‖Z₉‖_q ≤ q^E` as soon as `10 M - W_k ≤ E` for all `k`
  (`‖A_k^{(s)}‖_q ≤ q^{Ms}`).
* `rho_bound_big` (`q > n`): the five critical zeros absorb the bad rows
  (`X(k,l) = -24 [ε⁵] G_k(ε) (ε - x)^{-5}`, `absorb_identity`, `Gser_factor`), so no prime `> n`
  divides the denominator.
* `card_odd_dvd`, `cntQ_ge`, `Wlev_ge`: `q^e` consecutive odd numbers contain a multiple of `q^e`,
  hence every level loses at most `5` (`Wlev ≥ -5`), so `E_q ≤ 15 ⌊log_q 2n⌋` (`Eexp_le_small`).
* `Wlev_eq_Vl`, `realizable_disc`: for configuration `E` and `q` odd, the level-one count is the
  floor sum `Vl (n/q) (k/q)` of the continuum variables `x = n/q`, `y = k/q` (13 lines
  `ℓ_j(x) - y`; `Vl` is `40`-periodic in `x` and `1`-periodic in `y`: `Vl_add_40`, `Vl_add_int`).
* `Eexp`, `Dodd`, `Dfull`, `Dfull_clears` (via `int_of_padicNorm_le_one`), `Dfull_mul_norm`.

## Certificates (`s(x) = min_y Vl(x, y)` on `[1, 41)`)

`allCerts` lists 766 intervals `[a, b)` tiling `[1, 41)` (`allCerts_chain`), each with the integer
parts `N_j` of the 13 lines at its midpoint and the order of their fractional parts; `certOK_sound`
shows that such a certificate implies `sig ≤ Vl x y` for all `x ∈ [a, b)`, `y ∈ [0, 1)` off the
numerator break points.  The certificates are checked by the kernel (`certs0_ok` … `certs9_ok`,
`decide +kernel`: kernel reduction of `Bool` computations, no compiled code).  Consequences:
`Vl_lower` (`s ≥ -2`, so `E_q ≤ 12` for `q > √(2n)`) and `Vl_ge_Lfull` (the bound on
`Lfull = [1, 41) ∪ [41, 81)`, the second half by periodicity).  The data are produced, verbatim, by
`python/pair_den_certs.py` (exact rational arithmetic); only their kernel check matters for
soundness.  Independent numerical cross-check (not part of the proof): at the midpoint and at two
random rational points of every interval the brute-force `min_y Vl(x, y)` equals `sig`, i.e. the
certificates are the exact residue function `s(x)` (`sig ∈ [-2, 5]`).

## Analytic part (PNT)

* `theta_tendsto`: `θ(x)/x → 1` from `PNT_Stmt` and `ψ - θ = O(√x)` (Mathlib).
* `chain_sum`: over a chain of intervals, `∑_{n/b_i < q ≤ n/a_i} E_q log q ≤ ∑_i w_i (θ(n/a_i) -
  θ(n/b_i))` when `E_q ≤ w_i` on the `i`-th interval.
* `log_sum_bound`: small primes (`q² ≤ 2n`) contribute `≤ 15 (√(2n)+1) log 2n = o(n)`; primes
  `q ≤ n/81` contribute `≤ 12 θ(n/81)`; the 1532 intervals of `Lfull` contribute
  `n ∑ (10 - σ_i)(1/a_i - 1/b_i) + o(n)`.  The constant
  `T = ∑ (10 - σ_i)(1/a_i - 1/b_i) + 12/81 = 8.9607… ≤ 8.97 < 9` is checked in fixed-point integer
  arithmetic by the kernel (`Tint_le`, `margin_T`).

(The residue-level asymptotic constant with an infinite tail would be `10 - R⁽⁰⁾ = 8.9099`; the
truncation at `x = 81` costs `0.05` and is harmless.)

## Assembly

`Denominators_proof`: `D m = Dfull (40 m) (m · hE)`; integrality from `Dfull_clears` (every `m`);
the size bound from `log_sum_bound` applied to `E m q = Eexp (40 m) (m · hE) q` with
`Eexp_le_small` (`q² ≤ 2n`), `Vl_lower` (`q ≤ n/81`) and `Vl_ge_Lfull` (`n/81 < q ≤ n`) through
`Eexp_le_cert`, and `log (Dodd n h) = ∑_q Eexp n h q · log q` (`log_Dodd`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

namespace Den

section LocalBounds

open PowerSeries

/-! ### `q`-adic norm helpers -/

section Norm

variable {q : ℕ} [hq : Fact q.Prime]

lemma pn_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm q (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

lemma pn_pow (x : ℚ) (n : ℕ) : padicNorm q (x ^ n) = padicNorm q x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma pn_inv (x : ℚ) : padicNorm q x⁻¹ = (padicNorm q x)⁻¹ := by
  have := padicNorm.div (p := q) 1 x
  rw [one_div, padicNorm.one, one_div] at this
  exact this

lemma pn_int_le_one (z : ℤ) : padicNorm q (z : ℚ) ≤ 1 := padicNorm.of_int z

lemma pn_two (hq2 : q ≠ 2) : padicNorm q (2 : ℚ) = 1 := by
  have h := (padicNorm.nat_eq_one_iff (p := q) 2).2 (by
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 hdvd
    exact hq2 this)
  exact_mod_cast h

lemma pn_q_pos : (0 : ℚ) < q := by exact_mod_cast hq.out.pos

lemma one_lt_q : (1 : ℚ) < q := by exact_mod_cast hq.out.one_lt

lemma pn_pos {x : ℚ} (hx : x ≠ 0) : 0 < padicNorm q x :=
  lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hx).symm

omit hq in
/-- The norm of a non-zero integer: `‖z‖_q = (q ^ v_q(z))⁻¹`. -/
lemma pn_int_eq (z : ℤ) (hz : z ≠ 0) :
    padicNorm q (z : ℚ) = ((q : ℚ) ^ padicValInt q z)⁻¹ := by
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [padicNorm.eq_zpow_of_nonzero hz', padicValRat.of_int, zpow_neg, zpow_natCast]

/-- A non-zero integer of absolute value `< q^{M+1}` has `q`-adic norm `≥ q^{-M}`. -/
lemma pn_int_ge (z : ℤ) (hz : z ≠ 0) (M : ℕ) (hlt : z.natAbs < q ^ (M + 1)) :
    ((q : ℚ) ^ M)⁻¹ ≤ padicNorm q (z : ℚ) := by
  rw [pn_int_eq z hz]
  have hv : padicValInt q z ≤ M := by
    by_contra hv
    push Not at hv
    have h1 : ((q : ℤ) ^ (M + 1)) ∣ z :=
      (pow_dvd_pow (q : ℤ) hv).trans (padicValInt_dvd z)
    have h2 := Int.natAbs_dvd_natAbs.2 h1
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    have := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h2
    omega
  have hq0 := (pn_q_pos (q := q))
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ one_lt_q.le hv

end Norm

/-! ### Power series with bounded coefficient norms -/

/-- `‖[ε^j] F‖_q ≤ c q^{M j}` for all `j`. -/
def PSB (q M : ℕ) (c : ℚ) (F : PowerSeries ℚ) : Prop :=
  ∀ j : ℕ, padicNorm q (coeff j F) ≤ c * (q : ℚ) ^ (M * j)

section PSB

variable {q : ℕ} [hq : Fact q.Prime] {M : ℕ}

lemma PSB.mul {c₁ c₂ : ℚ} {F G : PowerSeries ℚ} (hF : PSB q M c₁ F) (hG : PSB q M c₂ G)
    (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) : PSB q M (c₁ * c₂) (F * G) := by
  intro j
  rw [coeff_mul]
  have hq0 := (pn_q_pos (q := q))
  apply padicNorm.sum_le' _ (by positivity)
  intro p hp
  rw [padicNorm.mul]
  have hpj := mem_antidiagonal.1 hp
  calc padicNorm q (coeff p.1 F) * padicNorm q (coeff p.2 G)
      ≤ (c₁ * (q : ℚ) ^ (M * p.1)) * (c₂ * (q : ℚ) ^ (M * p.2)) :=
        mul_le_mul (hF _) (hG _) (padicNorm.nonneg _) (by positivity)
    _ = c₁ * c₂ * (q : ℚ) ^ (M * j) := by rw [← hpj, mul_add, pow_add]; ring

lemma PSB.one : PSB q M 1 (1 : PowerSeries ℚ) := by
  intro j
  have hq0 := (pn_q_pos (q := q))
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · rw [padicNorm.zero]; positivity

lemma PSB.mono {c c' : ℚ} {F : PowerSeries ℚ} (hF : PSB q M c F) (hc : c ≤ c') :
    PSB q M c' F := by
  intro j
  have hq0 := (pn_q_pos (q := q))
  exact (hF j).trans (mul_le_mul_of_nonneg_right hc (by positivity))

lemma PSB.prod {ι : Type*} (s : Finset ι) (c : ι → ℚ) (F : ι → PowerSeries ℚ)
    (hF : ∀ i ∈ s, PSB q M (c i) (F i)) (hc : ∀ i ∈ s, 0 ≤ c i) :
    PSB q M (∏ i ∈ s, c i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PSB.one
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact PSB.mul (hF a (mem_insert_self a s))
      (ih (fun i hi => hF i (mem_insert_of_mem hi)) (fun i hi => hc i (mem_insert_of_mem hi)))
      (hc a (mem_insert_self a s)) (prod_nonneg fun i hi => hc i (mem_insert_of_mem hi))

lemma PSB.pow {c : ℚ} {F : PowerSeries ℚ} (hF : PSB q M c F) (hc : 0 ≤ c) (n : ℕ) :
    PSB q M (c ^ n) (F ^ n) := by
  have := PSB.prod (range n) (fun _ => c) (fun _ => F) (fun _ _ => hF) (fun _ _ => hc)
  simpa using this

/-- A linear factor `a + b ε`. -/
lemma PSB.lin {a b c : ℚ} (ha : padicNorm q a ≤ c) (hb : padicNorm q b ≤ c * (q : ℚ) ^ M) :
    PSB q M c (C a + C b * X) := by
  intro j
  have hq0 := (pn_q_pos (q := q))
  have hc : 0 ≤ c := (padicNorm.nonneg a).trans ha
  rcases j with _ | _ | j
  · simpa using ha
  · simpa using hb
  · have : coeff (j + 2) (C a + C b * X : PowerSeries ℚ) = 0 := by
      rw [map_add, coeff_C, coeff_C_mul, coeff_X]
      simp
    rw [this, padicNorm.zero]
    positivity

/-- `(β + ε)⁻¹ = β⁻¹ ∑_j (-1/β)^j ε^j`. -/
lemma inv_C_add_X (β : ℚ) (hβ : β ≠ 0) :
    (C β + X : PowerSeries ℚ)⁻¹ = C β⁻¹ * PowerSeries.mk (fun j => (-1 / β) ^ j) := by
  set G : PowerSeries ℚ := PowerSeries.mk fun j => (-1 / β) ^ j with hG
  have hGmul : G * (C β + X) = C β := by
    have h1 : G * (C β + X) = C β * G + G * X := by ring
    rw [h1]
    ext j
    rcases j with _ | j
    · simp [hG]
    · rw [map_add, coeff_C_mul, coeff_succ_mul_X, coeff_C]
      simp only [hG, coeff_mk, Nat.succ_ne_zero, ite_false]
      have hce : β * (-1 / β) = -1 := by field_simp
      calc β * (-1 / β) ^ (j + 1) + (-1 / β) ^ j
          = (-1 / β) ^ j * (β * (-1 / β) + 1) := by ring
        _ = 0 := by rw [hce]; ring
  have hconst : constantCoeff (C β + X : PowerSeries ℚ) ≠ 0 := by simp [hβ]
  rw [PowerSeries.inv_eq_iff_mul_eq_one hconst, mul_assoc, hGmul, ← map_mul,
    inv_mul_cancel₀ hβ, map_one]

lemma PSB.inv {β : ℚ} (hβ : β ≠ 0) (hM : (padicNorm q β)⁻¹ ≤ (q : ℚ) ^ M) :
    PSB q M (padicNorm q β)⁻¹ (C β + X)⁻¹ := by
  intro j
  rw [inv_C_add_X β hβ, coeff_C_mul, coeff_mk, padicNorm.mul, pn_pow, pn_inv,
    padicNorm.div, padicNorm.neg, padicNorm.one, one_div]
  have hb : 0 < padicNorm q β := pn_pos hβ
  have : (padicNorm q β)⁻¹ ^ j ≤ ((q : ℚ) ^ M) ^ j :=
    pow_le_pow_left₀ (inv_nonneg.2 hb.le) hM j
  rw [← pow_mul] at this
  exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hb.le)

end PSB

/-! ### The Taylor coefficients `r_{i,k}` -/

lemma prod_inv' {ι : Type*} (s : Finset ι) (φ : ι → PowerSeries ℚ) :
    (∏ j ∈ s, φ j)⁻¹ = ∏ j ∈ s, (φ j)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, PowerSeries.mul_inv_rev, ih, mul_comm]

/-- Constant of the numerator factors (capped at `q^{-M}`). -/
def NumC (q M n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) : ℚ :=
  ∏ m : Fin 6, ∏ u ∈ offsets n (h m), max (padicNorm q ((u : ℚ) - k + 1 / 2)) ((q : ℚ) ^ M)⁻¹

/-- Constant of the pole factors. -/
def PoleC (q n k : ℕ) : ℚ :=
  ∏ j ∈ (range (n + 1)).erase k, (padicNorm q ((j : ℚ) - k))⁻¹ ^ 6

lemma NumC_nonneg (q M n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) : 0 ≤ NumC q M n h k :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => (padicNorm.nonneg _).trans (le_max_left _ _)

lemma PoleC_nonneg (q n k : ℕ) : 0 ≤ PoleC q n k :=
  prod_nonneg fun _ _ => pow_nonneg (inv_nonneg.2 (padicNorm.nonneg _)) 6

lemma sub_ne_zero_of_mem_erase {n k j : ℕ} (hj : j ∈ (range (n + 1)).erase k) :
    ((j : ℚ) - k) ≠ 0 := by
  intro h0
  have : (j : ℚ) = k := by linarith
  exact (Finset.ne_of_mem_erase hj) (by exact_mod_cast this)

section Gser

variable {q : ℕ} [hq : Fact q.Prime] {M : ℕ}

lemma numFactor_PSB (k : ℕ) (u : ℤ) :
    PSB q M (max (padicNorm q ((u : ℚ) - k + 1 / 2)) ((q : ℚ) ^ M)⁻¹)
      (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X) := by
  have hq0 := (pn_q_pos (q := q))
  have e : (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X : PowerSeries ℚ) =
      C ((u : ℚ) - k + 1 / 2) + C 1 * X := by
    rw [map_one, one_mul]
    congr 2
    ring
  rw [e]
  apply PSB.lin
  · exact le_max_left _ _
  · rw [padicNorm.one]
    calc (1 : ℚ) = ((q : ℚ) ^ M)⁻¹ * (q : ℚ) ^ M := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

lemma numSer_PSB (n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) :
    PSB q M (NumC q M n h k) (numSer n h (-(k : ℚ))) := by
  unfold numSer NumC
  apply PSB.prod
  · intro m _
    apply PSB.prod
    · intro u _
      exact numFactor_PSB k u
    · intro u _
      exact (padicNorm.nonneg _).trans (le_max_left _ _)
  · intro m _
    exact prod_nonneg fun u _ => (padicNorm.nonneg _).trans (le_max_left _ _)

lemma poles_PSB (n k : ℕ)
    (hden : ∀ j ∈ (range (n + 1)).erase k, (padicNorm q ((j : ℚ) - k))⁻¹ ≤ (q : ℚ) ^ M) :
    PSB q M (PoleC q n k) (∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹ := by
  unfold PoleC
  rw [prod_inv']
  simp only [← PowerSeries.inv_pow]
  apply PSB.prod
  · intro j hj
    exact PSB.pow (PSB.inv (sub_ne_zero_of_mem_erase hj) (hden j hj))
      (inv_nonneg.2 (padicNorm.nonneg _)) 6
  · intro j _
    exact pow_nonneg (inv_nonneg.2 (padicNorm.nonneg _)) 6

lemma delta_PSB (hq2 : q ≠ 2) (n k : ℕ) :
    PSB q M 1 (C ((n : ℚ) - 2 * k) + C 2 * X) := by
  apply PSB.lin
  · have := pn_int_le_one (q := q) ((n : ℤ) - 2 * k)
    push_cast at this
    exact this
  · rw [pn_two hq2, one_mul]
    exact one_le_pow₀ one_lt_q.le

/-- General coefficient bound for `G_k`. -/
lemma Gser_PSB (hq2 : q ≠ 2) (n : ℕ) (h : Fin 6 → ℤ) (k : ℕ)
    (hden : ∀ j ∈ (range (n + 1)).erase k, (padicNorm q ((j : ℚ) - k))⁻¹ ≤ (q : ℚ) ^ M) :
    PSB q M (NumC q M n h k * PoleC q n k) (Gser n h k) := by
  have h123 := PSB.mul (PSB.mul (delta_PSB (M := M) hq2 n k) (numSer_PSB n h k) zero_le_one
    (NumC_nonneg _ _ _ _ _)) (poles_PSB n k hden) (by rw [one_mul]; exact NumC_nonneg _ _ _ _ _)
    (PoleC_nonneg _ _ _)
  rw [one_mul] at h123
  unfold Gser
  exact h123

end Gser

/-! ### The absorbed form of `X(k, ℓ)` -/

lemma coeff_absorb (G : PowerSeries ℚ) (a : ℚ) (j : ℕ) :
    coeff j ((C a + X) ^ 5 * G) = ∑ t ∈ range 6,
      (if t ≤ j then ((Nat.choose 5 t : ℚ) * a ^ (5 - t)) * coeff (j - t) G else 0) := by
  rw [add_comm, add_pow, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show X ^ t * C a ^ (5 - t) * ((Nat.choose 5 t : ℕ) : PowerSeries ℚ) * G =
      C ((Nat.choose 5 t : ℚ) * a ^ (5 - t)) * (X ^ t * G) by
    rw [map_mul, map_pow, map_natCast]; ring]
  rw [coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

/-- `∑_i (i)₄ [ε^{6-i}] ((ε - x)^5 G) x^{-(i+4)} = -24 [ε^5] G`. -/
lemma absorb_identity (G : PowerSeries ℚ) (x : ℚ) (hx : x ≠ 0) :
    ∑ i ∈ Icc (1 : ℕ) 6, ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) *
        coeff (6 - i) ((C (-x) + X) ^ 5 * G) * (x⁻¹) ^ (i + 4) = -24 * coeff 5 G := by
  simp only [coeff_absorb]
  rw [show Icc (1 : ℕ) 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) by decide]
  have c2 : Nat.choose 5 2 = 10 := by decide
  have c3 : Nat.choose 5 3 = 10 := by decide
  simp [Finset.sum_range_succ, c2, c3]
  field_simp
  ring

/-! ### Counting: capped valuations, Legendre -/

/-- Number of numerator factors `u - k + 1/2` (`u ∈ offsets n (h m)`) whose odd numerator
`2(u-k)+1` is divisible by `Q`. -/
def cntQ (n : ℕ) (h : Fin 6 → ℤ) (Q k : ℕ) (m : Fin 6) : ℕ :=
  #{u ∈ offsets n (h m) | (Q : ℤ) ∣ 2 * (u - k) + 1}

/-- The level-`Q` part of `v_q(G_k(0))`: numerator multiples of `Q` minus six times the pole
multiples. -/
def Wlev (n : ℕ) (h : Fin 6 → ℤ) (Q k : ℕ) : ℤ :=
  ∑ m, (cntQ n h Q k m : ℤ) - 6 * ((k / Q : ℕ) : ℤ) - 6 * (((n - k) / Q : ℕ) : ℤ)

/-- The capped valuation `∑_{e=1}^{M}` of the levels. -/
def Wtot (n : ℕ) (h : Fin 6 → ℤ) (q M k : ℕ) : ℤ :=
  ∑ e ∈ Icc 1 M, Wlev n h (q ^ e) k

section Count

variable {q : ℕ} [hq : Fact q.Prime]

lemma cap_count (z : ℤ) (hz : z ≠ 0) (M : ℕ) :
    max (padicNorm q (z : ℚ)) ((q : ℚ) ^ M)⁻¹ =
      ((q : ℚ) ^ #{e ∈ Icc 1 M | (q : ℤ) ^ e ∣ z})⁻¹ := by
  have hq0 := (pn_q_pos (q := q))
  have hfilt : {e ∈ Icc 1 M | (q : ℤ) ^ e ∣ z} = Icc 1 (min (padicValInt q z) M) := by
    ext e
    simp only [mem_filter, mem_Icc, padicValInt_dvd_iff, hz, false_or, le_min_iff]
    omega
  rw [hfilt, Nat.card_Icc, Nat.add_sub_cancel, pn_int_eq z hz]
  rcases le_total (padicValInt q z) M with h | h
  · rw [min_eq_left h, max_eq_left]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_lt_q.le h)
  · rw [min_eq_right h, max_eq_right]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_lt_q.le h)

lemma pn_half_odd (hq2 : q ≠ 2) (u : ℤ) (k : ℕ) :
    padicNorm q ((u : ℚ) - k + 1 / 2) = padicNorm q ((2 * (u - k) + 1 : ℤ) : ℚ) := by
  have e : ((u : ℚ) - k + 1 / 2) = ((2 * (u - k) + 1 : ℤ) : ℚ) / 2 := by
    push_cast; ring
  rw [e, padicNorm.div, pn_two hq2, div_one]

lemma odd_ne_zero (u : ℤ) (k : ℕ) : (2 * (u - k) + 1 : ℤ) ≠ 0 := by omega

lemma NumC_eq (hq2 : q ≠ 2) (M n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) :
    NumC q M n h k = ((q : ℚ) ^ (∑ e ∈ Icc 1 M, ∑ m, cntQ n h (q ^ e) k m))⁻¹ := by
  unfold NumC
  have hfac : ∀ m : Fin 6, ∀ u ∈ offsets n (h m),
      max (padicNorm q ((u : ℚ) - k + 1 / 2)) ((q : ℚ) ^ M)⁻¹ =
        ((q : ℚ) ^ #{e ∈ Icc 1 M | (q : ℤ) ^ e ∣ 2 * (u - k) + 1})⁻¹ := by
    intro m u _
    rw [pn_half_odd hq2, cap_count _ (odd_ne_zero u k)]
  rw [Finset.prod_congr rfl fun m _ => Finset.prod_congr rfl (hfac m)]
  simp only [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  simp only [cntQ, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro e _
  push_cast
  rfl

/-- `∏_{j ≤ n, j ≠ k} (j - k) = (-1)^k k! (n-k)!`. -/
lemma prod_range_sub (k : ℕ) :
    ∏ j ∈ range k, ((j : ℚ) - k) = (-1) ^ k * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have hterm : ∀ j ∈ range k, (((j + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ)) = (j : ℚ) - k := by
      intro j _
      push_cast
      ring
    rw [Finset.prod_congr rfl hterm, ih]
    push_cast
    ring

lemma prod_erase_sub (n k : ℕ) (hk : k ≤ n) :
    ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k) =
      (-1) ^ k * ((k.factorial : ℚ) * (n - k).factorial) := by
  induction n, hk using Nat.le_induction with
  | base =>
    rw [Finset.range_add_one, Finset.erase_insert Finset.notMem_range_self, Nat.sub_self,
      Nat.factorial_zero, Nat.cast_one, mul_one]
    exact prod_range_sub k
  | succ n hkn ih =>
    rw [Finset.range_add_one (n := n + 1), Finset.erase_insert_of_ne (by omega),
      Finset.prod_insert (by simp), ih, show n + 1 - k = (n - k) + 1 by omega,
      Nat.factorial_succ]
    push_cast [Nat.cast_sub hkn]
    ring

lemma pn_factorial (a M : ℕ) (ha : a < q ^ (M + 1)) :
    padicNorm q (a.factorial : ℚ) = ((q : ℚ) ^ (∑ e ∈ Icc 1 M, a / q ^ e))⁻¹ := by
  have hne : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  rw [padicNorm.eq_zpow_of_nonzero hne, padicValRat.of_nat, zpow_neg, zpow_natCast]
  congr 2
  have hlog : Nat.log q a < M + 1 := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp
    · exact Nat.log_lt_of_lt_pow (by omega) ha
  rw [padicValNat_factorial hlog]
  rfl

lemma PoleC_eq (M n k : ℕ) (hk : k ≤ n) (hn : n < q ^ (M + 1)) :
    PoleC q n k = ((q : ℚ) ^ (∑ e ∈ Icc 1 M, (k / q ^ e + (n - k) / q ^ e))) ^ 6 := by
  unfold PoleC
  rw [Finset.prod_pow, Finset.prod_inv_distrib, ← pn_prod, prod_erase_sub n k hk,
    padicNorm.mul, padicNorm.mul, pn_pow, padicNorm.neg, padicNorm.one, one_pow, one_mul,
    pn_factorial k M (by omega), pn_factorial (n - k) M (by omega), Finset.sum_add_distrib,
    pow_add]
  have hq0 := (pn_q_pos (q := q))
  field_simp

/-- The constant of `G_k`: `NumC · PoleC = q^{-W}`. -/
lemma Ck_eq (hq2 : q ≠ 2) (M n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) (hk : k ≤ n)
    (hn : n < q ^ (M + 1)) :
    NumC q M n h k * PoleC q n k = (q : ℚ) ^ (-Wtot n h q M k) := by
  have hq0 := (pn_q_pos (q := q))
  rw [NumC_eq hq2, PoleC_eq M n k hk hn]
  have hW : Wtot n h q M k = ((∑ e ∈ Icc 1 M, ∑ m, cntQ n h (q ^ e) k m : ℕ) : ℤ) -
      6 * ((∑ e ∈ Icc 1 M, (k / q ^ e + (n - k) / q ^ e) : ℕ) : ℤ) := by
    unfold Wtot Wlev
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hW]
  generalize (∑ e ∈ Icc 1 M, ∑ m, cntQ n h (q ^ e) k m) = T
  generalize (∑ e ∈ Icc 1 M, (k / q ^ e + (n - k) / q ^ e)) = S
  rw [show -((T : ℤ) - 6 * (S : ℤ)) = ((S * 6 : ℕ) : ℤ) - (T : ℤ) by push_cast; ring,
    zpow_sub₀ hq0.ne', zpow_natCast, zpow_natCast, pow_mul, div_eq_mul_inv, mul_comm]

end Count

/-! ### Per-prime bounds for `ρ₀`, `Z₇`, `Z₉` -/

/-- `X(k, ℓ) = ∑_i (i)₄ r_{i,k} (ℓ + 1/2)^{-(i+4)}`. -/
def Xkl (n : ℕ) (h : Fin 6 → ℤ) (k l : ℕ) : ℚ :=
  ∑ i ∈ Icc (1 : ℕ) 6, ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n h i k *
    (((l : ℚ) + 1 / 2)⁻¹) ^ (i + 4)

lemma rho0_eq_X (n : ℕ) (h : Fin 6 → ℤ) :
    rho0 n h = -∑ k ∈ range (n + 1), ∑ l ∈ range k, Xkl n h k l := by
  unfold rho0 genRho0 Xkl Ahalf
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

section RhoBound

variable {q : ℕ} [hq : Fact q.Prime]

lemma pn_poch_le (i : ℕ) : padicNorm q ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) ≤ 1 := by
  have := padicNorm.of_nat (p := q) (i * (i + 1) * (i + 2) * (i + 3))
  push_cast at this
  exact this

lemma pn_const_le (c : ℕ) : padicNorm q (c : ℚ) ≤ 1 := padicNorm.of_nat c

lemma hden_of_lt (M n k : ℕ) (hk : k ≤ n) (hn : n < q ^ (M + 1)) :
    ∀ j ∈ (range (n + 1)).erase k, (padicNorm q ((j : ℚ) - k))⁻¹ ≤ (q : ℚ) ^ M := by
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 (mem_of_mem_erase hj))
  have hjk : j ≠ k := ne_of_mem_erase hj
  have hz : ((j : ℤ) - k) ≠ 0 := by omega
  have habs : ((j : ℤ) - k).natAbs < q ^ (M + 1) := by omega
  have hge := pn_int_ge (q := q) ((j : ℤ) - k) hz M habs
  have hq0 := (pn_q_pos (q := q))
  push_cast at hge
  have hpos := pn_pos (q := q) (sub_ne_zero_of_mem_erase hj)
  calc (padicNorm q ((j : ℚ) - k))⁻¹ ≤ (((q : ℚ) ^ M)⁻¹)⁻¹ := inv_anti₀ (by positivity) hge
    _ = (q : ℚ) ^ M := inv_inv _

lemma rcoef_bound (hq2 : q ≠ 2) (M n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) (hk : k ≤ n)
    (hn : n < q ^ (M + 1)) (i : ℕ) :
    padicNorm q (rcoef n h i k) ≤ (q : ℚ) ^ (-Wtot n h q M k) * (q : ℚ) ^ (M * (6 - i)) := by
  have hq0 := (pn_q_pos (q := q))
  unfold rcoef
  split_ifs
  · have := Gser_PSB hq2 n h k (hden_of_lt M n k hk hn) (6 - i)
    rwa [Ck_eq hq2 M n h k hk hn] at this
  · rw [padicNorm.zero]; positivity

lemma Ahalf_bound (hq2 : q ≠ 2) (M n k s : ℕ) (hk : k ≤ n) (h2n : 2 * n < q ^ (M + 1)) :
    padicNorm q (Ahalf k s) ≤ (q : ℚ) ^ (M * s) := by
  have hq0 := (pn_q_pos (q := q))
  unfold Ahalf
  apply padicNorm.sum_le' _ (by positivity)
  intro l hl
  have hlk := mem_range.1 hl
  rw [pn_pow, pn_inv, pow_mul]
  apply pow_le_pow_left₀ (inv_nonneg.2 (padicNorm.nonneg _))
  have e : ((l : ℚ) + 1 / 2) = ((2 * l + 1 : ℤ) : ℚ) / 2 := by push_cast; ring
  rw [e, padicNorm.div, pn_two hq2, div_one]
  have hge := pn_int_ge (q := q) (2 * l + 1 : ℤ) (by omega) M (by omega)
  calc (padicNorm q (((2 * l + 1 : ℤ) : ℚ)))⁻¹ ≤ (((q : ℚ) ^ M)⁻¹)⁻¹ :=
        inv_anti₀ (by positivity) hge
    _ = (q : ℚ) ^ M := inv_inv _

/-- The general per-prime bound: `‖ρ₀‖_q, ‖Z₇‖_q, ‖Z₉‖_q ≤ q^E` as soon as
`10 M - W_k ≤ E` for every pole `k` (`2n < q^{M+1}`). -/
theorem rho_bound_gen (hq2 : q ≠ 2) (n : ℕ) (h : Fin 6 → ℤ) (M : ℕ)
    (hM : 2 * n < q ^ (M + 1)) (E : ℕ) (hE : ∀ k ≤ n, 10 * (M : ℤ) - Wtot n h q M k ≤ E) :
    padicNorm q (rho0 n h) ≤ (q : ℚ) ^ E ∧ padicNorm q (Z7 n h) ≤ (q : ℚ) ^ E ∧
      padicNorm q (Z9 n h) ≤ (q : ℚ) ^ E := by
  have hq0 := (pn_q_pos (q := q))
  have hn : n < q ^ (M + 1) := by omega
  have key : ∀ k ≤ n, ∀ a : ℕ, a ≤ 10 * M →
      (q : ℚ) ^ (-Wtot n h q M k) * (q : ℚ) ^ a ≤ (q : ℚ) ^ E := by
    intro k hk a ha
    rw [← zpow_natCast (q : ℚ) a, ← zpow_add₀ hq0.ne', ← zpow_natCast (q : ℚ) E]
    apply zpow_le_zpow_right₀ one_lt_q.le
    have := hE k hk
    omega
  have hr : ∀ i k, k ≤ n → padicNorm q (rcoef n h i k) ≤
      (q : ℚ) ^ (-Wtot n h q M k) * (q : ℚ) ^ (M * (6 - i)) :=
    fun i k hk => rcoef_bound hq2 M n h k hk hn i
  have hWpos : ∀ k, 0 < (q : ℚ) ^ (-Wtot n h q M k) := fun k => zpow_pos hq0 _
  refine ⟨?_, ?_, ?_⟩
  · unfold rho0 genRho0
    rw [padicNorm.neg]
    apply padicNorm.sum_le' _ (by positivity)
    intro i hi
    have hi6 : i ≤ 6 := (mem_Icc.1 hi).2
    apply padicNorm.sum_le' _ (by positivity)
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [padicNorm.mul, padicNorm.mul]
    calc padicNorm q ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * padicNorm q (rcoef n h i k) *
          padicNorm q (Ahalf k (i + 4))
        ≤ 1 * ((q : ℚ) ^ (-Wtot n h q M k) * (q : ℚ) ^ (M * (6 - i))) *
            (q : ℚ) ^ (M * (i + 4)) :=
          mul_le_mul (mul_le_mul (pn_poch_le i) (hr i k hkn) (padicNorm.nonneg _) zero_le_one)
            (Ahalf_bound hq2 M n k (i + 4) hkn hM) (padicNorm.nonneg _) (by positivity)
      _ = (q : ℚ) ^ (-Wtot n h q M k) * (q : ℚ) ^ (M * (6 - i) + M * (i + 4)) := by
          rw [pow_add]; ring
      _ ≤ (q : ℚ) ^ E := key k hkn _ (by
          have : M * (6 - i) + M * (i + 4) = M * 10 := by
            rw [← Nat.mul_add]; congr 1; omega
          omega)
  · unfold Z7 csum genCsum
    rw [padicNorm.mul]
    have h46 := pn_const_le (q := q) 46080
    push_cast at h46
    have hs : padicNorm q (∑ k ∈ range (n + 1), rcoef n h 3 k) ≤ (q : ℚ) ^ E := by
      apply padicNorm.sum_le' _ (by positivity)
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
      exact (hr 3 k hkn).trans (key k hkn _ (by omega))
    calc padicNorm q 46080 * padicNorm q (∑ k ∈ range (n + 1), rcoef n h 3 k)
        ≤ 1 * (q : ℚ) ^ E := mul_le_mul h46 hs (padicNorm.nonneg _) zero_le_one
      _ = (q : ℚ) ^ E := one_mul _
  · unfold Z9 csum genCsum
    rw [padicNorm.mul]
    have h86 := pn_const_le (q := q) 860160
    push_cast at h86
    have hs : padicNorm q (∑ k ∈ range (n + 1), rcoef n h 5 k) ≤ (q : ℚ) ^ E := by
      apply padicNorm.sum_le' _ (by positivity)
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
      exact (hr 5 k hkn).trans (key k hkn _ (by omega))
    calc padicNorm q 860160 * padicNorm q (∑ k ∈ range (n + 1), rcoef n h 5 k)
        ≤ 1 * (q : ℚ) ^ E := mul_le_mul h86 hs (padicNorm.nonneg _) zero_le_one
      _ = (q : ℚ) ^ E := one_mul _

/-! #### Primes `q > n`: the critical zeros absorb the bad denominators -/

/-- `G_k` with five copies of the critical factor `(ε - (ℓ + 1/2))` removed. -/
def Gp (n : ℕ) (h : Fin 6 → ℤ) (k l : ℕ) : PowerSeries ℚ :=
  (C ((n : ℚ) - 2 * k) + C 2 * X) *
    ((∏ u ∈ offsets n (h 0), (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X)) *
      ∏ i : Fin 5, ∏ u ∈ (offsets n (h i.succ)).erase ((k : ℤ) - l - 1),
        (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X)) *
    (∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹

lemma Gser_factor (n : ℕ) (h : Fin 6 → ℤ) (hpos : ∀ i : Fin 5, 0 ≤ h i.succ) (k l : ℕ)
    (hlk : l < k) (hkn : k ≤ n) :
    Gser n h k = (C (-((l : ℚ) + 1 / 2)) + X) ^ 5 * Gp n h k l := by
  have hmem : ∀ i : Fin 5, ((k : ℤ) - l - 1) ∈ offsets n (h i.succ) := by
    intro i
    have := hpos i
    simp only [offsets, mem_Ico]
    constructor <;> omega
  have hf : ∀ i : Fin 5, ∏ u ∈ offsets n (h i.succ), (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X) =
      (C (-((l : ℚ) + 1 / 2)) + X) * ∏ u ∈ (offsets n (h i.succ)).erase ((k : ℤ) - l - 1),
        (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X) := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (hmem i)]
    congr 3
    push_cast
    ring
  unfold Gser numSer Gp
  rw [Fin.prod_univ_succ, Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma Gp_PSB (hq2 : q ≠ 2) (n : ℕ) (h : Fin 6 → ℤ) (k l : ℕ) (hkn : k ≤ n) (hnq : n < q) :
    PSB q 0 1 (Gp n h k l) := by
  have hq0 := (pn_q_pos (q := q))
  have hnum : ∀ u : ℤ, PSB q 0 1 (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X) := by
    intro u
    apply (numFactor_PSB (M := 0) k u).mono
    rw [pow_zero, inv_one, pn_half_odd hq2]
    exact max_le (pn_int_le_one _) le_rfl
  have hP0 : PSB q 0 1 (∏ u ∈ offsets n (h 0), (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X)) := by
    have := PSB.prod (offsets n (h 0)) (fun _ => (1 : ℚ)) _ (fun u _ => hnum u)
      (fun _ _ => zero_le_one)
    simpa using this
  have hP1 : PSB q 0 1 (∏ i : Fin 5, ∏ u ∈ (offsets n (h i.succ)).erase ((k : ℤ) - l - 1),
      (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X)) := by
    have := PSB.prod (univ : Finset (Fin 5)) (fun _ => (1 : ℚ)) _ (fun i _ => by
      have := PSB.prod ((offsets n (h i.succ)).erase ((k : ℤ) - l - 1)) (fun _ => (1 : ℚ)) _
        (fun u _ => hnum u) (fun _ _ => zero_le_one)
      simpa using this) (fun _ _ => zero_le_one)
    simpa using this
  have hpole := poles_PSB (M := 0) n k (hden_of_lt 0 n k hkn (by simpa using hnq))
  rw [PoleC_eq 0 n k hkn (by simpa using hnq)] at hpole
  simp only [Finset.Icc_eq_empty_of_lt, zero_lt_one, sum_empty, pow_zero, one_pow]
    at hpole
  have := PSB.mul (PSB.mul (delta_PSB (M := 0) hq2 n k) (PSB.mul hP0 hP1 zero_le_one zero_le_one)
    zero_le_one (by norm_num)) hpole (by norm_num) zero_le_one
  simp only [mul_one] at this
  unfold Gp
  exact this

/-- For primes `q > n` all three coefficients are `q`-integral. -/
theorem rho_bound_big (hq2 : q ≠ 2) (n : ℕ) (h : Fin 6 → ℤ)
    (hpos : ∀ i : Fin 5, 0 ≤ h i.succ) (hnq : n < q) :
    padicNorm q (rho0 n h) ≤ 1 ∧ padicNorm q (Z7 n h) ≤ 1 ∧ padicNorm q (Z9 n h) ≤ 1 := by
  have hq0 := (pn_q_pos (q := q))
  have hn1 : n < q ^ (0 + 1) := by simpa using hnq
  have hr : ∀ i k, k ≤ n → padicNorm q (rcoef n h i k) ≤ 1 := by
    intro i k hk
    have := rcoef_bound hq2 0 n h k hk hn1 i
    simpa [Wtot] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [rho0_eq_X, padicNorm.neg]
    apply padicNorm.sum_le' _ zero_le_one
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    apply padicNorm.sum_le' _ zero_le_one
    intro l hl
    have hlk : l < k := mem_range.1 hl
    by_cases hbad : (q : ℤ) ∣ 2 * l + 1
    · -- bad row: absorbed form
      have hx : ((l : ℚ) + 1 / 2) ≠ 0 := by positivity
      have hX : Xkl n h k l = -24 * coeff 5 (Gp n h k l) := by
        unfold Xkl
        rw [← absorb_identity (Gp n h k l) ((l : ℚ) + 1 / 2) hx,
          ← Gser_factor n h hpos k l hlk hkn]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := mem_Icc.1 hi
        unfold rcoef
        simp only [hi'.1, hi'.2, hkn, and_self, ite_true]
      rw [hX, padicNorm.mul, padicNorm.neg]
      have h24 := pn_const_le (q := q) 24
      push_cast at h24
      have hc := Gp_PSB hq2 n h k l hkn hnq 5
      simp only [zero_mul, pow_zero, mul_one] at hc
      calc padicNorm q 24 * padicNorm q (coeff 5 (Gp n h k l)) ≤ 1 * 1 :=
            mul_le_mul h24 hc (padicNorm.nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · -- good row: `ℓ + 1/2` is a unit
      have hunit : padicNorm q (((l : ℚ) + 1 / 2)⁻¹) = 1 := by
        have e : ((l : ℚ) + 1 / 2) = ((2 * l + 1 : ℤ) : ℚ) / 2 := by push_cast; ring
        rw [pn_inv, e, padicNorm.div, pn_two hq2, div_one,
          (padicNorm.int_eq_one_iff _).2 hbad, inv_one]
      unfold Xkl
      apply padicNorm.sum_le' _ zero_le_one
      intro i _
      rw [padicNorm.mul, padicNorm.mul, pn_pow, hunit, one_pow, mul_one]
      calc padicNorm q ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * padicNorm q (rcoef n h i k)
          ≤ 1 * 1 := mul_le_mul (pn_poch_le i) (hr i k hkn) (padicNorm.nonneg _) zero_le_one
        _ = 1 := one_mul 1
  · unfold Z7 csum genCsum
    rw [padicNorm.mul]
    have h46 := pn_const_le (q := q) 46080
    push_cast at h46
    have hs : padicNorm q (∑ k ∈ range (n + 1), rcoef n h 3 k) ≤ 1 := by
      apply padicNorm.sum_le' _ zero_le_one
      intro k hk
      exact hr 3 k (Nat.lt_succ_iff.1 (mem_range.1 hk))
    calc padicNorm q 46080 * padicNorm q (∑ k ∈ range (n + 1), rcoef n h 3 k) ≤ 1 * 1 :=
          mul_le_mul h46 hs (padicNorm.nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · unfold Z9 csum genCsum
    rw [padicNorm.mul]
    have h86 := pn_const_le (q := q) 860160
    push_cast at h86
    have hs : padicNorm q (∑ k ∈ range (n + 1), rcoef n h 5 k) ≤ 1 := by
      apply padicNorm.sum_le' _ zero_le_one
      intro k hk
      exact hr 5 k (Nat.lt_succ_iff.1 (mem_range.1 hk))
    calc padicNorm q 860160 * padicNorm q (∑ k ∈ range (n + 1), rcoef n h 5 k) ≤ 1 * 1 :=
          mul_le_mul h86 hs (padicNorm.nonneg _) zero_le_one
      _ = 1 := one_mul 1

end RhoBound

end LocalBounds

/-! ### The residue-level valuation function `Vl` and its 13 lines -/

/-- Scaled slopes of the 13 lines (`80 ℓ_j(x) = A_j x + B_j`): six numerator upper ends
`(40 + c_m) x / 40 - 1/2`, six numerator lower ends `-c_m x / 40 - 1/2`, and the pole line `x`. -/
def lineA (j : ℕ) : ℤ := [46, 82, 84, 86, 90, 92, 34, -2, -4, -6, -10, -12, 80].getD j 0

def lineB (j : ℕ) : ℤ := if j < 12 then -40 else 0

def lineW (j : ℕ) : ℤ := if j < 6 then 1 else if j < 12 then -1 else -6

def ell (j : ℕ) (x : ℚ) : ℚ := ((lineA j : ℚ) * x + lineB j) / 80

/-- `Vl x y = ∑_m (⌊(1+η_m)x - y - 1/2⌋ - ⌊-η_m x - y - 1/2⌋) - 6⌊x - y⌋ - 6⌊y⌋`. -/
def Vl (x y : ℚ) : ℤ := (∑ j ∈ range 13, lineW j * ⌊ell j x - y⌋) - 6 * ⌊y⌋

/-- No numerator end point is hit exactly. -/
def Realizable (x y : ℚ) : Prop := ∀ j < 12, ∀ z : ℤ, ell j x - y ≠ z

/-! ### Certificates -/

structure DenCert where
  pa : ℤ
  qa : ℤ
  pb : ℤ
  qb : ℤ
  sig : ℤ
  V0 : ℤ
  N : List ℤ
  rows : List (ℕ × ℤ × ℤ)

def sv (j : ℕ) (N : List ℤ) (P Q : ℤ) : ℤ := lineA j * P + lineB j * Q - 80 * Q * N.getD j 0

def v0 (N : List ℤ) : ℤ := ((List.range 13).map (fun j => lineW j * N.getD j 0)).sum

def rowOK (c : DenCert) (r : ℕ × ℤ × ℤ) : Bool :=
  decide (r.2.1 = sv r.1 c.N c.pa c.qa) && decide (r.2.2 = sv r.1 c.N c.pb c.qb) &&
  decide (0 ≤ r.2.1) && decide (r.2.1 ≤ 80 * c.qa) && decide (0 ≤ r.2.2) &&
  decide (r.2.2 ≤ 80 * c.qb) &&
  !(decide (r.2.1 = 80 * c.qa) && decide (r.2.2 = 80 * c.qb)) &&
  (decide (r.1 < 12) || decide (r.2.1 < 80 * c.qa))

def prefOK (σ : ℤ) : ℤ → List (ℕ × ℤ × ℤ) → Bool
  | acc, [] => decide (σ ≤ acc)
  | acc, r :: rs => decide (σ ≤ acc) && prefOK σ (acc - lineW r.1) rs

def chainOK : List (ℕ × ℤ × ℤ) → Bool
  | [] => true
  | [_] => true
  | r :: s :: rs => decide (r.2.1 ≤ s.2.1) && decide (r.2.2 ≤ s.2.2) && chainOK (s :: rs)

def certOK (c : DenCert) : Bool :=
  decide (0 < c.qa) && decide (0 < c.qb) && decide (c.pa * c.qb < c.pb * c.qa) &&
  decide (c.V0 = v0 c.N) &&
  (c.rows.map Prod.fst).isPerm (List.range 13) &&
  c.rows.all (rowOK c) && chainOK c.rows && prefOK c.sig c.V0 c.rows

/-! ### Soundness -/

lemma prefOK_sound (σ : ℤ) (P : ℕ × ℤ × ℤ → Prop) [DecidablePred P] :
    ∀ (rows : List (ℕ × ℤ × ℤ)) (acc : ℤ), prefOK σ acc rows = true →
      σ ≤ acc - ((rows.takeWhile (fun r => decide (P r))).map (fun r => lineW r.1)).sum
  | [], acc, h => by simpa [prefOK] using h
  | r :: rs, acc, h => by
    simp only [prefOK, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hr : P r
    · have := prefOK_sound σ P rs (acc - lineW r.1) h.2
      have e : (r :: rs).takeWhile (fun r => decide (P r)) =
          r :: rs.takeWhile (fun r => decide (P r)) := by
        simp [hr]
      rw [e, List.map_cons, List.sum_cons]
      linarith
    · simp [hr, h.1]

lemma chainOK_chain : ∀ rows : List (ℕ × ℤ × ℤ), chainOK rows = true →
    rows.IsChain (fun r s => r.2.1 ≤ s.2.1 ∧ r.2.2 ≤ s.2.2)
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | r :: s :: rs, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.IsChain.cons_cons ⟨h.1.1, h.1.2⟩ (chainOK_chain (s :: rs) h.2)

lemma not_of_chain {α : Type*} (Q : α → Prop) : ∀ (L : List α) (a : α),
    (a :: L).IsChain (fun a b => Q b → Q a) → ¬ Q a → ∀ b ∈ L, ¬ Q b
  | [], _, _, _, b, hb => by simp at hb
  | c :: L, a, h, ha, b, hb => by
    rw [List.isChain_cons_cons] at h
    have hc : ¬ Q c := fun hQ => ha (h.1 hQ)
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact hc
    · exact not_of_chain Q L c h.2 hc b hb'

/-- Along a chain on which `Q` is inherited backwards, the sum of `f` over the elements
satisfying `Q` is the sum over the maximal initial segment. -/
lemma sum_ite_eq_takeWhile {α : Type*} (Q : α → Prop) [DecidablePred Q] (f : α → ℤ) :
    ∀ L : List α, L.IsChain (fun a b => Q b → Q a) →
      (L.map (fun a => if Q a then f a else 0)).sum =
        ((L.takeWhile (fun a => decide (Q a))).map f).sum
  | [], _ => by simp
  | a :: L, h => by
    by_cases ha : Q a
    · have ih := sum_ite_eq_takeWhile Q f L h.tail
      simp [ha, ih]
    · have hall : ∀ b ∈ a :: L, ¬ Q b := by
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact ha
        · exact not_of_chain Q L a h ha b hb'
      have h0 : (List.map (fun a => if Q a then f a else 0) (a :: L)) =
          List.map (fun _ => (0 : ℤ)) (a :: L) := by
        apply List.map_congr_left
        intro b hb
        simp [hall b hb]
      rw [h0]
      simp [ha]

lemma sv_cast (j : ℕ) (N : List ℤ) (P Q : ℤ) (hQ : (Q : ℚ) ≠ 0) :
    (sv j N P Q : ℚ) = 80 * Q * (ell j ((P : ℚ) / Q) - (N.getD j 0 : ℚ)) := by
  unfold sv ell
  push_cast
  field_simp

lemma sum_range_eq_list (n : ℕ) (f : ℕ → ℤ) :
    ∑ j ∈ range n, f j = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

lemma v0_eq (N : List ℤ) : v0 N = ∑ j ∈ range 13, lineW j * N.getD j 0 := by
  unfold v0
  rw [sum_range_eq_list]

lemma nonneg_of_pos_mul {c z : ℚ} (hc : 0 < c) (h : 0 ≤ c * z) : 0 ≤ z := by
  by_contra hz
  push Not at hz
  nlinarith

lemma le_one_of_pos_mul {c z : ℚ} (hc : 0 < c) (h : c * z ≤ c) : z ≤ 1 := by
  by_contra hz
  push Not at hz
  nlinarith

/-- Affine interpolation of `ℓ_j - N` between the endpoints. -/
lemma ell_interp (j : ℕ) (a b x N : ℚ) :
    (b - a) * (ell j x - N) = (b - x) * (ell j a - N) + (x - a) * (ell j b - N) := by
  unfold ell
  ring

theorem certOK_sound (c : DenCert) (hc : certOK c = true) (x y : ℚ)
    (hxa : (c.pa : ℚ) / c.qa ≤ x) (hxb : x < (c.pb : ℚ) / c.qb) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hR : Realizable x y) : c.sig ≤ Vl x y := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hqa, hqb⟩, hab⟩, hV0⟩, hperm⟩, hrows⟩, hchain⟩, hpref⟩ := hc
  rw [List.isPerm_iff] at hperm
  rw [List.all_eq_true] at hrows
  have hchain' := chainOK_chain _ hchain
  set a : ℚ := (c.pa : ℚ) / c.qa with ha_def
  set b : ℚ := (c.pb : ℚ) / c.qb with hb_def
  have hqa' : (0 : ℚ) < c.qa := by exact_mod_cast hqa
  have hqb' : (0 : ℚ) < c.qb := by exact_mod_cast hqb
  have hba : 0 < b - a := by
    have : (c.pa : ℚ) * c.qb < c.pb * c.qa := by exact_mod_cast hab
    rw [ha_def, hb_def, sub_pos, div_lt_div_iff₀ hqa' hqb']
    linarith
  set β : ℕ → ℚ := fun j => ell j x - (c.N.getD j 0 : ℚ) with hβ
  have hrow : ∀ r ∈ c.rows,
      0 ≤ β r.1 ∧ β r.1 ≤ 1 ∧ (β r.1 = 1 → x = a ∧ r.1 < 12) ∧
      (ell r.1 a - c.N.getD r.1 0) * (80 * c.qa) = r.2.1 ∧
      (ell r.1 b - c.N.getD r.1 0) * (80 * c.qb) = r.2.2 := by
    intro r hr
    have h := hrows r hr
    simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.or_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hu, hw⟩, hu0⟩, hu1⟩, hw0⟩, hw1⟩, hnb⟩, hZ⟩ := h
    have hu' : (r.2.1 : ℚ) = 80 * c.qa * (ell r.1 a - c.N.getD r.1 0) := by
      rw [hu, sv_cast _ _ _ _ hqa'.ne']
    have hw' : (r.2.2 : ℚ) = 80 * c.qb * (ell r.1 b - c.N.getD r.1 0) := by
      rw [hw, sv_cast _ _ _ _ hqb'.ne']
    have h80a : (0 : ℚ) < 80 * c.qa := by positivity
    have h80b : (0 : ℚ) < 80 * c.qb := by positivity
    have hA0 : 0 ≤ ell r.1 a - c.N.getD r.1 0 := by
      have : (0 : ℚ) ≤ r.2.1 := by exact_mod_cast hu0
      rw [hu'] at this
      exact nonneg_of_pos_mul h80a this
    have hA1 : ell r.1 a - c.N.getD r.1 0 ≤ 1 := by
      have : (r.2.1 : ℚ) ≤ 80 * c.qa := by exact_mod_cast hu1
      rw [hu'] at this
      exact le_one_of_pos_mul h80a this
    have hB0 : 0 ≤ ell r.1 b - c.N.getD r.1 0 := by
      have : (0 : ℚ) ≤ r.2.2 := by exact_mod_cast hw0
      rw [hw'] at this
      exact nonneg_of_pos_mul h80b this
    have hB1 : ell r.1 b - c.N.getD r.1 0 ≤ 1 := by
      have : (r.2.2 : ℚ) ≤ 80 * c.qb := by exact_mod_cast hw1
      rw [hw'] at this
      exact le_one_of_pos_mul h80b this
    have hI := ell_interp r.1 a b x (c.N.getD r.1 0)
    have hxa' : 0 ≤ x - a := by linarith
    have hbx : 0 < b - x := by linarith
    refine ⟨?_, ?_, ?_, by rw [hu']; ring, by rw [hw']; ring⟩
    · have : 0 ≤ (b - a) * β r.1 := by
        simp only [hβ]; rw [hI]; positivity
      exact nonneg_of_pos_mul hba this
    · have : (b - a) * β r.1 ≤ (b - a) := by
        simp only [hβ]; rw [hI]; nlinarith
      exact le_one_of_pos_mul hba this
    · intro h1
      have hsum : (b - x) * (1 - (ell r.1 a - c.N.getD r.1 0)) +
          (x - a) * (1 - (ell r.1 b - c.N.getD r.1 0)) = 0 := by
        have : (b - a) * β r.1 = (b - a) * 1 := by rw [h1]
        simp only [hβ] at this
        rw [hI] at this
        linarith
      have t1 : (b - x) * (1 - (ell r.1 a - c.N.getD r.1 0)) = 0 := by
        have := mul_nonneg hbx.le (sub_nonneg.2 hA1)
        have := mul_nonneg hxa' (sub_nonneg.2 hB1)
        linarith
      have t2 : (x - a) * (1 - (ell r.1 b - c.N.getD r.1 0)) = 0 := by linarith
      have ha1 : ell r.1 a - c.N.getD r.1 0 = 1 := by
        rcases mul_eq_zero.1 t1 with h | h
        · linarith
        · linarith
      have hxa_eq : x = a := by
        rcases mul_eq_zero.1 t2 with h | h
        · linarith
        · exfalso
          have hb1 : ell r.1 b - c.N.getD r.1 0 = 1 := by linarith
          have e1 : r.2.1 = 80 * c.qa := by
            have : (r.2.1 : ℚ) = 80 * c.qa := by rw [hu', ha1]; ring
            exact_mod_cast this
          have e2 : r.2.2 = 80 * c.qb := by
            have : (r.2.2 : ℚ) = 80 * c.qb := by rw [hw', hb1]; ring
            exact_mod_cast this
          rcases hnb with h' | h'
          · exact h' e1
          · exact h' e2
      refine ⟨hxa_eq, ?_⟩
      rcases hZ with hZ | hZ
      · exact hZ
      · exfalso
        have : (r.2.1 : ℚ) < 80 * c.qa := by exact_mod_cast hZ
        rw [hu', ha1] at this
        linarith
  have hmem : ∀ j < 13, ∃ r ∈ c.rows, r.1 = j := by
    intro j hj
    have : j ∈ c.rows.map Prod.fst := hperm.symm.subset (List.mem_range.2 hj)
    obtain ⟨r, hr, hrj⟩ := List.mem_map.1 this
    exact ⟨r, hr, hrj⟩
  have hfloor : ∀ j < 13, ⌊ell j x - y⌋ = c.N.getD j 0 - (if β j < y then 1 else 0) := by
    intro j hj
    obtain ⟨r, hr, rfl⟩ := hmem j hj
    obtain ⟨h0, h1, hone, -, -⟩ := hrow r hr
    rw [Int.floor_eq_iff]
    rcases lt_or_eq_of_le h1 with hlt | heq
    · split_ifs with hby
      · push_cast
        simp only [hβ] at hby hlt h0
        constructor <;> linarith
      · push_cast
        push Not at hby
        simp only [hβ] at hby hlt h0
        constructor <;> linarith
    · obtain ⟨hxa_eq, hj12⟩ := hone heq
      have hy_pos : 0 < y := by
        rcases lt_or_eq_of_le hy0 with h | h
        · exact h
        · exfalso
          apply hR r.1 hj12 (c.N.getD r.1 0 + 1)
          simp only [hβ] at heq
          rw [← h]
          push_cast
          linarith
      have : ¬ β r.1 < y := by rw [heq]; linarith
      simp only [this, ↓reduceIte]
      simp only [hβ] at heq
      push_cast
      constructor <;> linarith
  have hfy : ⌊y⌋ = 0 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  have hV : Vl x y = c.V0 - ∑ j ∈ range 13, lineW j * (if β j < y then 1 else 0) := by
    unfold Vl
    rw [hfy, hV0, v0_eq, ← Finset.sum_sub_distrib]
    simp only [mul_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hfloor j (Finset.mem_range.1 hj)]
    ring
  have hsum : ∑ j ∈ range 13, lineW j * (if β j < y then 1 else 0) =
      (c.rows.map (fun r => if β r.1 < y then lineW r.1 else 0)).sum := by
    rw [sum_range_eq_list]
    have e2 := (hperm.map (fun j => lineW j * (if β j < y then (1 : ℤ) else 0))).sum_eq
    rw [← e2, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp]
    split_ifs <;> simp
  have hchainβ : c.rows.IsChain (fun r s => β s.1 < y → β r.1 < y) := by
    have hsub : ∀ r ∈ c.rows, ∀ s ∈ c.rows, (r.2.1 ≤ s.2.1 ∧ r.2.2 ≤ s.2.2) →
        (β s.1 < y → β r.1 < y) := by
      intro r hr s hs hle hsy
      obtain ⟨-, -, -, hra, hrb⟩ := hrow r hr
      obtain ⟨-, -, -, hsa, hsb⟩ := hrow s hs
      have h1 : ell r.1 a - c.N.getD r.1 0 ≤ ell s.1 a - c.N.getD s.1 0 := by
        have : (r.2.1 : ℚ) ≤ s.2.1 := by exact_mod_cast hle.1
        rw [← hra, ← hsa] at this
        exact le_of_mul_le_mul_right this (by positivity)
      have h2 : ell r.1 b - c.N.getD r.1 0 ≤ ell s.1 b - c.N.getD s.1 0 := by
        have : (r.2.2 : ℚ) ≤ s.2.2 := by exact_mod_cast hle.2
        rw [← hrb, ← hsb] at this
        exact le_of_mul_le_mul_right this (by positivity)
      have hIr := ell_interp r.1 a b x (c.N.getD r.1 0)
      have hIs := ell_interp s.1 a b x (c.N.getD s.1 0)
      have : (b - a) * β r.1 ≤ (b - a) * β s.1 := by
        simp only [hβ]
        rw [hIr, hIs]
        have hxa' : 0 ≤ x - a := by linarith
        have hbx : 0 ≤ b - x := by linarith
        nlinarith
      have := le_of_mul_le_mul_left this hba
      linarith
    exact List.IsChain.imp_of_mem_imp (fun r s hr hs hle => hsub r hr s hs hle) hchain'
  have hfin := sum_ite_eq_takeWhile (fun r : ℕ × ℤ × ℤ => β r.1 < y) (fun r => lineW r.1)
    c.rows hchainβ
  have hp := prefOK_sound c.sig (fun r : ℕ × ℤ × ℤ => β r.1 < y) c.rows c.V0 hpref
  rw [hV, hsum, hfin]
  exact hp

/-! ### Compact certificates -/

/-- A compact certificate: the interval `[pa/qa, pb/qb)`, the claimed lower bound `sig`, and the
order of the 13 lines (the integer parts `N` are recomputed at the midpoint). -/
structure CC where
  pa : ℤ
  qa : ℤ
  pb : ℤ
  qb : ℤ
  sig : ℤ
  ord : List ℕ

def CC.N (c : CC) : List ℤ := (List.range 13).map fun j =>
  (lineA j * (c.pa * c.qb + c.pb * c.qa) + lineB j * (2 * c.qa * c.qb)) / (80 * (2 * c.qa * c.qb))

def CC.toDen (c : CC) : DenCert :=
  ⟨c.pa, c.qa, c.pb, c.qb, c.sig, v0 c.N, c.N,
    c.ord.map fun j => (j, sv j c.N c.pa c.qa, sv j c.N c.pb c.qb)⟩

def CC.a (c : CC) : ℚ := (c.pa : ℚ) / c.qa

def CC.b (c : CC) : ℚ := (c.pb : ℚ) / c.qb

def ccOK (c : CC) : Bool := certOK c.toDen

theorem ccOK_sound (c : CC) (hc : ccOK c = true) (x y : ℚ) (hxa : c.a ≤ x) (hxb : x < c.b)
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hR : Realizable x y) : c.sig ≤ Vl x y :=
  certOK_sound c.toDen hc x y hxa hxb hy0 hy1 hR

lemma ccOK_lt (c : CC) (hc : ccOK c = true) : 0 < c.qa ∧ 0 < c.qb ∧ c.a < c.b := by
  unfold ccOK certOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hqa, hqb⟩, hab⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  refine ⟨hqa, hqb, ?_⟩
  have hqa' : (0 : ℚ) < c.qa := by exact_mod_cast hqa
  have hqb' : (0 : ℚ) < c.qb := by exact_mod_cast hqb
  unfold CC.a CC.b
  rw [div_lt_div_iff₀ hqa' hqb']
  exact_mod_cast hab

/-! ### Chains of intervals -/

/-- `chainFrom (A₁, A₂) L (B₁, B₂)`: the intervals of `L` tile `[A₁/A₂, B₁/B₂)` in order. -/
def chainFrom : ℤ × ℤ → List CC → ℤ × ℤ → Bool
  | A, [], B => decide (A = B)
  | A, c :: L, B => decide (c.pa = A.1) && decide (c.qa = A.2) && chainFrom (c.pb, c.qb) L B

lemma chainFrom_cover : ∀ (L : List CC) (A B : ℤ × ℤ), chainFrom A L B = true →
    ∀ x : ℚ, (A.1 : ℚ) / A.2 ≤ x → x < (B.1 : ℚ) / B.2 → ∃ c ∈ L, c.a ≤ x ∧ x < c.b
  | [], A, B, h, x, h1, h2 => by
    simp only [chainFrom, decide_eq_true_eq] at h
    subst h
    exact absurd h1 (not_le.2 h2)
  | c :: L, A, B, h, x, h1, h2 => by
    simp only [chainFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpa, hqa⟩, hL⟩ := h
    by_cases hx : x < c.b
    · refine ⟨c, List.mem_cons_self, ?_, hx⟩
      unfold CC.a
      rw [hpa, hqa]
      exact h1
    · push Not at hx
      obtain ⟨c', hc', h'⟩ := chainFrom_cover L (c.pb, c.qb) B hL x hx h2
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩

/-! ### Periodicity of `Vl` -/

lemma lineW_sum : ∑ j ∈ range 13, lineW j = -6 := by
  simp [Finset.sum_range_succ, lineW]

lemma lineA_half (j : ℕ) (hj : j < 13) : ∃ z : ℤ, lineA j = 2 * z := by
  refine ⟨lineA j / 2, ?_⟩
  interval_cases j <;> decide

lemma lineW_lineA_sum : ∑ j ∈ range 13, lineW j * (lineA j / 2) = 0 := by
  simp [Finset.sum_range_succ, lineW, lineA]

lemma ell_add_40 (j : ℕ) (hj : j < 13) (x : ℚ) (t : ℤ) :
    ell j (x + 40 * t) = ell j x + ((lineA j / 2 : ℤ) : ℚ) * t := by
  obtain ⟨z, hz⟩ := lineA_half j hj
  have hz2 : lineA j / 2 = z := by omega
  unfold ell
  rw [hz2, hz]
  push_cast
  ring

theorem Vl_add_int (x y : ℚ) (z : ℤ) : Vl x (y + z) = Vl x y := by
  unfold Vl
  have h1 : ∀ j ∈ range 13, lineW j * ⌊ell j x - (y + z)⌋ =
      lineW j * ⌊ell j x - y⌋ - lineW j * z := by
    intro j _
    rw [show ell j x - (y + z) = (ell j x - y) + ((-z : ℤ) : ℚ) by push_cast; ring,
      Int.floor_add_intCast]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_mul, lineW_sum,
    Int.floor_add_intCast]
  ring

theorem Vl_add_40 (x y : ℚ) (t : ℤ) : Vl (x + 40 * t) y = Vl x y := by
  unfold Vl
  have h1 : ∀ j ∈ range 13, lineW j * ⌊ell j (x + 40 * t) - y⌋ =
      lineW j * ⌊ell j x - y⌋ + lineW j * (lineA j / 2) * t := by
    intro j hj
    rw [ell_add_40 j (mem_range.1 hj),
      show ell j x + ((lineA j / 2 : ℤ) : ℚ) * t - y = (ell j x - y) + ((lineA j / 2 * t : ℤ) : ℚ)
        by push_cast; ring, Int.floor_add_intCast]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, lineW_lineA_sum]
  ring

theorem Realizable_shift {x y : ℚ} (h : Realizable x y) (t z : ℤ) :
    Realizable (x + 40 * t) (y + z) := by
  intro j hj w hw
  apply h j hj (w - lineA j / 2 * t + z)
  rw [ell_add_40 j (by omega)] at hw
  push_cast
  linarith

/-- The cheap interval check: positive denominators and `a < b`. -/
def ivOK (c : CC) : Bool :=
  decide (0 < c.qa) && decide (0 < c.qb) && decide (c.pa * c.qb < c.pb * c.qa)

lemma ivOK_lt (c : CC) (hc : ivOK c = true) : 0 < c.qa ∧ 0 < c.qb ∧ c.a < c.b := by
  unfold ivOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hqa, hqb⟩, hab⟩ := hc
  refine ⟨hqa, hqb, ?_⟩
  have hqa' : (0 : ℚ) < c.qa := by exact_mod_cast hqa
  have hqb' : (0 : ℚ) < c.qb := by exact_mod_cast hqb
  unfold CC.a CC.b
  rw [div_lt_div_iff₀ hqa' hqb']
  exact_mod_cast hab

/-! ### Counting odd multiples -/

/-- `⌈(D - t)/(2t+1)⌉ = ⌊D/(2t+1) - 1/2⌋ + 1`. -/
lemma ceil_sub_eq_floor (D : ℤ) (t : ℕ) :
    ⌈((D : ℚ) - t) / ((2 * t + 1 : ℕ) : ℚ)⌉ =
      ⌊(D : ℚ) / ((2 * t + 1 : ℕ) : ℚ) - 1 / 2⌋ + 1 := by
  have hQpos : (0 : ℚ) < ((2 * t + 1 : ℕ) : ℚ) := by positivity
  set z := ⌊(D : ℚ) / ((2 * t + 1 : ℕ) : ℚ) - 1 / 2⌋ with hz
  have h1 : (z : ℚ) ≤ (D : ℚ) / ((2 * t + 1 : ℕ) : ℚ) - 1 / 2 := Int.floor_le _
  have h2 : (D : ℚ) / ((2 * t + 1 : ℕ) : ℚ) - 1 / 2 < z + 1 := Int.lt_floor_add_one _
  rw [le_sub_iff_add_le, le_div_iff₀ hQpos] at h1
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hQpos] at h2
  push_cast at h1 h2 hQpos
  have i1 : 2 * (z * (2 * t + 1)) + (2 * t + 1) ≤ 2 * D := by
    have : (2 * ((z : ℚ) * (2 * t + 1)) + (2 * t + 1)) ≤ 2 * D := by nlinarith
    exact_mod_cast this
  have i2 : 2 * D < 2 * (z * (2 * t + 1)) + 3 * (2 * t + 1) := by
    have : 2 * (D : ℚ) < 2 * ((z : ℚ) * (2 * t + 1)) + 3 * (2 * t + 1) := by nlinarith
    exact_mod_cast this
  generalize hP : z * (2 * (t : ℤ) + 1) = P at i1 i2
  have j1 : P < D - t := by omega
  have j2 : D - t ≤ P + (2 * t + 1) := by omega
  rw [Int.ceil_eq_iff]
  have hPq : (P : ℚ) = (z : ℚ) * (2 * t + 1) := by rw [← hP]; push_cast; ring
  push_cast
  constructor
  · rw [lt_div_iff₀ hQpos]
    have : (P : ℚ) < D - t := by exact_mod_cast j1
    rw [hPq] at this
    linarith
  · rw [div_le_iff₀ hQpos]
    have : (D : ℚ) - t ≤ P + (2 * t + 1) := by exact_mod_cast j2
    rw [hPq] at this
    linarith

/-- The number of `u ∈ [a, b)` with `Q ∣ 2(u - k) + 1` (`Q` odd) is
`⌊(b - k)/Q - 1/2⌋ - ⌊(a - k)/Q - 1/2⌋`. -/
lemma card_odd_dvd (a b k : ℤ) (Q : ℕ) (hQ : Odd Q) (hab : a ≤ b) :
    ((#{u ∈ Ico a b | (Q : ℤ) ∣ 2 * (u - k) + 1} : ℕ) : ℤ) =
      ⌊((b - k : ℤ) : ℚ) / Q - 1 / 2⌋ - ⌊((a - k : ℤ) : ℚ) / Q - 1 / 2⌋ := by
  obtain ⟨t, rfl⟩ := hQ
  have hQpos : (0 : ℤ) < ((2 * t + 1 : ℕ) : ℤ) := by positivity
  have hfilt : {u ∈ Ico a b | ((2 * t + 1 : ℕ) : ℤ) ∣ 2 * (u - k) + 1} =
      {u ∈ Ico a b | u ≡ k + t [ZMOD ((2 * t + 1 : ℕ) : ℤ)]} := by
    apply Finset.filter_congr
    intro u _
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
    push_cast
    constructor
    · intro hd
      have h2 : (2 * t + 1 : ℤ) ∣ 2 * (u - (k + t)) := by
        have : 2 * (u - (k + t)) = (2 * (u - k) + 1) - (2 * t + 1) := by ring
        rw [this]
        exact dvd_sub hd dvd_rfl
      have hcop : IsCoprime (2 * (t : ℤ) + 1) 2 := ⟨1, -t, by ring⟩
      exact hcop.dvd_of_dvd_mul_left h2
    · intro hd
      have : 2 * (u - k) + 1 = 2 * (u - (k + t)) + (2 * t + 1) := by ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right hd 2) dvd_rfl
  rw [hfilt, Int.Ico_filter_modEq_card _ _ hQpos]
  have e1 := ceil_sub_eq_floor (b - k) t
  have e2 := ceil_sub_eq_floor (a - k) t
  have eb : ((b : ℚ) - ((k + t : ℤ) : ℚ)) = (((b - k : ℤ) : ℚ) - t) := by push_cast; ring
  have ea : ((a : ℚ) - ((k + t : ℤ) : ℚ)) = (((a - k : ℤ) : ℚ) - t) := by push_cast; ring
  have hmono : ⌊((a - k : ℤ) : ℚ) / ((2 * t + 1 : ℕ) : ℚ) - 1 / 2⌋ ≤
      ⌊((b - k : ℤ) : ℚ) / ((2 * t + 1 : ℕ) : ℚ) - 1 / 2⌋ := by
    apply Int.floor_mono
    have : ((a - k : ℤ) : ℚ) ≤ ((b - k : ℤ) : ℚ) := by
      push_cast; linarith [(Int.cast_le (R := ℚ)).2 hab]
    have hQ' : (0 : ℚ) < ((2 * t + 1 : ℕ) : ℚ) := by positivity
    have := div_le_div_of_nonneg_right this hQ'.le
    linarith
  simp only [Int.cast_natCast] at *
  rw [eb, ea, e1, e2]
  push_cast at hmono ⊢
  omega

lemma cntQ_eq (n : ℕ) (h : Fin 6 → ℤ) (Q k : ℕ) (m : Fin 6) (hQ : Odd Q)
    (hlen : 0 ≤ (n : ℤ) + 2 * h m) :
    (cntQ n h Q k m : ℤ) = ⌊(((n : ℤ) + h m - k : ℤ) : ℚ) / Q - 1 / 2⌋ -
      ⌊((-h m - k : ℤ) : ℚ) / Q - 1 / 2⌋ := by
  unfold cntQ offsets
  exact card_odd_dvd _ _ _ Q hQ (by omega)

/-- `Q` consecutive odd numbers contain a multiple of `Q`: `cntQ ≥ ⌊N_m / Q⌋`. -/
lemma cntQ_ge (n : ℕ) (h : Fin 6 → ℤ) (Q k : ℕ) (m : Fin 6) (hQ : Odd Q)
    (hlen : 0 ≤ (n : ℤ) + 2 * h m) :
    ((n : ℤ) + 2 * h m) / (Q : ℤ) ≤ (cntQ n h Q k m : ℤ) := by
  rw [cntQ_eq n h Q k m hQ hlen]
  have hadd := Int.le_floor_add (((-h m - k : ℤ) : ℚ) / Q - 1 / 2)
    ((((n : ℤ) + 2 * h m : ℤ) : ℚ) / (Q : ℚ))
  rw [Rat.floor_intCast_div_natCast] at hadd
  have e : ((-h m - k : ℤ) : ℚ) / Q - 1 / 2 + ((((n : ℤ) + 2 * h m : ℤ) : ℚ) / (Q : ℚ)) =
      (((n : ℤ) + h m - k : ℤ) : ℚ) / Q - 1 / 2 := by push_cast; ring
  rw [e] at hadd
  linarith

/-- Every level of the residue valuation loses at most `5`. -/
lemma Wlev_ge (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (Q k : ℕ) (hQ : Odd Q)
    (hk : k ≤ n) : -5 ≤ Wlev n h Q k := by
  have hQpos : (0 : ℤ) < Q := by have := hQ.pos; exact_mod_cast this
  have hc : ∀ m, ((n : ℤ) + 2 * h m) / (Q : ℤ) ≤ (cntQ n h Q k m : ℤ) :=
    fun m => cntQ_ge n h Q k m hQ (hh.2.1 m)
  have hf : ∀ m, ((n : ℤ) + 2 * h m) - Q < Q * (((n : ℤ) + 2 * h m) / (Q : ℤ)) := by
    intro m
    have := Int.lt_ediv_add_one_mul_self ((n : ℤ) + 2 * h m) hQpos
    linarith
  have hsum : ∑ m, h m = 0 := hh.1
  have hdiv : ((k / Q : ℕ) : ℤ) + (((n - k) / Q : ℕ) : ℤ) ≤ ((n / Q : ℕ) : ℤ) := by
    have := Nat.div_add_div_le_add_div (x := k) (y := n - k) (z := Q)
    rw [Nat.add_sub_cancel' hk] at this
    exact_mod_cast this
  have hnQ : (Q : ℤ) * ((n / Q : ℕ) : ℤ) ≤ n := by
    have : ((n / Q : ℕ) : ℤ) * (Q : ℤ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n Q
    linarith
  unfold Wlev
  simp only [Fin.sum_univ_six] at hsum ⊢
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have f0 := hf 0
  have f1 := hf 1
  have f2 := hf 2
  have f3 := hf 3
  have f4 := hf 4
  have f5 := hf 5
  by_contra hcon
  push Not at hcon
  set S := ((n : ℤ) + 2 * h 0) / (Q : ℤ) + ((n : ℤ) + 2 * h 1) / (Q : ℤ) +
    ((n : ℤ) + 2 * h 2) / (Q : ℤ) + ((n : ℤ) + 2 * h 3) / (Q : ℤ) +
    ((n : ℤ) + 2 * h 4) / (Q : ℤ) + ((n : ℤ) + 2 * h 5) / (Q : ℤ) with hS
  have hS1 : S ≤ 6 * ((n / Q : ℕ) : ℤ) - 6 := by rw [hS]; linarith
  have hS2 := mul_le_mul_of_nonneg_left hS1 hQpos.le
  have hS3 : (Q : ℤ) * S = Q * (((n : ℤ) + 2 * h 0) / (Q : ℤ)) +
      Q * (((n : ℤ) + 2 * h 1) / (Q : ℤ)) + Q * (((n : ℤ) + 2 * h 2) / (Q : ℤ)) +
      Q * (((n : ℤ) + 2 * h 3) / (Q : ℤ)) + Q * (((n : ℤ) + 2 * h 4) / (Q : ℤ)) +
      Q * (((n : ℤ) + 2 * h 5) / (Q : ℤ)) := by
    rw [hS]; ring
  nlinarith

/-! ### The dictionary `Wlev = Vl` for configuration `E` -/

lemma lineB_lt (j : ℕ) (hj : j < 12) : lineB j = -40 := by simp [lineB, hj]

lemma ell_disc (j : ℕ) (hj : j < 12) (M k q : ℕ) (hq : 0 < q) :
    ell j (((40 * M : ℕ) : ℚ) / q) - (k : ℚ) / q =
      (((lineA j / 2) * M - k : ℤ) : ℚ) / q - 1 / 2 := by
  obtain ⟨z, hz⟩ := lineA_half j (by omega)
  have hz2 : lineA j / 2 = z := by omega
  have hq' : (q : ℚ) ≠ 0 := by positivity
  unfold ell
  rw [hz2, hz, lineB_lt j hj]
  push_cast
  field_simp
  ring

lemma ell12_disc (M k q : ℕ) (hq : 0 < q) :
    ell 12 (((40 * M : ℕ) : ℚ) / q) - (k : ℚ) / q = (((40 * M - k : ℤ)) : ℚ) / q := by
  have hq' : (q : ℚ) ≠ 0 := by positivity
  have hA : lineA 12 = 80 := by decide
  have hB : lineB 12 = 0 := by decide
  unfold ell
  rw [hA, hB]
  push_cast
  field_simp
  ring

lemma Vl_disc (M k q : ℕ) (hq : 0 < q) :
    Vl (((40 * M : ℕ) : ℚ) / q) ((k : ℚ) / q) =
      (∑ j ∈ range 12, lineW j * ⌊(((lineA j / 2) * M - k : ℤ) : ℚ) / q - 1 / 2⌋)
        - 6 * ⌊((40 * M - k : ℤ) : ℚ) / q⌋ - 6 * ⌊(k : ℚ) / q⌋ := by
  unfold Vl
  rw [Finset.sum_range_succ, ell12_disc M k q hq]
  have : ∀ j ∈ range 12, lineW j * ⌊ell j (((40 * M : ℕ) : ℚ) / q) - (k : ℚ) / q⌋ =
      lineW j * ⌊(((lineA j / 2) * M - k : ℤ) : ℚ) / q - 1 / 2⌋ := by
    intro j hj
    rw [ell_disc j (mem_range.1 hj) M k q hq]
  rw [Finset.sum_congr rfl this]
  simp only [lineW]
  norm_num
  ring

lemma realizable_disc (M q k : ℕ) (hq : Odd q) :
    Realizable (((40 * M : ℕ) : ℚ) / q) ((k : ℚ) / q) := by
  intro j hj z hz
  have hq0 : 0 < q := hq.pos
  rw [ell_disc j hj M k q hq0] at hz
  set A : ℤ := lineA j / 2 * M - k
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq0
  have h1 : (2 * A : ℚ) = 2 * ((q : ℚ) * z) + q := by
    field_simp at hz
    linarith
  have hZ : 2 * A = 2 * ((q : ℤ) * z) + q := by exact_mod_cast h1
  generalize (q : ℤ) * z = P at hZ
  obtain ⟨t, rfl⟩ := hq
  push_cast at hZ
  omega

lemma Wlev_eq_Vl (M q k : ℕ) (hq : Odd q) (hk : k ≤ 40 * M) :
    Wlev (40 * M) (fun i => (M : ℤ) * hE i) q k =
      Vl (((40 * M : ℕ) : ℚ) / q) ((k : ℚ) / q) := by
  have hq0 : 0 < q := hq.pos
  rw [Vl_disc M k q hq0]
  unfold Wlev
  have hadm := admissible_E M
  have hc : ∀ i : Fin 6, (cntQ (40 * M) (fun i => (M : ℤ) * hE i) q k i : ℤ) =
      ⌊((((40 + hE i) * M - k : ℤ)) : ℚ) / q - 1 / 2⌋ -
        ⌊(((-hE i) * M - k : ℤ) : ℚ) / q - 1 / 2⌋ := by
    intro i
    rw [cntQ_eq _ _ q k i hq (hadm.2.1 i)]
    congr 3 <;> push_cast <;> ring
  simp only [Fin.sum_univ_six, hc]
  have e1 : ((k / q : ℕ) : ℤ) = ⌊(k : ℚ) / q⌋ := by
    rw [Rat.floor_natCast_div_natCast]
    norm_cast
  have e2 : (((40 * M - k) / q : ℕ) : ℤ) = ⌊((40 * M - k : ℤ) : ℚ) / q⌋ := by
    have : ((40 * M - k : ℤ) : ℚ) = (((40 * M - k : ℕ) : ℤ) : ℚ) := by
      push_cast [Nat.cast_sub hk]
      ring
    rw [this, Rat.floor_intCast_div_natCast]
    push_cast
    rfl
  rw [e1, e2]
  simp [Finset.sum_range_succ, lineW, lineA, hE]
  ring

/-! ### The exponents and the common denominator -/

/-- `M(n, q) = ⌊log_q (2n)⌋`, the largest `M` with `q^M ≤ 2n`. -/
def Mlog (n q : ℕ) : ℕ := Nat.log q (2 * n)

/-- The exponent of the odd prime `q` in the common denominator (`0` for `q > n`). -/
def Eexp (n : ℕ) (h : Fin 6 → ℤ) (q : ℕ) : ℕ :=
  if q ≤ n then
    (range (n + 1)).sup fun k => (10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k).toNat
  else 0

lemma norm_le_Eexp (n : ℕ) (h : Fin 6 → ℤ) (hpos : ∀ i : Fin 5, 0 ≤ h i.succ) (q : ℕ)
    [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    padicNorm q (rho0 n h) ≤ (q : ℚ) ^ Eexp n h q ∧ padicNorm q (Z7 n h) ≤ (q : ℚ) ^ Eexp n h q ∧
      padicNorm q (Z9 n h) ≤ (q : ℚ) ^ Eexp n h q := by
  unfold Eexp
  split_ifs with hqn
  · apply rho_bound_gen hq2 n h (Mlog n q) (Nat.lt_pow_succ_log_self hq.out.one_lt _)
    intro k hk
    have h1 : (10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k) ≤
        ((10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k).toNat ≤
        (range (n + 1)).sup fun k => (10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k).toNat :=
      Finset.le_sup (f := fun k => (10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k).toNat)
        (mem_range.2 (by omega))
    have h3 : ((10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k).toNat : ℤ) ≤
        (((range (n + 1)).sup fun k => (10 * (Mlog n q : ℤ) - Wtot n h q (Mlog n q) k).toNat
          : ℕ) : ℤ) := by exact_mod_cast h2
    exact h1.trans h3
  · simpa using rho_bound_big hq2 n h hpos (by omega)

/-- Small primes: `E_q ≤ 15 M(n, q)`. -/
lemma Eexp_le_small (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (q : ℕ) (hq : Odd q) :
    Eexp n h q ≤ 15 * Mlog n q := by
  unfold Eexp
  split_ifs with hqn
  · apply Finset.sup_le
    intro k hk
    have hkn : k ≤ n := by simp at hk; omega
    have hW : -5 * (Mlog n q : ℤ) ≤ Wtot n h q (Mlog n q) k := by
      unfold Wtot
      have : ∀ e ∈ Icc 1 (Mlog n q), (-5 : ℤ) ≤ Wlev n h (q ^ e) k :=
        fun e _ => Wlev_ge n h hh (q ^ e) k hq.pow hkn
      calc -5 * (Mlog n q : ℤ) = ∑ _e ∈ Icc 1 (Mlog n q), (-5 : ℤ) := by simp; ring
        _ ≤ _ := Finset.sum_le_sum this
    omega
  · exact Nat.zero_le _

lemma Mlog_eq_one (n q : ℕ) (hqn : q ≤ 2 * n) (hsq : 2 * n < q ^ 2) :
    Mlog n q = 1 := by
  unfold Mlog
  rw [Nat.log_eq_iff (Or.inl one_ne_zero)]
  constructor
  · simpa using hqn
  · simpa using hsq

/-- Large primes: `E_q ≤ 10 - σ` if every level-one residue count is `≥ σ`. -/
lemma Eexp_le_large (n : ℕ) (h : Fin 6 → ℤ) (q : ℕ) (hqn : q ≤ n)
    (hsq : 2 * n < q ^ 2) (σ : ℤ) (hσ : σ ≤ 10) (hW : ∀ k ≤ n, σ ≤ Wlev n h q k) :
    (Eexp n h q : ℤ) ≤ 10 - σ := by
  unfold Eexp
  simp only [hqn, ↓reduceIte]
  rw [Mlog_eq_one n q (by omega) hsq]
  have : ((range (n + 1)).sup fun k => (10 * ((1 : ℕ) : ℤ) - Wtot n h q 1 k).toNat) ≤
      (10 - σ).toNat := by
    apply Finset.sup_le
    intro k hk
    have hWt : Wtot n h q 1 k = Wlev n h q k := by simp [Wtot]
    have := hW k (by simp at hk; omega)
    omega
  omega

/-- The odd primes `≤ n`. -/
def oddPrimesLE (n : ℕ) : Finset ℕ := (range (n + 1)).filter fun q => q.Prime ∧ q ≠ 2

/-- The odd part of the common denominator. -/
def Dodd (n : ℕ) (h : Fin 6 → ℤ) : ℕ := ∏ q ∈ oddPrimesLE n, q ^ Eexp n h q

/-- The common denominator: the full power of `2` of `Dcrude n` times `Dodd`. -/
def Dfull (n : ℕ) (h : Fin 6 → ℤ) : ℕ := 2 ^ padicValNat 2 (Dcrude n) * Dodd n h

lemma Dodd_pos (n : ℕ) (h : Fin 6 → ℤ) : 0 < Dodd n h := by
  unfold Dodd
  apply Finset.prod_pos
  intro q hq
  simp only [oddPrimesLE, mem_filter] at hq
  exact pow_pos hq.2.1.pos _

lemma Dfull_pos (n : ℕ) (h : Fin 6 → ℤ) : 0 < Dfull n h := by
  unfold Dfull
  have := Dodd_pos n h
  positivity

lemma padicNorm_prime_ne {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hne : q ≠ p) :
    padicNorm p (q : ℚ) = 1 := by
  have := Fact.mk hq
  exact padicNorm.padicNorm_of_prime_of_ne hne.symm

lemma padicNorm_Dodd_two (n : ℕ) (h : Fin 6 → ℤ) : padicNorm 2 (Dodd n h : ℚ) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Dodd
  push_cast
  rw [pn_prod]
  apply Finset.prod_eq_one
  intro q hq
  simp only [oddPrimesLE, mem_filter] at hq
  rw [pn_pow, padicNorm_prime_ne hq.2.1 hq.2.2, one_pow]

lemma padicNorm_Dodd_odd (n : ℕ) (h : Fin 6 → ℤ) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    padicNorm p (Dodd n h : ℚ) = ((p : ℚ) ^ Eexp n h p)⁻¹ := by
  unfold Dodd
  push_cast
  rw [pn_prod]
  by_cases hpn : p ≤ n
  · have hmem : p ∈ oddPrimesLE n := by
      simp only [oddPrimesLE, mem_filter, mem_range]
      exact ⟨by omega, hp.out, hp2⟩
    rw [Finset.prod_eq_single_of_mem p hmem]
    · rw [pn_pow, padicNorm.padicNorm_p_of_prime, inv_pow]
    · intro q hq hqp
      simp only [oddPrimesLE, mem_filter] at hq
      rw [pn_pow, padicNorm_prime_ne hq.2.1 hqp, one_pow]
  · have hE : Eexp n h p = 0 := by unfold Eexp; simp [hpn]
    rw [hE, pow_zero, inv_one]
    apply Finset.prod_eq_one
    intro q hq
    simp only [oddPrimesLE, mem_filter, mem_range] at hq
    rw [pn_pow, padicNorm_prime_ne hq.2.1 (by omega), one_pow]

lemma padicNorm_two_pow_odd (a p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    padicNorm p (((2 ^ a : ℕ) : ℕ) : ℚ) = 1 := by
  push_cast
  rw [pn_pow]
  have : padicNorm p ((2 : ℕ) : ℚ) = 1 := padicNorm_prime_ne Nat.prime_two (Ne.symm hp2)
  push_cast at this
  rw [this, one_pow]

lemma padicNorm_two : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := padicNorm.padicNorm_p_of_prime (p := 2)
  exact_mod_cast this

lemma padicNorm_two_pow_val (N : ℕ) (hN : N ≠ 0) :
    padicNorm 2 (((2 ^ padicValNat 2 N : ℕ)) : ℚ) = padicNorm 2 (N : ℚ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hv : padicValRat 2 (N : ℚ) = (padicValNat 2 N : ℤ) := padicValRat.of_nat
  rw [padicNorm.eq_zpow_of_nonzero hN', hv, zpow_neg, zpow_natCast]
  push_cast
  rw [pn_pow, padicNorm_two, inv_pow]

/-- A rational number whose `p`-adic norm is `≤ 1` for every prime `p` is an integer. -/
lemma int_of_padicNorm_le_one (r : ℚ) (h : ∀ p : ℕ, p.Prime → padicNorm p r ≤ 1) :
    ∃ z : ℤ, r = z := by
  refine ⟨r.num, ?_⟩
  have hden : r.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have := Fact.mk hp
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0] at hne
      exact hne rfl
    have hvden : 1 ≤ padicValNat p r.den := one_le_padicValNat_of_dvd r.den_nz hpd
    have hvnum : padicValInt p r.num = 0 := by
      rcases Rat.num_or_den_zero_padicVal r hp with h0 | h0
      · exact h0
      · omega
    have hv : padicValRat p r ≤ -1 := by
      rw [padicValRat_def, hvnum]
      omega
    have h1 := h p hp
    rw [padicNorm.eq_zpow_of_nonzero hr0] at h1
    have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    have : (1 : ℚ) < (p : ℚ) ^ (-padicValRat p r) := one_lt_zpow₀ hp1 (by omega)
    linarith
  exact ((Rat.den_eq_one_iff r).1 hden).symm

/-- `Dfull` clears the denominators of `ρ₀`, `Z₇`, `Z₉`. -/
theorem Dfull_clears (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h)
    (hpos : ∀ i : Fin 5, 0 ≤ h i.succ) (hCI : Stmt_CrudeInt) : ClearsDen (Dfull n h) n h := by
  obtain ⟨hDc, ⟨z1, hz1⟩, ⟨z2, hz2⟩, ⟨z3, hz3⟩⟩ := hCI.forms n h hh
  have key : ∀ x : ℚ, (∃ z : ℤ, (Dcrude n : ℚ) * x = z) →
      (∀ p : ℕ, ∀ _ : Fact p.Prime, p ≠ 2 → padicNorm p x ≤ (p : ℚ) ^ Eexp n h p) →
      ∃ z : ℤ, (Dfull n h : ℚ) * x = z := by
    intro x ⟨z, hz⟩ hodd
    apply int_of_padicNorm_le_one
    intro p hp
    have := Fact.mk hp
    unfold Dfull
    push_cast
    rw [padicNorm.mul, padicNorm.mul]
    by_cases hp2 : p = 2
    · subst hp2
      have e := padicNorm_two_pow_val (Dcrude n) hDc.ne'
      push_cast at e
      rw [e, padicNorm_Dodd_two, mul_one, ← padicNorm.mul, hz]
      exact padicNorm.of_int z
    · have e := padicNorm_two_pow_odd (padicValNat 2 (Dcrude n)) p hp2
      push_cast at e
      rw [e, one_mul, padicNorm_Dodd_odd n h p hp2]
      have hx := hodd p inferInstance hp2
      have hpos' : (0 : ℚ) < (p : ℚ) ^ Eexp n h p := by
        have : (0 : ℚ) < p := by exact_mod_cast hp.pos
        positivity
      calc ((p : ℚ) ^ Eexp n h p)⁻¹ * padicNorm p x
          ≤ ((p : ℚ) ^ Eexp n h p)⁻¹ * (p : ℚ) ^ Eexp n h p :=
            mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hpos'.le)
        _ = 1 := inv_mul_cancel₀ hpos'.ne'
  refine ⟨Dfull_pos n h, key _ ⟨z1, hz1⟩ ?_, key _ ⟨z2, hz2⟩ ?_, key _ ⟨z3, hz3⟩ ?_⟩
  · intro p _ hp2; exact (norm_le_Eexp n h hpos p hp2).1
  · intro p _ hp2; exact (norm_le_Eexp n h hpos p hp2).2.1
  · intro p _ hp2; exact (norm_le_Eexp n h hpos p hp2).2.2

/-- The odd part of `Dfull` is `Dodd`. -/
lemma Dfull_mul_norm (n : ℕ) (h : Fin 6 → ℤ) :
    (Dfull n h : ℝ) * ‖((Dfull n h : ℕ) : ℚ_[2])‖ = Dodd n h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e1 : ‖((Dfull n h : ℕ) : ℚ_[2])‖ = ((padicNorm 2 ((Dfull n h : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [← Padic.eq_padicNorm]
    push_cast
    rfl
  have e2 : padicNorm 2 ((Dfull n h : ℕ) : ℚ) = ((2 : ℚ) ^ padicValNat 2 (Dcrude n))⁻¹ := by
    unfold Dfull
    push_cast
    rw [padicNorm.mul, pn_pow, padicNorm_two, padicNorm_Dodd_two, mul_one, inv_pow]
  rw [e1, e2]
  unfold Dfull
  push_cast
  field_simp

/-! ### Sums over primes in intervals -/

/-- The primes in `(u, v]`. -/
def primesIoc (u v : ℕ) : Finset ℕ := (Ioc u v).filter Nat.Prime

lemma sum_primesIoc_split (u v w : ℕ) (huv : u ≤ v) (hvw : v ≤ w) (g : ℕ → ℝ) :
    ∑ p ∈ primesIoc u w, g p = ∑ p ∈ primesIoc u v, g p + ∑ p ∈ primesIoc v w, g p := by
  unfold primesIoc
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_consecutive _ huv hvw]

lemma theta_nat_sub (u v : ℕ) (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u = ∑ p ∈ primesIoc u v, Real.log p := by
  have h1 : Chebyshev.theta v = ∑ p ∈ primesIoc 0 v, Real.log p := by
    unfold Chebyshev.theta primesIoc
    rw [Nat.floor_natCast]
  have h2 : Chebyshev.theta u = ∑ p ∈ primesIoc 0 u, Real.log p := by
    unfold Chebyshev.theta primesIoc
    rw [Nat.floor_natCast]
  rw [h1, h2, sum_primesIoc_split 0 u v (Nat.zero_le u) huv]
  ring

lemma interval_sum_le (y a b w : ℝ) (hy : 0 ≤ y) (ha : 0 < a) (hab : a ≤ b)
    (f : ℕ → ℝ) (hf : ∀ q : ℕ, q.Prime → a ≤ y / q → y / q < b → f q ≤ w) :
    ∑ q ∈ primesIoc ⌊y / b⌋₊ ⌊y / a⌋₊, f q * Real.log q ≤
      w * (Chebyshev.theta (y / a) - Chebyshev.theta (y / b)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hfl : ⌊y / b⌋₊ ≤ ⌊y / a⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_left hy ha hab)
  rw [Chebyshev.theta_eq_theta_coe_floor (y / a), Chebyshev.theta_eq_theta_coe_floor (y / b),
    theta_nat_sub _ _ hfl, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  simp only [primesIoc, mem_filter, mem_Ioc] at hq
  obtain ⟨⟨h1, h2⟩, hqp⟩ := hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hyb : y / b < q := (Nat.floor_lt (by positivity)).1 h1
  have hya : (q : ℝ) ≤ y / a := (Nat.le_floor_iff (by positivity)).1 h2
  have e1 : a ≤ y / q := by
    rw [le_div_iff₀ hq0]
    rw [le_div_iff₀ ha] at hya
    linarith
  have e2 : y / q < b := by
    rw [div_lt_iff₀ hq0]
    rw [div_lt_iff₀ hb] at hyb
    linarith
  have := hf q hqp e1 e2
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  exact mul_le_mul_of_nonneg_right this hlog

lemma chainFrom_le : ∀ (L : List CC) (A B : ℤ × ℤ), chainFrom A L B = true →
    (∀ c ∈ L, ivOK c = true) → 0 < A.2 →
      ((A.1 : ℚ) / A.2 ≤ (B.1 : ℚ) / B.2 ∧ 0 < B.2)
  | [], A, B, h, _, hA => by
    simp only [chainFrom, decide_eq_true_eq] at h
    subst h
    exact ⟨le_rfl, hA⟩
  | c :: L, A, B, h, hok, _ => by
    simp only [chainFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpa, hqa⟩, hL⟩ := h
    obtain ⟨hqa', hqb', hab⟩ := ivOK_lt c (hok c List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := chainFrom_le L (c.pb, c.qb) B hL
      (fun c' hc' => hok c' (List.mem_cons_of_mem _ hc')) hqb'
    refine ⟨?_, ih2⟩
    have : (A.1 : ℚ) / A.2 = c.a := by unfold CC.a; rw [hpa, hqa]
    rw [this]
    exact hab.le.trans ih1

lemma CC.a_real (c : CC) : ((c.a : ℚ) : ℝ) = (c.pa : ℝ) / c.qa := by
  unfold CC.a; push_cast; rfl

lemma CC.b_real (c : CC) : ((c.b : ℚ) : ℝ) = (c.pb : ℝ) / c.qb := by
  unfold CC.b; push_cast; rfl

/-- Summing a bounded function over the primes of a chain of intervals. -/
lemma chain_sum (y : ℝ) (hy : 0 ≤ y) (f : ℕ → ℝ) (w : CC → ℝ) :
    ∀ (L : List CC) (A B : ℤ × ℤ), chainFrom A L B = true → (∀ c ∈ L, ivOK c = true) →
      0 < A.1 → 0 < A.2 →
      (∀ c ∈ L, ∀ q : ℕ, q.Prime → ((c.a : ℚ) : ℝ) ≤ y / q → y / q < ((c.b : ℚ) : ℝ) →
        f q ≤ w c) →
      (∀ c ∈ L, 0 ≤ w c) →
      ∑ q ∈ primesIoc ⌊y / ((B.1 : ℝ) / B.2)⌋₊ ⌊y / ((A.1 : ℝ) / A.2)⌋₊, f q * Real.log q ≤
        (L.map fun c => w c * (Chebyshev.theta (y / ((c.a : ℚ) : ℝ)) -
          Chebyshev.theta (y / ((c.b : ℚ) : ℝ)))).sum
  | [], A, B, h, _, _, _, _, _ => by
    simp only [chainFrom, decide_eq_true_eq] at h
    subst h
    simp [primesIoc]
  | c :: L, A, B, h, hok, hA1, hA2, hf, hw => by
    simp only [chainFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpa, hqa⟩, hL⟩ := h
    obtain ⟨hqa', hqb', hab⟩ := ivOK_lt c (hok c List.mem_cons_self)
    have hok' : ∀ c' ∈ L, ivOK c' = true := fun c' hc' => hok c' (List.mem_cons_of_mem _ hc')
    obtain ⟨hbB, hB2⟩ := chainFrom_le L (c.pb, c.qb) B hL hok' hqb'
    -- positivity of the endpoints
    have ha : (0 : ℚ) < c.a := by
      unfold CC.a; rw [hpa, hqa]
      have : (0 : ℚ) < A.1 := by exact_mod_cast hA1
      have : (0 : ℚ) < A.2 := by exact_mod_cast hA2
      positivity
    have hb : (0 : ℚ) < c.b := ha.trans hab
    have hpb : 0 < c.pb := by
      have hb' := hb
      unfold CC.b at hb'
      have hqb'' : (0 : ℚ) < c.qb := by exact_mod_cast hqb'
      have : (0 : ℚ) < c.pb := by
        by_contra hneg
        push Not at hneg
        have : (c.pb : ℚ) / c.qb ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hqb''.le
        linarith
      exact_mod_cast this
    have ih := chain_sum y hy f w L (c.pb, c.qb) B hL hok' hpb hqb'
      (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
    -- the three indices
    have eA : ((A.1 : ℝ) / A.2) = ((c.a : ℚ) : ℝ) := by rw [CC.a_real, hpa, hqa]
    have eb : ((c.pb, c.qb).1 : ℝ) / ((c.pb, c.qb).2 : ℝ) = ((c.b : ℚ) : ℝ) := by
      rw [CC.b_real]
    rw [eb] at ih
    rw [eA]
    have haR : (0 : ℝ) < ((c.a : ℚ) : ℝ) := by exact_mod_cast ha
    have hbR : (0 : ℝ) < ((c.b : ℚ) : ℝ) := by exact_mod_cast hb
    have habR : ((c.a : ℚ) : ℝ) ≤ ((c.b : ℚ) : ℝ) := by exact_mod_cast hab.le
    have hbBR : ((c.b : ℚ) : ℝ) ≤ (B.1 : ℝ) / B.2 := by
      have : (c.b : ℚ) ≤ (B.1 : ℚ) / B.2 := by
        have e : (c.b : ℚ) = ((c.pb, c.qb).1 : ℚ) / ((c.pb, c.qb).2 : ℚ) := rfl
        rw [e]
        exact hbB
      have := (Rat.cast_le (K := ℝ)).2 this
      push_cast at this
      exact this
    have i1 : ⌊y / ((B.1 : ℝ) / B.2)⌋₊ ≤ ⌊y / ((c.b : ℚ) : ℝ)⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hy hbR hbBR)
    have i2 : ⌊y / ((c.b : ℚ) : ℝ)⌋₊ ≤ ⌊y / ((c.a : ℚ) : ℝ)⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hy haR habR)
    rw [sum_primesIoc_split _ _ _ i1 i2, List.map_cons, List.sum_cons]
    have hc := interval_sum_le y ((c.a : ℚ) : ℝ) ((c.b : ℚ) : ℝ) (w c) hy haR habR
      f (fun q hq h1 h2 => hf c List.mem_cons_self q hq h1 h2)
    linarith

/-! ### The prime number theorem for `θ` -/

lemma theta_tendsto (hPNT : PNT_Stmt) :
    Tendsto (fun x => Chebyshev.theta x / x) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hsq : Tendsto (fun x : ℝ => C / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h1 : Tendsto (fun x => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hsq
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_nonneg (sub_nonneg.2 (Chebyshev.theta_le_psi x)) hx.le
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have hs := Real.sqrt_pos.2 hx
      rw [div_le_div_iff₀ hx hs]
      have := hC x
      have hss := Real.mul_self_sqrt hx.le
      have h0 : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := sub_nonneg.2 (Chebyshev.theta_le_psi x)
      nlinarith [Real.sqrt_nonneg x]
  have h2 := hPNT.sub h1
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards with x
  ring

lemma theta_eventually (hPNT : PNT_Stmt) (r : ℝ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, |Chebyshev.theta (40 * m / r) - 40 * m / r| ≤ δ * (40 * m / r) := by
  have ht := theta_tendsto hPNT
  have hmap : Tendsto (fun m : ℕ => 40 * (m : ℝ) / r) atTop atTop := by
    apply Tendsto.atTop_div_const hr
    exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hc := ht.comp hmap
  rw [Metric.tendsto_nhds] at hc
  filter_upwards [hc δ hδ, hmap.eventually (eventually_gt_atTop 0)] with m hm hpos
  simp only [Function.comp, Real.dist_eq] at hm
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have e : Chebyshev.theta (40 * m / r) - 40 * m / r =
      (40 * m / r) * (Chebyshev.theta (40 * m / r) / (40 * m / r) - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hpos, mul_comm δ]
  exact mul_le_mul_of_nonneg_left hm.le hpos.le

lemma eventually_forall_list {α : Type*} (L : List α) (P : α → ℕ → Prop)
    (h : ∀ a ∈ L, ∀ᶠ m in atTop, P a m) : ∀ᶠ m in atTop, ∀ a ∈ L, P a m := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    filter_upwards [h1, h2] with m hm1 hm2
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact hm1
    · exact hm2 b hb'

lemma list_sum_le {α : Type*} (L : List α) (f g : α → ℝ) (h : ∀ a ∈ L, f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-! ### The small-prime error term -/

lemma small_term_eventually (K : ℝ) :
    ∀ᶠ m : ℕ in atTop, K * ((Real.sqrt (2 * (40 * m : ℝ)) + 1) * Real.log (2 * (40 * m : ℝ))) ≤
      40 * m := by
  have hs : Tendsto (fun m : ℕ => Real.sqrt (Real.sqrt (2 * (40 * m : ℝ)))) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    apply Real.tendsto_sqrt_atTop.comp
    apply Tendsto.const_mul_atTop (by norm_num)
    exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  filter_upwards [hs.eventually (eventually_ge_atTop (16 * |K| + 1))] with m hm
  set x : ℝ := 2 * (40 * m : ℝ) with hx
  set s := Real.sqrt (Real.sqrt x) with hs_def
  have hx0 : 0 ≤ x := by positivity
  have hs1 : 1 ≤ s := by
    have : (0 : ℝ) ≤ 16 * |K| := by positivity
    linarith
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hs4 : s ^ 4 = x := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, Real.sq_sqrt hx0]
  have hlog : Real.log x = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]
    push_cast
    ring
  have hls : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hlx : Real.log x ≤ 4 * s := by linarith
  have hlx0 : 0 ≤ Real.log x := by linarith
  -- (√x + 1) log x ≤ 2 s² · 4 s = 8 s³
  have h1 : (Real.sqrt x + 1) * Real.log x ≤ 8 * s ^ 3 := by
    rw [← hs2]
    have : s ^ 2 + 1 ≤ 2 * s ^ 2 := by nlinarith
    calc (s ^ 2 + 1) * Real.log x ≤ (2 * s ^ 2) * (4 * s) := by
          apply mul_le_mul this hlx hlx0 (by positivity)
      _ = 8 * s ^ 3 := by ring
  have hprod : 0 ≤ (Real.sqrt x + 1) * Real.log x := by positivity
  have hK : K * ((Real.sqrt x + 1) * Real.log x) ≤ |K| * (8 * s ^ 3) := by
    calc K * ((Real.sqrt x + 1) * Real.log x) ≤ |K| * ((Real.sqrt x + 1) * Real.log x) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hprod
      _ ≤ |K| * (8 * s ^ 3) := mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
  have h40 : (40 * m : ℝ) = s ^ 4 / 2 := by rw [hs4, hx]; ring
  rw [h40]
  have : |K| * (8 * s ^ 3) ≤ s ^ 4 / 2 := by
    have h16 : 16 * |K| ≤ s := by linarith
    have hs3 : 0 ≤ s ^ 3 := by positivity
    nlinarith
  linarith

lemma list_sum_affine {α : Type*} (L : List α) (g : α → ℝ) (x K : ℝ) :
    (L.map fun c => x * g c + K).sum = x * (L.map g).sum + K * L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

/-- The main analytic estimate, abstracted from the arithmetic of the denominators. -/
theorem log_sum_bound (hPNT : PNT_Stmt) (E : ℕ → ℕ → ℕ) (L : List CC)
    (hL : chainFrom (1, 1) L (81, 1) = true) (hok : ∀ c ∈ L, ivOK c = true)
    (hsig : ∀ c ∈ L, -2 ≤ c.sig ∧ c.sig ≤ 10) (ha1 : ∀ c ∈ L, 1 ≤ c.a)
    (hb81 : ∀ c ∈ L, c.b ≤ 81) (hlen : L.length ≤ 2432)
    (hT : (L.map fun c => ((10 - c.sig : ℤ) : ℝ) *
        (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))).sum + 12 / 81 ≤ 897 / 100)
    (hsmall : ∀ m q : ℕ, q ∈ oddPrimesLE (40 * m) → q ^ 2 ≤ 2 * (40 * m) →
      E m q ≤ 15 * Mlog (40 * m) q)
    (hlarge : ∀ m q : ℕ, q ∈ oddPrimesLE (40 * m) → 2 * (40 * m) < q ^ 2 → (E m q : ℝ) ≤ 12)
    (hcert : ∀ m q : ℕ, ∀ c ∈ L, q.Prime → q ≠ 2 → q ≤ 40 * m → 2 * (40 * m) < q ^ 2 →
      ((c.a : ℚ) : ℝ) ≤ (40 * m : ℝ) / q → (40 * m : ℝ) / q < ((c.b : ℚ) : ℝ) →
        (E m q : ℝ) ≤ 10 - c.sig) :
    ∀ ε > 0, ∀ᶠ m in atTop,
      ∑ q ∈ oddPrimesLE (40 * m), (E m q : ℝ) * Real.log q ≤ (9 + ε) * (40 * m) := by
  intro ε hε
  set δ : ℝ := ε / 240000 with hδ
  have hδ0 : 0 < δ := by positivity
  -- eventual facts
  have hPa : ∀ᶠ m : ℕ in atTop, ∀ c ∈ L,
      |Chebyshev.theta (40 * m / ((c.a : ℚ) : ℝ)) - 40 * m / ((c.a : ℚ) : ℝ)| ≤
        δ * (40 * m / ((c.a : ℚ) : ℝ)) :=
    eventually_forall_list L _ fun c hc => theta_eventually hPNT _
      (by have := ha1 c hc; have : (0 : ℚ) < c.a := by linarith
          exact_mod_cast this) δ hδ0
  have hPb : ∀ᶠ m : ℕ in atTop, ∀ c ∈ L,
      |Chebyshev.theta (40 * m / ((c.b : ℚ) : ℝ)) - 40 * m / ((c.b : ℚ) : ℝ)| ≤
        δ * (40 * m / ((c.b : ℚ) : ℝ)) :=
    eventually_forall_list L _ fun c hc => theta_eventually hPNT _
      (by have := ha1 c hc; have := (ivOK_lt c (hok c hc)).2.2
          have : (0 : ℚ) < c.b := by linarith
          exact_mod_cast this) δ hδ0
  have hP81 := theta_eventually hPNT 81 (by norm_num) δ hδ0
  have hsm := small_term_eventually (60 / ε)
  filter_upwards [hPa, hPb, hP81, hsm, eventually_ge_atTop 330] with m hma hmb hm81 hmsm hm330
  set n : ℕ := 40 * m with hn
  have hnR : ((40 * m : ℕ) : ℝ) = 40 * (m : ℝ) := by push_cast; ring
  have hn13 : 13122 ≤ n := by omega
  -- split into small and large primes
  rw [← Finset.sum_filter_add_sum_filter_not (oddPrimesLE n) (fun q => q ^ 2 ≤ 2 * n)]
  -- the small primes
  have hS1 : ∑ q ∈ (oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n), (E m q : ℝ) * Real.log q ≤
      15 * ((Real.sqrt (2 * (40 * m : ℝ)) + 1) * Real.log (2 * (40 * m : ℝ))) := by
    have hterm : ∀ q ∈ (oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n),
        (E m q : ℝ) * Real.log q ≤ 15 * Real.log (2 * (40 * m : ℝ)) := by
      intro q hq
      simp only [mem_filter, oddPrimesLE, mem_range] at hq
      obtain ⟨⟨hqn, hqp, hq2⟩, hsq⟩ := hq
      have hE := hsmall m q
        (by simp only [oddPrimesLE, mem_filter, mem_range]; exact ⟨hqn, hqp, hq2⟩) hsq
      have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
      have hpow : q ^ Mlog n q ≤ 2 * n := Nat.pow_log_le_self q (by omega)
      have hlog2 : (Mlog n q : ℝ) * Real.log q ≤ Real.log (2 * (40 * m : ℝ)) := by
        rw [← Real.log_pow]
        apply Real.log_le_log (by have := hqp.pos; positivity)
        have : ((q ^ Mlog n q : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hpow
        push_cast at this
        rw [hn] at this
        push_cast at this
        linarith
      calc (E m q : ℝ) * Real.log q ≤ ((15 * Mlog n q : ℕ) : ℝ) * Real.log q := by
            apply mul_le_mul_of_nonneg_right _ hlogq
            exact_mod_cast hE
        _ = 15 * ((Mlog n q : ℝ) * Real.log q) := by push_cast; ring
        _ ≤ 15 * Real.log (2 * (40 * m : ℝ)) := by linarith
    have hcard : (((oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n)).card : ℝ) ≤
        Real.sqrt (2 * (40 * m : ℝ)) + 1 := by
      have hsub : (oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n) ⊆
          range (Nat.sqrt (2 * n) + 1) := by
        intro q hq
        simp only [mem_filter] at hq
        rw [mem_range]
        have := Nat.le_sqrt'.2 hq.2
        omega
      have h1 := Finset.card_le_card hsub
      rw [card_range] at h1
      have h2 : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ Real.sqrt ((2 * n : ℕ) : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      have h3 : (((oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n)).card : ℝ) ≤
          ((Nat.sqrt (2 * n) + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2 h3
      rw [hn] at h2
      push_cast at h2
      linarith
    have hlog0 : 0 ≤ Real.log (2 * (40 * m : ℝ)) := Real.log_nonneg (by
      have : (330 : ℝ) ≤ m := by exact_mod_cast hm330
      linarith)
    calc ∑ q ∈ (oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n), (E m q : ℝ) * Real.log q
        ≤ ∑ q ∈ (oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n),
            15 * Real.log (2 * (40 * m : ℝ)) := Finset.sum_le_sum hterm
      _ = (((oddPrimesLE n).filter (fun q => q ^ 2 ≤ 2 * n)).card : ℝ) *
            (15 * Real.log (2 * (40 * m : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Real.sqrt (2 * (40 * m : ℝ)) + 1) * (15 * Real.log (2 * (40 * m : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 15 * ((Real.sqrt (2 * (40 * m : ℝ)) + 1) * Real.log (2 * (40 * m : ℝ))) := by ring
  -- the large primes
  set N81 : ℕ := n / 81 with hN81
  set SL := (oddPrimesLE n).filter (fun q => ¬ q ^ 2 ≤ 2 * n) with hSL
  rw [← Finset.sum_filter_add_sum_filter_not SL (fun q => q ≤ N81)]
  have hS2 : ∑ q ∈ SL.filter (fun q => q ≤ N81), (E m q : ℝ) * Real.log q ≤
      12 * Chebyshev.theta ((40 * m : ℝ) / 81) := by
    have hth : Chebyshev.theta ((40 * m : ℝ) / 81) = ∑ p ∈ primesIoc 0 N81, Real.log p := by
      rw [Chebyshev.theta_eq_theta_coe_floor]
      have hfl : ⌊(40 * m : ℝ) / 81⌋₊ = N81 := by
        rw [hN81, hn, ← Nat.floor_div_eq_div (K := ℝ) (40 * m) 81]
        push_cast
        rfl
      rw [hfl]
      have := theta_nat_sub 0 N81 (Nat.zero_le _)
      simp only [CharP.cast_eq_zero, Chebyshev.theta_zero, sub_zero] at this
      exact this
    rw [hth, Finset.mul_sum]
    calc ∑ q ∈ SL.filter (fun q => q ≤ N81), (E m q : ℝ) * Real.log q
        ≤ ∑ q ∈ SL.filter (fun q => q ≤ N81), 12 * Real.log q := by
          apply Finset.sum_le_sum
          intro q hq
          simp only [hSL, mem_filter] at hq
          apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg q)
          exact hlarge m q hq.1.1 (by omega)
      _ ≤ ∑ p ∈ primesIoc 0 N81, 12 * Real.log p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            simp only [hSL, mem_filter, oddPrimesLE, mem_range] at hq
            simp only [primesIoc, mem_filter, mem_Ioc]
            exact ⟨⟨hq.1.1.2.1.pos, hq.2⟩, hq.1.1.2.1⟩
          · intro p _ _
            have := Real.log_natCast_nonneg p
            positivity
  have hS3 : ∑ q ∈ SL.filter (fun q => ¬ q ≤ N81), (E m q : ℝ) * Real.log q ≤
      (L.map fun c => ((10 - c.sig : ℤ) : ℝ) * (Chebyshev.theta ((40 * m : ℝ) / ((c.a : ℚ) : ℝ)) -
          Chebyshev.theta ((40 * m : ℝ) / ((c.b : ℚ) : ℝ)))).sum := by
    have hch := chain_sum (40 * m : ℝ) (by positivity) (fun q => (E m q : ℝ))
      (fun c => ((10 - c.sig : ℤ) : ℝ)) L (1, 1) (81, 1) hL hok (by norm_num) (by norm_num)
      (by
        intro c hc q hq h1 h2
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
        have hc1 : (1 : ℝ) ≤ ((c.a : ℚ) : ℝ) := by exact_mod_cast ha1 c hc
        have hc81 : ((c.b : ℚ) : ℝ) ≤ 81 := by exact_mod_cast hb81 c hc
        have hqn : (q : ℝ) ≤ 40 * m := by
          have := hc1.trans h1
          rw [le_div_iff₀ hq0] at this
          linarith
        have hq81 : (40 * m : ℝ) < 81 * q := by
          have := h2.trans_le hc81
          rw [div_lt_iff₀ hq0] at this
          linarith
        have hqn' : q ≤ 40 * m := by exact_mod_cast hqn
        have hq81' : 40 * m < 81 * q := by exact_mod_cast hq81
        have hq2 : q ≠ 2 := by omega
        have hsq : 2 * (40 * m) < q ^ 2 := by nlinarith
        have := hcert m q c hc hq hq2 hqn' hsq h1 h2
        push_cast at this ⊢
        exact this)
      (by
        intro c hc
        have := (hsig c hc).2
        have : (0 : ℤ) ≤ 10 - c.sig := by linarith
        exact_mod_cast this)
    have e1 : ⌊(40 * m : ℝ) / (((81, 1) : ℤ × ℤ).1 / ((81, 1) : ℤ × ℤ).2 : ℝ)⌋₊ = N81 := by
      rw [hN81, hn, ← Nat.floor_div_eq_div (K := ℝ) (40 * m) 81]
      simp only [Int.cast_ofNat, Int.cast_one, div_one]
      push_cast
      rfl
    have e2 : ⌊(40 * m : ℝ) / (((1, 1) : ℤ × ℤ).1 / ((1, 1) : ℤ × ℤ).2 : ℝ)⌋₊ = n := by
      push_cast
      rw [div_one, div_one, hn]
      exact_mod_cast Nat.floor_natCast (40 * m)
    rw [e1, e2] at hch
    refine le_trans ?_ hch
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [hSL, mem_filter, oddPrimesLE, mem_range] at hq
      simp only [primesIoc, mem_filter, mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hq.1.1.2.1⟩
    · intro q _ _
      have := Real.log_natCast_nonneg q
      positivity
  -- PNT on each interval
  have hPNTsum : (L.map fun c => ((10 - c.sig : ℤ) : ℝ) *
      (Chebyshev.theta ((40 * m : ℝ) / ((c.a : ℚ) : ℝ)) -
        Chebyshev.theta ((40 * m : ℝ) / ((c.b : ℚ) : ℝ)))).sum ≤
      (40 * m : ℝ) * (L.map fun c => ((10 - c.sig : ℤ) : ℝ) *
        (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))).sum + 24 * δ * (40 * m) * L.length := by
    rw [← list_sum_affine]
    apply list_sum_le
    intro c hc
    have hw0 : (0 : ℝ) ≤ ((10 - c.sig : ℤ) : ℝ) := by
      have := (hsig c hc).2
      have : (0 : ℤ) ≤ 10 - c.sig := by linarith
      exact_mod_cast this
    have hw12 : ((10 - c.sig : ℤ) : ℝ) ≤ 12 := by
      have := (hsig c hc).1
      have : 10 - c.sig ≤ (12 : ℤ) := by linarith
      exact_mod_cast this
    have hc1 : (1 : ℝ) ≤ ((c.a : ℚ) : ℝ) := by exact_mod_cast ha1 c hc
    have hcb1 : (1 : ℝ) ≤ ((c.b : ℚ) : ℝ) := by
      have := (ivOK_lt c (hok c hc)).2.2
      have : (1 : ℚ) ≤ c.b := by linarith [ha1 c hc]
      exact_mod_cast this
    have hm0 : (0 : ℝ) ≤ 40 * m := by positivity
    have hA := hma c hc
    have hB := hmb c hc
    rw [abs_le] at hA hB
    have hna : (40 * m : ℝ) / ((c.a : ℚ) : ℝ) ≤ 40 * m := div_le_self hm0 hc1
    have hnb : (40 * m : ℝ) / ((c.b : ℚ) : ℝ) ≤ 40 * m := div_le_self hm0 hcb1
    have hdiff : Chebyshev.theta ((40 * m : ℝ) / ((c.a : ℚ) : ℝ)) -
        Chebyshev.theta ((40 * m : ℝ) / ((c.b : ℚ) : ℝ)) ≤
        (40 * m : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ)) + 2 * δ * (40 * m) := by
      have e1 : (40 * m : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ)) =
          (40 * m : ℝ) / ((c.a : ℚ) : ℝ) - (40 * m : ℝ) / ((c.b : ℚ) : ℝ) := by ring
      rw [e1]
      nlinarith
    have hpos :
        0 ≤ (40 * m : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ)) + 2 * δ * (40 * m) := by
      have : 1 / ((c.b : ℚ) : ℝ) ≤ 1 / ((c.a : ℚ) : ℝ) := by
        apply one_div_le_one_div_of_le (by linarith)
        exact_mod_cast (ivOK_lt c (hok c hc)).2.2.le
      have : 0 ≤ (40 * m : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ)) :=
        mul_nonneg hm0 (by linarith)
      positivity
    calc ((10 - c.sig : ℤ) : ℝ) * (Chebyshev.theta ((40 * m : ℝ) / ((c.a : ℚ) : ℝ)) -
          Chebyshev.theta ((40 * m : ℝ) / ((c.b : ℚ) : ℝ)))
        ≤ ((10 - c.sig : ℤ) : ℝ) * ((40 * m : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ)) +
            2 * δ * (40 * m)) := mul_le_mul_of_nonneg_left hdiff hw0
      _ = (40 * m : ℝ) * (((10 - c.sig : ℤ) : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))) +
            ((10 - c.sig : ℤ) : ℝ) * (2 * δ * (40 * m)) := by ring
      _ ≤ (40 * m : ℝ) * (((10 - c.sig : ℤ) : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))) +
            24 * δ * (40 * m) := by
          have : ((10 - c.sig : ℤ) : ℝ) * (2 * δ * (40 * m)) ≤ 12 * (2 * δ * (40 * m)) :=
            mul_le_mul_of_nonneg_right hw12 (by positivity)
          linarith
  -- assemble
  rw [abs_le] at hm81
  have hlenR : (L.length : ℝ) ≤ 2432 := by exact_mod_cast hlen
  have hm0 : (0 : ℝ) ≤ 40 * m := by positivity
  have hsmall' : 15 * ((Real.sqrt (2 * (40 * m : ℝ)) + 1) * Real.log (2 * (40 * m : ℝ))) ≤
      ε / 4 * (40 * m) := by
    have h4 := mul_le_mul_of_nonneg_left hmsm (by positivity : (0 : ℝ) ≤ ε / 4)
    have e : ε / 4 * (60 / ε * ((Real.sqrt (2 * (40 * m : ℝ)) + 1) *
        Real.log (2 * (40 * m : ℝ)))) =
        15 * ((Real.sqrt (2 * (40 * m : ℝ)) + 1) * Real.log (2 * (40 * m : ℝ))) := by
      field_simp
      ring
    rw [e] at h4
    exact h4
  have hlen' : 24 * δ * (40 * m) * L.length ≤ 24 * δ * (40 * m) * 2432 :=
    mul_le_mul_of_nonneg_left hlenR (by positivity)
  have hTm : (40 * m : ℝ) * (L.map fun c => ((10 - c.sig : ℤ) : ℝ) *
        (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))).sum ≤ (40 * m) * (897 / 100 - 12 / 81) :=
    mul_le_mul_of_nonneg_left (by linarith) hm0
  have hδε : 24 * δ * (40 * m) * 2432 + 12 * δ * (40 * m) / 81 ≤ ε / 4 * (40 * m) := by
    rw [hδ]
    have : (24 * (ε / 240000) * 2432 + 12 * (ε / 240000) / 81) ≤ ε / 4 := by
      have : 0 < ε := hε
      nlinarith
    nlinarith
  nlinarith

/-! ### Certificate data -/
def certs0 : List CC := [
  ⟨1, 1, 20, 17, 0, [12, 0, 11, 10, 9, 8, 7, 1, 2, 3, 4, 5, 6]⟩,
  ⟨20, 17, 30, 23, -1, [6, 0, 12, 11, 10, 9, 8, 7, 1, 2, 3, 4, 5]⟩,
  ⟨30, 23, 4, 3, -1, [5, 6, 0, 11, 12, 10, 9, 8, 7, 1, 2, 3, 4]⟩,
  ⟨4, 3, 40, 29, -1, [4, 5, 6, 0, 11, 10, 12, 9, 8, 7, 1, 2, 3]⟩,
  ⟨40, 29, 60, 43, 0, [4, 6, 5, 11, 0, 10, 12, 9, 8, 7, 1, 2, 3]⟩,
  ⟨60, 43, 10, 7, 0, [3, 4, 6, 5, 11, 0, 10, 9, 12, 8, 7, 1, 2]⟩,
  ⟨10, 7, 60, 41, 0, [2, 3, 6, 4, 5, 11, 10, 0, 9, 8, 12, 7, 1]⟩,
  ⟨60, 41, 20, 13, 0, [1, 2, 3, 6, 4, 5, 11, 10, 0, 9, 8, 7, 12]⟩,
  ⟨20, 13, 80, 51, 1, [1, 2, 6, 3, 4, 11, 5, 10, 9, 0, 8, 7, 12]⟩,
  ⟨80, 51, 8, 5, 2, [1, 2, 6, 3, 11, 4, 10, 5, 9, 0, 8, 7, 12]⟩,
  ⟨8, 5, 80, 49, 2, [1, 6, 2, 3, 11, 10, 4, 5, 9, 8, 0, 7, 12]⟩,
  ⟨80, 49, 5, 3, 3, [1, 6, 2, 11, 3, 10, 4, 9, 5, 8, 0, 7, 12]⟩,
  ⟨5, 3, 80, 47, 4, [6, 1, 11, 2, 10, 3, 9, 4, 8, 5, 7, 0, 12]⟩,
  ⟨80, 47, 40, 23, 4, [6, 11, 1, 10, 2, 3, 9, 8, 4, 7, 5, 0, 12]⟩,
  ⟨40, 23, 16, 9, 4, [11, 6, 10, 1, 2, 9, 3, 8, 7, 4, 0, 5, 12]⟩,
  ⟨16, 9, 20, 11, 4, [11, 6, 10, 1, 9, 2, 8, 3, 7, 4, 0, 5, 12]⟩,
  ⟨20, 11, 80, 43, 4, [11, 10, 6, 9, 1, 8, 2, 7, 3, 0, 4, 5, 12]⟩,
  ⟨80, 43, 40, 21, 4, [11, 10, 6, 9, 8, 1, 7, 2, 3, 0, 4, 5, 12]⟩,
  ⟨40, 21, 2, 1, 4, [11, 10, 6, 9, 8, 7, 1, 2, 3, 0, 4, 5, 12]⟩,
  ⟨2, 1, 40, 19, -2, [12, 11, 10, 9, 6, 8, 7, 1, 2, 0, 3, 4, 5]⟩,
  ⟨40, 19, 50, 23, -2, [12, 11, 10, 9, 8, 6, 7, 1, 0, 2, 3, 4, 5]⟩,
  ⟨50, 23, 20, 9, -2, [5, 11, 12, 10, 9, 8, 6, 7, 1, 0, 2, 3, 4]⟩,
  ⟨20, 9, 30, 13, -2, [4, 5, 11, 10, 12, 9, 8, 7, 6, 0, 1, 2, 3]⟩,
  ⟨30, 13, 100, 43, -1, [4, 11, 5, 10, 12, 9, 8, 7, 6, 0, 1, 2, 3]⟩,
  ⟨100, 43, 40, 17, -1, [3, 4, 11, 5, 10, 9, 12, 8, 7, 6, 0, 1, 2]⟩,
  ⟨40, 17, 50, 21, 0, [3, 11, 4, 10, 5, 9, 12, 8, 7, 6, 0, 1, 2]⟩,
  ⟨50, 21, 12, 5, 0, [2, 3, 11, 4, 10, 5, 9, 8, 12, 7, 6, 0, 1]⟩,
  ⟨12, 5, 100, 41, 0, [2, 3, 11, 10, 4, 5, 9, 8, 12, 7, 6, 0, 1]⟩,
  ⟨100, 41, 120, 49, 0, [1, 2, 3, 11, 10, 4, 5, 9, 8, 7, 12, 6, 0]⟩,
  ⟨120, 49, 5, 2, 1, [1, 2, 11, 3, 10, 4, 9, 5, 8, 7, 12, 6, 0]⟩,
  ⟨5, 2, 120, 47, 2, [1, 11, 2, 10, 3, 9, 4, 8, 5, 7, 12, 6, 0]⟩,
  ⟨120, 47, 60, 23, 2, [11, 1, 10, 2, 3, 9, 8, 4, 7, 5, 12, 6, 0]⟩,
  ⟨60, 23, 8, 3, 3, [0, 11, 10, 1, 2, 9, 3, 8, 7, 4, 5, 6, 12]⟩,
  ⟨8, 3, 30, 11, 3, [0, 11, 10, 1, 9, 2, 8, 3, 7, 4, 5, 6, 12]⟩,
  ⟨30, 11, 80, 29, 3, [0, 11, 10, 9, 1, 8, 2, 7, 3, 4, 5, 6, 12]⟩,
  ⟨80, 29, 120, 43, 4, [11, 0, 10, 9, 1, 8, 2, 7, 3, 4, 6, 5, 12]⟩,
  ⟨120, 43, 20, 7, 4, [11, 0, 10, 9, 8, 1, 7, 2, 3, 4, 6, 5, 12]⟩,
  ⟨20, 7, 3, 1, 4, [11, 10, 0, 9, 8, 7, 1, 2, 3, 6, 4, 5, 12]⟩,
  ⟨3, 1, 70, 23, -2, [12, 11, 10, 0, 9, 8, 7, 1, 2, 3, 6, 4, 5]⟩,
  ⟨70, 23, 40, 13, -2, [5, 11, 12, 10, 0, 9, 8, 7, 1, 2, 3, 6, 4]⟩,
  ⟨40, 13, 28, 9, -1, [11, 5, 12, 10, 9, 0, 8, 7, 1, 2, 6, 3, 4]⟩,
  ⟨28, 9, 160, 51, -1, [4, 11, 5, 10, 12, 9, 0, 8, 7, 1, 2, 6, 3]⟩,
  ⟨160, 51, 16, 5, 0, [11, 4, 10, 5, 12, 9, 0, 8, 7, 1, 2, 6, 3]⟩,
  ⟨16, 5, 140, 43, 0, [11, 10, 4, 5, 12, 9, 8, 0, 7, 1, 6, 2, 3]⟩,
  ⟨140, 43, 160, 49, 0, [3, 11, 10, 4, 5, 9, 12, 8, 0, 7, 1, 6, 2]⟩,
  ⟨160, 49, 10, 3, 1, [11, 3, 10, 4, 9, 5, 12, 8, 0, 7, 1, 6, 2]⟩,
  ⟨10, 3, 160, 47, 2, [2, 10, 3, 9, 4, 8, 12, 5, 7, 0, 6, 1, 11]⟩,
  ⟨160, 47, 140, 41, 2, [10, 2, 3, 9, 8, 4, 12, 7, 5, 0, 6, 11, 1]⟩,
  ⟨140, 41, 80, 23, 2, [1, 10, 2, 3, 9, 8, 4, 7, 12, 5, 0, 6, 11]⟩,
  ⟨80, 23, 60, 17, 3, [10, 1, 2, 9, 3, 8, 7, 4, 12, 0, 5, 11, 6]⟩,
  ⟨60, 17, 32, 9, 3, [6, 10, 1, 2, 9, 3, 8, 7, 4, 0, 12, 5, 11]⟩,
  ⟨32, 9, 40, 11, 3, [6, 10, 1, 9, 2, 8, 3, 7, 4, 0, 12, 5, 11]⟩,
  ⟨40, 11, 160, 43, 3, [10, 6, 9, 1, 8, 2, 7, 3, 0, 4, 12, 5, 11]⟩,
  ⟨160, 43, 80, 21, 3, [10, 6, 9, 8, 1, 7, 2, 3, 0, 4, 12, 5, 11]⟩,
  ⟨80, 21, 50, 13, 3, [10, 6, 9, 8, 7, 1, 2, 3, 0, 4, 12, 5, 11]⟩,
  ⟨50, 13, 90, 23, 3, [10, 6, 9, 8, 7, 1, 2, 3, 0, 4, 12, 11, 5]⟩,
  ⟨90, 23, 200, 51, 3, [5, 10, 6, 9, 8, 7, 1, 2, 3, 0, 4, 11, 12]⟩,
  ⟨200, 51, 4, 1, 4, [10, 5, 6, 9, 8, 7, 1, 2, 3, 0, 11, 4, 12]⟩,
  ⟨4, 1, 200, 49, 0, [12, 4, 5, 9, 6, 8, 7, 1, 2, 0, 3, 11, 10]⟩,
  ⟨200, 49, 120, 29, 0, [12, 4, 9, 5, 6, 8, 7, 1, 2, 0, 11, 3, 10]⟩,
  ⟨120, 29, 25, 6, 0, [12, 4, 9, 6, 5, 8, 7, 1, 2, 11, 0, 3, 10]⟩,
  ⟨25, 6, 180, 43, 0, [12, 9, 4, 6, 8, 5, 7, 1, 11, 2, 0, 10, 3]⟩,
  ⟨180, 43, 80, 19, 0, [3, 9, 12, 4, 6, 8, 5, 7, 1, 11, 2, 0, 10]⟩,
  ⟨80, 19, 200, 47, 0, [3, 9, 12, 4, 8, 6, 5, 7, 1, 11, 0, 2, 10]⟩,
  ⟨200, 47, 30, 7, 0, [3, 9, 12, 8, 4, 6, 7, 5, 11, 1, 0, 10, 2]⟩,
  ⟨30, 7, 100, 23, 0, [2, 3, 9, 8, 12, 6, 4, 7, 5, 11, 1, 10, 0]⟩,
  ⟨100, 23, 180, 41, 1, [0, 2, 9, 3, 8, 6, 12, 7, 4, 5, 11, 10, 1]⟩,
  ⟨180, 41, 40, 9, 1, [1, 0, 2, 9, 3, 8, 6, 7, 12, 4, 5, 11, 10]⟩,
  ⟨40, 9, 50, 11, 2, [0, 1, 9, 2, 8, 3, 7, 6, 12, 4, 5, 11, 10]⟩,
  ⟨50, 11, 60, 13, 3, [0, 9, 1, 8, 2, 7, 3, 6, 12, 4, 5, 11, 10]⟩,
  ⟨60, 13, 200, 43, 3, [9, 0, 1, 8, 2, 7, 6, 3, 12, 4, 11, 5, 10]⟩,
  ⟨200, 43, 80, 17, 4, [9, 0, 8, 1, 7, 2, 6, 3, 12, 4, 11, 5, 10]⟩,
  ⟨80, 17, 100, 21, 4, [9, 0, 8, 1, 7, 2, 6, 3, 12, 11, 4, 10, 5]⟩,
  ⟨100, 21, 110, 23, 4, [9, 0, 8, 7, 1, 2, 6, 3, 12, 11, 4, 10, 5]⟩,
  ⟨110, 23, 24, 5, 4, [5, 9, 0, 8, 7, 1, 2, 6, 3, 11, 12, 4, 10]⟩,
  ⟨24, 5, 44, 9, 4, [5, 9, 8, 0, 7, 1, 6, 2, 3, 11, 12, 10, 4]⟩,
  ⟨44, 9, 240, 49, 4, [4, 5, 9, 8, 0, 7, 1, 6, 2, 3, 11, 10, 12]⟩,
  ⟨240, 49, 5, 1, 5, [4, 9, 5, 8, 0, 7, 1, 6, 2, 11, 3, 10, 12]⟩,
  ⟨5, 1, 240, 47, 0, [12, 9, 4, 8, 5, 7, 0, 6, 1, 11, 2, 10, 3]⟩,
  ⟨240, 47, 220, 43, 0, [12, 9, 8, 4, 7, 5, 0, 6, 11, 1, 10, 2, 3]⟩]

def certs1 : List CC := [
  ⟨220, 43, 120, 23, 0, [3, 9, 12, 8, 4, 7, 5, 0, 6, 11, 1, 10, 2]⟩,
  ⟨120, 23, 110, 21, 1, [9, 3, 12, 8, 7, 4, 0, 5, 11, 6, 10, 1, 2]⟩,
  ⟨110, 21, 16, 3, 1, [2, 9, 3, 8, 12, 7, 4, 0, 5, 11, 6, 10, 1]⟩,
  ⟨16, 3, 220, 41, 2, [9, 2, 8, 3, 12, 7, 4, 0, 5, 11, 6, 10, 1]⟩,
  ⟨220, 41, 70, 13, 2, [1, 9, 2, 8, 3, 7, 12, 4, 0, 5, 11, 6, 10]⟩,
  ⟨70, 13, 60, 11, 2, [1, 9, 2, 8, 3, 7, 12, 4, 0, 11, 5, 6, 10]⟩,
  ⟨60, 11, 280, 51, 3, [9, 1, 8, 2, 7, 3, 12, 0, 4, 11, 5, 10, 6]⟩,
  ⟨280, 51, 160, 29, 3, [9, 1, 8, 2, 7, 3, 12, 0, 11, 4, 10, 5, 6]⟩,
  ⟨160, 29, 240, 43, 3, [9, 1, 8, 2, 7, 3, 12, 11, 0, 4, 10, 6, 5]⟩,
  ⟨240, 43, 28, 5, 3, [9, 8, 1, 7, 2, 3, 12, 11, 0, 4, 10, 6, 5]⟩,
  ⟨28, 5, 130, 23, 3, [9, 8, 1, 7, 2, 3, 12, 11, 0, 10, 4, 6, 5]⟩,
  ⟨130, 23, 40, 7, 3, [5, 9, 8, 1, 7, 2, 3, 11, 12, 0, 10, 4, 6]⟩,
  ⟨40, 7, 52, 9, 4, [9, 5, 8, 7, 1, 2, 11, 3, 12, 10, 0, 6, 4]⟩,
  ⟨52, 9, 35, 6, 4, [4, 9, 5, 8, 7, 1, 2, 11, 3, 10, 12, 0, 6]⟩,
  ⟨35, 6, 100, 17, 5, [9, 4, 8, 5, 7, 1, 11, 2, 10, 3, 12, 0, 6]⟩,
  ⟨100, 17, 280, 47, 4, [6, 9, 4, 8, 5, 7, 1, 11, 2, 10, 3, 0, 12]⟩,
  ⟨280, 47, 6, 1, 4, [6, 9, 8, 4, 7, 5, 11, 1, 10, 2, 3, 0, 12]⟩,
  ⟨6, 1, 260, 43, -2, [12, 9, 6, 8, 4, 7, 5, 11, 1, 10, 2, 0, 3]⟩,
  ⟨260, 43, 140, 23, -2, [3, 9, 12, 6, 8, 4, 7, 5, 11, 1, 10, 2, 0]⟩,
  ⟨140, 23, 80, 13, -1, [0, 9, 3, 6, 12, 8, 7, 4, 5, 11, 10, 1, 2]⟩,
  ⟨80, 13, 130, 21, 0, [9, 0, 6, 3, 12, 8, 7, 4, 11, 5, 10, 1, 2]⟩,
  ⟨130, 21, 56, 9, 0, [2, 9, 0, 6, 3, 8, 12, 7, 4, 11, 5, 10, 1]⟩,
  ⟨56, 9, 320, 51, 0, [9, 2, 0, 6, 8, 3, 12, 7, 4, 11, 5, 10, 1]⟩,
  ⟨320, 51, 120, 19, 0, [9, 2, 0, 6, 8, 3, 12, 7, 11, 4, 10, 5, 1]⟩,
  ⟨120, 19, 260, 41, 0, [9, 0, 2, 8, 6, 3, 12, 7, 11, 4, 10, 5, 1]⟩,
  ⟨260, 41, 70, 11, 0, [1, 9, 0, 2, 8, 6, 3, 7, 12, 11, 4, 10, 5]⟩,
  ⟨70, 11, 32, 5, 1, [9, 1, 0, 8, 2, 6, 7, 3, 12, 11, 4, 10, 5]⟩,
  ⟨32, 5, 280, 43, 2, [9, 1, 8, 0, 6, 2, 7, 3, 12, 11, 10, 4, 5]⟩,
  ⟨280, 43, 150, 23, 2, [9, 8, 1, 0, 6, 7, 2, 3, 12, 11, 10, 4, 5]⟩,
  ⟨150, 23, 320, 49, 2, [5, 9, 8, 1, 0, 6, 7, 2, 3, 11, 12, 10, 4]⟩,
  ⟨320, 49, 20, 3, 2, [9, 5, 8, 1, 0, 6, 7, 2, 11, 3, 12, 10, 4]⟩,
  ⟨20, 3, 320, 47, 4, [4, 8, 5, 7, 6, 0, 1, 11, 2, 10, 12, 3, 9]⟩,
  ⟨320, 47, 200, 29, 5, [8, 4, 7, 5, 6, 0, 11, 1, 10, 2, 12, 3, 9]⟩,
  ⟨200, 29, 90, 13, 5, [8, 4, 7, 6, 5, 11, 0, 1, 10, 2, 12, 3, 9]⟩,
  ⟨90, 13, 160, 23, 5, [8, 4, 7, 6, 11, 5, 0, 1, 10, 2, 12, 3, 9]⟩,
  ⟨160, 23, 300, 43, 5, [8, 7, 4, 11, 6, 0, 5, 10, 1, 2, 12, 9, 3]⟩,
  ⟨300, 43, 7, 1, 5, [3, 8, 7, 4, 11, 6, 0, 5, 10, 1, 2, 9, 12]⟩,
  ⟨7, 1, 120, 17, 0, [12, 3, 8, 7, 4, 11, 6, 0, 5, 10, 1, 2, 9]⟩,
  ⟨120, 17, 64, 9, 0, [12, 3, 8, 7, 11, 4, 6, 0, 10, 5, 1, 2, 9]⟩,
  ⟨64, 9, 50, 7, 0, [12, 8, 3, 7, 11, 4, 6, 0, 10, 5, 1, 9, 2]⟩,
  ⟨50, 7, 36, 5, 0, [2, 8, 12, 3, 7, 11, 6, 4, 10, 0, 5, 1, 9]⟩,
  ⟨36, 5, 80, 11, 0, [2, 8, 12, 3, 7, 11, 6, 10, 4, 0, 5, 1, 9]⟩,
  ⟨80, 11, 300, 41, 1, [8, 2, 12, 7, 3, 11, 10, 6, 0, 4, 5, 9, 1]⟩,
  ⟨300, 41, 360, 49, 1, [1, 8, 2, 7, 12, 3, 11, 10, 6, 0, 4, 5, 9]⟩,
  ⟨360, 49, 170, 23, 1, [1, 8, 2, 7, 12, 11, 3, 10, 6, 0, 4, 9, 5]⟩,
  ⟨170, 23, 320, 43, 1, [5, 1, 8, 2, 7, 11, 12, 3, 10, 6, 0, 4, 9]⟩,
  ⟨320, 43, 15, 2, 2, [5, 8, 1, 7, 2, 11, 12, 3, 10, 6, 0, 4, 9]⟩,
  ⟨15, 2, 68, 9, 2, [8, 5, 1, 7, 11, 2, 12, 10, 3, 6, 0, 9, 4]⟩,
  ⟨68, 9, 160, 21, 2, [4, 8, 5, 1, 7, 11, 2, 10, 12, 3, 6, 0, 9]⟩,
  ⟨160, 21, 360, 47, 3, [4, 8, 5, 7, 1, 11, 2, 10, 12, 3, 6, 0, 9]⟩,
  ⟨360, 47, 100, 13, 4, [8, 4, 7, 5, 11, 1, 10, 2, 12, 3, 6, 0, 9]⟩,
  ⟨100, 13, 180, 23, 4, [8, 4, 7, 11, 5, 1, 10, 2, 12, 6, 3, 9, 0]⟩,
  ⟨180, 23, 400, 51, 4, [0, 8, 7, 4, 11, 5, 10, 1, 2, 6, 12, 9, 3]⟩,
  ⟨400, 51, 340, 43, 4, [0, 8, 7, 11, 4, 10, 5, 1, 2, 6, 12, 9, 3]⟩,
  ⟨340, 43, 8, 1, 4, [3, 0, 8, 7, 11, 4, 10, 5, 1, 2, 6, 9, 12]⟩,
  ⟨8, 1, 170, 21, 0, [12, 8, 0, 3, 11, 7, 10, 4, 1, 5, 9, 6, 2]⟩,
  ⟨170, 21, 400, 49, 0, [2, 8, 12, 0, 3, 11, 7, 10, 4, 1, 5, 9, 6]⟩,
  ⟨400, 49, 90, 11, 0, [2, 8, 12, 0, 11, 3, 7, 10, 4, 1, 9, 5, 6]⟩,
  ⟨90, 11, 140, 17, 1, [8, 2, 12, 0, 11, 7, 3, 10, 4, 9, 1, 5, 6]⟩,
  ⟨140, 17, 190, 23, 0, [6, 8, 2, 0, 12, 11, 7, 3, 10, 4, 9, 1, 5]⟩,
  ⟨190, 23, 240, 29, 0, [5, 6, 8, 2, 0, 11, 12, 7, 3, 10, 4, 9, 1]⟩,
  ⟨240, 29, 340, 41, 1, [6, 5, 8, 2, 11, 0, 12, 7, 3, 10, 4, 9, 1]⟩,
  ⟨340, 41, 25, 3, 1, [1, 6, 5, 8, 2, 11, 0, 7, 12, 3, 10, 4, 9]⟩,
  ⟨25, 3, 360, 43, 2, [6, 1, 8, 5, 11, 2, 7, 0, 12, 10, 3, 9, 4]⟩,
  ⟨360, 43, 160, 19, 2, [6, 8, 1, 5, 11, 7, 2, 0, 12, 10, 3, 9, 4]⟩,
  ⟨160, 19, 76, 9, 2, [8, 6, 1, 5, 11, 7, 0, 2, 12, 10, 3, 9, 4]⟩,
  ⟨76, 9, 110, 13, 2, [4, 8, 6, 1, 5, 11, 7, 0, 2, 10, 12, 3, 9]⟩,
  ⟨110, 13, 400, 47, 2, [4, 8, 6, 1, 11, 5, 7, 0, 2, 10, 12, 3, 9]⟩,
  ⟨400, 47, 60, 7, 3, [8, 4, 6, 11, 1, 7, 5, 0, 10, 2, 12, 3, 9]⟩,
  ⟨60, 7, 440, 51, 3, [8, 6, 4, 11, 7, 1, 5, 10, 0, 2, 12, 3, 9]⟩,
  ⟨440, 51, 200, 23, 3, [8, 6, 11, 4, 7, 1, 10, 5, 0, 2, 12, 3, 9]⟩,
  ⟨200, 23, 44, 5, 3, [8, 11, 6, 7, 4, 10, 1, 0, 5, 2, 12, 9, 3]⟩,
  ⟨44, 5, 380, 43, 3, [8, 11, 6, 7, 10, 4, 1, 0, 5, 2, 12, 9, 3]⟩,
  ⟨380, 43, 80, 9, 3, [3, 8, 11, 6, 7, 10, 4, 1, 0, 5, 2, 9, 12]⟩,
  ⟨80, 9, 440, 49, 4, [8, 3, 11, 7, 6, 10, 4, 0, 1, 5, 9, 2, 12]⟩,
  ⟨440, 49, 9, 1, 4, [8, 11, 3, 7, 6, 10, 4, 0, 1, 9, 5, 2, 12]⟩,
  ⟨9, 1, 190, 21, -2, [12, 8, 11, 3, 7, 6, 10, 4, 0, 1, 9, 5, 2]⟩,
  ⟨190, 21, 100, 11, -2, [2, 8, 12, 11, 3, 7, 6, 10, 4, 0, 1, 9, 5]⟩,
  ⟨100, 11, 210, 23, -1, [8, 2, 12, 11, 7, 3, 10, 6, 0, 4, 9, 1, 5]⟩,
  ⟨210, 23, 55, 6, -1, [5, 8, 2, 11, 12, 7, 3, 10, 6, 0, 4, 9, 1]⟩]

def certs2 : List CC := [
  ⟨55, 6, 120, 13, 0, [8, 5, 11, 2, 12, 7, 10, 3, 6, 0, 9, 4, 1]⟩,
  ⟨120, 13, 380, 41, 0, [8, 11, 5, 2, 12, 7, 10, 6, 3, 9, 0, 4, 1]⟩,
  ⟨380, 41, 400, 43, 0, [1, 8, 11, 5, 2, 7, 12, 10, 6, 3, 9, 0, 4]⟩,
  ⟨400, 43, 28, 3, 1, [8, 1, 11, 5, 7, 2, 12, 10, 6, 3, 9, 0, 4]⟩,
  ⟨28, 3, 440, 47, 1, [4, 8, 1, 11, 5, 7, 2, 10, 12, 6, 3, 9, 0]⟩,
  ⟨440, 47, 160, 17, 2, [8, 4, 11, 1, 7, 5, 10, 2, 12, 6, 3, 9, 0]⟩,
  ⟨160, 17, 200, 21, 2, [8, 11, 4, 1, 7, 10, 5, 2, 12, 6, 3, 9, 0]⟩,
  ⟨200, 21, 220, 23, 2, [8, 11, 4, 7, 1, 10, 5, 2, 12, 6, 3, 9, 0]⟩,
  ⟨220, 23, 48, 5, 2, [0, 8, 11, 7, 4, 10, 1, 5, 2, 6, 12, 9, 3]⟩,
  ⟨48, 5, 280, 29, 3, [8, 0, 11, 7, 10, 4, 1, 5, 6, 2, 12, 9, 3]⟩,
  ⟨280, 29, 420, 43, 3, [8, 11, 0, 7, 10, 4, 1, 6, 5, 2, 12, 9, 3]⟩,
  ⟨420, 43, 88, 9, 3, [3, 8, 11, 0, 7, 10, 4, 1, 6, 5, 2, 9, 12]⟩,
  ⟨88, 9, 480, 49, 4, [8, 3, 11, 0, 7, 10, 4, 1, 6, 5, 9, 2, 12]⟩,
  ⟨480, 49, 10, 1, 4, [8, 11, 3, 0, 7, 10, 4, 1, 6, 9, 5, 2, 12]⟩,
  ⟨10, 1, 520, 51, 2, [12, 2, 5, 10, 7, 0, 3, 9, 6, 1, 4, 11, 8]⟩,
  ⟨520, 51, 480, 47, 2, [12, 2, 10, 5, 7, 0, 3, 9, 6, 1, 11, 4, 8]⟩,
  ⟨480, 47, 92, 9, 2, [12, 10, 2, 7, 5, 0, 3, 9, 6, 11, 1, 8, 4]⟩,
  ⟨92, 9, 440, 43, 2, [4, 10, 12, 2, 7, 5, 0, 3, 9, 6, 11, 1, 8]⟩,
  ⟨440, 43, 420, 41, 2, [4, 10, 12, 7, 2, 5, 0, 3, 9, 6, 11, 8, 1]⟩,
  ⟨420, 41, 52, 5, 2, [1, 4, 10, 7, 12, 2, 5, 0, 3, 9, 6, 11, 8]⟩,
  ⟨52, 5, 240, 23, 3, [1, 10, 4, 7, 12, 2, 5, 0, 3, 9, 6, 11, 8]⟩,
  ⟨240, 23, 220, 21, 4, [10, 1, 7, 4, 12, 2, 0, 5, 9, 3, 11, 6, 8]⟩,
  ⟨220, 21, 200, 19, 4, [10, 7, 1, 4, 12, 2, 0, 5, 9, 3, 11, 6, 8]⟩,
  ⟨200, 19, 180, 17, 4, [10, 7, 1, 4, 12, 0, 2, 5, 9, 3, 11, 8, 6]⟩,
  ⟨180, 17, 520, 49, 3, [6, 10, 7, 1, 4, 0, 12, 2, 5, 9, 3, 11, 8]⟩,
  ⟨520, 49, 32, 3, 3, [6, 10, 7, 1, 4, 0, 12, 2, 9, 5, 11, 3, 8]⟩,
  ⟨32, 3, 460, 43, 3, [6, 10, 7, 1, 4, 0, 12, 9, 2, 5, 11, 8, 3]⟩,
  ⟨460, 43, 140, 13, 3, [3, 6, 10, 7, 1, 4, 0, 9, 12, 2, 5, 11, 8]⟩,
  ⟨140, 13, 65, 6, 4, [6, 3, 10, 7, 1, 4, 9, 0, 12, 2, 11, 5, 8]⟩,
  ⟨65, 6, 250, 23, 4, [6, 10, 3, 7, 1, 9, 4, 0, 12, 11, 2, 8, 5]⟩,
  ⟨250, 23, 120, 11, 4, [5, 6, 10, 3, 7, 1, 9, 4, 0, 11, 12, 2, 8]⟩,
  ⟨120, 11, 230, 21, 4, [5, 10, 6, 7, 3, 9, 1, 0, 4, 11, 12, 8, 2]⟩,
  ⟨230, 21, 560, 51, 4, [2, 5, 10, 6, 7, 3, 9, 1, 0, 4, 11, 8, 12]⟩,
  ⟨560, 51, 11, 1, 5, [2, 10, 5, 6, 7, 3, 9, 1, 0, 11, 4, 8, 12]⟩,
  ⟨11, 1, 320, 29, 0, [12, 2, 10, 5, 6, 7, 3, 9, 1, 0, 11, 4, 8]⟩,
  ⟨320, 29, 520, 47, 0, [12, 2, 10, 6, 5, 7, 3, 9, 1, 11, 0, 4, 8]⟩,
  ⟨520, 47, 100, 9, 0, [12, 10, 2, 6, 7, 5, 3, 9, 11, 1, 0, 8, 4]⟩,
  ⟨100, 9, 480, 43, 0, [4, 10, 12, 2, 7, 6, 5, 3, 9, 11, 0, 1, 8]⟩,
  ⟨480, 43, 56, 5, 0, [4, 10, 12, 7, 2, 6, 5, 3, 9, 11, 0, 8, 1]⟩,
  ⟨56, 5, 460, 41, 1, [10, 4, 12, 7, 6, 2, 5, 3, 9, 11, 8, 0, 1]⟩,
  ⟨460, 41, 260, 23, 1, [1, 10, 4, 7, 12, 6, 2, 5, 3, 9, 11, 8, 0]⟩,
  ⟨260, 23, 80, 7, 2, [0, 10, 1, 7, 4, 6, 12, 2, 5, 9, 3, 11, 8]⟩,
  ⟨80, 7, 150, 13, 3, [10, 0, 7, 1, 6, 4, 12, 2, 9, 5, 11, 3, 8]⟩,
  ⟨150, 13, 104, 9, 3, [10, 0, 7, 1, 6, 4, 12, 2, 9, 11, 5, 3, 8]⟩,
  ⟨104, 9, 500, 43, 3, [10, 0, 7, 1, 6, 4, 12, 9, 2, 11, 5, 8, 3]⟩,
  ⟨500, 43, 35, 3, 3, [3, 10, 0, 7, 1, 6, 4, 9, 12, 2, 11, 5, 8]⟩,
  ⟨35, 3, 270, 23, 4, [10, 3, 7, 0, 6, 1, 9, 4, 12, 11, 2, 8, 5]⟩,
  ⟨270, 23, 200, 17, 4, [5, 10, 3, 7, 0, 6, 1, 9, 4, 11, 12, 2, 8]⟩,
  ⟨200, 17, 130, 11, 4, [10, 5, 3, 7, 0, 6, 1, 9, 11, 4, 12, 2, 8]⟩,
  ⟨130, 11, 250, 21, 4, [10, 5, 7, 3, 0, 6, 9, 1, 11, 4, 12, 8, 2]⟩,
  ⟨250, 21, 560, 47, 4, [2, 10, 5, 7, 3, 0, 6, 9, 1, 11, 4, 8, 12]⟩,
  ⟨560, 47, 12, 1, 4, [10, 2, 7, 5, 3, 0, 6, 9, 11, 1, 8, 4, 12]⟩,
  ⟨12, 1, 520, 43, 2, [12, 4, 2, 7, 5, 0, 3, 9, 6, 11, 1, 8, 10]⟩,
  ⟨520, 43, 280, 23, 2, [12, 4, 7, 2, 5, 0, 3, 9, 6, 11, 8, 1, 10]⟩,
  ⟨280, 23, 500, 41, 2, [12, 7, 4, 2, 0, 5, 9, 3, 11, 6, 8, 10, 1]⟩,
  ⟨500, 41, 600, 49, 2, [1, 7, 12, 4, 2, 0, 5, 9, 3, 11, 6, 8, 10]⟩,
  ⟨600, 49, 160, 13, 2, [1, 7, 12, 4, 2, 0, 9, 5, 11, 3, 6, 8, 10]⟩,
  ⟨160, 13, 260, 21, 2, [1, 7, 12, 4, 2, 9, 0, 11, 5, 6, 3, 8, 10]⟩,
  ⟨260, 21, 360, 29, 3, [7, 1, 12, 4, 2, 9, 0, 11, 5, 6, 3, 8, 10]⟩,
  ⟨360, 29, 112, 9, 3, [7, 1, 12, 4, 2, 9, 11, 0, 6, 5, 3, 8, 10]⟩,
  ⟨112, 9, 25, 2, 3, [7, 1, 12, 4, 9, 2, 11, 0, 6, 5, 8, 3, 10]⟩,
  ⟨25, 2, 640, 51, 3, [7, 1, 12, 9, 4, 11, 2, 0, 6, 8, 5, 10, 3]⟩,
  ⟨640, 51, 540, 43, 3, [7, 1, 12, 9, 11, 4, 2, 0, 6, 8, 10, 5, 3]⟩,
  ⟨540, 43, 290, 23, 3, [3, 7, 1, 9, 12, 11, 4, 2, 0, 6, 8, 10, 5]⟩,
  ⟨290, 23, 240, 19, 3, [5, 3, 7, 1, 9, 11, 12, 4, 2, 0, 6, 8, 10]⟩,
  ⟨240, 19, 140, 11, 3, [5, 3, 7, 1, 9, 11, 12, 4, 0, 2, 8, 6, 10]⟩,
  ⟨140, 11, 600, 47, 4, [5, 7, 3, 9, 1, 11, 12, 0, 4, 8, 2, 10, 6]⟩,
  ⟨600, 47, 64, 5, 4, [7, 5, 3, 9, 11, 1, 12, 0, 8, 4, 10, 2, 6]⟩,
  ⟨64, 5, 90, 7, 4, [7, 5, 3, 9, 11, 1, 12, 8, 0, 10, 4, 6, 2]⟩,
  ⟨90, 7, 116, 9, 4, [2, 7, 5, 3, 9, 11, 1, 8, 12, 10, 0, 6, 4]⟩,
  ⟨116, 9, 220, 17, 4, [4, 2, 7, 5, 3, 9, 11, 1, 8, 10, 12, 0, 6]⟩,
  ⟨220, 17, 13, 1, 4, [6, 4, 2, 7, 5, 3, 9, 11, 1, 8, 10, 0, 12]⟩,
  ⟨13, 1, 560, 43, 0, [12, 6, 4, 2, 7, 5, 3, 9, 11, 1, 8, 10, 0]⟩,
  ⟨560, 43, 300, 23, 0, [12, 6, 4, 7, 2, 5, 3, 9, 11, 8, 1, 10, 0]⟩,
  ⟨300, 23, 640, 49, 0, [0, 6, 12, 7, 4, 2, 5, 9, 3, 11, 8, 10, 1]⟩,
  ⟨640, 49, 170, 13, 0, [0, 6, 12, 7, 4, 2, 9, 5, 11, 3, 8, 10, 1]⟩,
  ⟨170, 13, 540, 41, 0, [0, 6, 12, 7, 4, 2, 9, 11, 5, 3, 8, 10, 1]⟩,
  ⟨540, 41, 40, 3, 0, [1, 0, 6, 7, 12, 4, 2, 9, 11, 5, 3, 8, 10]⟩,
  ⟨40, 3, 310, 23, 2, [7, 6, 0, 1, 12, 11, 9, 2, 4, 10, 8, 3, 5]⟩,
  ⟨310, 23, 580, 43, 2, [5, 7, 6, 0, 1, 11, 12, 9, 2, 4, 10, 8, 3]⟩]

def certs3 : List CC := [
  ⟨580, 43, 68, 5, 2, [3, 5, 7, 6, 0, 1, 11, 9, 12, 2, 4, 10, 8]⟩,
  ⟨68, 5, 640, 47, 2, [3, 5, 7, 6, 0, 1, 11, 9, 12, 2, 10, 4, 8]⟩,
  ⟨640, 47, 150, 11, 3, [3, 7, 5, 6, 0, 11, 1, 9, 12, 10, 2, 8, 4]⟩,
  ⟨150, 11, 124, 9, 3, [7, 3, 5, 6, 0, 11, 9, 1, 12, 10, 8, 2, 4]⟩,
  ⟨124, 9, 400, 29, 3, [4, 7, 3, 5, 6, 0, 11, 9, 1, 10, 12, 8, 2]⟩,
  ⟨400, 29, 290, 21, 4, [4, 7, 3, 6, 5, 11, 0, 9, 1, 10, 12, 8, 2]⟩,
  ⟨290, 21, 180, 13, 4, [2, 4, 7, 3, 6, 5, 11, 0, 9, 1, 10, 8, 12]⟩,
  ⟨180, 13, 680, 49, 4, [2, 4, 7, 6, 3, 11, 5, 9, 0, 1, 10, 8, 12]⟩,
  ⟨680, 49, 320, 23, 4, [2, 4, 7, 6, 11, 3, 9, 5, 0, 1, 10, 8, 12]⟩,
  ⟨320, 23, 600, 43, 5, [2, 7, 4, 11, 6, 9, 3, 0, 5, 10, 1, 8, 12]⟩,
  ⟨600, 43, 14, 1, 5, [7, 2, 4, 11, 6, 9, 3, 0, 5, 10, 8, 1, 12]⟩,
  ⟨14, 1, 240, 17, 0, [12, 7, 2, 4, 11, 9, 6, 0, 3, 5, 10, 8, 1]⟩,
  ⟨240, 17, 580, 41, 0, [12, 7, 2, 11, 4, 9, 6, 0, 3, 10, 5, 8, 1]⟩,
  ⟨580, 41, 85, 6, 0, [1, 7, 12, 2, 11, 4, 9, 6, 0, 3, 10, 5, 8]⟩,
  ⟨85, 6, 128, 9, 0, [1, 7, 12, 11, 2, 9, 4, 6, 0, 10, 3, 8, 5]⟩,
  ⟨128, 9, 100, 7, 0, [1, 7, 12, 11, 9, 2, 4, 6, 0, 10, 8, 3, 5]⟩,
  ⟨100, 7, 330, 23, 1, [7, 1, 12, 11, 9, 2, 6, 4, 10, 0, 8, 3, 5]⟩,
  ⟨330, 23, 72, 5, 1, [5, 7, 1, 11, 12, 9, 2, 6, 4, 10, 0, 8, 3]⟩,
  ⟨72, 5, 620, 43, 1, [5, 7, 1, 11, 12, 9, 6, 2, 10, 4, 8, 0, 3]⟩,
  ⟨620, 43, 680, 47, 1, [3, 5, 7, 1, 11, 9, 12, 6, 2, 10, 4, 8, 0]⟩,
  ⟨680, 47, 160, 11, 2, [3, 7, 5, 11, 1, 9, 12, 6, 10, 2, 8, 4, 0]⟩,
  ⟨160, 11, 190, 13, 2, [7, 3, 5, 11, 9, 1, 12, 10, 6, 8, 2, 0, 4]⟩,
  ⟨190, 13, 44, 3, 3, [7, 3, 11, 5, 9, 1, 12, 10, 6, 8, 2, 0, 4]⟩,
  ⟨44, 3, 720, 49, 3, [4, 7, 3, 11, 5, 9, 1, 10, 12, 6, 8, 2, 0]⟩,
  ⟨720, 49, 280, 19, 3, [4, 7, 11, 3, 9, 5, 1, 10, 12, 6, 8, 2, 0]⟩,
  ⟨280, 19, 310, 21, 3, [4, 7, 11, 3, 9, 5, 1, 10, 12, 8, 6, 0, 2]⟩,
  ⟨310, 21, 340, 23, 3, [2, 4, 7, 11, 3, 9, 5, 1, 10, 8, 12, 6, 0]⟩,
  ⟨340, 23, 640, 43, 4, [0, 2, 7, 4, 11, 9, 3, 5, 10, 1, 8, 6, 12]⟩,
  ⟨640, 43, 760, 51, 4, [0, 7, 2, 4, 11, 9, 3, 5, 10, 8, 1, 6, 12]⟩,
  ⟨760, 51, 15, 1, 5, [0, 7, 2, 11, 4, 9, 3, 10, 5, 8, 1, 6, 12]⟩,
  ⟨15, 1, 136, 9, 0, [12, 7, 0, 11, 2, 9, 4, 10, 3, 8, 5, 6, 1]⟩,
  ⟨136, 9, 620, 41, 0, [12, 7, 0, 11, 9, 2, 4, 10, 8, 3, 5, 6, 1]⟩,
  ⟨620, 41, 440, 29, 0, [1, 7, 12, 0, 11, 9, 2, 4, 10, 8, 3, 5, 6]⟩,
  ⟨440, 29, 76, 5, 0, [1, 7, 12, 11, 0, 9, 2, 4, 10, 8, 3, 6, 5]⟩,
  ⟨76, 5, 350, 23, 0, [1, 7, 12, 11, 0, 9, 2, 10, 4, 8, 3, 6, 5]⟩,
  ⟨350, 23, 320, 21, 0, [5, 1, 7, 11, 12, 0, 9, 2, 10, 4, 8, 3, 6]⟩,
  ⟨320, 21, 260, 17, 1, [5, 7, 1, 11, 12, 0, 9, 2, 10, 4, 8, 3, 6]⟩,
  ⟨260, 17, 720, 47, 1, [6, 5, 7, 1, 11, 0, 12, 9, 2, 10, 4, 8, 3]⟩,
  ⟨720, 47, 660, 43, 1, [6, 7, 5, 11, 1, 0, 12, 9, 10, 2, 8, 4, 3]⟩,
  ⟨660, 43, 200, 13, 1, [3, 6, 7, 5, 11, 1, 0, 9, 12, 10, 2, 8, 4]⟩,
  ⟨200, 13, 170, 11, 2, [6, 3, 7, 11, 5, 1, 9, 0, 12, 10, 2, 8, 4]⟩,
  ⟨170, 11, 760, 49, 2, [6, 7, 3, 11, 5, 9, 1, 0, 12, 10, 8, 2, 4]⟩,
  ⟨760, 49, 140, 9, 2, [6, 7, 11, 3, 9, 5, 1, 0, 12, 10, 8, 2, 4]⟩,
  ⟨140, 9, 360, 23, 2, [4, 7, 6, 11, 3, 9, 5, 0, 1, 10, 12, 8, 2]⟩,
  ⟨360, 23, 800, 51, 3, [7, 4, 11, 6, 9, 3, 0, 5, 10, 1, 12, 8, 2]⟩,
  ⟨800, 51, 110, 7, 3, [7, 11, 4, 6, 9, 3, 0, 10, 5, 1, 12, 8, 2]⟩,
  ⟨110, 7, 680, 43, 3, [2, 7, 11, 6, 4, 9, 3, 10, 0, 5, 1, 8, 12]⟩,
  ⟨680, 43, 95, 6, 4, [7, 2, 11, 6, 4, 9, 3, 10, 0, 5, 8, 1, 12]⟩,
  ⟨95, 6, 16, 1, 4, [7, 11, 2, 6, 9, 4, 10, 3, 0, 8, 5, 1, 12]⟩,
  ⟨16, 1, 370, 23, -2, [12, 11, 7, 9, 6, 2, 10, 4, 8, 0, 3, 1, 5]⟩,
  ⟨370, 23, 660, 41, -2, [5, 11, 12, 7, 9, 6, 2, 10, 4, 8, 0, 3, 1]⟩,
  ⟨660, 41, 210, 13, -2, [1, 5, 11, 7, 12, 9, 6, 2, 10, 4, 8, 0, 3]⟩,
  ⟨210, 13, 760, 47, -1, [1, 11, 5, 7, 12, 9, 6, 2, 10, 4, 8, 0, 3]⟩,
  ⟨760, 47, 340, 21, 0, [11, 1, 7, 5, 12, 9, 6, 10, 2, 8, 4, 0, 3]⟩,
  ⟨340, 21, 700, 43, 0, [11, 7, 1, 5, 12, 9, 6, 10, 2, 8, 4, 0, 3]⟩,
  ⟨700, 43, 800, 49, 0, [3, 11, 7, 1, 5, 9, 12, 6, 10, 2, 8, 4, 0]⟩,
  ⟨800, 49, 180, 11, 1, [11, 3, 7, 1, 9, 5, 12, 6, 10, 2, 8, 4, 0]⟩,
  ⟨180, 11, 148, 9, 1, [11, 7, 3, 9, 1, 5, 12, 10, 6, 8, 2, 0, 4]⟩,
  ⟨148, 9, 280, 17, 1, [4, 11, 7, 3, 9, 1, 5, 10, 12, 6, 8, 2, 0]⟩,
  ⟨280, 17, 380, 23, 2, [11, 4, 7, 3, 9, 1, 10, 5, 12, 6, 8, 2, 0]⟩,
  ⟨380, 23, 480, 29, 2, [0, 11, 7, 4, 9, 3, 10, 1, 5, 6, 12, 8, 2]⟩,
  ⟨480, 29, 50, 3, 3, [11, 0, 7, 4, 9, 3, 10, 1, 6, 5, 12, 8, 2]⟩,
  ⟨50, 3, 720, 43, 4, [2, 7, 0, 9, 4, 10, 3, 6, 1, 8, 12, 5, 11]⟩,
  ⟨720, 43, 84, 5, 4, [7, 2, 0, 9, 4, 10, 3, 6, 8, 1, 12, 5, 11]⟩,
  ⟨84, 5, 320, 19, 4, [7, 2, 0, 9, 10, 4, 3, 6, 8, 1, 12, 5, 11]⟩,
  ⟨320, 19, 152, 9, 4, [7, 0, 2, 9, 10, 4, 3, 8, 6, 1, 12, 5, 11]⟩,
  ⟨152, 9, 220, 13, 5, [7, 0, 9, 2, 10, 4, 8, 3, 6, 1, 12, 5, 11]⟩,
  ⟨220, 13, 390, 23, 5, [7, 9, 0, 2, 10, 4, 8, 6, 3, 1, 12, 11, 5]⟩,
  ⟨390, 23, 17, 1, 5, [5, 7, 9, 0, 2, 10, 4, 8, 6, 3, 1, 11, 12]⟩,
  ⟨17, 1, 800, 47, 0, [12, 5, 7, 9, 0, 2, 10, 4, 8, 6, 3, 1, 11]⟩,
  ⟨800, 47, 700, 41, 0, [12, 7, 5, 9, 0, 10, 2, 8, 4, 6, 3, 11, 1]⟩,
  ⟨700, 41, 120, 7, 0, [1, 7, 12, 5, 9, 0, 10, 2, 8, 4, 6, 3, 11]⟩,
  ⟨120, 7, 740, 43, 1, [7, 1, 12, 9, 5, 10, 0, 2, 8, 6, 4, 11, 3]⟩,
  ⟨740, 43, 880, 51, 1, [3, 7, 1, 9, 12, 5, 10, 0, 2, 8, 6, 4, 11]⟩,
  ⟨880, 51, 190, 11, 1, [3, 7, 1, 9, 12, 10, 5, 0, 2, 8, 6, 11, 4]⟩,
  ⟨190, 11, 52, 3, 2, [7, 3, 9, 1, 12, 10, 5, 0, 8, 2, 6, 11, 4]⟩,
  ⟨52, 3, 400, 23, 2, [4, 7, 3, 9, 1, 10, 12, 5, 0, 8, 2, 6, 11]⟩,
  ⟨400, 23, 35, 2, 3, [7, 4, 9, 3, 10, 1, 12, 0, 5, 8, 2, 11, 6]⟩,
  ⟨35, 2, 88, 5, 3, [7, 9, 4, 10, 3, 1, 12, 0, 8, 5, 11, 2, 6]⟩,
  ⟨88, 5, 370, 21, 3, [7, 9, 10, 4, 3, 1, 12, 8, 0, 5, 11, 6, 2]⟩]

def certs4 : List CC := [
  ⟨370, 21, 300, 17, 3, [2, 7, 9, 10, 4, 3, 1, 8, 12, 0, 5, 11, 6]⟩,
  ⟨300, 17, 760, 43, 3, [6, 2, 7, 9, 10, 4, 3, 1, 8, 0, 12, 5, 11]⟩,
  ⟨760, 43, 230, 13, 3, [6, 7, 2, 9, 10, 4, 3, 8, 1, 0, 12, 5, 11]⟩,
  ⟨230, 13, 160, 9, 3, [6, 7, 2, 9, 10, 4, 3, 8, 1, 0, 12, 11, 5]⟩,
  ⟨160, 9, 410, 23, 3, [7, 6, 9, 2, 10, 4, 8, 3, 0, 1, 12, 11, 5]⟩,
  ⟨410, 23, 840, 47, 3, [5, 7, 6, 9, 2, 10, 4, 8, 3, 0, 1, 11, 12]⟩,
  ⟨840, 47, 520, 29, 4, [7, 5, 6, 9, 10, 2, 8, 4, 3, 0, 11, 1, 12]⟩,
  ⟨520, 29, 880, 49, 4, [7, 6, 5, 9, 10, 2, 8, 4, 3, 11, 0, 1, 12]⟩,
  ⟨880, 49, 18, 1, 4, [7, 6, 9, 5, 10, 2, 8, 4, 11, 3, 0, 1, 12]⟩,
  ⟨18, 1, 920, 51, -2, [12, 7, 9, 6, 5, 10, 2, 8, 4, 11, 0, 3, 1]⟩,
  ⟨920, 51, 740, 41, -2, [12, 7, 9, 6, 10, 5, 2, 8, 11, 4, 0, 3, 1]⟩,
  ⟨740, 41, 380, 21, -2, [1, 7, 12, 9, 6, 10, 5, 2, 8, 11, 4, 0, 3]⟩,
  ⟨380, 21, 780, 43, -1, [7, 1, 12, 9, 6, 10, 5, 2, 8, 11, 4, 0, 3]⟩,
  ⟨780, 43, 200, 11, -1, [3, 7, 1, 9, 12, 6, 10, 5, 2, 8, 11, 4, 0]⟩,
  ⟨200, 11, 164, 9, 0, [7, 3, 9, 1, 12, 10, 6, 5, 8, 2, 11, 0, 4]⟩,
  ⟨164, 9, 420, 23, 0, [4, 7, 3, 9, 1, 10, 12, 6, 5, 8, 2, 11, 0]⟩,
  ⟨420, 23, 55, 3, 1, [0, 7, 4, 9, 3, 10, 1, 6, 12, 5, 8, 2, 11]⟩,
  ⟨55, 3, 92, 5, 2, [7, 0, 9, 4, 10, 3, 6, 1, 12, 8, 5, 11, 2]⟩,
  ⟨92, 5, 240, 13, 2, [7, 0, 9, 10, 4, 3, 6, 1, 12, 8, 5, 11, 2]⟩,
  ⟨240, 13, 130, 7, 2, [7, 9, 0, 10, 4, 6, 3, 1, 12, 8, 11, 5, 2]⟩,
  ⟨130, 7, 800, 43, 2, [2, 7, 9, 10, 0, 6, 4, 3, 1, 8, 12, 11, 5]⟩,
  ⟨800, 43, 56, 3, 3, [7, 2, 9, 10, 0, 6, 4, 3, 8, 1, 12, 11, 5]⟩,
  ⟨56, 3, 430, 23, 3, [7, 9, 2, 10, 0, 6, 4, 8, 3, 1, 12, 11, 5]⟩,
  ⟨430, 23, 880, 47, 3, [5, 7, 9, 2, 10, 0, 6, 4, 8, 3, 1, 11, 12]⟩,
  ⟨880, 47, 920, 49, 4, [7, 5, 9, 10, 2, 0, 6, 8, 4, 3, 11, 1, 12]⟩,
  ⟨920, 49, 320, 17, 4, [7, 9, 5, 10, 2, 0, 6, 8, 4, 11, 3, 1, 12]⟩,
  ⟨320, 17, 360, 19, 4, [7, 9, 10, 5, 2, 0, 6, 8, 11, 4, 3, 1, 12]⟩,
  ⟨360, 19, 19, 1, 4, [7, 9, 10, 5, 0, 2, 8, 6, 11, 4, 3, 1, 12]⟩,
  ⟨19, 1, 780, 41, -2, [12, 7, 9, 10, 5, 0, 2, 8, 6, 11, 4, 3, 1]⟩,
  ⟨780, 41, 400, 21, -2, [1, 7, 12, 9, 10, 5, 0, 2, 8, 6, 11, 4, 3]⟩,
  ⟨400, 21, 820, 43, -1, [7, 1, 12, 9, 10, 5, 0, 2, 8, 6, 11, 4, 3]⟩,
  ⟨820, 43, 210, 11, -1, [3, 7, 1, 9, 12, 10, 5, 0, 2, 8, 6, 11, 4]⟩,
  ⟨210, 11, 172, 9, 0, [7, 3, 9, 1, 12, 10, 5, 0, 8, 2, 6, 11, 4]⟩,
  ⟨172, 9, 440, 23, 0, [4, 7, 3, 9, 1, 10, 12, 5, 0, 8, 2, 6, 11]⟩,
  ⟨440, 23, 115, 6, 1, [7, 4, 9, 3, 10, 1, 12, 0, 5, 8, 2, 11, 6]⟩,
  ⟨115, 6, 96, 5, 1, [7, 9, 4, 10, 3, 1, 12, 0, 8, 5, 11, 2, 6]⟩,
  ⟨96, 5, 250, 13, 1, [7, 9, 10, 4, 3, 1, 12, 8, 0, 5, 11, 6, 2]⟩,
  ⟨250, 13, 560, 29, 1, [7, 9, 10, 4, 3, 1, 12, 8, 0, 11, 5, 6, 2]⟩,
  ⟨560, 29, 410, 21, 1, [7, 9, 10, 4, 3, 1, 12, 8, 11, 0, 6, 5, 2]⟩,
  ⟨410, 21, 840, 43, 1, [2, 7, 9, 10, 4, 3, 1, 8, 12, 11, 0, 6, 5]⟩,
  ⟨840, 43, 176, 9, 2, [7, 2, 9, 10, 4, 3, 8, 1, 12, 11, 0, 6, 5]⟩,
  ⟨176, 9, 450, 23, 2, [7, 9, 2, 10, 4, 8, 3, 1, 12, 11, 0, 6, 5]⟩,
  ⟨450, 23, 920, 47, 2, [5, 7, 9, 2, 10, 4, 8, 3, 1, 11, 12, 0, 6]⟩,
  ⟨920, 47, 960, 49, 3, [7, 5, 9, 10, 2, 8, 4, 3, 11, 1, 12, 0, 6]⟩,
  ⟨960, 49, 1000, 51, 3, [7, 9, 5, 10, 2, 8, 4, 11, 3, 1, 12, 0, 6]⟩,
  ⟨1000, 51, 20, 1, 3, [7, 9, 10, 5, 2, 8, 11, 4, 3, 1, 12, 0, 6]⟩,
  ⟨20, 1, 1040, 51, 3, [6, 0, 12, 1, 3, 4, 11, 8, 2, 5, 10, 9, 7]⟩,
  ⟨1040, 51, 1000, 49, 3, [6, 0, 12, 1, 3, 11, 4, 8, 2, 10, 5, 9, 7]⟩,
  ⟨1000, 49, 960, 47, 3, [6, 0, 12, 1, 11, 3, 4, 8, 2, 10, 9, 5, 7]⟩,
  ⟨960, 47, 470, 23, 3, [6, 0, 12, 11, 1, 3, 8, 4, 10, 2, 9, 7, 5]⟩,
  ⟨470, 23, 184, 9, 3, [5, 6, 0, 11, 12, 1, 3, 8, 4, 10, 2, 9, 7]⟩,
  ⟨184, 9, 880, 43, 3, [5, 6, 0, 11, 12, 1, 8, 3, 4, 10, 9, 2, 7]⟩,
  ⟨880, 43, 430, 21, 3, [5, 6, 0, 11, 12, 8, 1, 3, 4, 10, 9, 7, 2]⟩,
  ⟨430, 21, 600, 29, 3, [2, 5, 6, 0, 11, 8, 12, 1, 3, 4, 10, 9, 7]⟩,
  ⟨600, 29, 270, 13, 4, [2, 6, 5, 11, 0, 8, 12, 1, 3, 4, 10, 9, 7]⟩,
  ⟨270, 13, 104, 5, 4, [2, 6, 11, 5, 0, 8, 12, 1, 3, 4, 10, 9, 7]⟩,
  ⟨104, 5, 125, 6, 5, [6, 2, 11, 5, 8, 0, 12, 1, 3, 10, 4, 9, 7]⟩,
  ⟨125, 6, 480, 23, 5, [6, 11, 2, 8, 5, 0, 12, 1, 10, 3, 9, 4, 7]⟩,
  ⟨480, 23, 188, 9, 5, [11, 6, 2, 8, 0, 5, 12, 10, 1, 9, 3, 7, 4]⟩,
  ⟨188, 9, 230, 11, 5, [4, 11, 6, 2, 8, 0, 5, 10, 12, 1, 9, 3, 7]⟩,
  ⟨230, 11, 900, 43, 5, [4, 11, 6, 8, 2, 0, 5, 10, 12, 9, 1, 7, 3]⟩,
  ⟨900, 43, 440, 21, 5, [3, 4, 11, 6, 8, 2, 0, 5, 10, 9, 12, 1, 7]⟩,
  ⟨440, 21, 860, 41, 5, [3, 4, 11, 6, 8, 2, 0, 5, 10, 9, 12, 7, 1]⟩,
  ⟨860, 41, 21, 1, 5, [1, 3, 4, 11, 6, 8, 2, 0, 5, 10, 9, 7, 12]⟩,
  ⟨21, 1, 400, 19, 2, [12, 1, 3, 4, 11, 6, 8, 2, 0, 5, 10, 9, 7]⟩,
  ⟨400, 19, 360, 17, 2, [12, 1, 3, 4, 11, 8, 6, 0, 2, 5, 10, 9, 7]⟩,
  ⟨360, 17, 1040, 49, 2, [12, 1, 3, 11, 4, 8, 6, 0, 2, 10, 5, 9, 7]⟩,
  ⟨1040, 49, 1000, 47, 2, [12, 1, 11, 3, 4, 8, 6, 0, 2, 10, 9, 5, 7]⟩,
  ⟨1000, 47, 490, 23, 2, [12, 11, 1, 3, 8, 4, 6, 0, 10, 2, 9, 7, 5]⟩,
  ⟨490, 23, 64, 3, 2, [5, 11, 12, 1, 3, 8, 4, 6, 0, 10, 2, 9, 7]⟩,
  ⟨64, 3, 920, 43, 2, [5, 11, 12, 1, 8, 3, 4, 6, 0, 10, 9, 2, 7]⟩,
  ⟨920, 43, 150, 7, 2, [5, 11, 12, 8, 1, 3, 4, 6, 0, 10, 9, 7, 2]⟩,
  ⟨150, 7, 280, 13, 2, [2, 5, 11, 8, 12, 1, 3, 6, 4, 10, 0, 9, 7]⟩,
  ⟨280, 13, 108, 5, 3, [2, 11, 5, 8, 12, 1, 6, 3, 4, 10, 9, 0, 7]⟩,
  ⟨108, 5, 65, 3, 3, [2, 11, 5, 8, 12, 1, 6, 3, 10, 4, 9, 0, 7]⟩,
  ⟨65, 3, 500, 23, 4, [11, 2, 8, 5, 12, 6, 1, 10, 3, 9, 4, 7, 0]⟩,
  ⟨500, 23, 196, 9, 4, [0, 11, 2, 8, 5, 6, 12, 10, 1, 9, 3, 7, 4]⟩,
  ⟨196, 9, 240, 11, 4, [4, 0, 11, 2, 8, 5, 6, 10, 12, 1, 9, 3, 7]⟩,
  ⟨240, 11, 940, 43, 4, [0, 4, 11, 8, 2, 5, 10, 6, 12, 9, 1, 7, 3]⟩,
  ⟨940, 43, 460, 21, 4, [3, 0, 4, 11, 8, 2, 5, 10, 6, 9, 12, 1, 7]⟩]

def certs5 : List CC := [
  ⟨460, 21, 900, 41, 4, [3, 0, 4, 11, 8, 2, 5, 10, 6, 9, 12, 7, 1]⟩,
  ⟨900, 41, 1120, 51, 4, [1, 3, 0, 4, 11, 8, 2, 5, 10, 6, 9, 7, 12]⟩,
  ⟨1120, 51, 22, 1, 5, [1, 3, 0, 11, 4, 8, 2, 10, 5, 6, 9, 7, 12]⟩,
  ⟨22, 1, 1080, 49, 2, [12, 1, 0, 3, 11, 4, 8, 2, 10, 5, 9, 6, 7]⟩,
  ⟨1080, 49, 640, 29, 2, [12, 1, 0, 11, 3, 4, 8, 2, 10, 9, 5, 6, 7]⟩,
  ⟨640, 29, 1040, 47, 2, [12, 1, 11, 0, 3, 4, 8, 2, 10, 9, 6, 5, 7]⟩,
  ⟨1040, 47, 510, 23, 2, [12, 11, 1, 0, 3, 8, 4, 10, 2, 9, 6, 7, 5]⟩,
  ⟨510, 23, 200, 9, 2, [5, 11, 12, 1, 0, 3, 8, 4, 10, 2, 9, 6, 7]⟩,
  ⟨200, 9, 290, 13, 2, [5, 11, 12, 0, 1, 8, 3, 4, 10, 9, 2, 7, 6]⟩,
  ⟨290, 13, 960, 43, 3, [11, 5, 12, 0, 1, 8, 3, 4, 10, 9, 2, 7, 6]⟩,
  ⟨960, 43, 380, 17, 3, [11, 5, 12, 0, 8, 1, 3, 4, 10, 9, 7, 2, 6]⟩,
  ⟨380, 17, 470, 21, 2, [6, 11, 5, 0, 12, 8, 1, 3, 4, 10, 9, 7, 2]⟩,
  ⟨470, 21, 112, 5, 2, [2, 6, 11, 5, 0, 8, 12, 1, 3, 4, 10, 9, 7]⟩,
  ⟨112, 5, 45, 2, 3, [6, 2, 11, 5, 8, 0, 12, 1, 3, 10, 4, 9, 7]⟩,
  ⟨45, 2, 520, 23, 3, [6, 11, 2, 8, 5, 0, 12, 1, 10, 3, 9, 4, 7]⟩,
  ⟨520, 23, 68, 3, 3, [11, 6, 2, 8, 0, 5, 12, 10, 1, 9, 3, 7, 4]⟩,
  ⟨68, 3, 250, 11, 3, [4, 11, 6, 2, 8, 0, 5, 10, 12, 1, 9, 3, 7]⟩,
  ⟨250, 11, 1160, 51, 3, [4, 11, 6, 8, 2, 0, 5, 10, 12, 9, 1, 7, 3]⟩,
  ⟨1160, 51, 980, 43, 4, [11, 4, 6, 8, 2, 0, 10, 5, 12, 9, 1, 7, 3]⟩,
  ⟨980, 43, 160, 7, 4, [3, 11, 4, 6, 8, 2, 0, 10, 5, 9, 12, 1, 7]⟩,
  ⟨160, 7, 940, 41, 5, [11, 3, 6, 4, 8, 2, 10, 0, 9, 5, 12, 7, 1]⟩,
  ⟨940, 41, 1080, 47, 5, [1, 11, 3, 6, 4, 8, 2, 10, 0, 9, 5, 7, 12]⟩,
  ⟨1080, 47, 23, 1, 5, [11, 1, 3, 6, 8, 4, 10, 2, 0, 9, 7, 5, 12]⟩,
  ⟨23, 1, 530, 23, 0, [12, 11, 1, 3, 6, 8, 4, 10, 2, 0, 9, 7, 5]⟩,
  ⟨530, 23, 300, 13, 0, [5, 11, 12, 1, 3, 6, 8, 4, 10, 2, 0, 9, 7]⟩,
  ⟨300, 13, 208, 9, 1, [11, 5, 12, 1, 6, 3, 8, 4, 10, 2, 9, 0, 7]⟩,
  ⟨208, 9, 440, 19, 1, [11, 5, 12, 1, 6, 8, 3, 4, 10, 9, 2, 0, 7]⟩,
  ⟨440, 19, 116, 5, 1, [11, 5, 12, 1, 8, 6, 3, 4, 10, 9, 0, 2, 7]⟩,
  ⟨116, 5, 1000, 43, 1, [11, 5, 12, 1, 8, 6, 3, 10, 4, 9, 0, 2, 7]⟩,
  ⟨1000, 43, 70, 3, 1, [11, 5, 12, 8, 1, 6, 3, 10, 4, 9, 0, 7, 2]⟩,
  ⟨70, 3, 680, 29, 2, [2, 8, 12, 5, 6, 1, 10, 3, 9, 4, 7, 0, 11]⟩,
  ⟨680, 29, 540, 23, 2, [2, 8, 12, 6, 5, 1, 10, 3, 9, 4, 7, 11, 0]⟩,
  ⟨540, 23, 400, 17, 2, [0, 2, 8, 6, 12, 5, 10, 1, 9, 3, 7, 4, 11]⟩,
  ⟨400, 17, 212, 9, 2, [0, 2, 8, 6, 12, 10, 5, 1, 9, 3, 7, 11, 4]⟩,
  ⟨212, 9, 260, 11, 2, [4, 0, 2, 8, 6, 10, 12, 5, 1, 9, 3, 7, 11]⟩,
  ⟨260, 11, 1160, 49, 3, [0, 4, 8, 2, 10, 6, 12, 5, 9, 1, 7, 3, 11]⟩,
  ⟨1160, 49, 1020, 43, 3, [0, 4, 8, 2, 10, 6, 12, 9, 5, 1, 7, 11, 3]⟩,
  ⟨1020, 43, 500, 21, 3, [3, 0, 4, 8, 2, 10, 6, 9, 12, 5, 1, 7, 11]⟩,
  ⟨500, 21, 1120, 47, 3, [3, 0, 4, 8, 2, 10, 6, 9, 12, 5, 7, 1, 11]⟩,
  ⟨1120, 47, 310, 13, 4, [3, 0, 8, 4, 10, 2, 6, 9, 12, 7, 5, 11, 1]⟩,
  ⟨310, 13, 980, 41, 4, [3, 0, 8, 4, 10, 2, 6, 9, 12, 7, 11, 5, 1]⟩,
  ⟨980, 41, 550, 23, 4, [1, 3, 0, 8, 4, 10, 2, 6, 9, 7, 12, 11, 5]⟩,
  ⟨550, 23, 24, 1, 4, [5, 1, 3, 0, 8, 4, 10, 2, 6, 9, 7, 11, 12]⟩,
  ⟨24, 1, 145, 6, 2, [12, 1, 5, 8, 0, 3, 10, 4, 9, 6, 2, 11, 7]⟩,
  ⟨145, 6, 1040, 43, 2, [12, 1, 8, 5, 0, 10, 3, 9, 4, 6, 11, 2, 7]⟩,
  ⟨1040, 43, 170, 7, 2, [12, 8, 1, 5, 0, 10, 3, 9, 4, 6, 11, 7, 2]⟩,
  ⟨170, 7, 1240, 51, 2, [2, 8, 12, 1, 5, 10, 0, 3, 9, 6, 4, 11, 7]⟩,
  ⟨1240, 51, 560, 23, 2, [2, 8, 12, 1, 10, 5, 0, 3, 9, 6, 11, 4, 7]⟩,
  ⟨560, 23, 220, 9, 2, [2, 8, 12, 10, 1, 0, 5, 9, 3, 11, 6, 7, 4]⟩,
  ⟨220, 9, 1200, 49, 2, [4, 2, 8, 10, 12, 0, 1, 5, 9, 3, 11, 7, 6]⟩,
  ⟨1200, 49, 270, 11, 2, [4, 2, 8, 10, 12, 0, 1, 9, 5, 11, 3, 7, 6]⟩,
  ⟨270, 11, 320, 13, 3, [4, 8, 2, 10, 12, 0, 9, 1, 5, 11, 7, 3, 6]⟩,
  ⟨320, 13, 1060, 43, 3, [4, 8, 2, 10, 12, 9, 0, 1, 11, 5, 7, 6, 3]⟩,
  ⟨1060, 43, 1160, 47, 3, [3, 4, 8, 2, 10, 9, 12, 0, 1, 11, 5, 7, 6]⟩,
  ⟨1160, 47, 420, 17, 4, [3, 8, 4, 10, 2, 9, 12, 0, 11, 1, 7, 5, 6]⟩,
  ⟨420, 17, 520, 21, 4, [6, 3, 8, 4, 10, 2, 9, 0, 12, 11, 1, 7, 5]⟩,
  ⟨520, 21, 570, 23, 4, [6, 3, 8, 4, 10, 2, 9, 0, 12, 11, 7, 1, 5]⟩,
  ⟨570, 23, 124, 5, 4, [5, 6, 3, 8, 4, 10, 2, 9, 0, 11, 12, 7, 1]⟩,
  ⟨124, 5, 720, 29, 4, [5, 6, 3, 8, 10, 4, 2, 9, 0, 11, 12, 7, 1]⟩,
  ⟨720, 29, 1020, 41, 4, [6, 5, 3, 8, 10, 4, 2, 9, 11, 0, 12, 7, 1]⟩,
  ⟨1020, 41, 224, 9, 4, [1, 6, 5, 3, 8, 10, 4, 2, 9, 11, 0, 7, 12]⟩,
  ⟨224, 9, 25, 1, 5, [1, 6, 5, 8, 3, 10, 4, 9, 2, 11, 0, 7, 12]⟩,
  ⟨25, 1, 1280, 51, 0, [12, 6, 1, 8, 5, 10, 3, 9, 4, 11, 2, 7, 0]⟩,
  ⟨1280, 51, 1080, 43, 0, [12, 6, 1, 8, 10, 5, 3, 9, 11, 4, 2, 7, 0]⟩,
  ⟨1080, 43, 580, 23, 0, [12, 6, 8, 1, 10, 5, 3, 9, 11, 4, 7, 2, 0]⟩,
  ⟨580, 23, 530, 21, 0, [0, 6, 12, 8, 10, 1, 5, 9, 3, 11, 7, 4, 2]⟩,
  ⟨530, 21, 480, 19, 0, [2, 0, 6, 8, 12, 10, 1, 5, 9, 3, 11, 7, 4]⟩,
  ⟨480, 19, 1240, 49, 0, [0, 2, 8, 6, 12, 10, 1, 5, 9, 3, 11, 7, 4]⟩,
  ⟨1240, 49, 76, 3, 0, [0, 2, 8, 6, 12, 10, 1, 9, 5, 11, 3, 7, 4]⟩,
  ⟨76, 3, 330, 13, 0, [4, 0, 2, 8, 6, 10, 12, 1, 9, 5, 11, 3, 7]⟩,
  ⟨330, 13, 280, 11, 0, [4, 0, 2, 8, 6, 10, 12, 1, 9, 11, 5, 3, 7]⟩,
  ⟨280, 11, 1200, 47, 1, [0, 4, 8, 2, 10, 6, 12, 9, 1, 11, 5, 7, 3]⟩,
  ⟨1200, 47, 1100, 43, 2, [0, 8, 4, 10, 2, 6, 12, 9, 11, 1, 7, 5, 3]⟩,
  ⟨1100, 43, 128, 5, 2, [3, 0, 8, 4, 10, 2, 6, 9, 12, 11, 1, 7, 5]⟩,
  ⟨128, 5, 590, 23, 3, [3, 8, 0, 10, 4, 6, 2, 9, 12, 11, 1, 7, 5]⟩,
  ⟨590, 23, 180, 7, 3, [5, 3, 8, 0, 10, 4, 6, 2, 9, 11, 12, 1, 7]⟩,
  ⟨180, 7, 232, 9, 3, [5, 3, 8, 10, 0, 6, 4, 2, 9, 11, 12, 7, 1]⟩,
  ⟨232, 9, 155, 6, 4, [5, 8, 3, 10, 0, 6, 4, 9, 2, 11, 12, 7, 1]⟩,
  ⟨155, 6, 1060, 41, 4, [8, 5, 10, 3, 0, 6, 9, 4, 11, 2, 12, 7, 1]⟩,
  ⟨1060, 41, 440, 17, 4, [1, 8, 5, 10, 3, 0, 6, 9, 4, 11, 2, 7, 12]⟩]

def certs6 : List CC := [
  ⟨440, 17, 26, 1, 4, [1, 8, 10, 5, 3, 0, 6, 9, 11, 4, 2, 7, 12]⟩,
  ⟨26, 1, 1120, 43, 0, [12, 1, 8, 10, 5, 0, 3, 9, 6, 11, 4, 2, 7]⟩,
  ⟨1120, 43, 600, 23, 0, [12, 8, 1, 10, 5, 0, 3, 9, 6, 11, 4, 7, 2]⟩,
  ⟨600, 23, 1280, 49, 0, [12, 8, 10, 1, 0, 5, 9, 3, 11, 6, 7, 4, 2]⟩,
  ⟨1280, 49, 340, 13, 0, [12, 8, 10, 1, 0, 9, 5, 11, 3, 6, 7, 4, 2]⟩,
  ⟨340, 13, 550, 21, 0, [12, 8, 10, 1, 9, 0, 11, 5, 6, 3, 7, 4, 2]⟩,
  ⟨550, 21, 760, 29, 0, [2, 8, 12, 10, 1, 9, 0, 11, 5, 6, 3, 7, 4]⟩,
  ⟨760, 29, 236, 9, 0, [2, 8, 12, 10, 1, 9, 11, 0, 6, 5, 3, 7, 4]⟩,
  ⟨236, 9, 290, 11, 0, [4, 2, 8, 10, 12, 1, 9, 11, 0, 6, 5, 3, 7]⟩,
  ⟨290, 11, 1240, 47, 1, [4, 8, 2, 10, 12, 9, 1, 11, 0, 6, 5, 7, 3]⟩,
  ⟨1240, 47, 132, 5, 2, [8, 4, 10, 2, 12, 9, 11, 1, 0, 6, 7, 5, 3]⟩,
  ⟨132, 5, 1140, 43, 2, [8, 10, 4, 2, 12, 9, 11, 1, 0, 6, 7, 5, 3]⟩,
  ⟨1140, 43, 610, 23, 2, [3, 8, 10, 4, 2, 9, 12, 11, 1, 0, 6, 7, 5]⟩,
  ⟨610, 23, 80, 3, 2, [5, 3, 8, 10, 4, 2, 9, 11, 12, 1, 0, 6, 7]⟩,
  ⟨80, 3, 1100, 41, 4, [10, 8, 3, 5, 11, 9, 2, 4, 12, 7, 6, 0, 1]⟩,
  ⟨1100, 41, 350, 13, 4, [1, 10, 8, 3, 5, 11, 9, 2, 4, 7, 12, 6, 0]⟩,
  ⟨350, 13, 1320, 49, 4, [1, 10, 8, 3, 11, 5, 9, 2, 4, 7, 12, 6, 0]⟩,
  ⟨1320, 49, 620, 23, 4, [1, 10, 8, 11, 3, 9, 5, 2, 4, 7, 12, 6, 0]⟩,
  ⟨620, 23, 1160, 43, 5, [0, 10, 1, 8, 11, 9, 3, 5, 2, 7, 4, 6, 12]⟩,
  ⟨1160, 43, 27, 1, 5, [0, 10, 8, 1, 11, 9, 3, 5, 7, 2, 4, 6, 12]⟩,
  ⟨27, 1, 460, 17, 0, [12, 0, 10, 8, 1, 11, 9, 3, 5, 7, 2, 4, 6]⟩,
  ⟨460, 17, 244, 9, -1, [6, 0, 12, 10, 8, 1, 11, 9, 3, 5, 7, 2, 4]⟩,
  ⟨244, 9, 190, 7, -1, [4, 6, 0, 10, 12, 8, 1, 11, 9, 3, 5, 7, 2]⟩,
  ⟨190, 7, 136, 5, 0, [2, 6, 4, 10, 0, 8, 12, 1, 11, 9, 3, 5, 7]⟩,
  ⟨136, 5, 1280, 47, 1, [6, 2, 10, 4, 8, 0, 12, 1, 11, 9, 3, 5, 7]⟩,
  ⟨1280, 47, 300, 11, 1, [6, 10, 2, 8, 4, 0, 12, 11, 1, 9, 3, 7, 5]⟩,
  ⟨300, 11, 520, 19, 1, [10, 6, 8, 2, 0, 4, 12, 11, 9, 1, 7, 3, 5]⟩,
  ⟨520, 19, 630, 23, 1, [10, 8, 6, 0, 2, 4, 12, 11, 9, 1, 7, 3, 5]⟩,
  ⟨630, 23, 1180, 43, 1, [5, 10, 8, 6, 0, 2, 4, 11, 12, 9, 1, 7, 3]⟩,
  ⟨1180, 43, 1400, 51, 1, [3, 5, 10, 8, 6, 0, 2, 4, 11, 9, 12, 1, 7]⟩,
  ⟨1400, 51, 55, 2, 2, [3, 10, 5, 8, 6, 0, 2, 11, 4, 9, 12, 1, 7]⟩,
  ⟨55, 2, 248, 9, 3, [10, 3, 8, 5, 6, 0, 11, 2, 9, 4, 12, 1, 7]⟩,
  ⟨248, 9, 800, 29, 3, [10, 8, 3, 5, 6, 0, 11, 9, 2, 4, 12, 1, 7]⟩,
  ⟨800, 29, 580, 21, 3, [10, 8, 3, 6, 5, 11, 0, 9, 2, 4, 12, 1, 7]⟩,
  ⟨580, 21, 360, 13, 3, [10, 8, 3, 6, 5, 11, 0, 9, 2, 4, 12, 7, 1]⟩,
  ⟨360, 13, 1360, 49, 3, [10, 8, 6, 3, 11, 5, 9, 0, 2, 4, 12, 7, 1]⟩,
  ⟨1360, 49, 1140, 41, 3, [10, 8, 6, 11, 3, 9, 5, 0, 2, 4, 12, 7, 1]⟩,
  ⟨1140, 41, 640, 23, 3, [1, 10, 8, 6, 11, 3, 9, 5, 0, 2, 4, 7, 12]⟩,
  ⟨640, 23, 1200, 43, 4, [10, 1, 8, 11, 6, 9, 3, 0, 5, 2, 7, 4, 12]⟩,
  ⟨1200, 43, 28, 1, 4, [10, 8, 1, 11, 6, 9, 3, 0, 5, 7, 2, 4, 12]⟩,
  ⟨28, 1, 1320, 47, 0, [12, 4, 8, 1, 11, 9, 6, 0, 3, 5, 7, 2, 10]⟩,
  ⟨1320, 47, 590, 21, 0, [12, 8, 4, 11, 1, 9, 6, 0, 3, 7, 5, 10, 2]⟩,
  ⟨590, 21, 310, 11, 0, [2, 8, 12, 4, 11, 1, 9, 6, 0, 3, 7, 5, 10]⟩,
  ⟨310, 11, 480, 17, 1, [8, 2, 12, 4, 11, 9, 1, 6, 0, 7, 3, 5, 10]⟩,
  ⟨480, 17, 650, 23, 1, [8, 2, 12, 11, 4, 9, 1, 6, 0, 7, 3, 10, 5]⟩,
  ⟨650, 23, 85, 3, 1, [5, 8, 2, 11, 12, 4, 9, 1, 6, 0, 7, 3, 10]⟩,
  ⟨85, 3, 1220, 43, 2, [8, 5, 11, 2, 12, 9, 4, 6, 1, 7, 0, 10, 3]⟩,
  ⟨1220, 43, 256, 9, 2, [3, 8, 5, 11, 2, 9, 12, 4, 6, 1, 7, 0, 10]⟩,
  ⟨256, 9, 370, 13, 2, [8, 3, 5, 11, 9, 2, 12, 4, 6, 1, 7, 0, 10]⟩,
  ⟨370, 13, 200, 7, 3, [8, 3, 11, 5, 9, 2, 12, 4, 6, 1, 7, 0, 10]⟩,
  ⟨200, 7, 660, 23, 3, [8, 11, 3, 9, 5, 2, 12, 6, 4, 7, 1, 10, 0]⟩,
  ⟨660, 23, 1180, 41, 3, [0, 8, 11, 9, 3, 5, 2, 6, 12, 7, 4, 10, 1]⟩,
  ⟨1180, 41, 144, 5, 3, [1, 0, 8, 11, 9, 3, 5, 2, 6, 7, 12, 4, 10]⟩,
  ⟨144, 5, 1240, 43, 4, [1, 8, 0, 11, 9, 3, 5, 6, 2, 7, 12, 10, 4]⟩,
  ⟨1240, 43, 260, 9, 4, [8, 1, 0, 11, 9, 3, 5, 6, 7, 2, 12, 10, 4]⟩,
  ⟨260, 9, 1360, 47, 4, [4, 8, 0, 1, 11, 9, 3, 5, 7, 6, 2, 10, 12]⟩,
  ⟨1360, 47, 840, 29, 5, [8, 4, 0, 11, 1, 9, 3, 7, 5, 6, 10, 2, 12]⟩,
  ⟨840, 29, 29, 1, 5, [8, 4, 11, 0, 1, 9, 3, 7, 6, 5, 10, 2, 12]⟩,
  ⟨29, 1, 1480, 51, 0, [12, 8, 4, 11, 0, 1, 9, 3, 7, 6, 5, 10, 2]⟩,
  ⟨1480, 51, 610, 21, 0, [12, 8, 11, 4, 0, 1, 9, 3, 7, 6, 10, 5, 2]⟩,
  ⟨610, 21, 320, 11, 0, [2, 8, 12, 11, 4, 0, 1, 9, 3, 7, 6, 10, 5]⟩,
  ⟨320, 11, 670, 23, 1, [8, 2, 12, 11, 0, 4, 9, 1, 7, 3, 10, 6, 5]⟩,
  ⟨670, 23, 175, 6, 1, [5, 8, 2, 11, 12, 0, 4, 9, 1, 7, 3, 10, 6]⟩,
  ⟨175, 6, 380, 13, 2, [8, 5, 11, 2, 12, 0, 9, 4, 1, 7, 10, 3, 6]⟩,
  ⟨380, 13, 1260, 43, 2, [8, 11, 5, 2, 12, 9, 0, 4, 1, 7, 10, 6, 3]⟩,
  ⟨1260, 43, 88, 3, 2, [3, 8, 11, 5, 2, 9, 12, 0, 4, 1, 7, 10, 6]⟩,
  ⟨88, 3, 1440, 49, 3, [8, 3, 11, 5, 9, 2, 12, 0, 4, 1, 7, 10, 6]⟩,
  ⟨1440, 49, 500, 17, 3, [8, 11, 3, 9, 5, 2, 12, 0, 4, 1, 7, 10, 6]⟩,
  ⟨500, 17, 560, 19, 2, [6, 8, 11, 3, 9, 5, 2, 0, 12, 4, 1, 7, 10]⟩,
  ⟨560, 19, 620, 21, 2, [8, 6, 11, 3, 9, 5, 0, 2, 12, 4, 1, 7, 10]⟩,
  ⟨620, 21, 680, 23, 2, [8, 6, 11, 3, 9, 5, 0, 2, 12, 4, 7, 1, 10]⟩,
  ⟨680, 23, 148, 5, 2, [8, 11, 6, 9, 3, 0, 5, 2, 12, 7, 4, 10, 1]⟩,
  ⟨148, 5, 1220, 41, 2, [8, 11, 6, 9, 3, 0, 5, 2, 12, 7, 10, 4, 1]⟩,
  ⟨1220, 41, 1280, 43, 2, [1, 8, 11, 6, 9, 3, 0, 5, 2, 7, 12, 10, 4]⟩,
  ⟨1280, 43, 268, 9, 3, [8, 1, 11, 6, 9, 3, 0, 5, 7, 2, 12, 10, 4]⟩,
  ⟨268, 9, 1400, 47, 3, [4, 8, 1, 11, 6, 9, 3, 0, 5, 7, 2, 10, 12]⟩,
  ⟨1400, 47, 1520, 51, 4, [8, 4, 11, 1, 6, 9, 3, 0, 7, 5, 10, 2, 12]⟩,
  ⟨1520, 51, 30, 1, 4, [8, 11, 4, 1, 6, 9, 3, 0, 7, 10, 5, 2, 12]⟩,
  ⟨30, 1, 1480, 49, 2, [12, 2, 5, 9, 6, 1, 4, 10, 7, 0, 3, 11, 8]⟩,
  ⟨1480, 49, 272, 9, 2, [12, 2, 9, 5, 6, 1, 4, 10, 7, 0, 11, 3, 8]⟩]

def certs7 : List CC := [
  ⟨272, 9, 1300, 43, 2, [12, 9, 2, 5, 6, 1, 4, 10, 7, 0, 11, 8, 3]⟩,
  ⟨1300, 43, 880, 29, 2, [3, 9, 12, 2, 5, 6, 1, 4, 10, 7, 0, 11, 8]⟩,
  ⟨880, 29, 152, 5, 2, [3, 9, 12, 2, 6, 5, 1, 4, 10, 7, 11, 0, 8]⟩,
  ⟨152, 5, 700, 23, 2, [3, 9, 12, 6, 2, 5, 1, 10, 4, 7, 11, 8, 0]⟩,
  ⟨700, 23, 640, 21, 3, [0, 9, 3, 6, 12, 2, 5, 10, 1, 7, 4, 11, 8]⟩,
  ⟨640, 21, 520, 17, 3, [0, 9, 3, 6, 12, 2, 5, 10, 7, 1, 4, 11, 8]⟩,
  ⟨520, 17, 1440, 47, 3, [0, 9, 3, 6, 12, 2, 10, 5, 7, 1, 11, 4, 8]⟩,
  ⟨1440, 47, 92, 3, 3, [0, 9, 3, 6, 12, 10, 2, 7, 5, 11, 1, 8, 4]⟩,
  ⟨92, 3, 1320, 43, 3, [4, 0, 9, 3, 6, 10, 12, 2, 7, 5, 11, 1, 8]⟩,
  ⟨1320, 43, 1260, 41, 3, [4, 0, 9, 3, 6, 10, 12, 7, 2, 5, 11, 8, 1]⟩,
  ⟨1260, 41, 400, 13, 3, [1, 4, 0, 9, 3, 6, 10, 7, 12, 2, 5, 11, 8]⟩,
  ⟨400, 13, 185, 6, 4, [1, 4, 9, 0, 6, 3, 10, 7, 12, 2, 11, 5, 8]⟩,
  ⟨185, 6, 710, 23, 4, [1, 9, 4, 0, 6, 10, 3, 7, 12, 11, 2, 8, 5]⟩,
  ⟨710, 23, 340, 11, 4, [5, 1, 9, 4, 0, 6, 10, 3, 7, 11, 12, 2, 8]⟩,
  ⟨340, 11, 650, 21, 4, [5, 9, 1, 0, 4, 10, 6, 7, 3, 11, 12, 8, 2]⟩,
  ⟨650, 21, 31, 1, 4, [2, 5, 9, 1, 0, 4, 10, 6, 7, 3, 11, 8, 12]⟩,
  ⟨31, 1, 1520, 49, 2, [12, 2, 5, 9, 1, 0, 4, 10, 6, 7, 3, 11, 8]⟩,
  ⟨1520, 49, 280, 9, 2, [12, 2, 9, 5, 1, 0, 4, 10, 6, 7, 11, 3, 8]⟩,
  ⟨280, 9, 1340, 43, 2, [12, 9, 2, 5, 0, 1, 4, 10, 7, 6, 11, 8, 3]⟩,
  ⟨1340, 43, 156, 5, 2, [3, 9, 12, 2, 5, 0, 1, 4, 10, 7, 6, 11, 8]⟩,
  ⟨156, 5, 720, 23, 2, [3, 9, 12, 2, 5, 0, 1, 10, 4, 7, 6, 11, 8]⟩,
  ⟨720, 23, 1600, 51, 3, [9, 3, 12, 2, 0, 5, 10, 1, 7, 4, 11, 6, 8]⟩,
  ⟨1600, 51, 220, 7, 3, [9, 3, 12, 2, 0, 10, 5, 1, 7, 11, 4, 6, 8]⟩,
  ⟨220, 7, 1480, 47, 3, [9, 3, 12, 2, 10, 0, 5, 7, 1, 11, 6, 4, 8]⟩,
  ⟨1480, 47, 410, 13, 3, [9, 3, 12, 10, 2, 0, 7, 5, 11, 1, 6, 8, 4]⟩,
  ⟨410, 13, 284, 9, 3, [9, 3, 12, 10, 2, 0, 7, 11, 5, 1, 6, 8, 4]⟩,
  ⟨284, 9, 600, 19, 3, [4, 9, 3, 10, 12, 2, 0, 7, 11, 5, 1, 6, 8]⟩,
  ⟨600, 19, 1360, 43, 3, [4, 9, 3, 10, 12, 0, 2, 7, 11, 5, 1, 8, 6]⟩,
  ⟨1360, 43, 95, 3, 3, [4, 9, 3, 10, 12, 0, 7, 2, 11, 5, 8, 1, 6]⟩,
  ⟨95, 3, 1300, 41, 4, [9, 4, 10, 3, 12, 7, 0, 11, 2, 8, 5, 6, 1]⟩,
  ⟨1300, 41, 920, 29, 4, [1, 9, 4, 10, 3, 7, 12, 0, 11, 2, 8, 5, 6]⟩,
  ⟨920, 29, 730, 23, 4, [1, 9, 4, 10, 3, 7, 12, 11, 0, 2, 8, 6, 5]⟩,
  ⟨730, 23, 540, 17, 4, [5, 1, 9, 4, 10, 3, 7, 11, 12, 0, 2, 8, 6]⟩,
  ⟨540, 17, 350, 11, 4, [6, 5, 1, 9, 4, 10, 3, 7, 11, 0, 12, 2, 8]⟩,
  ⟨350, 11, 1560, 49, 4, [6, 5, 9, 1, 4, 10, 7, 3, 11, 0, 12, 8, 2]⟩,
  ⟨1560, 49, 670, 21, 4, [6, 9, 5, 1, 4, 10, 7, 11, 3, 0, 12, 8, 2]⟩,
  ⟨670, 21, 32, 1, 4, [2, 6, 9, 5, 1, 4, 10, 7, 11, 3, 0, 8, 12]⟩,
  ⟨32, 1, 1380, 43, 0, [12, 9, 6, 2, 1, 5, 10, 4, 11, 7, 8, 0, 3]⟩,
  ⟨1380, 43, 1640, 51, 0, [3, 9, 12, 6, 2, 1, 5, 10, 4, 11, 7, 8, 0]⟩,
  ⟨1640, 51, 740, 23, 0, [3, 9, 12, 6, 2, 1, 10, 5, 11, 4, 7, 8, 0]⟩,
  ⟨740, 23, 420, 13, 1, [0, 9, 3, 6, 12, 2, 10, 1, 5, 11, 7, 4, 8]⟩,
  ⟨420, 13, 1520, 47, 2, [9, 0, 6, 3, 12, 2, 10, 1, 11, 5, 7, 4, 8]⟩,
  ⟨1520, 47, 680, 21, 2, [9, 0, 6, 3, 12, 10, 2, 11, 1, 7, 5, 8, 4]⟩,
  ⟨680, 21, 292, 9, 2, [9, 0, 6, 3, 12, 10, 2, 11, 7, 1, 5, 8, 4]⟩,
  ⟨292, 9, 65, 2, 2, [4, 9, 0, 6, 3, 10, 12, 2, 11, 7, 1, 5, 8]⟩,
  ⟨65, 2, 1400, 43, 2, [9, 4, 0, 6, 10, 3, 12, 11, 2, 7, 1, 8, 5]⟩,
  ⟨1400, 43, 750, 23, 2, [9, 4, 0, 6, 10, 3, 12, 11, 7, 2, 8, 1, 5]⟩,
  ⟨750, 23, 1600, 49, 2, [5, 9, 4, 0, 6, 10, 3, 11, 12, 7, 2, 8, 1]⟩,
  ⟨1600, 49, 1340, 41, 2, [9, 5, 4, 0, 6, 10, 11, 3, 12, 7, 2, 8, 1]⟩,
  ⟨1340, 41, 360, 11, 2, [1, 9, 5, 4, 0, 6, 10, 11, 3, 7, 12, 2, 8]⟩,
  ⟨360, 11, 164, 5, 2, [9, 1, 5, 0, 4, 10, 6, 11, 7, 3, 12, 8, 2]⟩,
  ⟨164, 5, 230, 7, 3, [9, 1, 5, 0, 10, 4, 6, 11, 7, 3, 12, 8, 2]⟩,
  ⟨230, 7, 296, 9, 4, [2, 9, 1, 5, 10, 0, 6, 4, 11, 7, 3, 8, 12]⟩,
  ⟨296, 9, 560, 17, 4, [9, 2, 1, 5, 10, 0, 6, 4, 11, 7, 8, 3, 12]⟩,
  ⟨560, 17, 33, 1, 4, [9, 2, 1, 10, 5, 0, 6, 11, 4, 7, 8, 3, 12]⟩,
  ⟨33, 1, 1420, 43, 0, [12, 9, 2, 1, 10, 5, 0, 6, 11, 4, 7, 8, 3]⟩,
  ⟨1420, 43, 760, 23, 0, [3, 9, 12, 2, 1, 10, 5, 0, 6, 11, 4, 7, 8]⟩,
  ⟨760, 23, 430, 13, 1, [9, 3, 12, 2, 10, 1, 0, 5, 11, 6, 7, 4, 8]⟩,
  ⟨430, 13, 960, 29, 1, [9, 3, 12, 2, 10, 1, 0, 11, 5, 6, 7, 4, 8]⟩,
  ⟨960, 29, 1560, 47, 1, [9, 3, 12, 2, 10, 1, 11, 0, 6, 5, 7, 4, 8]⟩,
  ⟨1560, 47, 100, 3, 1, [9, 3, 12, 10, 2, 11, 1, 0, 6, 7, 5, 8, 4]⟩,
  ⟨100, 3, 1640, 49, 2, [4, 10, 12, 3, 11, 2, 7, 6, 0, 1, 8, 5, 9]⟩,
  ⟨1640, 49, 770, 23, 2, [4, 10, 12, 11, 3, 2, 7, 6, 0, 1, 8, 9, 5]⟩,
  ⟨770, 23, 1440, 43, 2, [5, 4, 10, 11, 12, 3, 2, 7, 6, 0, 1, 8, 9]⟩,
  ⟨1440, 43, 168, 5, 2, [5, 4, 10, 11, 12, 3, 7, 2, 6, 0, 8, 1, 9]⟩,
  ⟨168, 5, 370, 11, 3, [5, 10, 4, 11, 12, 3, 7, 6, 2, 8, 0, 1, 9]⟩,
  ⟨370, 11, 1380, 41, 3, [5, 10, 4, 11, 12, 7, 3, 6, 8, 2, 0, 9, 1]⟩,
  ⟨1380, 41, 640, 19, 3, [1, 5, 10, 4, 11, 7, 12, 3, 6, 8, 2, 0, 9]⟩,
  ⟨640, 19, 1720, 51, 3, [1, 5, 10, 4, 11, 7, 12, 3, 8, 6, 0, 2, 9]⟩,
  ⟨1720, 51, 304, 9, 4, [1, 10, 5, 11, 4, 7, 12, 3, 8, 6, 0, 2, 9]⟩,
  ⟨304, 9, 710, 21, 4, [1, 10, 5, 11, 4, 7, 12, 8, 3, 6, 0, 9, 2]⟩,
  ⟨710, 21, 440, 13, 4, [2, 1, 10, 5, 11, 4, 7, 8, 12, 3, 6, 0, 9]⟩,
  ⟨440, 13, 780, 23, 4, [2, 1, 10, 11, 5, 4, 7, 8, 12, 6, 3, 9, 0]⟩,
  ⟨780, 23, 1460, 43, 5, [0, 2, 10, 1, 11, 5, 7, 4, 8, 6, 12, 9, 3]⟩,
  ⟨1460, 43, 34, 1, 5, [3, 0, 2, 10, 1, 11, 5, 7, 4, 8, 6, 9, 12]⟩,
  ⟨34, 1, 1600, 47, 2, [12, 0, 3, 2, 10, 1, 11, 5, 7, 4, 8, 9, 6]⟩,
  ⟨1600, 47, 580, 17, 2, [12, 0, 3, 10, 2, 11, 1, 7, 5, 8, 4, 9, 6]⟩,
  ⟨580, 17, 205, 6, 1, [6, 0, 12, 3, 10, 2, 11, 1, 7, 5, 8, 4, 9]⟩,
  ⟨205, 6, 308, 9, 1, [6, 0, 12, 10, 3, 11, 2, 1, 7, 8, 5, 9, 4]⟩,
  ⟨308, 9, 240, 7, 1, [4, 6, 0, 10, 12, 3, 11, 2, 1, 7, 8, 5, 9]⟩]

def certs8 : List CC := [
  ⟨240, 7, 790, 23, 2, [6, 4, 10, 0, 12, 11, 3, 2, 7, 1, 8, 9, 5]⟩,
  ⟨790, 23, 172, 5, 2, [5, 6, 4, 10, 0, 11, 12, 3, 2, 7, 1, 8, 9]⟩,
  ⟨172, 5, 1480, 43, 2, [5, 6, 10, 4, 0, 11, 12, 3, 2, 7, 1, 8, 9]⟩,
  ⟨1480, 43, 1000, 29, 2, [5, 6, 10, 4, 0, 11, 12, 3, 7, 2, 8, 1, 9]⟩,
  ⟨1000, 29, 1760, 51, 3, [6, 5, 10, 4, 11, 0, 12, 3, 7, 2, 8, 1, 9]⟩,
  ⟨1760, 51, 380, 11, 3, [6, 10, 5, 11, 4, 0, 12, 3, 7, 2, 8, 1, 9]⟩,
  ⟨380, 11, 450, 13, 3, [10, 6, 5, 11, 0, 4, 12, 7, 3, 8, 2, 9, 1]⟩,
  ⟨450, 13, 1420, 41, 3, [10, 6, 11, 5, 0, 4, 12, 7, 3, 8, 2, 9, 1]⟩,
  ⟨1420, 41, 104, 3, 3, [1, 10, 6, 11, 5, 0, 4, 7, 12, 3, 8, 2, 9]⟩,
  ⟨104, 3, 730, 21, 3, [1, 10, 6, 11, 5, 0, 4, 7, 12, 8, 3, 9, 2]⟩,
  ⟨730, 21, 800, 23, 3, [2, 1, 10, 6, 11, 5, 0, 4, 7, 8, 12, 3, 9]⟩,
  ⟨800, 23, 1500, 43, 4, [2, 10, 1, 11, 6, 0, 5, 7, 4, 8, 12, 9, 3]⟩,
  ⟨1500, 43, 1640, 47, 4, [3, 2, 10, 1, 11, 6, 0, 5, 7, 4, 8, 9, 12]⟩,
  ⟨1640, 47, 35, 1, 5, [3, 10, 2, 11, 1, 6, 0, 7, 5, 8, 4, 9, 12]⟩,
  ⟨35, 1, 1720, 49, 0, [12, 10, 3, 11, 2, 6, 1, 7, 0, 8, 5, 9, 4]⟩,
  ⟨1720, 49, 316, 9, 0, [12, 10, 11, 3, 2, 6, 1, 7, 0, 8, 9, 5, 4]⟩,
  ⟨316, 9, 176, 5, 0, [4, 10, 12, 11, 3, 2, 6, 1, 7, 0, 8, 9, 5]⟩,
  ⟨176, 5, 810, 23, 1, [10, 4, 12, 11, 3, 6, 2, 1, 7, 8, 0, 9, 5]⟩,
  ⟨810, 23, 740, 21, 1, [5, 10, 4, 11, 12, 3, 6, 2, 1, 7, 8, 0, 9]⟩,
  ⟨740, 21, 600, 17, 1, [5, 10, 4, 11, 12, 3, 6, 2, 7, 1, 8, 0, 9]⟩,
  ⟨600, 17, 1520, 43, 2, [10, 5, 11, 4, 12, 3, 6, 2, 7, 1, 8, 0, 9]⟩,
  ⟨1520, 43, 460, 13, 2, [10, 5, 11, 4, 12, 3, 6, 7, 2, 8, 1, 0, 9]⟩,
  ⟨460, 13, 390, 11, 2, [10, 11, 5, 4, 12, 6, 3, 7, 2, 8, 1, 9, 0]⟩,
  ⟨390, 11, 320, 9, 2, [10, 11, 5, 4, 12, 6, 7, 3, 8, 2, 9, 1, 0]⟩,
  ⟨320, 9, 1460, 41, 2, [10, 11, 5, 4, 12, 7, 6, 8, 3, 9, 2, 0, 1]⟩,
  ⟨1460, 41, 820, 23, 2, [1, 10, 11, 5, 4, 7, 12, 6, 8, 3, 9, 2, 0]⟩,
  ⟨820, 23, 250, 7, 3, [0, 10, 1, 11, 5, 7, 4, 6, 12, 8, 9, 3, 2]⟩,
  ⟨250, 7, 1680, 47, 3, [2, 10, 0, 1, 11, 5, 7, 6, 4, 8, 12, 9, 3]⟩,
  ⟨1680, 47, 680, 19, 4, [10, 2, 0, 11, 1, 7, 5, 6, 8, 4, 12, 9, 3]⟩,
  ⟨680, 19, 1540, 43, 4, [10, 0, 2, 11, 1, 7, 5, 8, 6, 4, 12, 9, 3]⟩,
  ⟨1540, 43, 215, 6, 4, [3, 10, 0, 2, 11, 1, 7, 5, 8, 6, 4, 9, 12]⟩,
  ⟨215, 6, 1040, 29, 4, [10, 3, 0, 11, 2, 1, 7, 8, 5, 6, 9, 4, 12]⟩,
  ⟨1040, 29, 1760, 49, 4, [10, 3, 11, 0, 2, 1, 7, 8, 6, 5, 9, 4, 12]⟩,
  ⟨1760, 49, 36, 1, 4, [10, 11, 3, 0, 2, 1, 7, 8, 6, 9, 5, 4, 12]⟩,
  ⟨36, 1, 1840, 51, 2, [12, 4, 11, 0, 3, 2, 1, 7, 8, 9, 6, 5, 10]⟩,
  ⟨1840, 51, 830, 23, 2, [12, 11, 4, 0, 3, 2, 1, 7, 8, 9, 6, 10, 5]⟩,
  ⟨830, 23, 470, 13, 2, [5, 11, 12, 4, 0, 3, 2, 1, 7, 8, 9, 6, 10]⟩,
  ⟨470, 13, 760, 21, 3, [11, 5, 12, 4, 0, 3, 2, 1, 7, 8, 9, 6, 10]⟩,
  ⟨760, 21, 1560, 43, 3, [11, 5, 12, 4, 0, 3, 2, 7, 1, 8, 9, 6, 10]⟩,
  ⟨1560, 43, 400, 11, 3, [11, 5, 12, 4, 0, 3, 7, 2, 8, 1, 9, 6, 10]⟩,
  ⟨400, 11, 328, 9, 3, [11, 5, 12, 0, 4, 7, 3, 8, 2, 9, 1, 10, 6]⟩,
  ⟨328, 9, 620, 17, 3, [11, 5, 12, 0, 4, 7, 8, 3, 9, 2, 1, 10, 6]⟩,
  ⟨620, 17, 840, 23, 2, [6, 11, 5, 0, 12, 4, 7, 8, 3, 9, 2, 1, 10]⟩,
  ⟨840, 23, 1500, 41, 2, [11, 6, 0, 5, 12, 7, 4, 8, 9, 3, 2, 10, 1]⟩,
  ⟨1500, 41, 1720, 47, 2, [1, 11, 6, 0, 5, 7, 12, 4, 8, 9, 3, 2, 10]⟩,
  ⟨1720, 47, 110, 3, 3, [11, 1, 6, 0, 7, 5, 12, 8, 4, 9, 3, 10, 2]⟩,
  ⟨110, 3, 1800, 49, 4, [2, 6, 1, 7, 0, 8, 12, 5, 9, 4, 10, 3, 11]⟩,
  ⟨1800, 49, 1580, 43, 4, [2, 6, 1, 7, 0, 8, 12, 9, 5, 4, 10, 11, 3]⟩,
  ⟨1580, 43, 184, 5, 4, [3, 2, 6, 1, 7, 0, 8, 9, 12, 5, 4, 10, 11]⟩,
  ⟨184, 5, 1880, 51, 4, [3, 6, 2, 1, 7, 8, 0, 9, 12, 5, 10, 4, 11]⟩,
  ⟨1880, 51, 332, 9, 4, [3, 6, 2, 1, 7, 8, 0, 9, 12, 10, 5, 11, 4]⟩,
  ⟨332, 9, 480, 13, 4, [4, 3, 6, 2, 1, 7, 8, 0, 9, 10, 12, 5, 11]⟩,
  ⟨480, 13, 850, 23, 4, [4, 6, 3, 2, 1, 7, 8, 9, 0, 10, 12, 11, 5]⟩,
  ⟨850, 23, 37, 1, 4, [5, 4, 6, 3, 2, 1, 7, 8, 9, 0, 10, 11, 12]⟩,
  ⟨37, 1, 260, 7, 2, [12, 5, 4, 6, 3, 2, 1, 7, 8, 9, 0, 10, 11]⟩,
  ⟨260, 7, 1600, 43, 2, [12, 5, 6, 4, 3, 2, 7, 1, 8, 9, 10, 0, 11]⟩,
  ⟨1600, 43, 1080, 29, 2, [12, 5, 6, 4, 3, 7, 2, 8, 1, 9, 10, 0, 11]⟩,
  ⟨1080, 29, 410, 11, 2, [12, 6, 5, 4, 3, 7, 2, 8, 1, 9, 10, 11, 0]⟩,
  ⟨410, 11, 112, 3, 2, [12, 6, 5, 4, 7, 3, 8, 2, 9, 1, 10, 11, 0]⟩,
  ⟨112, 3, 860, 23, 2, [12, 6, 5, 4, 7, 8, 3, 9, 2, 1, 10, 11, 0]⟩,
  ⟨860, 23, 1760, 47, 2, [0, 6, 12, 5, 7, 4, 8, 9, 3, 2, 10, 1, 11]⟩,
  ⟨1760, 47, 75, 2, 2, [0, 6, 12, 7, 5, 8, 4, 9, 3, 10, 2, 11, 1]⟩,
  ⟨75, 2, 1840, 49, 2, [0, 6, 12, 7, 8, 5, 9, 4, 10, 3, 11, 2, 1]⟩,
  ⟨1840, 49, 1540, 41, 2, [0, 6, 12, 7, 8, 9, 5, 4, 10, 11, 3, 2, 1]⟩,
  ⟨1540, 41, 188, 5, 2, [1, 0, 6, 7, 12, 8, 9, 5, 4, 10, 11, 3, 2]⟩,
  ⟨188, 5, 790, 21, 2, [1, 0, 6, 7, 12, 8, 9, 5, 10, 4, 11, 3, 2]⟩,
  ⟨790, 21, 640, 17, 2, [2, 1, 0, 6, 7, 8, 12, 9, 5, 10, 4, 11, 3]⟩,
  ⟨640, 17, 1620, 43, 2, [2, 1, 0, 6, 7, 8, 12, 9, 10, 5, 11, 4, 3]⟩,
  ⟨1620, 43, 490, 13, 2, [3, 2, 1, 0, 6, 7, 8, 9, 12, 10, 5, 11, 4]⟩,
  ⟨490, 13, 340, 9, 2, [3, 2, 1, 0, 6, 7, 8, 9, 12, 10, 11, 5, 4]⟩,
  ⟨340, 9, 870, 23, 2, [4, 3, 2, 0, 1, 7, 6, 8, 9, 10, 12, 11, 5]⟩,
  ⟨870, 23, 720, 19, 2, [5, 4, 3, 2, 0, 1, 7, 6, 8, 9, 10, 11, 12]⟩,
  ⟨720, 19, 38, 1, 2, [5, 4, 3, 0, 2, 1, 7, 8, 6, 9, 10, 11, 12]⟩,
  ⟨38, 1, 800, 21, 2, [12, 5, 4, 0, 3, 2, 1, 7, 8, 9, 6, 10, 11]⟩,
  ⟨800, 21, 1640, 43, 2, [12, 5, 4, 0, 3, 2, 7, 1, 8, 9, 6, 10, 11]⟩,
  ⟨1640, 43, 420, 11, 2, [12, 5, 4, 0, 3, 7, 2, 8, 1, 9, 6, 10, 11]⟩,
  ⟨420, 11, 344, 9, 2, [12, 5, 0, 4, 7, 3, 8, 2, 9, 1, 10, 6, 11]⟩,
  ⟨344, 9, 880, 23, 2, [12, 5, 0, 4, 7, 8, 3, 9, 2, 1, 10, 6, 11]⟩,
  ⟨880, 23, 1800, 47, 2, [12, 0, 5, 7, 4, 8, 9, 3, 2, 10, 1, 11, 6]⟩,
  ⟨1800, 47, 115, 3, 2, [12, 0, 7, 5, 8, 4, 9, 3, 10, 2, 11, 1, 6]⟩]

def certs9 : List CC := [
  ⟨115, 3, 1880, 49, 2, [12, 7, 0, 8, 5, 9, 4, 10, 3, 11, 2, 6, 1]⟩,
  ⟨1880, 49, 192, 5, 2, [12, 7, 0, 8, 9, 5, 4, 10, 11, 3, 2, 6, 1]⟩,
  ⟨192, 5, 1960, 51, 2, [12, 7, 8, 0, 9, 5, 10, 4, 11, 3, 6, 2, 1]⟩,
  ⟨1960, 51, 500, 13, 2, [12, 7, 8, 0, 9, 10, 5, 11, 4, 3, 6, 2, 1]⟩,
  ⟨500, 13, 1580, 41, 2, [12, 7, 8, 9, 0, 10, 11, 5, 4, 6, 3, 2, 1]⟩,
  ⟨1580, 41, 270, 7, 2, [1, 7, 12, 8, 9, 0, 10, 11, 5, 4, 6, 3, 2]⟩,
  ⟨270, 7, 1660, 43, 2, [2, 1, 7, 8, 12, 9, 10, 0, 11, 5, 6, 4, 3]⟩,
  ⟨1660, 43, 1120, 29, 2, [3, 2, 1, 7, 8, 9, 12, 10, 0, 11, 5, 6, 4]⟩,
  ⟨1120, 29, 116, 3, 2, [3, 2, 1, 7, 8, 9, 12, 10, 11, 0, 6, 5, 4]⟩,
  ⟨116, 3, 890, 23, 2, [4, 3, 2, 1, 7, 8, 9, 10, 12, 11, 0, 6, 5]⟩,
  ⟨890, 23, 660, 17, 2, [5, 4, 3, 2, 1, 7, 8, 9, 10, 11, 12, 0, 6]⟩,
  ⟨660, 17, 39, 1, 2, [6, 5, 4, 3, 2, 1, 7, 8, 9, 10, 11, 0, 12]⟩,
  ⟨39, 1, 820, 21, 0, [12, 6, 5, 4, 3, 2, 1, 7, 8, 9, 10, 11, 0]⟩,
  ⟨820, 21, 1680, 43, 0, [12, 6, 5, 4, 3, 2, 7, 1, 8, 9, 10, 11, 0]⟩,
  ⟨1680, 43, 430, 11, 0, [12, 6, 5, 4, 3, 7, 2, 8, 1, 9, 10, 11, 0]⟩,
  ⟨430, 11, 352, 9, 0, [12, 6, 5, 4, 7, 3, 8, 2, 9, 1, 10, 11, 0]⟩,
  ⟨352, 9, 900, 23, 0, [12, 6, 5, 4, 7, 8, 3, 9, 2, 1, 10, 11, 0]⟩,
  ⟨900, 23, 1840, 47, 0, [0, 6, 12, 5, 7, 4, 8, 9, 3, 2, 10, 1, 11]⟩,
  ⟨1840, 47, 235, 6, 0, [0, 6, 12, 7, 5, 8, 4, 9, 3, 10, 2, 11, 1]⟩,
  ⟨235, 6, 1920, 49, 0, [0, 6, 12, 7, 8, 5, 9, 4, 10, 3, 11, 2, 1]⟩,
  ⟨1920, 49, 196, 5, 0, [0, 6, 12, 7, 8, 9, 5, 4, 10, 11, 3, 2, 1]⟩,
  ⟨196, 5, 2000, 51, 0, [0, 6, 12, 7, 8, 9, 5, 10, 4, 11, 3, 2, 1]⟩,
  ⟨2000, 51, 510, 13, 0, [0, 6, 12, 7, 8, 9, 10, 5, 11, 4, 3, 2, 1]⟩,
  ⟨510, 13, 1620, 41, 0, [0, 6, 12, 7, 8, 9, 10, 11, 5, 4, 3, 2, 1]⟩,
  ⟨1620, 41, 830, 21, 0, [1, 0, 6, 7, 12, 8, 9, 10, 11, 5, 4, 3, 2]⟩,
  ⟨830, 21, 1700, 43, 0, [2, 1, 0, 6, 7, 8, 12, 9, 10, 11, 5, 4, 3]⟩,
  ⟨1700, 43, 356, 9, 0, [3, 2, 1, 0, 6, 7, 8, 9, 12, 10, 11, 5, 4]⟩,
  ⟨356, 9, 910, 23, 0, [4, 3, 2, 1, 0, 6, 7, 8, 9, 10, 12, 11, 5]⟩,
  ⟨910, 23, 40, 1, 0, [5, 4, 3, 2, 1, 0, 6, 7, 8, 9, 10, 11, 12]⟩,
  ⟨40, 1, 930, 23, 0, [12, 11, 10, 9, 8, 7, 6, 0, 1, 2, 3, 4, 5]⟩,
  ⟨930, 23, 364, 9, 0, [5, 11, 12, 10, 9, 8, 7, 6, 0, 1, 2, 3, 4]⟩,
  ⟨364, 9, 1740, 43, 0, [4, 5, 11, 10, 12, 9, 8, 7, 6, 0, 1, 2, 3]⟩,
  ⟨1740, 43, 850, 21, 0, [3, 4, 5, 11, 10, 9, 12, 8, 7, 6, 0, 1, 2]⟩,
  ⟨850, 21, 1660, 41, 0, [2, 3, 4, 5, 11, 10, 9, 8, 12, 7, 6, 0, 1]⟩,
  ⟨1660, 41, 530, 13, 0, [1, 2, 3, 4, 5, 11, 10, 9, 8, 7, 12, 6, 0]⟩,
  ⟨530, 13, 2080, 51, 1, [1, 2, 3, 4, 11, 5, 10, 9, 8, 7, 12, 6, 0]⟩,
  ⟨2080, 51, 204, 5, 2, [1, 2, 3, 11, 4, 10, 5, 9, 8, 7, 12, 6, 0]⟩,
  ⟨204, 5, 2000, 49, 2, [1, 2, 3, 11, 10, 4, 5, 9, 8, 7, 12, 6, 0]⟩,
  ⟨2000, 49, 245, 6, 3, [1, 2, 11, 3, 10, 4, 9, 5, 8, 7, 12, 6, 0]⟩,
  ⟨245, 6, 1920, 47, 4, [1, 11, 2, 10, 3, 9, 4, 8, 5, 7, 12, 6, 0]⟩,
  ⟨1920, 47, 940, 23, 4, [11, 1, 10, 2, 3, 9, 8, 4, 7, 5, 12, 6, 0]⟩,
  ⟨940, 23, 368, 9, 5, [0, 11, 10, 1, 2, 9, 3, 8, 7, 4, 5, 6, 12]⟩,
  ⟨368, 9, 450, 11, 5, [0, 11, 10, 1, 9, 2, 8, 3, 7, 4, 5, 6, 12]⟩,
  ⟨450, 11, 1760, 43, 5, [0, 11, 10, 9, 1, 8, 2, 7, 3, 4, 5, 6, 12]⟩,
  ⟨1760, 43, 860, 21, 5, [0, 11, 10, 9, 8, 1, 7, 2, 3, 4, 5, 6, 12]⟩,
  ⟨860, 21, 41, 1, 5, [0, 11, 10, 9, 8, 7, 1, 2, 3, 4, 5, 6, 12]⟩]

def allCerts : List CC :=
  certs0 ++ certs1 ++ certs2 ++ certs3 ++ certs4 ++ certs5 ++ certs6 ++ certs7 ++ certs8 ++ certs9

/-! ### Kernel-checked facts about the certificates -/

/-- The certificate of `[a + 40, b + 40)` obtained by periodicity. -/
def CC.shift (c : CC) : CC := ⟨c.pa + 40 * c.qa, c.qa, c.pb + 40 * c.qb, c.qb, c.sig, c.ord⟩

/-- The intervals used for the prime number theorem: `[1, 41)` and its translate `[41, 81)`. -/
def Lfull : List CC := allCerts ++ allCerts.map CC.shift

/-- Range checks: `-2 ≤ sig ≤ 10`, `1 ≤ a`, `b ≤ 81`. -/
def boundsOK (c : CC) : Bool :=
  decide (-2 ≤ c.sig) && decide (c.sig ≤ 10) && decide (c.qa ≤ c.pa) && decide (c.pb ≤ 81 * c.qb)

theorem certs0_ok : certs0.all ccOK = true := by decide +kernel

theorem certs1_ok : certs1.all ccOK = true := by decide +kernel

theorem certs2_ok : certs2.all ccOK = true := by decide +kernel

theorem certs3_ok : certs3.all ccOK = true := by decide +kernel

theorem certs4_ok : certs4.all ccOK = true := by decide +kernel

theorem certs5_ok : certs5.all ccOK = true := by decide +kernel

theorem certs6_ok : certs6.all ccOK = true := by decide +kernel

theorem certs7_ok : certs7.all ccOK = true := by decide +kernel

theorem certs8_ok : certs8.all ccOK = true := by decide +kernel

theorem certs9_ok : certs9.all ccOK = true := by decide +kernel

theorem allCerts_ok : allCerts.all ccOK = true := by
  simp only [allCerts, List.all_append, certs0_ok, certs1_ok, certs2_ok, certs3_ok, certs4_ok,
    certs5_ok, certs6_ok, certs7_ok, certs8_ok, certs9_ok, Bool.and_self]

theorem allCerts_chain : chainFrom (1, 1) allCerts (41, 1) = true := by decide +kernel

theorem Lfull_chain : chainFrom (1, 1) Lfull (81, 1) = true := by decide +kernel

theorem Lfull_iv : Lfull.all ivOK = true := by decide +kernel

theorem Lfull_bounds : Lfull.all boundsOK = true := by decide +kernel

theorem Lfull_length : Lfull.length = 1532 := by decide +kernel

/-- Fixed-point scale for the numerical margin. -/
def Sfix : ℤ := 10 ^ 15

/-- `Sfix · (10 - σ) (1/a - 1/b)`, rounded up. -/
def Uterm (c : CC) : ℤ :=
  (Sfix * (10 - c.sig) * c.qa) / c.pa + 1 - (Sfix * (10 - c.sig) * c.qb) / c.pb

def Tint : ℤ := (Lfull.map Uterm).sum + (12 * Sfix) / 81 + 1

theorem Tint_le : 100 * Tint ≤ 897 * Sfix := by decide +kernel

/-! ### Lower bounds for `Vl` from the certificates -/

lemma boundsOK_spec (c : CC) (h : boundsOK c = true) :
    -2 ≤ c.sig ∧ c.sig ≤ 10 ∧ c.qa ≤ c.pa ∧ c.pb ≤ 81 * c.qb := by
  unfold boundsOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

lemma Lfull_boundsOK (c : CC) (hc : c ∈ Lfull) :
    -2 ≤ c.sig ∧ c.sig ≤ 10 ∧ c.qa ≤ c.pa ∧ c.pb ≤ 81 * c.qb :=
  boundsOK_spec c (List.all_eq_true.1 Lfull_bounds c hc)

lemma Lfull_ivOK (c : CC) (hc : c ∈ Lfull) : ivOK c = true :=
  List.all_eq_true.1 Lfull_iv c hc

lemma allCerts_sub (c : CC) (hc : c ∈ allCerts) : c ∈ Lfull := List.mem_append_left _ hc

theorem Vl_ge_of_cert (c : CC) (hc : c ∈ allCerts) (x y : ℚ) (hxa : c.a ≤ x) (hxb : x < c.b)
    (hR : Realizable x y) : c.sig ≤ Vl x y := by
  have hok : ccOK c = true := List.all_eq_true.1 allCerts_ok c hc
  have e : Vl x y = Vl x (y - ⌊y⌋) := by
    have := Vl_add_int x (y - ⌊y⌋) ⌊y⌋
    rw [sub_add_cancel] at this
    exact this
  rw [e]
  have hR' : Realizable x (y - ⌊y⌋) := by
    have := Realizable_shift hR 0 (-⌊y⌋)
    simpa [sub_eq_add_neg] using this
  exact ccOK_sound c hok x (y - ⌊y⌋) hxa hxb (Int.fract_nonneg y) (Int.fract_lt_one y) hR'

lemma CC.shift_a (c : CC) (hq : c.qa ≠ 0) : c.shift.a = c.a + 40 := by
  unfold CC.shift CC.a
  have : (c.qa : ℚ) ≠ 0 := by exact_mod_cast hq
  push_cast
  field_simp

lemma CC.shift_b (c : CC) (hq : c.qb ≠ 0) : c.shift.b = c.b + 40 := by
  unfold CC.shift CC.b
  have : (c.qb : ℚ) ≠ 0 := by exact_mod_cast hq
  push_cast
  field_simp

theorem Vl_ge_Lfull (c : CC) (hc : c ∈ Lfull) (x y : ℚ) (hxa : c.a ≤ x) (hxb : x < c.b)
    (hR : Realizable x y) : c.sig ≤ Vl x y := by
  rcases List.mem_append.1 hc with h | h
  · exact Vl_ge_of_cert c h x y hxa hxb hR
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 h
    obtain ⟨hqa, hqb, -⟩ := ivOK_lt c₀ (Lfull_ivOK c₀ (allCerts_sub c₀ hc₀))
    rw [CC.shift_a c₀ hqa.ne'] at hxa
    rw [CC.shift_b c₀ hqb.ne'] at hxb
    have e : Vl x y = Vl (x - 40) y := by
      have := Vl_add_40 (x - 40) y 1
      rw [show x - 40 + 40 * ((1 : ℤ) : ℚ) = x by push_cast; ring] at this
      exact this
    rw [e]
    have hR' : Realizable (x - 40) y := by
      have := Realizable_shift hR (-1) 0
      simpa [sub_eq_add_neg] using this
    exact Vl_ge_of_cert c₀ hc₀ (x - 40) y (by linarith) (by linarith) hR'

theorem Vl_lower (x y : ℚ) (hR : Realizable x y) : -2 ≤ Vl x y := by
  set t : ℤ := ⌊(x - 1) / 40⌋ with ht
  set x' : ℚ := x - 40 * t with hx'
  have h1 : (t : ℚ) ≤ (x - 1) / 40 := Int.floor_le _
  have h2 : (x - 1) / 40 < t + 1 := Int.lt_floor_add_one _
  have hx'1 : 1 ≤ x' := by rw [hx']; linarith
  have hx'2 : x' < 41 := by rw [hx']; linarith
  have e : Vl x y = Vl x' y := by
    have := Vl_add_40 x' y t
    rw [show x' + 40 * (t : ℚ) = x by rw [hx']; ring] at this
    exact this
  rw [e]
  obtain ⟨c, hc, hca, hcb⟩ := chainFrom_cover allCerts (1, 1) (41, 1) allCerts_chain x'
    (by norm_num; exact hx'1) (by norm_num; exact hx'2)
  have hR' : Realizable x' y := by
    have := Realizable_shift hR (-t) 0
    simpa [hx', sub_eq_add_neg] using this
  have := Vl_ge_of_cert c hc x' y hca hcb hR'
  have hs := (Lfull_boundsOK c (allCerts_sub c hc)).1
  linarith

/-! ### The numerical margin -/

lemma list_sum_mul_left {α : Type*} (L : List α) (f : α → ℝ) (s : ℝ) :
    (L.map fun a => s * f a).sum = s * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma list_sum_intCast {α : Type*} (L : List α) (f : α → ℤ) :
    (((L.map f).sum : ℤ) : ℝ) = (L.map fun a => (f a : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]

lemma Uterm_bound (c : CC) (hiv : ivOK c = true) (hb : -2 ≤ c.sig ∧ c.sig ≤ 10 ∧ c.qa ≤ c.pa) :
    (Sfix : ℝ) * (((10 - c.sig : ℤ) : ℝ) * (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))) ≤
      (Uterm c : ℝ) := by
  obtain ⟨hqa, hqb, hab⟩ := ivOK_lt c hiv
  have hpa : 0 < c.pa := by linarith [hb.2.2]
  have hpb : 0 < c.pb := by
    have ha0 : (0 : ℚ) < c.a := by
      unfold CC.a
      have : (0 : ℚ) < c.pa := by exact_mod_cast hpa
      have : (0 : ℚ) < c.qa := by exact_mod_cast hqa
      positivity
    have hb0 : (0 : ℚ) < c.b := ha0.trans hab
    unfold CC.b at hb0
    have hqb' : (0 : ℚ) < c.qb := by exact_mod_cast hqb
    have : (0 : ℚ) < c.pb := by
      by_contra hneg
      push Not at hneg
      have : (c.pb : ℚ) / c.qb ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hqb'.le
      linarith
    exact_mod_cast this
  set w : ℤ := 10 - c.sig with hw
  have hA := Int.lt_ediv_add_one_mul_self (Sfix * w * c.qa) hpa
  have hB := Int.ediv_mul_le (Sfix * w * c.qb) hpb.ne'
  have hpaR : (0 : ℝ) < c.pa := by exact_mod_cast hpa
  have hpbR : (0 : ℝ) < c.pb := by exact_mod_cast hpb
  have hqaR : (0 : ℝ) < c.qa := by exact_mod_cast hqa
  have hqbR : (0 : ℝ) < c.qb := by exact_mod_cast hqb
  have hA' : (((Sfix * w * c.qa : ℤ)) : ℝ) / c.pa < (((Sfix * w * c.qa) / c.pa : ℤ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hpaR]
    have : ((Sfix * w * c.qa : ℤ) : ℝ) < ((((Sfix * w * c.qa) / c.pa + 1) * c.pa : ℤ) : ℝ) := by
      exact_mod_cast hA
    push_cast at this ⊢
    linarith
  have hB' : ((((Sfix * w * c.qb) / c.pb : ℤ)) : ℝ) ≤ (((Sfix * w * c.qb : ℤ)) : ℝ) / c.pb := by
    rw [le_div_iff₀ hpbR]
    have : (((((Sfix * w * c.qb) / c.pb) * c.pb : ℤ)) : ℝ) ≤ ((Sfix * w * c.qb : ℤ) : ℝ) := by
      exact_mod_cast hB
    push_cast at this ⊢
    linarith
  have ea : 1 / ((c.a : ℚ) : ℝ) = (c.qa : ℝ) / c.pa := by
    unfold CC.a; push_cast; field_simp
  have eb : 1 / ((c.b : ℚ) : ℝ) = (c.qb : ℝ) / c.pb := by
    unfold CC.b; push_cast; field_simp
  rw [ea, eb]
  unfold Uterm
  rw [← hw]
  push_cast at hA' hB' ⊢
  have e1 : (Sfix : ℝ) * ((w : ℝ) * ((c.qa : ℝ) / c.pa - (c.qb : ℝ) / c.pb)) =
      (Sfix : ℝ) * w * c.qa / c.pa - (Sfix : ℝ) * w * c.qb / c.pb := by ring
  rw [e1]
  linarith

theorem margin_T : (Lfull.map fun c => ((10 - c.sig : ℤ) : ℝ) *
    (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))).sum + 12 / 81 ≤ 897 / 100 := by
  have hS : (0 : ℝ) < Sfix := by unfold Sfix; norm_num
  have h1 : (Sfix : ℝ) * (Lfull.map fun c => ((10 - c.sig : ℤ) : ℝ) *
      (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))).sum ≤ ((Lfull.map Uterm).sum : ℝ) := by
    rw [← list_sum_mul_left, list_sum_intCast]
    apply list_sum_le
    intro c hc
    obtain ⟨h1, h2, h3, -⟩ := Lfull_boundsOK c hc
    exact Uterm_bound c (Lfull_ivOK c hc) ⟨h1, h2, h3⟩
  have h2 : (Sfix : ℝ) * (12 / 81) ≤ (((12 * Sfix) / 81 : ℤ) : ℝ) + 1 := by
    have := Int.lt_ediv_add_one_mul_self (12 * Sfix) (by norm_num : (0 : ℤ) < 81)
    have : ((12 * Sfix : ℤ) : ℝ) < ((((12 * Sfix) / 81 + 1) * 81 : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith
  have h3 : ((100 * Tint : ℤ) : ℝ) ≤ ((897 * Sfix : ℤ) : ℝ) := by exact_mod_cast Tint_le
  unfold Tint at h3
  simp only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_ofNat] at h3
  have h4 : (Sfix : ℝ) * ((Lfull.map fun c => ((10 - c.sig : ℤ) : ℝ) *
      (1 / ((c.a : ℚ) : ℝ) - 1 / ((c.b : ℚ) : ℝ))).sum + 12 / 81) ≤ (Sfix : ℝ) * (897 / 100) := by
    rw [mul_add]
    linarith
  exact le_of_mul_le_mul_left h4 hS

/-! ### Assembly for configuration `E` -/

lemma log_Dodd (n : ℕ) (h : Fin 6 → ℤ) :
    Real.log (Dodd n h : ℝ) = ∑ q ∈ oddPrimesLE n, (Eexp n h q : ℝ) * Real.log q := by
  unfold Dodd
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro q _
    rw [Real.log_pow]
  · intro q hq
    simp only [oddPrimesLE, mem_filter] at hq
    have : (0 : ℝ) < q := by exact_mod_cast hq.2.1.pos
    positivity

lemma configE_pos (m : ℕ) : ∀ i : Fin 5, 0 ≤ configE.h m i.succ := by
  intro i
  rw [configE_h]
  fin_cases i <;> simp [hE]

lemma odd_of_mem_oddPrimesLE {n q : ℕ} (hq : q ∈ oddPrimesLE n) : Odd q := by
  simp only [oddPrimesLE, mem_filter] at hq
  exact hq.2.1.odd_of_ne_two hq.2.2

/-- The residue-level exponent bound at a large prime, from the certificates. -/
lemma Eexp_le_cert (m q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ≤ 40 * m)
    (hsq : 2 * (40 * m) < q ^ 2) (σ : ℤ) (hσ : σ ≤ 10)
    (hV : ∀ y : ℚ, Realizable (((40 * m : ℕ) : ℚ) / q) y → σ ≤ Vl (((40 * m : ℕ) : ℚ) / q) y) :
    (Eexp (40 * m) (configE.h m) q : ℤ) ≤ 10 - σ := by
  have hodd : Odd q := hq.odd_of_ne_two hq2
  apply Eexp_le_large (40 * m) (configE.h m) q hqn hsq σ hσ
  intro k hk
  have e : Wlev (40 * m) (configE.h m) q k = Vl (((40 * m : ℕ) : ℚ) / q) ((k : ℚ) / q) :=
    Wlev_eq_Vl m q k hodd hk
  rw [e]
  exact hV _ (realizable_disc m q k hodd)


end Den

set_option linter.unusedVariables false in
open Den in
theorem Denominators_proof (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hCI : Stmt_CrudeInt) :
    Stmt_Denominators configE deltaE := by
  intro hPNT
  refine ⟨fun m => Dfull (configE.n m) (configE.h m), ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun m =>
      Dfull_clears _ _ (configE.adm m) (configE_pos m) hCI
  · intro ε hε
    have hmain := log_sum_bound hPNT (fun m q => Eexp (40 * m) (configE.h m) q) Lfull
      Lfull_chain Lfull_ivOK
      (fun c hc => ⟨(Lfull_boundsOK c hc).1, (Lfull_boundsOK c hc).2.1⟩)
      (fun c hc => by
        obtain ⟨-, -, h3, -⟩ := Lfull_boundsOK c hc
        obtain ⟨hqa, -, -⟩ := ivOK_lt c (Lfull_ivOK c hc)
        unfold CC.a
        have hqa' : (0 : ℚ) < c.qa := by exact_mod_cast hqa
        rw [le_div_iff₀ hqa', one_mul]
        exact_mod_cast h3)
      (fun c hc => by
        obtain ⟨-, -, -, h4⟩ := Lfull_boundsOK c hc
        obtain ⟨-, hqb, -⟩ := ivOK_lt c (Lfull_ivOK c hc)
        unfold CC.b
        have hqb' : (0 : ℚ) < c.qb := by exact_mod_cast hqb
        rw [div_le_iff₀ hqb']
        exact_mod_cast h4)
      (by rw [Lfull_length]; norm_num)
      margin_T
      (fun m q hq hsq => Eexp_le_small (40 * m) (configE.h m) (configE.adm m) q
        (odd_of_mem_oddPrimesLE hq))
      (fun m q hq hsq => by
        have hq' := hq
        simp only [oddPrimesLE, mem_filter, mem_range] at hq'
        obtain ⟨hqn, hqp, hq2⟩ := hq'
        have := Eexp_le_cert m q hqp hq2 (by omega) hsq (-2) (by norm_num)
          (fun y hy => Vl_lower _ y hy)
        have : ((Eexp (40 * m) (configE.h m) q : ℤ) : ℝ) ≤ ((10 - (-2) : ℤ) : ℝ) := by
          exact_mod_cast this
        push_cast at this ⊢
        linarith)
      (fun m q c hc hqp hq2 hqn hsq h1 h2 => by
        have hq0 : (0 : ℚ) < q := by exact_mod_cast hqp.pos
        have e : ((((40 * m : ℕ) : ℚ) / q : ℚ) : ℝ) = (40 * m : ℝ) / q := by push_cast; ring
        have h1' : c.a ≤ ((40 * m : ℕ) : ℚ) / q := by
          rw [← e] at h1
          exact_mod_cast h1
        have h2' : ((40 * m : ℕ) : ℚ) / q < c.b := by
          rw [← e] at h2
          exact_mod_cast h2
        have := Eexp_le_cert m q hqp hq2 hqn hsq c.sig (Lfull_boundsOK c hc).2.1
          (fun y hy => Vl_ge_Lfull c hc _ y h1' h2' hy)
        have : ((Eexp (40 * m) (configE.h m) q : ℤ) : ℝ) ≤ ((10 - c.sig : ℤ) : ℝ) := by
          exact_mod_cast this
        push_cast at this ⊢
        linarith)
      ε hε
    filter_upwards [hmain] with m hm
    rw [Dfull_mul_norm]
    have hpos : (0 : ℝ) < (Dodd (configE.n m) (configE.h m) : ℝ) := by
      exact_mod_cast Dodd_pos _ _
    rw [← Real.exp_log hpos, log_Dodd]
    apply Real.exp_le_exp.2
    rw [configE_n, deltaE]
    push_cast
    exact hm

end Zeta2.Pair

end
