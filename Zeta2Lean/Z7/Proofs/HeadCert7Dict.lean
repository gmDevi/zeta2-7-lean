module

public import Zeta2Lean.Z7.Proofs.ResCert7Floor

@[expose] public section

/-!
# `HeadCert7`, part 1: the local model from 23 floor values; sweep states

Helper of `HeadCert7.lean` (notes: `notes/HeadCert7.md`).

## The 23-line system `HC7.sysH`

`sysE7` (the 20 lines of the floor-sum form of `E`, `ResCert7Floor.lean`) plus three lines of
weight `0` (in units of `x/80`, `ℓ_j(x) = (A_j x + B_j)/80`):
* `j = 20`: `x/2` (floor), `j = 21`: `x/2` (ceiling), `j = 22`: `x/2 + 1/2` (floor).

## The dictionary

At a discrete point `x = 40u/q`, `y = k₀/q` (`q` odd, `k₀ < q`) the floor values
`F_j = F_j(ℓ_j(x) - y)` are integer divisions (`HC7.hF`), and the literal local model is a
function of them (`HC7.localModel_eq_cmodF`):
* pole `j` exists iff `j ≤ F₁₂ = ⌊x - y⌋`; its order is
  `1 + ∑_{l=1}^{3} [F_{16+l} ≤ j ≤ F_{12+l}]` (`HC7.apoleF`);
* the zero at `w = -(2t - 1)` has multiplicity `∑_m [t ≤ F_m + 1] - [t ≤ F_{m+6} + 1]`
  (`HC7.muF`);
* the `δ`-zero is present iff `F₂₁ = F₂₀` (`x/2 - y ∈ ℤ`), at `w = -2 F₂₀`;
* pole `j` has `max(0, j - F₂₂)` bad pairs of sign `+1` if `j > F₂₀`, else `max(0, F₂₂ - j)`
  of sign `-1` (none at the centre `j = F₂₀` when `F₂₁ = F₂₀`) (`HC7.psgn`, `HC7.pcnt`).

## Sweep states

`HC7.sweep` (a variant of `ECert7.ok_sound`): for a valid certificate (`HC7.okS`: the lines do
not cross on `[a, b]`, sorted by their fractional parts, no floor line directly before an identical
ceiling line) and a realizable point (`HC7.Real'`: a floor line and a ceiling line are integral
together only if they are identical), the vector of floor values is one of the `n + 1` prefix
states `HC7.stF` (the first `p` lines of `ord` have dropped by one).
-/

set_option linter.style.longLine false

open Finset

namespace Zeta2.Z7

namespace HC7

/-! ## The 23-line system -/

/-- `sysE7` plus `x/2` (floor, ceiling) and `x/2 + 1/2` (floor), weights `0`. -/
def sysH : LineSys7 where
  n := 23
  A := [70, 66, 66, 62, 58, 54, 10, 14, 14, 18, 22, 26, 80, 76, 72, 68, 0, 4, 8, 12, 40, 40, 40]
  B := [-40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    40]
  W := [1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 0, 0, 0]
  C := [false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, true, true, true, false, true, false]
  K := -4

lemma sysH_n : sysH.n = 23 := rfl

lemma sysH_la (j : ℕ) (hj : j < 20) : sysH.la j = sysE7.la j := by
  interval_cases j <;> rfl

lemma sysH_lb (j : ℕ) (hj : j < 20) : sysH.lb j = sysE7.lb j := by
  interval_cases j <;> rfl

lemma sysH_lc (j : ℕ) (hj : j < 20) : sysH.lc j = sysE7.lc j := by
  interval_cases j <;> rfl

lemma sysH_fl (j : ℕ) (hj : j < 20) (x y : ℚ) :
    sysH.fl j (sysH.ell j x - y) = sysE7.fl j (sysE7.ell j x - y) := by
  unfold LineSys7.fl LineSys7.ell
  rw [sysH_la j hj, sysH_lb j hj, sysH_lc j hj]

/-! ## The local model as a function of the floor vector -/

/-- The pole order `1 + ∑_{l=1}^{3} [F_{16+l} ≤ j ≤ F_{12+l}]`. -/
def apoleF (F : ℕ → ℤ) (j : ℤ) : ℤ :=
  1 + (if F 17 ≤ j ∧ j ≤ F 13 then 1 else 0) + (if F 18 ≤ j ∧ j ≤ F 14 then 1 else 0) +
    (if F 19 ≤ j ∧ j ≤ F 15 then 1 else 0)

/-- `[t ≤ F + 1]`. -/
def ind (t F : ℤ) : ℤ := if t ≤ F + 1 then 1 else 0

/-- The multiplicity of the zero `w = -(2t - 1)`. -/
def muF (F : ℕ → ℤ) (t : ℤ) : ℤ :=
  (ind t (F 0) - ind t (F 6)) + (ind t (F 1) - ind t (F 7)) + (ind t (F 2) - ind t (F 8)) +
    (ind t (F 3) - ind t (F 9)) + (ind t (F 4) - ind t (F 10)) + (ind t (F 5) - ind t (F 11))

/-- The sign of the bad pairs of pole `j`. -/
def psgn (F : ℕ → ℤ) (j : ℤ) : ℤ := if F 20 < j then 1 else -1

/-- The number of bad pairs of pole `j`. -/
def pcnt (F : ℕ → ℤ) (j : ℤ) : ℕ := if F 20 < j then (j - F 22).toNat else (F 22 - j).toNat

/-- The local model as a function of the floor vector (same list layout as `localModel`). -/
def cmodF (X : ℕ) (F : ℕ → ℤ) : LocalType where
  items :=
    ((List.range (X + 1)).filterMap fun j : ℕ =>
        if (j : ℤ) ≤ F 12 then some (-(2 * (j : ℤ)), -apoleF F j) else none) ++
    (((List.range (X + 2) : List ℕ) : List ℤ).filterMap fun t : ℤ =>
        if muF F t ≠ 0 then some (-(2 * t - 1), muF F t) else none) ++
    (if F 21 = F 20 then [(-(2 * F 20), 1)] else [])
  pairs :=
    (List.range (X + 1)).flatMap fun j : ℕ =>
      if (j : ℤ) ≤ F 12 ∧ ¬ (F 21 = F 20 ∧ (j : ℤ) = F 20) then
        (List.range (pcnt F j)).map fun t : ℕ =>
          (-(2 * (j : ℤ)), -(2 * (j : ℤ)) + psgn F j * (2 * (t : ℤ) + 1), psgn F j)
      else []

/-- `cmodF` only reads `F 0, …, F 22`. -/
lemma cmodF_congr (X : ℕ) (F G : ℕ → ℤ) (h : ∀ j < 23, F j = G j) : cmodF X F = cmodF X G := by
  have e : ∀ j, j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] → F j = G j := by
    intro j hj
    apply h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  unfold cmodF apoleF muF psgn pcnt
  simp only [e 0 (by simp), e 1 (by simp), e 2 (by simp), e 3 (by simp), e 4 (by simp),
    e 5 (by simp), e 6 (by simp), e 7 (by simp), e 8 (by simp), e 9 (by simp), e 10 (by simp),
    e 11 (by simp), e 12 (by simp), e 13 (by simp), e 14 (by simp), e 15 (by simp),
    e 17 (by simp), e 18 (by simp), e 19 (by simp), e 20 (by simp), e 21 (by simp),
    e 22 (by simp)]

/-! ## The floor vector at a discrete point -/

/-- The 23 floor values at `(40u/q, k₀/q)` as integer divisions. -/
def hF (u q k₀ : ℕ) (j : ℕ) : ℤ :=
  if j < 12 then RC7.zc q (sysH.la j / 2 * u - k₀) - 1
  else if j = 22 then RC7.zc q (sysH.la j / 2 * u - k₀)
  else if sysH.lc j then (sysH.la j / 2 * u - k₀ - 1) / q + 1
  else (sysH.la j / 2 * u - k₀) / q

section hFvals

variable (u q k₀ : ℕ)

lemma hF_12 : hF u q k₀ 12 = (40 * u - k₀) / q := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_13 : hF u q k₀ 13 = (38 * u - k₀) / q := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_14 : hF u q k₀ 14 = (36 * u - k₀) / q := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_15 : hF u q k₀ 15 = (34 * u - k₀) / q := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_17 : hF u q k₀ 17 = (2 * u - k₀ - 1) / q + 1 := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_18 : hF u q k₀ 18 = (4 * u - k₀ - 1) / q + 1 := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_19 : hF u q k₀ 19 = (6 * u - k₀ - 1) / q + 1 := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_20 : hF u q k₀ 20 = (20 * u - k₀) / q := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_21 : hF u q k₀ 21 = (20 * u - k₀ - 1) / q + 1 := by
  simp [hF, sysH, LineSys7.la, LineSys7.lc]
lemma hF_22 : hF u q k₀ 22 = RC7.zc q (20 * u - k₀) := by
  simp [hF, sysH, LineSys7.la]

end hFvals

/-! ## Integer-division facts -/

lemma le_div_iff' {q : ℕ} (hq : 0 < q) (j M : ℤ) : j ≤ M / q ↔ j * q ≤ M :=
  Int.le_ediv_iff_mul_le (by exact_mod_cast hq)

lemma ceil_le_iff' {q : ℕ} (hq : 0 < q) (j M : ℤ) : (M - 1) / q + 1 ≤ j ↔ M ≤ j * q := by
  have h := Int.ediv_lt_iff_lt_mul (a := M - 1) (b := j) (c := q) (by exact_mod_cast hq)
  omega

lemma div_lt_iff' {q : ℕ} (hq : 0 < q) (j M : ℤ) : M / q < j ↔ M < j * q :=
  Int.ediv_lt_iff_lt_mul (by exact_mod_cast hq)

/-- `⌈M/q⌉ = ⌊M/q⌋` iff `q ∣ M`. -/
lemma ceil_eq_floor_iff {q : ℕ} (hq : 0 < q) (M : ℤ) :
    (M - 1) / q + 1 = M / q ↔ (q : ℤ) ∣ M := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  constructor
  · intro h
    have h1 := (le_div_iff' hq (M / q) M).1 le_rfl
    have h2 : M - 1 < ((M - 1) / q + 1) * q :=
      (div_lt_iff' hq ((M - 1) / q + 1) (M - 1)).1 (by omega)
    rw [h] at h2
    have : M = M / q * q := by linarith
    exact ⟨M / q, by rw [mul_comm]; exact this⟩
  · rintro ⟨m, rfl⟩
    have e1 : (q : ℤ) * m / q = m := Int.mul_ediv_cancel_left m hq'.ne'
    have e2 : ((q : ℤ) * m - 1) / q = m - 1 := by
      have := (Int.ediv_emod_unique hq').2
        (show ((q : ℤ) - 1) + q * (m - 1) = (q : ℤ) * m - 1 ∧ 0 ≤ (q : ℤ) - 1 ∧ (q : ℤ) - 1 < q from
          ⟨by ring, by omega, by omega⟩)
      exact this.1
    rw [e1, e2]
    ring

/-! ## The dictionary: poles -/

section dict

variable {u q k₀ : ℕ}

lemma pole_cond (hq : 0 < q) (j : ℕ) : (j : ℤ) ≤ hF u q k₀ 12 ↔ k₀ + j * q ≤ 40 * u := by
  rw [hF_12, le_div_iff' hq]
  have hP : (j : ℤ) * q = ((j * q : ℕ) : ℤ) := by push_cast; ring
  rw [hP]
  generalize j * q = P
  omega

lemma lev_cond (hq : 0 < q) (j : ℕ) (A B : ℕ) :
    (((A : ℤ) * u - k₀ - 1) / q + 1 ≤ (j : ℤ) ∧ (j : ℤ) ≤ ((B : ℤ) * u - k₀) / q) ↔
      (A * u ≤ k₀ + j * q ∧ k₀ + j * q ≤ B * u) := by
  rw [ceil_le_iff' hq, le_div_iff' hq]
  have hP : (j : ℤ) * q = ((j * q : ℕ) : ℤ) := by push_cast; ring
  rw [hP]
  generalize j * q = P
  have hA : ((A : ℤ) * u) = ((A * u : ℕ) : ℤ) := by push_cast; ring
  have hB : ((B : ℤ) * u) = ((B * u : ℕ) : ℤ) := by push_cast; ring
  rw [hA, hB]
  generalize A * u = a
  generalize B * u = b
  omega

lemma apole_eq (hq : 0 < q) (j : ℕ) (hj : k₀ + j * q ≤ 40 * u) :
    ((apole u (k₀ + j * q) : ℕ) : ℤ) = apoleF (hF u q k₀) j := by
  rw [RC7.apole_ind u _ hj]
  unfold apoleF
  rw [hF_17, hF_13, hF_18, hF_14, hF_19, hF_15]
  have e1 := lev_cond (u := u) (k₀ := k₀) hq j 2 38
  have e2 := lev_cond (u := u) (k₀ := k₀) hq j 4 36
  have e3 := lev_cond (u := u) (k₀ := k₀) hq j 6 34
  push_cast at e1 e2 e3
  simp only [e1, e2, e3]

lemma pole_item (hq : 0 < q) (j : ℕ) :
    (if k₀ + j * q ≤ 40 * u then some (-(2 * (j : ℤ)), -((apole u (k₀ + j * q) : ℕ) : ℤ))
      else none) =
    (if (j : ℤ) ≤ hF u q k₀ 12 then some (-(2 * (j : ℤ)), -apoleF (hF u q k₀) j) else none) := by
  by_cases h : k₀ + j * q ≤ 40 * u
  · rw [ite_eq_left h, ite_eq_left ((pole_cond hq j).2 h), apole_eq hq j h]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((pole_cond hq j).1 h'))]

/-! ## The dictionary: zeros -/

lemma ind_eq (hq : 0 < q) (t : ℕ) (m : ℕ) (hm : m < 12) :
    ind (t : ℤ) (hF u q k₀ m) =
      if (t : ℤ) * q ≤ sysH.la m / 2 * u - k₀ + ((q : ℤ) - 1) / 2 then 1 else 0 := by
  unfold ind hF
  rw [ite_eq_left hm]
  unfold RC7.zc
  rw [sub_add_cancel]
  exact if_congr (le_div_iff' hq _ _) rfl rfl

lemma zero_mult (hq : Odd q) (t : ℕ) :
    (if 0 ≤ (k₀ : ℤ) + t * q - (q + 1) / 2 ∧ (k₀ : ℤ) + t * q - (q + 1) / 2 < 40 * u ∧
        mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat ≠ 0 then
      ((mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat : ℕ) : ℤ) else 0) = muF (hF u q k₀) t := by
  rw [RC7.zero_term u q k₀ t hq]
  have hq0 := hq.pos
  unfold muF
  rw [ind_eq hq0 t 0 (by norm_num), ind_eq hq0 t 1 (by norm_num), ind_eq hq0 t 2 (by norm_num),
    ind_eq hq0 t 3 (by norm_num), ind_eq hq0 t 4 (by norm_num), ind_eq hq0 t 5 (by norm_num),
    ind_eq hq0 t 6 (by norm_num), ind_eq hq0 t 7 (by norm_num), ind_eq hq0 t 8 (by norm_num),
    ind_eq hq0 t 9 (by norm_num), ind_eq hq0 t 10 (by norm_num), ind_eq hq0 t 11 (by norm_num)]
  simp only [Fin.sum_univ_six, eta, sysH, LineSys7.la]
  norm_num
  rfl

lemma zero_item (hq : Odd q) (t : ℕ) :
    (if 0 ≤ (k₀ : ℤ) + t * q - (q + 1) / 2 ∧ (k₀ : ℤ) + t * q - (q + 1) / 2 < 40 * u ∧
        mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat ≠ 0 then
      some (-(2 * (t : ℤ) - 1), ((mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat : ℕ) : ℤ))
      else none) =
    (if muF (hF u q k₀) t ≠ 0 then some (-(2 * (t : ℤ) - 1), muF (hF u q k₀) t) else none) := by
  have hz := zero_mult (u := u) (k₀ := k₀) hq t
  by_cases h : 0 ≤ (k₀ : ℤ) + t * q - (q + 1) / 2 ∧ (k₀ : ℤ) + t * q - (q + 1) / 2 < 40 * u ∧
        mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat ≠ 0
  · rw [ite_eq_left h] at hz
    have hne : muF (hF u q k₀) t ≠ 0 := by
      rw [← hz]
      exact_mod_cast h.2.2
    rw [ite_eq_left h, ite_eq_left hne, hz]
  · rw [ite_eq_right h] at hz
    have hne : ¬ muF (hF u q k₀) t ≠ 0 := by
      rw [← hz]
      simp
    rw [ite_eq_right h, ite_eq_right hne]

/-! ## The dictionary: the `δ`-zero -/

lemma dvd_iff_ceil (hq : Odd q) :
    hF u q k₀ 21 = hF u q k₀ 20 ↔ (q : ℤ) ∣ 20 * u - k₀ := by
  rw [hF_21, hF_20, ceil_eq_floor_iff hq.pos]

lemma delta_cond (hq : Odd q) :
    hF u q k₀ 21 = hF u q k₀ 20 ↔ (2 * (k₀ : ℤ) - 40 * u) % q = 0 := by
  rw [dvd_iff_ceil hq, ← Int.dvd_iff_emod_eq_zero]
  have e : 2 * (k₀ : ℤ) - 40 * u = -2 * (20 * u - k₀) := by ring
  rw [e]
  constructor
  · intro h
    exact Dvd.dvd.mul_left h _
  · intro h
    have hcop : IsCoprime (q : ℤ) (-2) := by
      rw [IsCoprime.neg_right_iff]
      obtain ⟨s, hs⟩ := hq
      refine ⟨1, -(s : ℤ), ?_⟩
      push_cast [hs]
      ring
    exact hcop.dvd_of_dvd_mul_left h

lemma delta_item (hq : Odd q) :
    (if (2 * (k₀ : ℤ) - 40 * u) % q = 0 then [((2 * (k₀ : ℤ) - 40 * u) / q, (1 : ℤ))] else []) =
    (if hF u q k₀ 21 = hF u q k₀ 20 then [(-(2 * hF u q k₀ 20), (1 : ℤ))] else []) := by
  by_cases h : (2 * (k₀ : ℤ) - 40 * u) % q = 0
  · have h' := (delta_cond (u := u) (k₀ := k₀) hq).2 h
    rw [ite_eq_left h, ite_eq_left h', hF_20]
    have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
    obtain ⟨m, hm⟩ := (dvd_iff_ceil (u := u) (k₀ := k₀) hq).1 h'
    have e1 : 2 * (k₀ : ℤ) - 40 * u = q * (-2 * m) := by linear_combination (-2 : ℤ) * hm
    rw [e1, hm, Int.mul_ediv_cancel_left _ hq0.ne', Int.mul_ediv_cancel_left _ hq0.ne']
    ring_nf
  · have h' : ¬ hF u q k₀ 21 = hF u q k₀ 20 := fun h' => h ((delta_cond hq).1 h')
    rw [ite_eq_right h, ite_eq_right h']

/-! ## The dictionary: bad pairs -/

lemma flatMap_singleton_cast : ∀ l : List ℕ,
    List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun t : ℕ => (t : ℤ))
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_singleton_cast l]

/-- The coerced range `((List.range N : List ℕ) : List ℤ)`. -/
lemma coe_range (N : ℕ) :
    ((List.range N : List ℕ) : List ℤ) = (List.range N).map (fun t : ℕ => (t : ℤ)) := by
  simp only [← flatMap_singleton_cast]
  rfl

/-- `filterMap` over a range with an initial-segment condition. -/
lemma filterMap_range_lt {β : Type*} (g : ℕ → β) (T : ℕ) : ∀ N : ℕ,
    (List.range N).filterMap (fun t : ℕ => if t < T then some (g t) else none) =
      (List.range (min T N)).map g
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.filterMap_append, filterMap_range_lt g T N]
    by_cases h : N < T
    · rw [min_eq_right (by omega : N + 1 ≤ T), min_eq_right (by omega : N ≤ T)]
      simp [h, List.range_succ]
    · rw [min_eq_left (by omega : T ≤ N + 1), min_eq_left (by omega : T ≤ N)]
      simp [h]

lemma pair_exists (hq : Odd q) (j : ℕ) :
    (k₀ + j * q ≤ 40 * u ∧ (k₀ : ℤ) + j * q - 20 * u ≠ 0) ↔
      ((j : ℤ) ≤ hF u q k₀ 12 ∧ ¬ (hF u q k₀ 21 = hF u q k₀ 20 ∧ (j : ℤ) = hF u q k₀ 20)) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.pos.ne'
  rw [pole_cond hq.pos j, dvd_iff_ceil hq, hF_20]
  apply and_congr_right
  intro _
  constructor
  · rintro hd ⟨⟨m, hm⟩, hj⟩
    apply hd
    rw [hm, Int.mul_ediv_cancel_left _ hq0] at hj
    rw [hj]
    linear_combination -hm
  · intro h hd
    apply h
    have hM : (20 * (u : ℤ) - k₀) = q * j := by linear_combination -hd
    refine ⟨⟨j, hM⟩, ?_⟩
    rw [hM, Int.mul_ediv_cancel_left _ hq0]

lemma pair_sign (hq : Odd q) (j : ℕ) (hd : (k₀ : ℤ) + j * q - 20 * u ≠ 0) :
    ((k₀ : ℤ) + j * q - 20 * u).sign = psgn (hF u q k₀) j := by
  unfold psgn
  rw [hF_20]
  by_cases h : (20 * (u : ℤ) - k₀) / q < j
  · rw [ite_eq_left h]
    have := (div_lt_iff' hq.pos _ _).1 h
    exact Int.sign_eq_one_of_pos (by linarith)
  · rw [ite_eq_right h]
    have := (div_lt_iff' hq.pos (j : ℤ) (20 * (u : ℤ) - k₀)).not.1 h
    exact Int.sign_eq_neg_one_of_neg (by omega)

lemma pair_cond (hq : Odd q) (j t : ℕ) (hd : (k₀ : ℤ) + j * q - 20 * u ≠ 0) :
    ((2 * (t : ℤ) + 1) * q < 2 * |(k₀ : ℤ) + j * q - 20 * u|) ↔ t < pcnt (hF u q k₀) j := by
  obtain ⟨s, hs⟩ := hq
  have hq0 : 0 < q := by omega
  have hqs : ((q : ℤ) - 1) / 2 = s := by push_cast [hs]; omega
  unfold pcnt
  rw [hF_20, hF_22]
  unfold RC7.zc
  rw [hqs]
  have hP : (j : ℤ) * q = ((j * q : ℕ) : ℤ) := by push_cast; ring
  have hQ : (t : ℤ) * q = ((t * q : ℕ) : ℤ) := by push_cast; ring
  by_cases h : (20 * (u : ℤ) - k₀) / q < j
  · rw [ite_eq_left h]
    have hpos := (div_lt_iff' hq0 _ _).1 h
    rw [abs_of_pos (by linarith), Int.lt_toNat]
    have e : (t : ℤ) < j - (20 * u - k₀ + s) / q ↔ (20 * (u : ℤ) - k₀ + s) / q < j - t := by omega
    rw [e, div_lt_iff' hq0]
    have e2 : ((j : ℤ) - t) * q = j * q - t * q := by ring
    rw [e2]
    have e3 : (2 * (t : ℤ) + 1) * q = 2 * (t * q) + q := by ring
    rw [e3]
    rw [hP, hQ] at *
    generalize j * q = P at *
    generalize t * q = Q at *
    push_cast [hs] at *
    omega
  · rw [ite_eq_right h]
    have hneg : ¬ (20 * (u : ℤ) - k₀ < j * q) := fun h' => h ((div_lt_iff' hq0 _ _).2 h')
    have hlt : (k₀ : ℤ) + j * q - 20 * u < 0 := by omega
    rw [abs_of_neg hlt, Int.lt_toNat]
    have e : (t : ℤ) < (20 * u - k₀ + s) / q - j ↔ (t : ℤ) + j + 1 ≤ (20 * (u : ℤ) - k₀ + s) / q := by
      omega
    rw [e, le_div_iff' hq0]
    have e2 : ((t : ℤ) + j + 1) * q = t * q + j * q + q := by ring
    rw [e2]
    have e3 : (2 * (t : ℤ) + 1) * q = 2 * (t * q) + q := by ring
    rw [e3]
    rw [hP, hQ] at *
    generalize j * q = P at *
    generalize t * q = Q at *
    push_cast [hs] at *
    omega

lemma pair_list (hq : Odd q) (j : ℕ) (hd : (k₀ : ℤ) + j * q - 20 * u ≠ 0) :
    List.filterMap (fun t : ℤ =>
        if (2 * t + 1) * (q : ℤ) < 2 * |(k₀ : ℤ) + j * q - 20 * u| then
          some (-(2 * (j : ℤ)), -(2 * (j : ℤ)) + ((k₀ : ℤ) + j * q - 20 * u).sign * (2 * t + 1),
            ((k₀ : ℤ) + j * q - 20 * u).sign)
        else none)
      ((List.range (((k₀ : ℤ) + j * q - 20 * u).natAbs / q + 1) : List ℕ) : List ℤ) =
    (List.range (pcnt (hF u q k₀) j)).map fun t : ℕ =>
      (-(2 * (j : ℤ)), -(2 * (j : ℤ)) + psgn (hF u q k₀) j * (2 * (t : ℤ) + 1),
        psgn (hF u q k₀) j) := by
  rw [coe_range, List.filterMap_map, pair_sign hq j hd]
  set T := pcnt (hF u q k₀) j with hT
  set N := ((k₀ : ℤ) + j * q - 20 * u).natAbs / q + 1 with hN
  have hTN : T ≤ N := by
    by_contra hlt
    push Not at hlt
    have hc := (pair_cond (u := u) (k₀ := k₀) hq j N hd).2 hlt
    have hq0 : 0 < q := hq.pos
    have h1 : ((k₀ : ℤ) + j * q - 20 * u).natAbs < N * q := by
      rw [hN]
      have := Nat.div_add_mod (((k₀ : ℤ) + j * q - 20 * u).natAbs) q
      have := Nat.mod_lt (((k₀ : ℤ) + j * q - 20 * u).natAbs) hq0
      nlinarith
    have h2 : (|(k₀ : ℤ) + j * q - 20 * u|) < (N : ℤ) * q := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h1
    nlinarith
  have hfun : ∀ t ∈ List.range N,
      ((fun t : ℤ =>
        if (2 * t + 1) * (q : ℤ) < 2 * |(k₀ : ℤ) + j * q - 20 * u| then
          some (-(2 * (j : ℤ)), -(2 * (j : ℤ)) + psgn (hF u q k₀) j * (2 * t + 1),
            psgn (hF u q k₀) j)
        else none) ∘ (fun t : ℕ => (t : ℤ))) t =
      (fun t : ℕ => if t < T then some ((fun t : ℕ =>
        (-(2 * (j : ℤ)), -(2 * (j : ℤ)) + psgn (hF u q k₀) j * (2 * (t : ℤ) + 1),
          psgn (hF u q k₀) j)) t) else none) t := by
    intro t _
    simp only [Function.comp]
    exact if_congr (pair_cond hq j t hd) rfl rfl
  rw [List.filterMap_congr hfun, filterMap_range_lt, min_eq_left hTN]

/-- **The dictionary** (proof §4.8, Lemma 4.11): the literal local model is `cmodF` of the
floor vector `hF` (odd `q`). -/
theorem localModel_eq_cmodF (hq : Odd q) :
    localModel u q k₀ = cmodF (40 * u / q) (hF u q k₀) := by
  have hq0 := hq.pos
  unfold localModel cmodF
  congr 1
  · congr 1
    · congr 1
      · apply List.filterMap_congr
        intro j _
        exact pole_item hq0 j
      · apply List.filterMap_congr
        intro t ht
        rw [coe_range, List.mem_map] at ht
        obtain ⟨t', _, rfl⟩ := ht
        exact zero_item hq t'
    · exact delta_item hq
  · apply List.flatMap_congr
    intro j _
    by_cases h : k₀ + j * q ≤ 40 * u ∧ (k₀ : ℤ) + j * q - 20 * u ≠ 0
    · rw [ite_eq_left h, ite_eq_left ((pair_exists hq j).1 h)]
      exact pair_list hq j h.2
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((pair_exists hq j).2 h'))]

/-! ## The floor vector is the vector of floor values of `sysH` -/

/-- `hF` is the floor vector of `sysH` at the discrete point. -/
theorem hF_spec (hq : Odd q) (j : ℕ) (hj : j < 23) :
    hF u q k₀ j = sysH.fl j (sysH.ell j (((40 * u : ℕ) : ℚ) / q) - (k₀ : ℚ) / q) := by
  have hq0 := hq.pos
  by_cases h20 : j < 20
  · rw [sysH_fl j h20, RC7.fl_disc u q k₀ hq j h20]
    unfold hF RC7.gv
    rw [sysH_la j h20]
    by_cases h12 : j < 12
    · rw [ite_eq_left h12, ite_eq_left h12]
    · rw [ite_eq_right h12, ite_eq_right h12, ite_eq_right (by omega : j ≠ 22)]
      by_cases h16 : j < 16
      · have hc : sysH.lc j = false := by
          interval_cases j <;> first | omega | rfl
        rw [ite_eq_left h16, hc]
        rfl
      · have hc : sysH.lc j = true := by
          interval_cases j <;> first | omega | rfl
        rw [ite_eq_right h16, hc]
        rfl
  · have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hell : ∀ (A B : ℤ), A = 40 → ((A : ℚ) * (((40 * u : ℕ) : ℚ) / q) + B) / 80 - (k₀ : ℚ) / q =
        ((20 * u - k₀ : ℤ) : ℚ) / q + (B : ℚ) / 80 := by
      intro A B hA
      rw [RC7.ell_disc A B 20 (by omega) u q k₀ hq0]
    have hj' : j = 20 ∨ j = 21 ∨ j = 22 := by omega
    unfold LineSys7.fl LineSys7.ell
    rcases hj' with rfl | rfl | rfl
    · have hb : sysH.lb 20 = 0 := rfl
      have hc : sysH.lc 20 = false := rfl
      rw [hF_20, hell _ _ (by rfl), hb, hc]
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_zero, zero_div, add_zero]
      exact (Rat.floor_intCast_div_natCast _ _).symm
    · have hb : sysH.lb 21 = 0 := rfl
      have hc : sysH.lc 21 = true := rfl
      rw [hF_21, hell _ _ (by rfl), hb, hc]
      simp only [↓reduceIte, Int.cast_zero, zero_div, add_zero]
      rw [RC7.ceil_div q hq0]
    · have hb : sysH.lb 22 = 40 := rfl
      have hc : sysH.lc 22 = false := rfl
      rw [hF_22, hell _ _ (by rfl), hb, hc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have e : ((20 * u - k₀ : ℤ) : ℚ) / q + ((40 : ℤ) : ℚ) / 80 =
          (((20 * u - k₀ : ℤ) : ℚ) / q - 1 / 2) + 1 := by
        push_cast
        ring
      rw [e, Int.floor_add_one, RC7.floor_half q hq]
      ring

/-! ## `E` from the floor vector -/

/-- `E` as a function of the floor vector: the `sysE7` floor sum plus the `δ`-zero. -/
def EF (F : ℕ → ℤ) : ℤ :=
  ((List.range 20).map fun j => sysE7.lw j * F j).sum + sysE7.K + (if F 21 = F 20 then 1 else 0)

lemma EF_congr (F G : ℕ → ℤ) (h : ∀ j < 23, F j = G j) : EF F = EF G := by
  unfold EF
  rw [h 21 (by norm_num), h 20 (by norm_num)]
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [h j (by simp at hj; omega)]

/-- **`E` of a local model from its floor vector** (the floor-sum form, Lemma 4.12). -/
theorem localModel_E_eq_EF (hq : Odd q) (hk : k₀ < q) :
    (localModel u q k₀).E = EF (hF u q k₀) := by
  rw [localModel_E_eq_sysE7 u q k₀ hq hk]
  unfold EF LineSys7.val
  rw [ECert7.sum_range_eq_list]
  have e : ∀ j ∈ List.range sysE7.n,
      sysE7.lw j * sysE7.fl j (sysE7.ell j (((40 * u : ℕ) : ℚ) / q) - (k₀ : ℚ) / q) =
        sysE7.lw j * hF u q k₀ j := by
    intro j hj
    have hj' : j < 20 := by simpa [sysE7_n] using hj
    rw [hF_spec hq j (by omega), sysH_fl j hj']
  rw [List.map_congr_left e, sysE7_n]
  congr 1
  by_cases h : (2 * (k₀ : ℤ) - 40 * u) % q = 0
  · rw [ite_eq_left h, ite_eq_left ((delta_cond hq).2 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((delta_cond hq).1 h'))]

end dict

/-! ## Sweep states (a variant of `ECert7.ok_sound`) -/

/-- Realizability, generalized: a floor line and a ceiling line are integral at the same point only
if they are identical. -/
def Real' (S : LineSys7) (x y : ℚ) : Prop :=
  ∀ i < S.n, ∀ j < S.n, S.lc i = false → S.lc j = true → ∀ z z' : ℤ,
    S.ell i x - y = z → S.ell j x - y = z' → S.la i = S.la j ∧ S.lb i = S.lb j

/-- No floor line directly before an identical ceiling line in the order. -/
def noFC (S : LineSys7) : List ℕ → Bool
  | [] => true
  | [_] => true
  | r :: s :: rs =>
    !(decide (S.lc r = false) && decide (S.lc s = true) && decide (S.la r = S.la s) &&
        decide (S.lb r = S.lb s)) && noFC S (s :: rs)

/-- The certificate check (no bound `sig`: the states are examined one by one). -/
def okS (S : LineSys7) (c : ECert7) : Bool :=
  decide (0 < c.qa) && decide (0 < c.qb) && decide (c.pa * c.qb < c.pb * c.qa) &&
    c.ord.isPerm (List.range S.n) && c.ord.all (c.lineOK S) && c.chainOK S c.ord && noFC S c.ord

/-- The prefix state `p`: the first `p` lines of `ord` have dropped. -/
def stF (S : LineSys7) (c : ECert7) (p : ℕ) (j : ℕ) : ℤ :=
  c.N S j + (if S.lc j then 1 else 0) - (if j ∈ c.ord.take p then 1 else 0)

lemma chain_both (S : LineSys7) (c : ECert7) : ∀ L : List ℕ, c.chainOK S L = true →
    noFC S L = true →
    L.IsChain (fun r s => (c.sa S r ≤ c.sa S s ∧ c.sb S r ≤ c.sb S s) ∧
      ¬ (S.lc r = false ∧ S.lc s = true ∧ S.la r = S.la s ∧ S.lb r = S.lb s))
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.IsChain.singleton _
  | r :: s :: rs, h, h' => by
    simp only [ECert7.chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [noFC, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at h'
    refine List.IsChain.cons_cons ⟨⟨h.1.1, h.1.2⟩, ?_⟩ (chain_both S c (s :: rs) h.2 h'.2)
    rintro ⟨h1, h2, h3, h4⟩
    rcases h'.1 with ((h5 | h5) | h5) | h5 <;> contradiction

lemma mem_takeWhile_of_chain {α : Type*} (Q : α → Bool) :
    ∀ (L : List α), L.IsChain (fun a b => Q b = true → Q a = true) →
      ∀ a ∈ L, Q a = true → a ∈ L.takeWhile Q
  | [], _, a, ha, _ => by simp at ha
  | b :: L, h, a, ha, hQa => by
    have hQb : Q b = true := by
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact hQa
      · have ih := mem_takeWhile_of_chain Q L h.tail a ha' hQa
        cases L with
        | nil => simp at ha'
        | cons c L' =>
          rw [List.isChain_cons_cons] at h
          have hc : Q c = true := by
            by_contra hc
            simp [hc] at ih
          exact h.1 hc
    rw [List.takeWhile_cons, ite_eq_left hQb]
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_takeWhile_of_chain Q L h.tail a ha' hQa)

/-- **Sweep states**: under a valid certificate, at a realizable point of `[a, b) × [0, 1)` the
floor vector is one of the prefix states `stF S c p`, `p ≤ n`. -/
theorem sweep (S : LineSys7) (c : ECert7) (hc : okS S c = true) (x y : ℚ)
    (hxa : (c.pa : ℚ) / c.qa ≤ x) (hxb : x < (c.pb : ℚ) / c.qb) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hR : Real' S x y) :
    ∃ p ≤ S.n, ∀ j < S.n, S.fl j (S.ell j x - y) = stF S c p j := by
  simp only [okS, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hqa, hqb⟩, hab⟩, hperm⟩, hrows⟩, hchain⟩, hnofc⟩ := hc
  rw [List.isPerm_iff] at hperm
  rw [List.all_eq_true] at hrows
  have hchain' := chain_both S c _ hchain hnofc
  have hmem : ∀ j, j ∈ c.ord ↔ j < S.n := by
    intro j
    rw [hperm.mem_iff, List.mem_range]
  set a : ℚ := (c.pa : ℚ) / c.qa with ha_def
  set b : ℚ := (c.pb : ℚ) / c.qb with hb_def
  have hqa' : (0 : ℚ) < c.qa := by exact_mod_cast hqa
  have hqb' : (0 : ℚ) < c.qb := by exact_mod_cast hqb
  have hba : 0 < b - a := by
    have : (c.pa : ℚ) * c.qb < c.pb * c.qa := by exact_mod_cast hab
    rw [ha_def, hb_def, sub_pos, div_lt_div_iff₀ hqa' hqb']
    linarith
  set β : ℕ → ℚ := fun j => S.ell j x - (c.N S j : ℚ) with hβ
  have hrow : ∀ j ∈ c.ord,
      0 ≤ β j ∧ β j ≤ 1 ∧ (S.lc j = false → β j < 1) ∧
      (S.ell j a - c.N S j) * (80 * c.qa) = c.sa S j ∧
      (S.ell j b - c.N S j) * (80 * c.qb) = c.sb S j := by
    intro j hj
    have h := hrows j hj
    simp only [ECert7.lineOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨hu0, hu1⟩, hw0⟩, hw1⟩, hZ⟩ := h
    have hu' : (c.sa S j : ℚ) = 80 * c.qa * (S.ell j a - c.N S j) := by
      rw [ECert7.sa, LineSys7.sv_cast _ _ _ _ _ hqa'.ne']
    have hw' : (c.sb S j : ℚ) = 80 * c.qb * (S.ell j b - c.N S j) := by
      rw [ECert7.sb, LineSys7.sv_cast _ _ _ _ _ hqb'.ne']
    have h80a : (0 : ℚ) < 80 * c.qa := by positivity
    have h80b : (0 : ℚ) < 80 * c.qb := by positivity
    have hA0 : 0 ≤ S.ell j a - c.N S j := by
      have : (0 : ℚ) ≤ c.sa S j := by exact_mod_cast hu0
      rw [hu'] at this
      exact ECert7.nonneg_of_pos_mul h80a this
    have hA1 : S.ell j a - c.N S j ≤ 1 := by
      have : (c.sa S j : ℚ) ≤ 80 * c.qa := by exact_mod_cast hu1
      rw [hu'] at this
      exact ECert7.le_one_of_pos_mul h80a this
    have hB0 : 0 ≤ S.ell j b - c.N S j := by
      have : (0 : ℚ) ≤ c.sb S j := by exact_mod_cast hw0
      rw [hw'] at this
      exact ECert7.nonneg_of_pos_mul h80b this
    have hB1 : S.ell j b - c.N S j ≤ 1 := by
      have : (c.sb S j : ℚ) ≤ 80 * c.qb := by exact_mod_cast hw1
      rw [hw'] at this
      exact ECert7.le_one_of_pos_mul h80b this
    have hI := S.ell_interp j a b x (c.N S j)
    have hxa' : 0 ≤ x - a := by linarith
    have hbx : 0 < b - x := by linarith
    refine ⟨?_, ?_, ?_, by rw [hu']; ring, by rw [hw']; ring⟩
    · have : 0 ≤ (b - a) * β j := by
        simp only [hβ]; rw [hI]; positivity
      exact ECert7.nonneg_of_pos_mul hba this
    · have : (b - a) * β j ≤ (b - a) := by
        simp only [hβ]; rw [hI]; nlinarith
      exact ECert7.le_one_of_pos_mul hba this
    · intro hcj
      have hA1' : S.ell j a - c.N S j < 1 := by
        rcases hZ with hZ | hZ
        · rw [hcj] at hZ
          exact absurd hZ (by decide)
        · have : (c.sa S j : ℚ) < 80 * c.qa := by exact_mod_cast hZ
          rw [hu'] at this
          exact ECert7.lt_one_of_pos_mul h80a this
      have : (b - a) * β j < (b - a) := by
        simp only [hβ]; rw [hI]; nlinarith
      exact ECert7.lt_one_of_pos_mul hba this
  -- the drop indicator
  set Dd : ℕ → Bool := fun j => if S.lc j then decide (β j ≤ y) else decide (β j < y) with hDd
  have hfl : ∀ j ∈ c.ord, S.fl j (S.ell j x - y) =
      c.N S j + (if S.lc j then 1 else 0) - (if Dd j = true then 1 else 0) := by
    intro j hj
    obtain ⟨h0, h1, hfl1, -, -⟩ := hrow j hj
    have e : S.ell j x - y = (c.N S j : ℚ) + β j - y := by simp only [hβ]; ring
    unfold LineSys7.fl
    rw [e]
    cases hcj : S.lc j
    · rw [ECert7.floor_sweep _ _ _ h0 (hfl1 hcj) hy0 hy1]
      simp [hDd, hcj]
    · rw [ECert7.ceil_sweep _ _ _ h0 h1 hy0 hy1]
      simp [hDd, hcj]
  have hchainD : c.ord.IsChain (fun r s => Dd s = true → Dd r = true) := by
    have hsub : ∀ r ∈ c.ord, ∀ s ∈ c.ord,
        ((c.sa S r ≤ c.sa S s ∧ c.sb S r ≤ c.sb S s) ∧
          ¬ (S.lc r = false ∧ S.lc s = true ∧ S.la r = S.la s ∧ S.lb r = S.lb s)) →
        (Dd s = true → Dd r = true) := by
      intro r hr s hs ⟨hle, hnot⟩ hsy
      obtain ⟨-, -, -, hra, hrb⟩ := hrow r hr
      obtain ⟨-, -, -, hsa, hsb⟩ := hrow s hs
      have h1 : S.ell r a - c.N S r ≤ S.ell s a - c.N S s := by
        have : (c.sa S r : ℚ) ≤ c.sa S s := by exact_mod_cast hle.1
        rw [← hra, ← hsa] at this
        exact le_of_mul_le_mul_right this (by positivity)
      have h2 : S.ell r b - c.N S r ≤ S.ell s b - c.N S s := by
        have : (c.sb S r : ℚ) ≤ c.sb S s := by exact_mod_cast hle.2
        rw [← hrb, ← hsb] at this
        exact le_of_mul_le_mul_right this (by positivity)
      have hIr := S.ell_interp r a b x (c.N S r)
      have hIs := S.ell_interp s a b x (c.N S s)
      have hle' : (b - a) * β r ≤ (b - a) * β s := by
        simp only [hβ]
        rw [hIr, hIs]
        have hxa' : 0 ≤ x - a := by linarith
        have hbx : 0 ≤ b - x := by linarith
        nlinarith
      have hβrs := le_of_mul_le_mul_left hle' hba
      simp only [hDd] at hsy ⊢
      cases hcs : S.lc s <;> cases hcr : S.lc r <;>
        simp only [hcs, Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq]
          at hsy ⊢
      · linarith
      · linarith
      · by_contra hcon
        push Not at hcon
        have hr_eq : β r = y := le_antisymm (by linarith) hcon
        have hs_eq : β s = y := by linarith
        have hid := hR r ((hmem r).1 hr) s ((hmem s).1 hs) hcr hcs (c.N S r) (c.N S s)
          (by simp only [hβ] at hr_eq; linarith) (by simp only [hβ] at hs_eq; linarith)
        exact hnot ⟨hcr, hcs, hid.1, hid.2⟩
      · linarith
    exact List.IsChain.imp_of_mem_imp (fun r s hr hs hle => hsub r hr s hs hle) hchain'
  set P := c.ord.takeWhile Dd with hP
  have hpre : P = c.ord.take P.length := List.prefix_iff_eq_take.1 (List.takeWhile_prefix Dd)
  have hlen : c.ord.length = S.n := by
    rw [hperm.length_eq, List.length_range]
  refine ⟨P.length, ?_, ?_⟩
  · rw [← hlen]
    exact (List.takeWhile_prefix Dd).length_le
  · intro j hj
    have hjm := (hmem j).2 hj
    rw [hfl j hjm]
    unfold stF
    congr 1
    have hiff : Dd j = true ↔ j ∈ c.ord.take P.length := by
      rw [← hpre]
      constructor
      · intro hd
        exact mem_takeWhile_of_chain Dd c.ord hchainD j hjm hd
      · intro hm
        exact List.mem_takeWhile_imp hm
    by_cases hd : Dd j = true
    · rw [ite_eq_left hd, ite_eq_left (hiff.1 hd)]
    · rw [ite_eq_right hd, ite_eq_right (fun h => hd (hiff.2 h))]

/-! ## Realizability of the discrete points for `sysH` -/

lemma sysH_facts : ∀ i < 23, sysH.la i % 2 = 0 ∧ 0 ≤ sysH.la i ∧ sysH.la i ≤ 80 ∧
    (sysH.lb i = -40 ∨ sysH.lb i = 0 ∨ sysH.lb i = 40) ∧ (sysH.lc i = true → sysH.lb i = 0) := by
  decide

/-- A discrete point `(40u/q, k₀/q)` with `q > 40` prime, `q ∤ u` is realizable for `sysH`: a line
with `B = ±40` is never integral (`q` odd), and two integral lines with `B = 0` have
`q ∣ (A/2 - A'/2) u`, so `A = A'`. -/
theorem sysH_real_disc (u q k₀ : ℕ) (hq : q.Prime) (h40 : 40 < q) (hqu : ¬ q ∣ u) :
    Real' sysH (((40 * u : ℕ) : ℚ) / q) ((k₀ : ℚ) / q) := by
  have hq0 : 0 < q := hq.pos
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  obtain ⟨s, hs⟩ := hodd
  have hqz : (q : ℤ) = 2 * s + 1 := by exact_mod_cast hs
  have hqQ : (q : ℚ) ≠ 0 := by positivity
  intro i hi j hj hci hcj z z' h1 h2
  rw [sysH_n] at hi hj
  obtain ⟨hAi, -, hAi1, hBi, -⟩ := sysH_facts i hi
  obtain ⟨hAj, hAj0, hAj1, -, hBj⟩ := sysH_facts j hj
  have hAi0 : 0 ≤ sysH.la i := (sysH_facts i hi).2.1
  have hBj0 := hBj hcj
  unfold LineSys7.ell at h1 h2
  rw [RC7.ell_disc _ _ (sysH.la i / 2) (by omega) u q k₀ hq0] at h1
  rw [RC7.ell_disc _ _ (sysH.la j / 2) (by omega) u q k₀ hq0] at h2
  rw [hBj0] at h2
  have h2a : ((sysH.la j / 2 * u - k₀ : ℤ) : ℚ) / q = z' := by simpa using h2
  have h2b : ((sysH.la j / 2 * u - k₀ : ℤ) : ℚ) = (q : ℚ) * (z' : ℚ) := by
    rw [← h2a]
    field_simp
  have h2' : sysH.la j / 2 * u - k₀ = q * z' := by exact_mod_cast h2b
  have key : ∀ B : ℤ, sysH.lb i = B → ((sysH.la i / 2 * u - k₀ : ℤ) : ℚ) / q + (B : ℚ) / 80 = z →
      2 * (sysH.la i / 2 * u - k₀) * 40 + B * q = 80 * (q * z) := by
    intro B hB h
    have e : ((2 * (sysH.la i / 2 * u - k₀) * 40 + B * q : ℤ) : ℚ) =
        80 * ((q : ℚ) * (((sysH.la i / 2 * u - k₀ : ℤ) : ℚ) / q + (B : ℚ) / 80)) := by
      push_cast
      field_simp
      ring
    rw [h] at e
    exact_mod_cast e
  rcases hBi with hB | hB | hB
  · exfalso
    have := key (-40) hB (by rw [hB] at h1; exact h1)
    generalize sysH.la i / 2 * (u : ℤ) = X at this
    generalize (q : ℤ) * z = w at this
    omega
  · rw [hB] at h1
    have h1a : ((sysH.la i / 2 * u - k₀ : ℤ) : ℚ) / q = z := by simpa using h1
    have h1b : ((sysH.la i / 2 * u - k₀ : ℤ) : ℚ) = (q : ℚ) * (z : ℚ) := by
      rw [← h1a]
      field_simp
    have h1' : sysH.la i / 2 * u - k₀ = q * z := by exact_mod_cast h1b
    have hd : (sysH.la i / 2 - sysH.la j / 2) * (u : ℤ) = q * (z - z') := by
      linear_combination h1' - h2'
    have hdvd : (q : ℤ) ∣ (sysH.la i / 2 - sysH.la j / 2) * u := ⟨z - z', hd⟩
    have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    rcases hprime.dvd_or_dvd hdvd with h | h
    · have h0 : sysH.la i / 2 - sysH.la j / 2 = 0 := by
        apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h
        have : (sysH.la i / 2 - sysH.la j / 2).natAbs ≤ 40 := by omega
        simp only [Int.natAbs_natCast]
        omega
      exact ⟨by omega, by rw [hB, hBj0]⟩
    · exact absurd (Int.natCast_dvd_natCast.mp h) hqu
  · exfalso
    have := key 40 hB (by rw [hB] at h1; exact h1)
    generalize sysH.la i / 2 * (u : ℤ) = X at this
    generalize (q : ℤ) * z = w at this
    omega

end HC7

end Zeta2.Z7
