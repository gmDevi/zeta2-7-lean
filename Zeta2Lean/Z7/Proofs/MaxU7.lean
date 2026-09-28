module

public import Zeta2Lean.Z7.Statements
public import Zeta2Lean.Pair.Proofs.Landscape.Numerics

@[expose] public section

/-!
# Lemma G7: the certified maximum of the growth potential `U`

gap: 'growth' (certificate).  Difficulty 3.  No dependencies.

**Statement.** `Stmt_MaxU7 g7`: `U(κ) ≤ 0.71` for `κ ∈ [0, 1]`, where
`U(κ) = ∑_j w_j F(p_j - κ)`, `F(z) = z log|z| - z` (`Upot`, 18 terms `upotTerms`, breakpoints
`p_j ∈ (1/40)ℤ ∩ [0, 1]`).  True maximum `0.7067022242…` at `κ* = 0.1067347…` and `1 - κ*`.

**Certificate (chords and tangents).**  `F'' (z) = 1/z`, so `F` is convex on `[0, ∞)` and concave
on `(-∞, 0]`.  `[0, 1]` is cut into 42 boxes `[a, b]` with endpoints in `(1/80) ℤ`, refining
the `1/40` grid (so no breakpoint `p_j` lies inside a box).  On a box, each summand
`w_j F(p_j - κ)` is convex or concave in `κ`:
* convex: bounded above by its chord (`chord_up_pos`, `chord_up_neg`), i.e. by the values
  `w_j F(p_j - a)`, `w_j F(p_j - b)`;
* concave: bounded above by its tangent at the midpoint `m` (`tangent_up_pos`, `tangent_up_neg`).
The sum of these majorants is affine in `κ`, so it suffices to bound it at `κ = a` and `κ = b`
(`EA ≤ 0.71`, `EB ≤ 0.71`); these are closed statements about `log` at rationals with
denominators `≤ 320`, certified by the `artanh` enclosures of
`Zeta2Lean/Pair/Proofs/Landscape/Numerics.lean` (`log_le_of_le_mul`, …).

The box list, the log table and the box proofs are generated (exact `Fraction` arithmetic) by
`Zeta2Lean/Z7/Proofs/MaxU7_gen.py`; the worst box bound is recorded there.
-/

set_option linter.style.longLine false

open Real

noncomputable section

namespace Zeta2.Z7

namespace MaxU7Cert

open Zeta2.Pair.Landscape

/-! ## Convexity of `F(z) = z log|z| - z` -/

theorem Fx_zero : Fx 0 = 0 := by simp [Fx]

theorem Fx_neg (z : ℝ) : Fx (-z) = -Fx z := by
  unfold Fx; rw [abs_neg]; ring

/-- Tangent (lower) bound on `[0, ∞)`. -/
theorem tangent_pos {z0 z : ℝ} (h0 : 0 < z0) (hz : 0 ≤ z) :
    Fx z0 + Real.log |z0| * (z - z0) ≤ Fx z := by
  unfold Fx
  rw [abs_of_pos h0, abs_of_nonneg hz]
  rcases hz.eq_or_lt with h | hz'
  · subst h; simp only [zero_mul, sub_zero, zero_sub]; nlinarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hz' h0)
    rw [Real.log_div hz'.ne' h0.ne', inv_div] at h1
    have h2 : z * (1 - z0 / z) = z - z0 := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 hz'.le
    rw [h2] at h3
    nlinarith

/-- Tangent (upper) bound on `(-∞, 0]`. -/
theorem tangent_neg {z0 z : ℝ} (h0 : z0 < 0) (hz : z ≤ 0) :
    Fx z ≤ Fx z0 + Real.log |z0| * (z - z0) := by
  have h := tangent_pos (z0 := -z0) (z := -z) (by linarith) (by linarith)
  rw [Fx_neg, Fx_neg, abs_neg] at h
  nlinarith

/-- Chord (upper) bound on `[0, ∞)`. -/
theorem chord_pos {z1 z z2 : ℝ} (h0 : 0 ≤ z1) (h1 : z1 ≤ z) (h2 : z ≤ z2) :
    (z2 - z1) * Fx z ≤ (z - z1) * Fx z2 + (z2 - z) * Fx z1 := by
  rcases (le_trans h0 h1).eq_or_lt with h | hz
  · have e1 : z1 = 0 := le_antisymm (h ▸ h1) h0
    subst e1; rw [← h, Fx_zero]; simp
  · have t1 := tangent_pos (z0 := z) (z := z1) hz h0
    have t2 := tangent_pos (z0 := z) (z := z2) hz (by linarith)
    have p1 := mul_le_mul_of_nonneg_left t1 (sub_nonneg.2 h2)
    have p2 := mul_le_mul_of_nonneg_left t2 (sub_nonneg.2 h1)
    nlinarith

/-- Chord (lower) bound on `(-∞, 0]`. -/
theorem chord_neg {z1 z z2 : ℝ} (h1 : z1 ≤ z) (h2 : z ≤ z2) (h3 : z2 ≤ 0) :
    (z - z1) * Fx z2 + (z2 - z) * Fx z1 ≤ (z2 - z1) * Fx z := by
  have h := chord_pos (z1 := -z2) (z := -z) (z2 := -z1) (by linarith) (by linarith) (by linarith)
  rw [Fx_neg, Fx_neg, Fx_neg] at h
  nlinarith

/-! ## Summand majorants -/

theorem chord_up_pos {w z1 z z2 : ℝ} (hw : 0 ≤ w) (h0 : 0 ≤ z1) (h1 : z1 ≤ z) (h2 : z ≤ z2) :
    (z2 - z1) * (w * Fx z) ≤ (z - z1) * (w * Fx z2) + (z2 - z) * (w * Fx z1) := by
  have := mul_le_mul_of_nonneg_left (chord_pos h0 h1 h2) hw
  nlinarith

theorem chord_up_neg {w z1 z z2 : ℝ} (hw : w ≤ 0) (h1 : z1 ≤ z) (h2 : z ≤ z2) (h3 : z2 ≤ 0) :
    (z2 - z1) * (w * Fx z) ≤ (z - z1) * (w * Fx z2) + (z2 - z) * (w * Fx z1) := by
  have := mul_le_mul_of_nonpos_left (chord_neg h1 h2 h3) hw
  nlinarith

theorem tangent_up_pos {w z0 z : ℝ} (hw : 0 ≤ w) (h0 : z0 < 0) (hz : z ≤ 0) :
    w * Fx z ≤ w * (Fx z0 + Real.log |z0| * (z - z0)) :=
  mul_le_mul_of_nonneg_left (tangent_neg h0 hz) hw

theorem tangent_up_neg {w z0 z : ℝ} (hw : w ≤ 0) (h0 : 0 < z0) (hz : 0 ≤ z) :
    w * Fx z ≤ w * (Fx z0 + Real.log |z0| * (z - z0)) :=
  mul_le_mul_of_nonpos_left (tangent_pos h0 hz) hw

/-- From bounds on `log |z|` to bounds on `F(z)` (`z ≥ 0`). -/
theorem Fx_bounds_pos {z lo hi : ℝ} (hz : 0 ≤ z) (hl : lo ≤ Real.log |z|) (hh : Real.log |z| ≤ hi) :
    z * lo - z ≤ Fx z ∧ Fx z ≤ z * hi - z := by
  unfold Fx
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hl hz], by nlinarith [mul_le_mul_of_nonneg_left hh hz]⟩

/-- From bounds on `log |z|` to bounds on `F(z)` (`z ≤ 0`). -/
theorem Fx_bounds_neg {z lo hi : ℝ} (hz : z ≤ 0) (hl : lo ≤ Real.log |z|) (hh : Real.log |z| ≤ hi) :
    z * hi - z ≤ Fx z ∧ Fx z ≤ z * lo - z := by
  unfold Fx
  exact ⟨by nlinarith [mul_le_mul_of_nonpos_left hh hz], by nlinarith [mul_le_mul_of_nonpos_left hl hz]⟩

theorem logabs_bounds {z q lo hi : ℝ} (hzq : |z| = q) (hl : lo ≤ Real.log q) (hh : Real.log q ≤ hi) :
    lo ≤ Real.log |z| ∧ Real.log |z| ≤ hi := by
  rw [hzq]; exact ⟨hl, hh⟩

/-- `U` written out. -/
theorem Upot_expand (κ : ℝ) :
    Upot κ = (1 : ℝ) * Fx ((0 : ℝ) / 40 - κ) + (1 : ℝ) * Fx ((2 : ℝ) / 40 - κ) + (1 : ℝ) * Fx ((4 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((5 : ℝ) / 40 - κ) + (1 : ℝ) * Fx ((6 : ℝ) / 40 - κ) + (-2 : ℝ) * Fx ((7 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((9 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((11 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((13 : ℝ) / 40 - κ) + (1 : ℝ) * Fx ((27 : ℝ) / 40 - κ) + (1 : ℝ) * Fx ((29 : ℝ) / 40 - κ) + (1 : ℝ) * Fx ((31 : ℝ) / 40 - κ) + (2 : ℝ) * Fx ((33 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((34 : ℝ) / 40 - κ) + (1 : ℝ) * Fx ((35 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((36 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((38 : ℝ) / 40 - κ) + (-1 : ℝ) * Fx ((40 : ℝ) / 40 - κ) := by
  simp only [Upot, upotTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-! ## Certified values of `log` and `F` at the grid points (generated) -/

theorem lq0 : (-5075173818003327 / 1000000000000000 : ℝ) ≤ Real.log (1 / 160 : ℝ) ∧ Real.log (1 / 160 : ℝ) ≤ (-1268793453286983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 160 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-5075173818003327 / 1000000000000000 : ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 160 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-1268793453286983 / 250000000000000 : ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq1 : (-4382026637203327 / 1000000000000000 : ℝ) ≤ Real.log (1 / 80 : ℝ) ∧ Real.log (1 / 80 : ℝ) ≤ (-1095506658211983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 80 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-4382026637203327 / 1000000000000000 : ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 80 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-1095506658211983 / 250000000000000 : ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq2 : (-79531230560121 / 20000000000000 : ℝ) ≤ Real.log (3 / 160 : ℝ) ∧ Real.log (3 / 160 : ℝ) ≤ (-795312305001209 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 160 : ℝ)) (z := (1 / 11 : ℝ)) (L := (-79531230560121 / 20000000000000 : ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 160 : ℝ)) (z := (1 / 11 : ℝ)) (U := (-795312305001209 / 200000000000000 : ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq3 : (-3688879456403327 / 1000000000000000 : ℝ) ≤ Real.log (1 / 40 : ℝ) ∧ Real.log (1 / 40 : ℝ) ≤ (-922219863136983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 40 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-3688879456403327 / 1000000000000000 : ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 40 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-922219863136983 / 250000000000000 : ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq4 : (-65668286944121 / 20000000000000 : ℝ) ≤ Real.log (3 / 80 : ℝ) ∧ Real.log (3 / 80 : ℝ) ≤ (-656682868941209 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 80 : ℝ)) (z := (1 / 11 : ℝ)) (L := (-65668286944121 / 20000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 80 : ℝ)) (z := (1 / 11 : ℝ)) (U := (-656682868941209 / 200000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq5 : (-2995732275603327 / 1000000000000000 : ℝ) ≤ Real.log (1 / 20 : ℝ) ∧ Real.log (1 / 20 : ℝ) ≤ (-748933068061983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 20 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-2995732275603327 / 1000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 20 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-748933068061983 / 250000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq6 : (-1438974626548709 / 500000000000000 : ℝ) ≤ Real.log (9 / 160 : ℝ) ∧ Real.log (9 / 160 : ℝ) ≤ (-2877949236433427 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (9 / 160 : ℝ)) (z := (2 / 7 : ℝ)) (L := (-1438974626548709 / 500000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (9 / 160 : ℝ)) (z := (2 / 7 : ℝ)) (U := (-2877949236433427 / 1000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq7 : (-108304247 / 39062500 : ℝ) ≤ Real.log (1 / 16 : ℝ) ∧ Real.log (1 / 16 : ℝ) ≤ (-6931471803 / 2500000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 16 : ℝ)) (z := (0 : ℝ)) (L := (-108304247 / 39062500 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 16 : ℝ)) (z := (0 : ℝ)) (U := (-6931471803 / 2500000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq8 : (-669319635848919 / 250000000000000 : ℝ) ≤ Real.log (11 / 160 : ℝ) ∧ Real.log (11 / 160 : ℝ) ≤ (-107091141655827 / 40000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (11 / 160 : ℝ)) (z := (1 / 21 : ℝ)) (L := (-669319635848919 / 250000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (11 / 160 : ℝ)) (z := (1 / 21 : ℝ)) (U := (-107091141655827 / 40000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq9 : (-51805343328121 / 20000000000000 : ℝ) ≤ Real.log (3 / 40 : ℝ) ∧ Real.log (3 / 40 : ℝ) ≤ (-518053432881209 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 40 : ℝ)) (z := (1 / 11 : ℝ)) (L := (-51805343328121 / 20000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 40 : ℝ)) (z := (1 / 11 : ℝ)) (U := (-518053432881209 / 200000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq10 : (-1218058243295429 / 500000000000000 : ℝ) ≤ Real.log (7 / 80 : ℝ) ∧ Real.log (7 / 80 : ℝ) ≤ (-2436116484578741 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (7 / 80 : ℝ)) (z := (1 / 6 : ℝ)) (L := (-1218058243295429 / 500000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (7 / 80 : ℝ)) (z := (1 / 6 : ℝ)) (U := (-2436116484578741 / 1000000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq11 : (-2302585094803327 / 1000000000000000 : ℝ) ≤ Real.log (1 / 10 : ℝ) ∧ Real.log (1 / 10 : ℝ) ≤ (-575646272986983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 10 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-2302585094803327 / 1000000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 10 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-575646272986983 / 250000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq12 : (-2241960476043791 / 1000000000000000 : ℝ) ≤ Real.log (17 / 160 : ℝ) ∧ Real.log (17 / 160 : ℝ) ≤ (-2241960470100571 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (17 / 160 : ℝ)) (z := (7 / 27 : ℝ)) (L := (-2241960476043791 / 1000000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (17 / 160 : ℝ)) (z := (7 / 27 : ℝ)) (U := (-2241960470100571 / 1000000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq13 : (-1092401036148709 / 500000000000000 : ℝ) ≤ Real.log (9 / 80 : ℝ) ∧ Real.log (9 / 80 : ℝ) ≤ (-2184802056133427 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (9 / 80 : ℝ)) (z := (2 / 7 : ℝ)) (L := (-1092401036148709 / 500000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (9 / 80 : ℝ)) (z := (2 / 7 : ℝ)) (U := (-2184802056133427 / 1000000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq14 : (-266341859827139 / 125000000000000 : ℝ) ≤ Real.log (19 / 160 : ℝ) ∧ Real.log (19 / 160 : ℝ) ≤ (-2130734834442829 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (19 / 160 : ℝ)) (z := (9 / 29 : ℝ)) (L := (-266341859827139 / 125000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (19 / 160 : ℝ)) (z := (9 / 29 : ℝ)) (U := (-2130734834442829 / 1000000000000000 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq15 : (-324912741 / 156250000 : ℝ) ≤ Real.log (1 / 8 : ℝ) ∧ Real.log (1 / 8 : ℝ) ≤ (-20794415409 / 10000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 8 : ℝ)) (z := (0 : ℝ)) (L := (-324912741 / 156250000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 8 : ℝ)) (z := (0 : ℝ)) (U := (-20794415409 / 10000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq16 : (-496032840648919 / 250000000000000 : ℝ) ≤ Real.log (11 / 80 : ℝ) ∧ Real.log (11 / 80 : ℝ) ≤ (-79365254443827 / 40000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (11 / 80 : ℝ)) (z := (1 / 21 : ℝ)) (L := (-496032840648919 / 250000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (11 / 80 : ℝ)) (z := (1 / 21 : ℝ)) (U := (-79365254443827 / 40000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq17 : (-37942399712121 / 20000000000000 : ℝ) ≤ Real.log (3 / 20 : ℝ) ∧ Real.log (3 / 20 : ℝ) ≤ (-379423996821209 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 20 : ℝ)) (z := (1 / 11 : ℝ)) (L := (-37942399712121 / 20000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 20 : ℝ)) (z := (1 / 11 : ℝ)) (U := (-379423996821209 / 200000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq18 : (-464074497771463 / 250000000000000 : ℝ) ≤ Real.log (5 / 32 : ℝ) ∧ Real.log (5 / 32 : ℝ) ≤ (-185629798958579 / 100000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (5 / 32 : ℝ)) (z := (1 / 9 : ℝ)) (L := (-464074497771463 / 250000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (5 / 32 : ℝ)) (z := (1 / 9 : ℝ)) (U := (-185629798958579 / 100000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq19 : (-1817077277933003 / 1000000000000000 : ℝ) ≤ Real.log (13 / 80 : ℝ) ∧ Real.log (13 / 80 : ℝ) ≤ (-1817077276432507 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (13 / 80 : ℝ)) (z := (3 / 23 : ℝ)) (L := (-1817077277933003 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (13 / 80 : ℝ)) (z := (3 / 23 : ℝ)) (U := (-1817077276432507 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq20 : (-355867389990489 / 200000000000000 : ℝ) ≤ Real.log (27 / 160 : ℝ) ∧ Real.log (27 / 160 : ℝ) ≤ (-1779336948449653 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (27 / 160 : ℝ)) (z := (7 / 47 : ℝ)) (L := (-355867389990489 / 200000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (27 / 160 : ℝ)) (z := (7 / 47 : ℝ)) (U := (-1779336948449653 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq21 : (-871484652895429 / 500000000000000 : ℝ) ≤ Real.log (7 / 40 : ℝ) ∧ Real.log (7 / 40 : ℝ) ≤ (-1742969304278741 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (7 / 40 : ℝ)) (z := (1 / 6 : ℝ)) (L := (-871484652895429 / 500000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (7 / 40 : ℝ)) (z := (1 / 6 : ℝ)) (U := (-1742969304278741 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq22 : (-418494108605599 / 250000000000000 : ℝ) ≤ Real.log (3 / 16 : ℝ) ∧ Real.log (3 / 16 : ℝ) ≤ (-1673976432791113 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 16 : ℝ)) (z := (1 / 5 : ℝ)) (L := (-418494108605599 / 250000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 16 : ℝ)) (z := (1 / 5 : ℝ)) (U := (-1673976432791113 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq23 : (-1609437914003327 / 1000000000000000 : ℝ) ≤ Real.log (1 / 5 : ℝ) ∧ Real.log (1 / 5 : ℝ) ≤ (-402359477911983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 5 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-1609437914003327 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 5 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-402359477911983 / 250000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq24 : (-315733251275139 / 200000000000000 : ℝ) ≤ Real.log (33 / 160 : ℝ) ∧ Real.log (33 / 160 : ℝ) ≤ (-1578666252971497 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (33 / 160 : ℝ)) (z := (13 / 53 : ℝ)) (L := (-315733251275139 / 200000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (33 / 160 : ℝ)) (z := (13 / 53 : ℝ)) (U := (-1578666252971497 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq25 : (-1548813295243791 / 1000000000000000 : ℝ) ≤ Real.log (17 / 80 : ℝ) ∧ Real.log (17 / 80 : ℝ) ≤ (-1548813289800571 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (17 / 80 : ℝ)) (z := (7 / 27 : ℝ)) (L := (-1548813295243791 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (17 / 80 : ℝ)) (z := (7 / 27 : ℝ)) (U := (-1548813289800571 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq26 : (-379956440514921 / 250000000000000 : ℝ) ≤ Real.log (7 / 32 : ℝ) ∧ Real.log (7 / 32 : ℝ) ≤ (-379956438220963 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (7 / 32 : ℝ)) (z := (3 / 11 : ℝ)) (L := (-379956440514921 / 250000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (7 / 32 : ℝ)) (z := (3 / 11 : ℝ)) (U := (-379956438220963 / 250000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq27 : (-745827445748709 / 500000000000000 : ℝ) ≤ Real.log (9 / 40 : ℝ) ∧ Real.log (9 / 40 : ℝ) ≤ (-1491654875833427 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (9 / 40 : ℝ)) (z := (2 / 7 : ℝ)) (L := (-745827445748709 / 500000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (9 / 40 : ℝ)) (z := (2 / 7 : ℝ)) (U := (-1491654875833427 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq28 : (-179698462227139 / 125000000000000 : ℝ) ≤ Real.log (19 / 80 : ℝ) ∧ Real.log (19 / 80 : ℝ) ≤ (-1437587654142829 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (19 / 80 : ℝ)) (z := (9 / 29 : ℝ)) (L := (-179698462227139 / 125000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (19 / 80 : ℝ)) (z := (9 / 29 : ℝ)) (U := (-1437587654142829 / 1000000000000000 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq29 : (-108304247 / 78125000 : ℝ) ≤ Real.log (1 / 4 : ℝ) ∧ Real.log (1 / 4 : ℝ) ≤ (-6931471803 / 5000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 4 : ℝ)) (z := (0 : ℝ)) (L := (-108304247 / 78125000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 4 : ℝ)) (z := (0 : ℝ)) (U := (-6931471803 / 5000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq30 : (-167188024678821 / 125000000000000 : ℝ) ≤ Real.log (21 / 80 : ℝ) ∧ Real.log (21 / 80 : ℝ) ≤ (-1337504196430567 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (21 / 80 : ℝ)) (z := (1 / 41 : ℝ)) (L := (-167188024678821 / 125000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (21 / 80 : ℝ)) (z := (1 / 41 : ℝ)) (U := (-1337504196430567 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq31 : (-322746045448919 / 250000000000000 : ℝ) ≤ Real.log (11 / 40 : ℝ) ∧ Real.log (11 / 40 : ℝ) ≤ (-51639367231827 / 40000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (11 / 40 : ℝ)) (z := (1 / 21 : ℝ)) (L := (-322746045448919 / 250000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (11 / 40 : ℝ)) (z := (1 / 21 : ℝ)) (U := (-51639367231827 / 40000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq32 : (-623266209612421 / 500000000000000 : ℝ) ≤ Real.log (23 / 80 : ℝ) ∧ Real.log (23 / 80 : ℝ) ≤ (-1246532418224841 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (23 / 80 : ℝ)) (z := (3 / 43 : ℝ)) (L := (-623266209612421 / 500000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (23 / 80 : ℝ)) (z := (3 / 43 : ℝ)) (U := (-1246532418224841 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq33 : (-24079456096121 / 20000000000000 : ℝ) ≤ Real.log (3 / 10 : ℝ) ∧ Real.log (3 / 10 : ℝ) ≤ (-240794560761209 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 10 : ℝ)) (z := (1 / 11 : ℝ)) (L := (-24079456096121 / 20000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 10 : ℝ)) (z := (1 / 11 : ℝ)) (U := (-240794560761209 / 200000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq34 : (-290787702571463 / 250000000000000 : ℝ) ≤ Real.log (5 / 16 : ℝ) ∧ Real.log (5 / 16 : ℝ) ≤ (-116315080928579 / 100000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (5 / 16 : ℝ)) (z := (1 / 9 : ℝ)) (L := (-290787702571463 / 250000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (5 / 16 : ℝ)) (z := (1 / 9 : ℝ)) (U := (-116315080928579 / 100000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq35 : (-1123930097133003 / 1000000000000000 : ℝ) ≤ Real.log (13 / 40 : ℝ) ∧ Real.log (13 / 40 : ℝ) ≤ (-1123930096132507 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (13 / 40 : ℝ)) (z := (3 / 23 : ℝ)) (L := (-1123930097133003 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (13 / 40 : ℝ)) (z := (3 / 23 : ℝ)) (U := (-1123930096132507 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq36 : (-217237953830489 / 200000000000000 : ℝ) ≤ Real.log (27 / 80 : ℝ) ∧ Real.log (27 / 80 : ℝ) ≤ (-1086189768149653 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (27 / 80 : ℝ)) (z := (7 / 47 : ℝ)) (L := (-217237953830489 / 200000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (27 / 80 : ℝ)) (z := (7 / 47 : ℝ)) (U := (-1086189768149653 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq37 : (-524911062495429 / 500000000000000 : ℝ) ≤ Real.log (7 / 20 : ℝ) ∧ Real.log (7 / 20 : ℝ) ≤ (-1049822123978741 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (7 / 20 : ℝ)) (z := (1 / 6 : ℝ)) (L := (-524911062495429 / 500000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (7 / 20 : ℝ)) (z := (1 / 6 : ℝ)) (U := (-1049822123978741 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq38 : (-101473080521043 / 100000000000000 : ℝ) ≤ Real.log (29 / 80 : ℝ) ∧ Real.log (29 / 80 : ℝ) ≤ (-1014730804167317 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (29 / 80 : ℝ)) (z := (9 / 49 : ℝ)) (L := (-101473080521043 / 100000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (29 / 80 : ℝ)) (z := (9 / 49 : ℝ)) (U := (-1014730804167317 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq39 : (-245207313405599 / 250000000000000 : ℝ) ≤ Real.log (3 / 8 : ℝ) ∧ Real.log (3 / 8 : ℝ) ≤ (-980829252491113 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 8 : ℝ)) (z := (1 / 5 : ℝ)) (L := (-245207313405599 / 250000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 8 : ℝ)) (z := (1 / 5 : ℝ)) (U := (-980829252491113 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq40 : (-948039431019327 / 1000000000000000 : ℝ) ≤ Real.log (31 / 80 : ℝ) ∧ Real.log (31 / 80 : ℝ) ≤ (-37921577186663 / 40000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (31 / 80 : ℝ)) (z := (11 / 51 : ℝ)) (L := (-948039431019327 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (31 / 80 : ℝ)) (z := (11 / 51 : ℝ)) (U := (-37921577186663 / 40000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq41 : (-916290733203327 / 1000000000000000 : ℝ) ≤ Real.log (2 / 5 : ℝ) ∧ Real.log (2 / 5 : ℝ) ≤ (-229072682836983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (2 / 5 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-916290733203327 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (2 / 5 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-229072682836983 / 250000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq42 : (-177103815115139 / 200000000000000 : ℝ) ≤ Real.log (33 / 80 : ℝ) ∧ Real.log (33 / 80 : ℝ) ≤ (-885519072671497 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (33 / 80 : ℝ)) (z := (13 / 53 : ℝ)) (L := (-177103815115139 / 200000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (33 / 80 : ℝ)) (z := (13 / 53 : ℝ)) (U := (-885519072671497 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq43 : (-855666114443791 / 1000000000000000 : ℝ) ≤ Real.log (17 / 40 : ℝ) ∧ Real.log (17 / 40 : ℝ) ≤ (-855666109500571 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (17 / 40 : ℝ)) (z := (7 / 27 : ℝ)) (L := (-855666114443791 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (17 / 40 : ℝ)) (z := (7 / 27 : ℝ)) (U := (-855666109500571 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq44 : (-206669645314921 / 250000000000000 : ℝ) ≤ Real.log (7 / 16 : ℝ) ∧ Real.log (7 / 16 : ℝ) ≤ (-206669643145963 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (7 / 16 : ℝ)) (z := (3 / 11 : ℝ)) (L := (-206669645314921 / 250000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (7 / 16 : ℝ)) (z := (3 / 11 : ℝ)) (U := (-206669643145963 / 250000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq45 : (-399253855348709 / 500000000000000 : ℝ) ≤ Real.log (9 / 20 : ℝ) ∧ Real.log (9 / 20 : ℝ) ≤ (-798507695533427 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (9 / 20 : ℝ)) (z := (2 / 7 : ℝ)) (L := (-399253855348709 / 500000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (9 / 20 : ℝ)) (z := (2 / 7 : ℝ)) (U := (-798507695533427 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq46 : (-771108747138631 / 1000000000000000 : ℝ) ≤ Real.log (37 / 80 : ℝ) ∧ Real.log (37 / 80 : ℝ) ≤ (-192777180298063 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (37 / 80 : ℝ)) (z := (17 / 57 : ℝ)) (L := (-771108747138631 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (37 / 80 : ℝ)) (z := (17 / 57 : ℝ)) (U := (-192777180298063 / 250000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq47 : (-93055064627139 / 125000000000000 : ℝ) ≤ Real.log (19 / 40 : ℝ) ∧ Real.log (19 / 40 : ℝ) ≤ (-744440473842829 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (19 / 40 : ℝ)) (z := (9 / 29 : ℝ)) (L := (-93055064627139 / 125000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (19 / 40 : ℝ)) (z := (9 / 29 : ℝ)) (U := (-744440473842829 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq48 : (-718465056754683 / 1000000000000000 : ℝ) ≤ Real.log (39 / 80 : ℝ) ∧ Real.log (39 / 80 : ℝ) ≤ (-359232493495689 / 500000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (39 / 80 : ℝ)) (z := (19 / 59 : ℝ)) (L := (-718465056754683 / 1000000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (39 / 80 : ℝ)) (z := (19 / 59 : ℝ)) (U := (-359232493495689 / 500000000000000 : ℝ)) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq49 : (-108304247 / 156250000 : ℝ) ≤ Real.log (1 / 2 : ℝ) ∧ Real.log (1 / 2 : ℝ) ≤ (-6931471803 / 10000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (1 / 2 : ℝ)) (z := (0 : ℝ)) (L := (-108304247 / 156250000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (1 / 2 : ℝ)) (z := (0 : ℝ)) (U := (-6931471803 / 10000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq50 : (-668454568209629 / 1000000000000000 : ℝ) ≤ Real.log (41 / 80 : ℝ) ∧ Real.log (41 / 80 : ℝ) ≤ (-167113641927407 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (41 / 80 : ℝ)) (z := (1 / 81 : ℝ)) (L := (-668454568209629 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (41 / 80 : ℝ)) (z := (1 / 81 : ℝ)) (U := (-167113641927407 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq51 : (-80544627078821 / 125000000000000 : ℝ) ≤ Real.log (21 / 40 : ℝ) ∧ Real.log (21 / 40 : ℝ) ≤ (-644357016130567 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (21 / 40 : ℝ)) (z := (1 / 41 : ℝ)) (L := (-80544627078821 / 125000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (21 / 40 : ℝ)) (z := (1 / 41 : ℝ)) (U := (-644357016130567 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq52 : (-310413259610187 / 500000000000000 : ℝ) ≤ Real.log (43 / 80 : ℝ) ∧ Real.log (43 / 80 : ℝ) ≤ (-620826518720373 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (43 / 80 : ℝ)) (z := (3 / 83 : ℝ)) (L := (-310413259610187 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (43 / 80 : ℝ)) (z := (3 / 83 : ℝ)) (U := (-620826518720373 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq53 : (-149459250248919 / 250000000000000 : ℝ) ≤ Real.log (11 / 20 : ℝ) ∧ Real.log (11 / 20 : ℝ) ≤ (-23913480019827 / 40000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (11 / 20 : ℝ)) (z := (1 / 21 : ℝ)) (L := (-149459250248919 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (11 / 20 : ℝ)) (z := (1 / 21 : ℝ)) (U := (-23913480019827 / 40000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq54 : (-575364145143617 / 1000000000000000 : ℝ) ≤ Real.log (9 / 16 : ℝ) ∧ Real.log (9 / 16 : ℝ) ≤ (-17980129520113 / 31250000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (9 / 16 : ℝ)) (z := (1 / 17 : ℝ)) (L := (-575364145143617 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (9 / 16 : ℝ)) (z := (1 / 17 : ℝ)) (U := (-17980129520113 / 31250000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq55 : (-276692619212421 / 500000000000000 : ℝ) ≤ Real.log (23 / 40 : ℝ) ∧ Real.log (23 / 40 : ℝ) ≤ (-553385237924841 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (23 / 40 : ℝ)) (z := (3 / 43 : ℝ)) (L := (-276692619212421 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (23 / 40 : ℝ)) (z := (3 / 43 : ℝ)) (U := (-553385237924841 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq56 : (-531879033203879 / 1000000000000000 : ℝ) ≤ Real.log (47 / 80 : ℝ) ∧ Real.log (47 / 80 : ℝ) ≤ (-531879032703877 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (47 / 80 : ℝ)) (z := (7 / 87 : ℝ)) (L := (-531879033203879 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (47 / 80 : ℝ)) (z := (7 / 87 : ℝ)) (U := (-531879032703877 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq57 : (-10216512480121 / 20000000000000 : ℝ) ≤ Real.log (3 / 5 : ℝ) ∧ Real.log (3 / 5 : ℝ) ≤ (-102165124701209 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 5 : ℝ)) (z := (1 / 11 : ℝ)) (L := (-10216512480121 / 20000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 5 : ℝ)) (z := (1 / 11 : ℝ)) (U := (-102165124701209 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq58 : (-957434251569 / 1953125000000 : ℝ) ≤ Real.log (49 / 80 : ℝ) ∧ Real.log (49 / 80 : ℝ) ≤ (-490206336303309 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (49 / 80 : ℝ)) (z := (9 / 89 : ℝ)) (L := (-957434251569 / 1953125000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (49 / 80 : ℝ)) (z := (9 / 89 : ℝ)) (U := (-490206336303309 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq59 : (-117500907371463 / 250000000000000 : ℝ) ≤ Real.log (5 / 8 : ℝ) ∧ Real.log (5 / 8 : ℝ) ≤ (-47000362898579 / 100000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (5 / 8 : ℝ)) (z := (1 / 9 : ℝ)) (L := (-117500907371463 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (5 / 8 : ℝ)) (z := (1 / 9 : ℝ)) (U := (-47000362898579 / 100000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq60 : (-225100501094897 / 500000000000000 : ℝ) ≤ Real.log (51 / 80 : ℝ) ∧ Real.log (51 / 80 : ℝ) ≤ (-45020100168961 / 100000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (51 / 80 : ℝ)) (z := (11 / 91 : ℝ)) (L := (-225100501094897 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (51 / 80 : ℝ)) (z := (11 / 91 : ℝ)) (U := (-45020100168961 / 100000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq61 : (-430782916333003 / 1000000000000000 : ℝ) ≤ Real.log (13 / 20 : ℝ) ∧ Real.log (13 / 20 : ℝ) ≤ (-430782915832507 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (13 / 20 : ℝ)) (z := (3 / 23 : ℝ)) (L := (-430782916333003 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (13 / 20 : ℝ)) (z := (3 / 23 : ℝ)) (U := (-430782915832507 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq62 : (-411734721363033 / 1000000000000000 : ℝ) ≤ Real.log (53 / 80 : ℝ) ∧ Real.log (53 / 80 : ℝ) ≤ (-411734720861811 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (53 / 80 : ℝ)) (z := (13 / 93 : ℝ)) (L := (-411734721363033 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (53 / 80 : ℝ)) (z := (13 / 93 : ℝ)) (U := (-411734720861811 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq63 : (-78608517670489 / 200000000000000 : ℝ) ≤ Real.log (27 / 40 : ℝ) ∧ Real.log (27 / 40 : ℝ) ≤ (-393042587849653 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (27 / 40 : ℝ)) (z := (7 / 47 : ℝ)) (L := (-78608517670489 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (27 / 40 : ℝ)) (z := (7 / 47 : ℝ)) (U := (-393042587849653 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq64 : (-374693449687427 / 1000000000000000 : ℝ) ≤ Real.log (11 / 16 : ℝ) ∧ Real.log (11 / 16 : ℝ) ≤ (-74938689836289 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (11 / 16 : ℝ)) (z := (3 / 19 : ℝ)) (L := (-374693449687427 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (11 / 16 : ℝ)) (z := (3 / 19 : ℝ)) (U := (-74938689836289 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq65 : (-178337472095429 / 500000000000000 : ℝ) ≤ Real.log (7 / 10 : ℝ) ∧ Real.log (7 / 10 : ℝ) ≤ (-356674943678741 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (7 / 10 : ℝ)) (z := (1 / 6 : ℝ)) (L := (-178337472095429 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (7 / 10 : ℝ)) (z := (1 / 6 : ℝ)) (U := (-356674943678741 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq66 : (-338975367102647 / 1000000000000000 : ℝ) ≤ Real.log (57 / 80 : ℝ) ∧ Real.log (57 / 80 : ℝ) ≤ (-42371920822411 / 125000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (57 / 80 : ℝ)) (z := (17 / 97 : ℝ)) (L := (-338975367102647 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (57 / 80 : ℝ)) (z := (17 / 97 : ℝ)) (U := (-42371920822411 / 125000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq67 : (-32158362441043 / 100000000000000 : ℝ) ≤ Real.log (29 / 40 : ℝ) ∧ Real.log (29 / 40 : ℝ) ≤ (-321583623867317 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (29 / 40 : ℝ)) (z := (9 / 49 : ℝ)) (L := (-32158362441043 / 100000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (29 / 40 : ℝ)) (z := (9 / 49 : ℝ)) (U := (-321583623867317 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq68 : (-78249970183389 / 250000000000000 : ℝ) ≤ Real.log (117 / 160 : ℝ) ∧ Real.log (117 / 160 : ℝ) ≤ (-156499940087923 / 500000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (117 / 160 : ℝ)) (z := (37 / 197 : ℝ)) (L := (-78249970183389 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (117 / 160 : ℝ)) (z := (37 / 197 : ℝ)) (U := (-156499940087923 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq69 : (-304489191084377 / 1000000000000000 : ℝ) ≤ Real.log (59 / 80 : ℝ) ∧ Real.log (59 / 80 : ℝ) ≤ (-30448919050783 / 100000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (59 / 80 : ℝ)) (z := (19 / 99 : ℝ)) (L := (-304489191084377 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (59 / 80 : ℝ)) (z := (19 / 99 : ℝ)) (U := (-30448919050783 / 100000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq70 : (-296050322462479 / 1000000000000000 : ℝ) ≤ Real.log (119 / 160 : ℝ) ∧ Real.log (119 / 160 : ℝ) ≤ (-296050321861821 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (119 / 160 : ℝ)) (z := (39 / 199 : ℝ)) (L := (-296050322462479 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (119 / 160 : ℝ)) (z := (39 / 199 : ℝ)) (U := (-296050321861821 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq71 : (-71920518205599 / 250000000000000 : ℝ) ≤ Real.log (3 / 4 : ℝ) ∧ Real.log (3 / 4 : ℝ) ≤ (-287682072191113 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (3 / 4 : ℝ)) (z := (1 / 5 : ℝ)) (L := (-71920518205599 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (3 / 4 : ℝ)) (z := (1 / 5 : ℝ)) (U := (-287682072191113 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq72 : (-135576385478787 / 500000000000000 : ℝ) ≤ Real.log (61 / 80 : ℝ) ∧ Real.log (61 / 80 : ℝ) ≤ (-271152770239323 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (61 / 80 : ℝ)) (z := (21 / 101 : ℝ)) (L := (-135576385478787 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (61 / 80 : ℝ)) (z := (21 / 101 : ℝ)) (U := (-271152770239323 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq73 : (-254892250219327 / 1000000000000000 : ℝ) ≤ Real.log (31 / 40 : ℝ) ∧ Real.log (31 / 40 : ℝ) ≤ (-10195689974663 / 40000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (31 / 40 : ℝ)) (z := (11 / 51 : ℝ)) (L := (-254892250219327 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (31 / 40 : ℝ)) (z := (11 / 51 : ℝ)) (U := (-10195689974663 / 40000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq74 : (-49372015722547 / 200000000000000 : ℝ) ≤ Real.log (25 / 32 : ℝ) ∧ Real.log (25 / 32 : ℝ) ≤ (-246860077668617 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (25 / 32 : ℝ)) (z := (9 / 41 : ℝ)) (L := (-49372015722547 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (25 / 32 : ℝ)) (z := (9 / 41 : ℝ)) (U := (-246860077668617 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq75 : (-238891909074311 / 1000000000000000 : ℝ) ≤ Real.log (63 / 80 : ℝ) ∧ Real.log (63 / 80 : ℝ) ≤ (-119445954009281 / 500000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (63 / 80 : ℝ)) (z := (23 / 103 : ℝ)) (L := (-238891909074311 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (63 / 80 : ℝ)) (z := (23 / 103 : ℝ)) (U := (-119445954009281 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq76 : (-115493364850873 / 500000000000000 : ℝ) ≤ Real.log (127 / 160 : ℝ) ∧ Real.log (127 / 160 : ℝ) ≤ (-115493364255171 / 500000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (127 / 160 : ℝ)) (z := (47 / 207 : ℝ)) (L := (-115493364850873 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (127 / 160 : ℝ)) (z := (47 / 207 : ℝ)) (U := (-115493364255171 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq77 : (-223143552403327 / 1000000000000000 : ℝ) ≤ Real.log (4 / 5 : ℝ) ∧ Real.log (4 / 5 : ℝ) ≤ (-55785887761983 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (4 / 5 : ℝ)) (z := (3 / 13 : ℝ)) (L := (-223143552403327 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (4 / 5 : ℝ)) (z := (3 / 13 : ℝ)) (U := (-55785887761983 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq78 : (-207639366296933 / 1000000000000000 : ℝ) ≤ Real.log (13 / 16 : ℝ) ∧ Real.log (13 / 16 : ℝ) ≤ (-41527872901623 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (13 / 16 : ℝ)) (z := (5 / 21 : ℝ)) (L := (-207639366296933 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (13 / 16 : ℝ)) (z := (5 / 21 : ℝ)) (U := (-41527872901623 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq79 : (-38474378955139 / 200000000000000 : ℝ) ≤ Real.log (33 / 40 : ℝ) ∧ Real.log (33 / 40 : ℝ) ≤ (-192371892371497 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (33 / 40 : ℝ)) (z := (13 / 53 : ℝ)) (L := (-38474378955139 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (33 / 40 : ℝ)) (z := (13 / 53 : ℝ)) (U := (-192371892371497 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq80 : (-92412344765489 / 500000000000000 : ℝ) ≤ Real.log (133 / 160 : ℝ) ∧ Real.log (133 / 160 : ℝ) ≤ (-92412343366103 / 500000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (133 / 160 : ℝ)) (z := (53 / 213 : ℝ)) (L := (-92412344765489 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (133 / 160 : ℝ)) (z := (53 / 213 : ℝ)) (U := (-92412343366103 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq81 : (-88667009130713 / 500000000000000 : ℝ) ≤ Real.log (67 / 80 : ℝ) ∧ Real.log (67 / 80 : ℝ) ≤ (-177334014998309 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (67 / 80 : ℝ)) (z := (27 / 107 : ℝ)) (L := (-88667009130713 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (67 / 80 : ℝ)) (z := (27 / 107 : ℝ)) (U := (-177334014998309 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq82 : (-42474760078133 / 250000000000000 : ℝ) ≤ Real.log (27 / 32 : ℝ) ∧ Real.log (27 / 32 : ℝ) ≤ (-16989903650507 / 100000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (27 / 32 : ℝ)) (z := (11 / 43 : ℝ)) (L := (-42474760078133 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (27 / 32 : ℝ)) (z := (11 / 43 : ℝ)) (U := (-16989903650507 / 100000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq83 : (-162518933643791 / 1000000000000000 : ℝ) ≤ Real.log (17 / 20 : ℝ) ∧ Real.log (17 / 20 : ℝ) ≤ (-162518929200571 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (17 / 20 : ℝ)) (z := (7 / 27 : ℝ)) (L := (-162518933643791 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (17 / 20 : ℝ)) (z := (7 / 27 : ℝ)) (U := (-162518929200571 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq84 : (-147920135802533 / 1000000000000000 : ℝ) ≤ Real.log (69 / 80 : ℝ) ∧ Real.log (69 / 80 : ℝ) ≤ (-7396006488069 / 50000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (69 / 80 : ℝ)) (z := (29 / 109 : ℝ)) (L := (-147920135802533 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (69 / 80 : ℝ)) (z := (29 / 109 : ℝ)) (U := (-7396006488069 / 50000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq85 : (-33382850114921 / 250000000000000 : ℝ) ≤ Real.log (7 / 8 : ℝ) ∧ Real.log (7 / 8 : ℝ) ≤ (-33382848070963 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (7 / 8 : ℝ)) (z := (3 / 11 : ℝ)) (L := (-33382850114921 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (7 / 8 : ℝ)) (z := (3 / 11 : ℝ)) (U := (-33382848070963 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq86 : (-7900870874207 / 62500000000000 : ℝ) ≤ Real.log (141 / 160 : ℝ) ∧ Real.log (141 / 160 : ℝ) ≤ (-25282784899749 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (141 / 160 : ℝ)) (z := (61 / 221 : ℝ)) (L := (-7900870874207 / 62500000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (141 / 160 : ℝ)) (z := (61 / 221 : ℝ)) (U := (-25282784899749 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq87 : (-29836692062139 / 250000000000000 : ℝ) ≤ Real.log (71 / 80 : ℝ) ∧ Real.log (71 / 80 : ℝ) ≤ (-29836689314143 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (71 / 80 : ℝ)) (z := (31 / 111 : ℝ)) (L := (-29836692062139 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (71 / 80 : ℝ)) (z := (31 / 111 : ℝ)) (U := (-29836689314143 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq88 : (-4493167891377 / 40000000000000 : ℝ) ≤ Real.log (143 / 160 : ℝ) ∧ Real.log (143 / 160 : ℝ) ≤ (-28082296143897 / 250000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (143 / 160 : ℝ)) (z := (63 / 223 : ℝ)) (L := (-4493167891377 / 40000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (143 / 160 : ℝ)) (z := (63 / 223 : ℝ)) (U := (-28082296143897 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq89 : (-91567212435613 / 1000000000000000 : ℝ) ≤ Real.log (73 / 80 : ℝ) ∧ Real.log (73 / 80 : ℝ) ≤ (-91567193035597 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (73 / 80 : ℝ)) (z := (33 / 113 : ℝ)) (L := (-91567212435613 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (73 / 80 : ℝ)) (z := (33 / 113 : ℝ)) (U := (-91567193035597 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq90 : (-64538553536539 / 1000000000000000 : ℝ) ≤ Real.log (15 / 16 : ℝ) ∧ Real.log (15 / 16 : ℝ) ≤ (-32269260222167 / 500000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (15 / 16 : ℝ)) (z := (7 / 23 : ℝ)) (L := (-64538553536539 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (15 / 16 : ℝ)) (z := (7 / 23 : ℝ)) (U := (-32269260222167 / 500000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq91 : (-9555316590339 / 250000000000000 : ℝ) ≤ Real.log (77 / 80 : ℝ) ∧ Real.log (77 / 80 : ℝ) ≤ (-7644242355843 / 200000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (77 / 80 : ℝ)) (z := (37 / 117 : ℝ)) (L := (-9555316590339 / 250000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (77 / 80 : ℝ)) (z := (37 / 117 : ℝ)) (U := (-7644242355843 / 200000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lq92 : (-1257886782209 / 100000000000000 : ℝ) ≤ Real.log (79 / 80 : ℝ) ∧ Real.log (79 / 80 : ℝ) ≤ (-12578780593379 / 1000000000000000 : ℝ) :=
  ⟨le_log_of_le_mul (q := (79 / 80 : ℝ)) (z := (39 / 119 : ℝ)) (L := (-1257886782209 / 100000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog]),
   log_le_of_mul_le (q := (79 / 80 : ℝ)) (z := (39 / 119 : ℝ)) (U := (-12578780593379 / 1000000000000000 : ℝ)) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Slog, Rlog])⟩

theorem lz0 : (-1257886782209 / 100000000000000 : ℝ) ≤ Real.log |(-79 / 80 : ℝ)| ∧ Real.log |(-79 / 80 : ℝ)| ≤ (-12578780593379 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq92).1 (lq92).2

theorem fz0 : (79993723666876941 / 80000000000000000 : ℝ) ≤ Fx (-79 / 80 : ℝ) ∧ Fx (-79 / 80 : ℝ) ≤ (7999373055794511 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-79 / 80 : ℝ)) (by norm_num) (lz0).1 (lz0).2
  constructor <;> linarith [h.1, h.2]

theorem lz1 : (-9555316590339 / 250000000000000 : ℝ) ≤ Real.log |(-77 / 80 : ℝ)| ∧ Real.log |(-77 / 80 : ℝ)| ≤ (-7644242355843 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq91).1 (lq91).2

theorem fz1 : (15988606661399911 / 16000000000000000 : ℝ) ≤ Fx (-77 / 80 : ℝ) ∧ Fx (-77 / 80 : ℝ) ≤ (19985759377456103 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-77 / 80 : ℝ)) (by norm_num) (lz1).1 (lz1).2
  constructor <;> linarith [h.1, h.2]

theorem lz2 : (-64538553536539 / 1000000000000000 : ℝ) ≤ Real.log |(-15 / 16 : ℝ)| ∧ Real.log |(-15 / 16 : ℝ)| ≤ (-32269260222167 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq90).1 (lq90).2

theorem fz2 : (1596807780666501 / 1600000000000000 : ℝ) ≤ Fx (-15 / 16 : ℝ) ∧ Fx (-15 / 16 : ℝ) ≤ (3193615660609617 / 3200000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-15 / 16 : ℝ)) (by norm_num) (lz2).1 (lz2).2
  constructor <;> linarith [h.1, h.2]

theorem lz3 : (-91567212435613 / 1000000000000000 : ℝ) ≤ Real.log |(-73 / 80 : ℝ)| ∧ Real.log |(-73 / 80 : ℝ)| ≤ (-91567193035597 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq89).1 (lq89).2

theorem fz3 : (79684405091598581 / 80000000000000000 : ℝ) ≤ Fx (-73 / 80 : ℝ) ∧ Fx (-73 / 80 : ℝ) ≤ (79684406507799749 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-73 / 80 : ℝ)) (by norm_num) (lz3).1 (lz3).2
  constructor <;> linarith [h.1, h.2]

theorem lz4 : (-4493167891377 / 40000000000000 : ℝ) ≤ Real.log |(-143 / 160 : ℝ)| ∧ Real.log |(-143 / 160 : ℝ)| ≤ (-28082296143897 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq88).1 (lq88).2

theorem fz4 : (39765768348577271 / 40000000000000000 : ℝ) ≤ Fx (-143 / 160 : ℝ) ∧ Fx (-143 / 160 : ℝ) ≤ (6362523008466911 / 6400000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-143 / 160 : ℝ)) (by norm_num) (lz4).1 (lz4).2
  constructor <;> linarith [h.1, h.2]

theorem lz5 : (-29836692062139 / 250000000000000 : ℝ) ≤ Real.log |(-71 / 80 : ℝ)| ∧ Real.log |(-71 / 80 : ℝ)| ≤ (-29836689314143 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq87).1 (lq87).2

theorem fz5 : (19868404941304153 / 20000000000000000 : ℝ) ≤ Fx (-71 / 80 : ℝ) ∧ Fx (-71 / 80 : ℝ) ≤ (19868405136411869 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-71 / 80 : ℝ)) (by norm_num) (lz5).1 (lz5).2
  constructor <;> linarith [h.1, h.2]

theorem lz6 : (-7900870874207 / 62500000000000 : ℝ) ≤ Real.log |(-141 / 160 : ℝ)| ∧ Real.log |(-141 / 160 : ℝ)| ≤ (-25282784899749 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq86).1 (lq86).2

theorem fz6 : (31764872670864609 / 32000000000000000 : ℝ) ≤ Fx (-141 / 160 : ℝ) ∧ Fx (-141 / 160 : ℝ) ≤ (9926522793263187 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-141 / 160 : ℝ)) (by norm_num) (lz6).1 (lz6).2
  constructor <;> linarith [h.1, h.2]

theorem lz7 : (-33382850114921 / 250000000000000 : ℝ) ≤ Real.log |(-7 / 8 : ℝ)| ∧ Real.log |(-7 / 8 : ℝ)| ≤ (-33382848070963 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq85).1 (lq85).2

theorem fz7 : (1983679936496741 / 2000000000000000 : ℝ) ≤ Fx (-7 / 8 : ℝ) ∧ Fx (-7 / 8 : ℝ) ≤ (1983679950804447 / 2000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-7 / 8 : ℝ)) (by norm_num) (lz7).1 (lz7).2
  constructor <;> linarith [h.1, h.2]

theorem lz8 : (-147920135802533 / 1000000000000000 : ℝ) ≤ Real.log |(-69 / 80 : ℝ)| ∧ Real.log |(-69 / 80 : ℝ)| ≤ (-7396006488069 / 50000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq84).1 (lq84).2

theorem fz8 : (3960324447676761 / 4000000000000000 : ℝ) ≤ Fx (-69 / 80 : ℝ) ∧ Fx (-69 / 80 : ℝ) ≤ (79206489370374777 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-69 / 80 : ℝ)) (by norm_num) (lz8).1 (lz8).2
  constructor <;> linarith [h.1, h.2]

theorem lz9 : (-162518933643791 / 1000000000000000 : ℝ) ≤ Real.log |(-17 / 20 : ℝ)| ∧ Real.log |(-17 / 20 : ℝ)| ≤ (-162518929200571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq83).1 (lq83).2

theorem fz9 : (19762821796409707 / 20000000000000000 : ℝ) ≤ Fx (-17 / 20 : ℝ) ∧ Fx (-17 / 20 : ℝ) ≤ (19762821871944447 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-17 / 20 : ℝ)) (by norm_num) (lz9).1 (lz9).2
  constructor <;> linarith [h.1, h.2]

theorem lz10 : (-42474760078133 / 250000000000000 : ℝ) ≤ Real.log |(-27 / 32 : ℝ)| ∧ Real.log |(-27 / 32 : ℝ)| ≤ (-16989903650507 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq82).1 (lq82).2

theorem fz10 : (3158727398563689 / 3200000000000000 : ℝ) ≤ Fx (-27 / 32 : ℝ) ∧ Fx (-27 / 32 : ℝ) ≤ (7896818522109591 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-27 / 32 : ℝ)) (by norm_num) (lz10).1 (lz10).2
  constructor <;> linarith [h.1, h.2]

theorem lz11 : (-88667009130713 / 500000000000000 : ℝ) ≤ Real.log |(-67 / 80 : ℝ)| ∧ Real.log |(-67 / 80 : ℝ)| ≤ (-177334014998309 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq81).1 (lq81).2

theorem fz11 : (78881379004886703 / 80000000000000000 : ℝ) ≤ Fx (-67 / 80 : ℝ) ∧ Fx (-67 / 80 : ℝ) ≤ (39440689611757771 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-67 / 80 : ℝ)) (by norm_num) (lz11).1 (lz11).2
  constructor <;> linarith [h.1, h.2]

theorem lz12 : (-92412344765489 / 500000000000000 : ℝ) ≤ Real.log |(-133 / 160 : ℝ)| ∧ Real.log |(-133 / 160 : ℝ)| ≤ (-92412343366103 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq80).1 (lq80).2

theorem fz12 : (78790841667691699 / 80000000000000000 : ℝ) ≤ Fx (-133 / 160 : ℝ) ∧ Fx (-133 / 160 : ℝ) ≤ (78790841853810037 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-133 / 160 : ℝ)) (by norm_num) (lz12).1 (lz12).2
  constructor <;> linarith [h.1, h.2]

theorem lz13 : (-38474378955139 / 200000000000000 : ℝ) ≤ Real.log |(-33 / 40 : ℝ)| ∧ Real.log |(-33 / 40 : ℝ)| ≤ (-192371892371497 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq79).1 (lq79).2

theorem fz13 : (39348272448259401 / 40000000000000000 : ℝ) ≤ Fx (-33 / 40 : ℝ) ∧ Fx (-33 / 40 : ℝ) ≤ (7869654505519587 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-33 / 40 : ℝ)) (by norm_num) (lz13).1 (lz13).2
  constructor <;> linarith [h.1, h.2]

theorem lz14 : (-207639366296933 / 1000000000000000 : ℝ) ≤ Real.log |(-13 / 16 : ℝ)| ∧ Real.log |(-13 / 16 : ℝ)| ≤ (-41527872901623 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq78).1 (lq78).2

theorem fz14 : (3139862347721099 / 3200000000000000 : ℝ) ≤ Fx (-13 / 16 : ℝ) ∧ Fx (-13 / 16 : ℝ) ≤ (15699311761860129 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-13 / 16 : ℝ)) (by norm_num) (lz14).1 (lz14).2
  constructor <;> linarith [h.1, h.2]

theorem lz15 : (-223143552403327 / 1000000000000000 : ℝ) ≤ Real.log |(-4 / 5 : ℝ)| ∧ Real.log |(-4 / 5 : ℝ)| ≤ (-55785887761983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq77).1 (lq77).2

theorem fz15 : (305785887761983 / 312500000000000 : ℝ) ≤ Fx (-4 / 5 : ℝ) ∧ Fx (-4 / 5 : ℝ) ≤ (1223143552403327 / 1250000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-4 / 5 : ℝ)) (by norm_num) (lz15).1 (lz15).2
  constructor <;> linarith [h.1, h.2]

theorem lz16 : (-115493364850873 / 500000000000000 : ℝ) ≤ Real.log |(-127 / 160 : ℝ)| ∧ Real.log |(-127 / 160 : ℝ)| ≤ (-115493364255171 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq76).1 (lq76).2

theorem fz16 : (78167657260406717 / 80000000000000000 : ℝ) ≤ Fx (-127 / 160 : ℝ) ∧ Fx (-127 / 160 : ℝ) ≤ (78167657336060871 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-127 / 160 : ℝ)) (by norm_num) (lz16).1 (lz16).2
  constructor <;> linarith [h.1, h.2]

theorem lz17 : (-238891909074311 / 1000000000000000 : ℝ) ≤ Real.log |(-63 / 80 : ℝ)| ∧ Real.log |(-63 / 80 : ℝ)| ≤ (-119445954009281 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq75).1 (lq75).2

theorem fz17 : (39025095102584703 / 40000000000000000 : ℝ) ≤ Fx (-63 / 80 : ℝ) ∧ Fx (-63 / 80 : ℝ) ≤ (78050190271681593 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-63 / 80 : ℝ)) (by norm_num) (lz17).1 (lz17).2
  constructor <;> linarith [h.1, h.2]

theorem lz18 : (-49372015722547 / 200000000000000 : ℝ) ≤ Real.log |(-25 / 32 : ℝ)| ∧ Real.log |(-25 / 32 : ℝ)| ≤ (-246860077668617 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq74).1 (lq74).2

theorem fz18 : (1246860077668617 / 1280000000000000 : ℝ) ≤ Fx (-25 / 32 : ℝ) ∧ Fx (-25 / 32 : ℝ) ≤ (249372015722547 / 256000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-25 / 32 : ℝ)) (by norm_num) (lz18).1 (lz18).2
  constructor <;> linarith [h.1, h.2]

theorem lz19 : (-254892250219327 / 1000000000000000 : ℝ) ≤ Real.log |(-31 / 40 : ℝ)| ∧ Real.log |(-31 / 40 : ℝ)| ≤ (-10195689974663 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq73).1 (lq73).2

theorem fz19 : (1556066389214553 / 1600000000000000 : ℝ) ≤ Fx (-31 / 40 : ℝ) ∧ Fx (-31 / 40 : ℝ) ≤ (38901659756799137 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-31 / 40 : ℝ)) (by norm_num) (lz19).1 (lz19).2
  constructor <;> linarith [h.1, h.2]

theorem lz20 : (-135576385478787 / 500000000000000 : ℝ) ≤ Real.log |(-61 / 80 : ℝ)| ∧ Real.log |(-61 / 80 : ℝ)| ≤ (-271152770239323 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq72).1 (lq72).2

theorem fz20 : (77540318984598703 / 80000000000000000 : ℝ) ≤ Fx (-61 / 80 : ℝ) ∧ Fx (-61 / 80 : ℝ) ≤ (38770159514206007 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-61 / 80 : ℝ)) (by norm_num) (lz20).1 (lz20).2
  constructor <;> linarith [h.1, h.2]

theorem lz21 : (-71920518205599 / 250000000000000 : ℝ) ≤ Real.log |(-3 / 4 : ℝ)| ∧ Real.log |(-3 / 4 : ℝ)| ≤ (-287682072191113 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq71).1 (lq71).2

theorem fz21 : (3863046216573339 / 4000000000000000 : ℝ) ≤ Fx (-3 / 4 : ℝ) ∧ Fx (-3 / 4 : ℝ) ≤ (965761554616797 / 1000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 4 : ℝ)) (by norm_num) (lz21).1 (lz21).2
  constructor <;> linarith [h.1, h.2]

theorem lz22 : (-296050322462479 / 1000000000000000 : ℝ) ≤ Real.log |(-119 / 160 : ℝ)| ∧ Real.log |(-119 / 160 : ℝ)| ≤ (-296050321861821 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq70).1 (lq70).2

theorem fz22 : (154229988301556699 / 160000000000000000 : ℝ) ≤ Fx (-119 / 160 : ℝ) ∧ Fx (-119 / 160 : ℝ) ≤ (154229988373035001 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-119 / 160 : ℝ)) (by norm_num) (lz22).1 (lz22).2
  constructor <;> linarith [h.1, h.2]

theorem lz23 : (-304489191084377 / 1000000000000000 : ℝ) ≤ Real.log |(-59 / 80 : ℝ)| ∧ Real.log |(-59 / 80 : ℝ)| ≤ (-30448919050783 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq69).1 (lq69).2

theorem fz23 : (7696486223996197 / 8000000000000000 : ℝ) ≤ Fx (-59 / 80 : ℝ) ∧ Fx (-59 / 80 : ℝ) ≤ (76964862273978243 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-59 / 80 : ℝ)) (by norm_num) (lz23).1 (lz23).2
  constructor <;> linarith [h.1, h.2]

theorem lz24 : (-78249970183389 / 250000000000000 : ℝ) ≤ Real.log |(-117 / 160 : ℝ)| ∧ Real.log |(-117 / 160 : ℝ)| ≤ (-156499940087923 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq68).1 (lq68).2

theorem fz24 : (76810492990286991 / 80000000000000000 : ℝ) ≤ Fx (-117 / 160 : ℝ) ∧ Fx (-117 / 160 : ℝ) ≤ (38405246511456513 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-117 / 160 : ℝ)) (by norm_num) (lz24).1 (lz24).2
  constructor <;> linarith [h.1, h.2]

theorem lz25 : (-32158362441043 / 100000000000000 : ℝ) ≤ Real.log |(-29 / 40 : ℝ)| ∧ Real.log |(-29 / 40 : ℝ)| ≤ (-321583623867317 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq67).1 (lq67).2

theorem fz25 : (38325925092152193 / 40000000000000000 : ℝ) ≤ Fx (-29 / 40 : ℝ) ∧ Fx (-29 / 40 : ℝ) ≤ (3832592510790247 / 4000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-29 / 40 : ℝ)) (by norm_num) (lz25).1 (lz25).2
  constructor <;> linarith [h.1, h.2]

theorem lz26 : (-338975367102647 / 1000000000000000 : ℝ) ≤ Real.log |(-57 / 80 : ℝ)| ∧ Real.log |(-57 / 80 : ℝ)| ≤ (-42371920822411 / 125000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq66).1 (lq66).2

theorem fz26 : (9540199486877427 / 10000000000000000 : ℝ) ≤ Fx (-57 / 80 : ℝ) ∧ Fx (-57 / 80 : ℝ) ≤ (76321595924850879 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-57 / 80 : ℝ)) (by norm_num) (lz26).1 (lz26).2
  constructor <;> linarith [h.1, h.2]

theorem lz27 : (-178337472095429 / 500000000000000 : ℝ) ≤ Real.log |(-7 / 10 : ℝ)| ∧ Real.log |(-7 / 10 : ℝ)| ≤ (-356674943678741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq65).1 (lq65).2

theorem fz27 : (9496724605751187 / 10000000000000000 : ℝ) ≤ Fx (-7 / 10 : ℝ) ∧ Fx (-7 / 10 : ℝ) ≤ (4748362304668003 / 5000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-7 / 10 : ℝ)) (by norm_num) (lz27).1 (lz27).2
  constructor <;> linarith [h.1, h.2]

theorem lz28 : (-374693449687427 / 1000000000000000 : ℝ) ≤ Real.log |(-11 / 16 : ℝ)| ∧ Real.log |(-11 / 16 : ℝ)| ≤ (-74938689836289 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq64).1 (lq64).2

theorem fz28 : (3024325588199179 / 3200000000000000 : ℝ) ≤ Fx (-11 / 16 : ℝ) ∧ Fx (-11 / 16 : ℝ) ≤ (15121627946561697 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-11 / 16 : ℝ)) (by norm_num) (lz28).1 (lz28).2
  constructor <;> linarith [h.1, h.2]

theorem lz29 : (-78608517670489 / 200000000000000 : ℝ) ≤ Real.log |(-27 / 40 : ℝ)| ∧ Real.log |(-27 / 40 : ℝ)| ≤ (-393042587849653 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq63).1 (lq63).2

theorem fz29 : (37612149871940631 / 40000000000000000 : ℝ) ≤ Fx (-27 / 40 : ℝ) ∧ Fx (-27 / 40 : ℝ) ≤ (7522429977103203 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-27 / 40 : ℝ)) (by norm_num) (lz29).1 (lz29).2
  constructor <;> linarith [h.1, h.2]

theorem lz30 : (-411734721363033 / 1000000000000000 : ℝ) ≤ Real.log |(-53 / 80 : ℝ)| ∧ Real.log |(-53 / 80 : ℝ)| ≤ (-411734720861811 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq62).1 (lq62).2

theorem fz30 : (74821940205675983 / 80000000000000000 : ℝ) ≤ Fx (-53 / 80 : ℝ) ∧ Fx (-53 / 80 : ℝ) ≤ (74821940232240749 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-53 / 80 : ℝ)) (by norm_num) (lz30).1 (lz30).2
  constructor <;> linarith [h.1, h.2]

theorem lz31 : (-430782916333003 / 1000000000000000 : ℝ) ≤ Real.log |(-13 / 20 : ℝ)| ∧ Real.log |(-13 / 20 : ℝ)| ≤ (-430782915832507 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq61).1 (lq61).2

theorem fz31 : (18600177905822591 / 20000000000000000 : ℝ) ≤ Fx (-13 / 20 : ℝ) ∧ Fx (-13 / 20 : ℝ) ≤ (18600177912329039 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-13 / 20 : ℝ)) (by norm_num) (lz31).1 (lz31).2
  constructor <;> linarith [h.1, h.2]

theorem lz32 : (-225100501094897 / 500000000000000 : ℝ) ≤ Real.log |(-51 / 80 : ℝ)| ∧ Real.log |(-51 / 80 : ℝ)| ≤ (-45020100168961 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq60).1 (lq60).2

theorem fz32 : (7396025108617011 / 8000000000000000 : ℝ) ≤ Fx (-51 / 80 : ℝ) ∧ Fx (-51 / 80 : ℝ) ≤ (36980125555839747 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-51 / 80 : ℝ)) (by norm_num) (lz32).1 (lz32).2
  constructor <;> linarith [h.1, h.2]

theorem lz33 : (-117500907371463 / 250000000000000 : ℝ) ≤ Real.log |(-5 / 8 : ℝ)| ∧ Real.log |(-5 / 8 : ℝ)| ≤ (-47000362898579 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq59).1 (lq59).2

theorem fz33 : (147000362898579 / 160000000000000 : ℝ) ≤ Fx (-5 / 8 : ℝ) ∧ Fx (-5 / 8 : ℝ) ≤ (367500907371463 / 400000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-5 / 8 : ℝ)) (by norm_num) (lz33).1 (lz33).2
  constructor <;> linarith [h.1, h.2]

theorem lz34 : (-957434251569 / 1953125000000 : ℝ) ≤ Real.log |(-49 / 80 : ℝ)| ∧ Real.log |(-49 / 80 : ℝ)| ≤ (-490206336303309 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq58).1 (lq58).2

theorem fz34 : (73020110478862141 / 80000000000000000 : ℝ) ≤ Fx (-49 / 80 : ℝ) ∧ Fx (-49 / 80 : ℝ) ≤ (142617403326881 / 156250000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-49 / 80 : ℝ)) (by norm_num) (lz34).1 (lz34).2
  constructor <;> linarith [h.1, h.2]

theorem lz35 : (-10216512480121 / 20000000000000 : ℝ) ≤ Real.log |(-3 / 5 : ℝ)| ∧ Real.log |(-3 / 5 : ℝ)| ≤ (-102165124701209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq57).1 (lq57).2

theorem fz35 : (906495374103627 / 1000000000000000 : ℝ) ≤ Fx (-3 / 5 : ℝ) ∧ Fx (-3 / 5 : ℝ) ≤ (90649537440363 / 100000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 5 : ℝ)) (by norm_num) (lz35).1 (lz35).2
  constructor <;> linarith [h.1, h.2]

theorem lz36 : (-531879033203879 / 1000000000000000 : ℝ) ≤ Real.log |(-47 / 80 : ℝ)| ∧ Real.log |(-47 / 80 : ℝ)| ≤ (-531879032703877 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq56).1 (lq56).2

theorem fz36 : (71998314537082219 / 80000000000000000 : ℝ) ≤ Fx (-47 / 80 : ℝ) ∧ Fx (-47 / 80 : ℝ) ≤ (71998314560582313 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-47 / 80 : ℝ)) (by norm_num) (lz36).1 (lz36).2
  constructor <;> linarith [h.1, h.2]

theorem lz37 : (-276692619212421 / 500000000000000 : ℝ) ≤ Real.log |(-23 / 40 : ℝ)| ∧ Real.log |(-23 / 40 : ℝ)| ≤ (-553385237924841 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq55).1 (lq55).2

theorem fz37 : (35727860472271343 / 40000000000000000 : ℝ) ≤ Fx (-23 / 40 : ℝ) ∧ Fx (-23 / 40 : ℝ) ≤ (17863930241885683 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-23 / 40 : ℝ)) (by norm_num) (lz37).1 (lz37).2
  constructor <;> linarith [h.1, h.2]

theorem lz38 : (-575364145143617 / 1000000000000000 : ℝ) ≤ Real.log |(-9 / 16 : ℝ)| ∧ Real.log |(-9 / 16 : ℝ)| ≤ (-17980129520113 / 31250000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq54).1 (lq54).2

theorem fz38 : (443071165681017 / 500000000000000 : ℝ) ≤ Fx (-9 / 16 : ℝ) ∧ Fx (-9 / 16 : ℝ) ≤ (14178277306292553 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-9 / 16 : ℝ)) (by norm_num) (lz38).1 (lz38).2
  constructor <;> linarith [h.1, h.2]

theorem lz39 : (-149459250248919 / 250000000000000 : ℝ) ≤ Real.log |(-11 / 20 : ℝ)| ∧ Real.log |(-11 / 20 : ℝ)| ≤ (-23913480019827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq53).1 (lq53).2

theorem fz39 : (703048280218097 / 800000000000000 : ℝ) ≤ Fx (-11 / 20 : ℝ) ∧ Fx (-11 / 20 : ℝ) ≤ (4394051752738109 / 5000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-11 / 20 : ℝ)) (by norm_num) (lz39).1 (lz39).2
  constructor <;> linarith [h.1, h.2]

theorem lz40 : (-310413259610187 / 500000000000000 : ℝ) ≤ Real.log |(-43 / 80 : ℝ)| ∧ Real.log |(-43 / 80 : ℝ)| ≤ (-620826518720373 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq52).1 (lq52).2

theorem fz40 : (69695540304976039 / 80000000000000000 : ℝ) ≤ Fx (-43 / 80 : ℝ) ∧ Fx (-43 / 80 : ℝ) ≤ (34847770163238041 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-43 / 80 : ℝ)) (by norm_num) (lz40).1 (lz40).2
  constructor <;> linarith [h.1, h.2]

theorem lz41 : (-80544627078821 / 125000000000000 : ℝ) ≤ Real.log |(-21 / 40 : ℝ)| ∧ Real.log |(-21 / 40 : ℝ)| ≤ (-644357016130567 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq51).1 (lq51).2

theorem fz41 : (34531497338741907 / 40000000000000000 : ℝ) ≤ Fx (-21 / 40 : ℝ) ∧ Fx (-21 / 40 : ℝ) ≤ (4316437168655241 / 5000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-21 / 40 : ℝ)) (by norm_num) (lz41).1 (lz41).2
  constructor <;> linarith [h.1, h.2]

theorem lz42 : (-668454568209629 / 1000000000000000 : ℝ) ≤ Real.log |(-41 / 80 : ℝ)| ∧ Real.log |(-41 / 80 : ℝ)| ≤ (-167113641927407 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq50).1 (lq50).2

theorem fz42 : (17101659319023687 / 20000000000000000 : ℝ) ≤ Fx (-41 / 80 : ℝ) ∧ Fx (-41 / 80 : ℝ) ≤ (68406637296594789 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-41 / 80 : ℝ)) (by norm_num) (lz42).1 (lz42).2
  constructor <;> linarith [h.1, h.2]

theorem lz43 : (-108304247 / 156250000 : ℝ) ≤ Real.log |(-1 / 2 : ℝ)| ∧ Real.log |(-1 / 2 : ℝ)| ≤ (-6931471803 / 10000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq49).1 (lq49).2

theorem fz43 : (16931471803 / 20000000000 : ℝ) ≤ Fx (-1 / 2 : ℝ) ∧ Fx (-1 / 2 : ℝ) ≤ (264554247 / 312500000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 2 : ℝ)) (by norm_num) (lz43).1 (lz43).2
  constructor <;> linarith [h.1, h.2]

theorem lz44 : (-718465056754683 / 1000000000000000 : ℝ) ≤ Real.log |(-39 / 80 : ℝ)| ∧ Real.log |(-39 / 80 : ℝ)| ≤ (-359232493495689 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq48).1 (lq48).2

theorem fz44 : (33510067246331871 / 40000000000000000 : ℝ) ≤ Fx (-39 / 80 : ℝ) ∧ Fx (-39 / 80 : ℝ) ≤ (67020137213432637 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-39 / 80 : ℝ)) (by norm_num) (lz44).1 (lz44).2
  constructor <;> linarith [h.1, h.2]

theorem lz45 : (-93055064627139 / 125000000000000 : ℝ) ≤ Real.log |(-19 / 40 : ℝ)| ∧ Real.log |(-19 / 40 : ℝ)| ≤ (-744440473842829 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq47).1 (lq47).2

theorem fz45 : (33144369003013751 / 40000000000000000 : ℝ) ≤ Fx (-19 / 40 : ℝ) ∧ Fx (-19 / 40 : ℝ) ≤ (4143046227915641 / 5000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-19 / 40 : ℝ)) (by norm_num) (lz45).1 (lz45).2
  constructor <;> linarith [h.1, h.2]

theorem lz46 : (-771108747138631 / 1000000000000000 : ℝ) ≤ Real.log |(-37 / 80 : ℝ)| ∧ Real.log |(-37 / 80 : ℝ)| ≤ (-192777180298063 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq46).1 (lq46).2

theorem fz46 : (16382755671028331 / 20000000000000000 : ℝ) ≤ Fx (-37 / 80 : ℝ) ∧ Fx (-37 / 80 : ℝ) ≤ (65531023644129347 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-37 / 80 : ℝ)) (by norm_num) (lz46).1 (lz46).2
  constructor <;> linarith [h.1, h.2]

theorem lz47 : (-399253855348709 / 500000000000000 : ℝ) ≤ Real.log |(-9 / 20 : ℝ)| ∧ Real.log |(-9 / 20 : ℝ)| ≤ (-798507695533427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq45).1 (lq45).2

theorem fz47 : (16186569259800843 / 20000000000000000 : ℝ) ≤ Fx (-9 / 20 : ℝ) ∧ Fx (-9 / 20 : ℝ) ≤ (8093284698138381 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-9 / 20 : ℝ)) (by norm_num) (lz47).1 (lz47).2
  constructor <;> linarith [h.1, h.2]

theorem lz48 : (-206669645314921 / 250000000000000 : ℝ) ≤ Real.log |(-7 / 16 : ℝ)| ∧ Real.log |(-7 / 16 : ℝ)| ≤ (-206669643145963 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq44).1 (lq44).2

theorem fz48 : (3196687502021741 / 4000000000000000 : ℝ) ≤ Fx (-7 / 16 : ℝ) ∧ Fx (-7 / 16 : ℝ) ≤ (3196687517204447 / 4000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-7 / 16 : ℝ)) (by norm_num) (lz48).1 (lz48).2
  constructor <;> linarith [h.1, h.2]

theorem lz49 : (-855666114443791 / 1000000000000000 : ℝ) ≤ Real.log |(-17 / 40 : ℝ)| ∧ Real.log |(-17 / 40 : ℝ)| ≤ (-855666109500571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq43).1 (lq43).2

theorem fz49 : (31546323861509707 / 40000000000000000 : ℝ) ≤ Fx (-17 / 40 : ℝ) ∧ Fx (-17 / 40 : ℝ) ≤ (31546323945544447 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-17 / 40 : ℝ)) (by norm_num) (lz49).1 (lz49).2
  constructor <;> linarith [h.1, h.2]

theorem lz50 : (-177103815115139 / 200000000000000 : ℝ) ≤ Real.log |(-33 / 80 : ℝ)| ∧ Real.log |(-33 / 80 : ℝ)| ≤ (-885519072671497 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq42).1 (lq42).2

theorem fz50 : (62222129398159401 / 80000000000000000 : ℝ) ≤ Fx (-33 / 80 : ℝ) ∧ Fx (-33 / 80 : ℝ) ≤ (12444425898799587 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-33 / 80 : ℝ)) (by norm_num) (lz50).1 (lz50).2
  constructor <;> linarith [h.1, h.2]

theorem lz51 : (-916290733203327 / 1000000000000000 : ℝ) ≤ Real.log |(-2 / 5 : ℝ)| ∧ Real.log |(-2 / 5 : ℝ)| ≤ (-229072682836983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq41).1 (lq41).2

theorem fz51 : (479072682836983 / 625000000000000 : ℝ) ≤ Fx (-2 / 5 : ℝ) ∧ Fx (-2 / 5 : ℝ) ≤ (1916290733203327 / 2500000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-2 / 5 : ℝ)) (by norm_num) (lz51).1 (lz51).2
  constructor <;> linarith [h.1, h.2]

theorem lz52 : (-948039431019327 / 1000000000000000 : ℝ) ≤ Real.log |(-31 / 80 : ℝ)| ∧ Real.log |(-31 / 80 : ℝ)| ≤ (-37921577186663 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq40).1 (lq40).2

theorem fz52 : (2415568892786553 / 3200000000000000 : ℝ) ≤ Fx (-31 / 80 : ℝ) ∧ Fx (-31 / 80 : ℝ) ≤ (60389222361599137 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-31 / 80 : ℝ)) (by norm_num) (lz52).1 (lz52).2
  constructor <;> linarith [h.1, h.2]

theorem lz53 : (-245207313405599 / 250000000000000 : ℝ) ≤ Real.log |(-3 / 8 : ℝ)| ∧ Real.log |(-3 / 8 : ℝ)| ≤ (-980829252491113 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq39).1 (lq39).2

theorem fz53 : (5942487757473339 / 8000000000000000 : ℝ) ≤ Fx (-3 / 8 : ℝ) ∧ Fx (-3 / 8 : ℝ) ≤ (1485621940216797 / 2000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 8 : ℝ)) (by norm_num) (lz53).1 (lz53).2
  constructor <;> linarith [h.1, h.2]

theorem lz54 : (-101473080521043 / 100000000000000 : ℝ) ≤ Real.log |(-29 / 80 : ℝ)| ∧ Real.log |(-29 / 80 : ℝ)| ≤ (-1014730804167317 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq38).1 (lq38).2

theorem fz54 : (58427193320852193 / 80000000000000000 : ℝ) ≤ Fx (-29 / 80 : ℝ) ∧ Fx (-29 / 80 : ℝ) ≤ (5842719335110247 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-29 / 80 : ℝ)) (by norm_num) (lz54).1 (lz54).2
  constructor <;> linarith [h.1, h.2]

theorem lz55 : (-524911062495429 / 500000000000000 : ℝ) ≤ Real.log |(-7 / 20 : ℝ)| ∧ Real.log |(-7 / 20 : ℝ)| ≤ (-1049822123978741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq37).1 (lq37).2

theorem fz55 : (14348754867851187 / 20000000000000000 : ℝ) ≤ Fx (-7 / 20 : ℝ) ∧ Fx (-7 / 20 : ℝ) ≤ (7174377437468003 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-7 / 20 : ℝ)) (by norm_num) (lz55).1 (lz55).2
  constructor <;> linarith [h.1, h.2]

theorem lz56 : (-217237953830489 / 200000000000000 : ℝ) ≤ Real.log |(-27 / 80 : ℝ)| ∧ Real.log |(-27 / 80 : ℝ)| ≤ (-1086189768149653 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq36).1 (lq36).2

theorem fz56 : (56327123740040631 / 80000000000000000 : ℝ) ≤ Fx (-27 / 80 : ℝ) ∧ Fx (-27 / 80 : ℝ) ≤ (11265424753423203 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-27 / 80 : ℝ)) (by norm_num) (lz56).1 (lz56).2
  constructor <;> linarith [h.1, h.2]

theorem lz57 : (-1123930097133003 / 1000000000000000 : ℝ) ≤ Real.log |(-13 / 40 : ℝ)| ∧ Real.log |(-13 / 40 : ℝ)| ≤ (-1123930096132507 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq35).1 (lq35).2

theorem fz57 : (27611091249722591 / 40000000000000000 : ℝ) ≤ Fx (-13 / 40 : ℝ) ∧ Fx (-13 / 40 : ℝ) ≤ (27611091262729039 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-13 / 40 : ℝ)) (by norm_num) (lz57).1 (lz57).2
  constructor <;> linarith [h.1, h.2]

theorem lz58 : (-290787702571463 / 250000000000000 : ℝ) ≤ Real.log |(-5 / 16 : ℝ)| ∧ Real.log |(-5 / 16 : ℝ)| ≤ (-116315080928579 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq34).1 (lq34).2

theorem fz58 : (216315080928579 / 320000000000000 : ℝ) ≤ Fx (-5 / 16 : ℝ) ∧ Fx (-5 / 16 : ℝ) ≤ (540787702571463 / 800000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-5 / 16 : ℝ)) (by norm_num) (lz58).1 (lz58).2
  constructor <;> linarith [h.1, h.2]

theorem lz59 : (-24079456096121 / 20000000000000 : ℝ) ≤ Real.log |(-3 / 10 : ℝ)| ∧ Real.log |(-3 / 10 : ℝ)| ≤ (-240794560761209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq33).1 (lq33).2

theorem fz59 : (1322383682283627 / 2000000000000000 : ℝ) ≤ Fx (-3 / 10 : ℝ) ∧ Fx (-3 / 10 : ℝ) ≤ (132238368288363 / 200000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 10 : ℝ)) (by norm_num) (lz59).1 (lz59).2
  constructor <;> linarith [h.1, h.2]

theorem lz60 : (-623266209612421 / 500000000000000 : ℝ) ≤ Real.log |(-23 / 80 : ℝ)| ∧ Real.log |(-23 / 80 : ℝ)| ≤ (-1246532418224841 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq32).1 (lq32).2

theorem fz60 : (51670245619171343 / 80000000000000000 : ℝ) ≤ Fx (-23 / 80 : ℝ) ∧ Fx (-23 / 80 : ℝ) ≤ (25835122821085683 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-23 / 80 : ℝ)) (by norm_num) (lz60).1 (lz60).2
  constructor <;> linarith [h.1, h.2]

theorem lz61 : (-322746045448919 / 250000000000000 : ℝ) ≤ Real.log |(-11 / 40 : ℝ)| ∧ Real.log |(-11 / 40 : ℝ)| ≤ (-51639367231827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq31).1 (lq31).2

theorem fz61 : (1008033039550097 / 1600000000000000 : ℝ) ≤ Fx (-11 / 40 : ℝ) ∧ Fx (-11 / 40 : ℝ) ≤ (6300206499938109 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-11 / 40 : ℝ)) (by norm_num) (lz61).1 (lz61).2
  constructor <;> linarith [h.1, h.2]

theorem lz62 : (-167188024678821 / 125000000000000 : ℝ) ≤ Real.log |(-21 / 80 : ℝ)| ∧ Real.log |(-21 / 80 : ℝ)| ≤ (-1337504196430567 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq30).1 (lq30).2

theorem fz62 : (49087588125041907 / 80000000000000000 : ℝ) ≤ Fx (-21 / 80 : ℝ) ∧ Fx (-21 / 80 : ℝ) ≤ (6135948518255241 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-21 / 80 : ℝ)) (by norm_num) (lz62).1 (lz62).2
  constructor <;> linarith [h.1, h.2]

theorem lz63 : (-108304247 / 78125000 : ℝ) ≤ Real.log |(-1 / 4 : ℝ)| ∧ Real.log |(-1 / 4 : ℝ)| ≤ (-6931471803 / 5000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq29).1 (lq29).2

theorem fz63 : (11931471803 / 20000000000 : ℝ) ≤ Fx (-1 / 4 : ℝ) ∧ Fx (-1 / 4 : ℝ) ≤ (186429247 / 312500000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 4 : ℝ)) (by norm_num) (lz63).1 (lz63).2
  constructor <;> linarith [h.1, h.2]

theorem lz64 : (-179698462227139 / 125000000000000 : ℝ) ≤ Real.log |(-19 / 80 : ℝ)| ∧ Real.log |(-19 / 80 : ℝ)| ≤ (-1437587654142829 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq28).1 (lq28).2

theorem fz64 : (46314165428713751 / 80000000000000000 : ℝ) ≤ Fx (-19 / 80 : ℝ) ∧ Fx (-19 / 80 : ℝ) ≤ (5789270782315641 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-19 / 80 : ℝ)) (by norm_num) (lz64).1 (lz64).2
  constructor <;> linarith [h.1, h.2]

theorem lz65 : (-745827445748709 / 500000000000000 : ℝ) ≤ Real.log |(-9 / 40 : ℝ)| ∧ Real.log |(-9 / 40 : ℝ)| ≤ (-1491654875833427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq27).1 (lq27).2

theorem fz65 : (22424893882500843 / 40000000000000000 : ℝ) ≤ Fx (-9 / 40 : ℝ) ∧ Fx (-9 / 40 : ℝ) ≤ (11212447011738381 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-9 / 40 : ℝ)) (by norm_num) (lz65).1 (lz65).2
  constructor <;> linarith [h.1, h.2]

theorem lz66 : (-379956440514921 / 250000000000000 : ℝ) ≤ Real.log |(-7 / 32 : ℝ)| ∧ Real.log |(-7 / 32 : ℝ)| ≤ (-379956438220963 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq26).1 (lq26).2

theorem fz66 : (4409695067546741 / 8000000000000000 : ℝ) ≤ Fx (-7 / 32 : ℝ) ∧ Fx (-7 / 32 : ℝ) ≤ (4409695083604447 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-7 / 32 : ℝ)) (by norm_num) (lz66).1 (lz66).2
  constructor <;> linarith [h.1, h.2]

theorem lz67 : (-1548813295243791 / 1000000000000000 : ℝ) ≤ Real.log |(-17 / 80 : ℝ)| ∧ Real.log |(-17 / 80 : ℝ)| ≤ (-1548813289800571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq25).1 (lq25).2

theorem fz67 : (43329825926609707 / 80000000000000000 : ℝ) ≤ Fx (-17 / 80 : ℝ) ∧ Fx (-17 / 80 : ℝ) ≤ (43329826019144447 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-17 / 80 : ℝ)) (by norm_num) (lz67).1 (lz67).2
  constructor <;> linarith [h.1, h.2]

theorem lz68 : (-315733251275139 / 200000000000000 : ℝ) ≤ Real.log |(-33 / 160 : ℝ)| ∧ Real.log |(-33 / 160 : ℝ)| ≤ (-1578666252971497 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq24).1 (lq24).2

theorem fz68 : (85095986348059401 / 160000000000000000 : ℝ) ≤ Fx (-33 / 160 : ℝ) ∧ Fx (-33 / 160 : ℝ) ≤ (17019197292079587 / 32000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-33 / 160 : ℝ)) (by norm_num) (lz68).1 (lz68).2
  constructor <;> linarith [h.1, h.2]

theorem lz69 : (-1609437914003327 / 1000000000000000 : ℝ) ≤ Real.log |(-1 / 5 : ℝ)| ∧ Real.log |(-1 / 5 : ℝ)| ≤ (-402359477911983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq23).1 (lq23).2

theorem fz69 : (652359477911983 / 1250000000000000 : ℝ) ≤ Fx (-1 / 5 : ℝ) ∧ Fx (-1 / 5 : ℝ) ≤ (2609437914003327 / 5000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 5 : ℝ)) (by norm_num) (lz69).1 (lz69).2
  constructor <;> linarith [h.1, h.2]

theorem lz70 : (-418494108605599 / 250000000000000 : ℝ) ≤ Real.log |(-3 / 16 : ℝ)| ∧ Real.log |(-3 / 16 : ℝ)| ≤ (-1673976432791113 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq22).1 (lq22).2

theorem fz70 : (8021929298373339 / 16000000000000000 : ℝ) ≤ Fx (-3 / 16 : ℝ) ∧ Fx (-3 / 16 : ℝ) ≤ (2005482325816797 / 4000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 16 : ℝ)) (by norm_num) (lz70).1 (lz70).2
  constructor <;> linarith [h.1, h.2]

theorem lz71 : (-871484652895429 / 500000000000000 : ℝ) ≤ Real.log |(-7 / 40 : ℝ)| ∧ Real.log |(-7 / 40 : ℝ)| ≤ (-1742969304278741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq21).1 (lq21).2

theorem fz71 : (19200785129951187 / 40000000000000000 : ℝ) ≤ Fx (-7 / 40 : ℝ) ∧ Fx (-7 / 40 : ℝ) ≤ (9600392570268003 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-7 / 40 : ℝ)) (by norm_num) (lz71).1 (lz71).2
  constructor <;> linarith [h.1, h.2]

theorem lz72 : (-355867389990489 / 200000000000000 : ℝ) ≤ Real.log |(-27 / 160 : ℝ)| ∧ Real.log |(-27 / 160 : ℝ)| ≤ (-1779336948449653 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq20).1 (lq20).2

theorem fz72 : (75042097608140631 / 160000000000000000 : ℝ) ≤ Fx (-27 / 160 : ℝ) ∧ Fx (-27 / 160 : ℝ) ≤ (15008419529743203 / 32000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-27 / 160 : ℝ)) (by norm_num) (lz72).1 (lz72).2
  constructor <;> linarith [h.1, h.2]

theorem lz73 : (-1817077277933003 / 1000000000000000 : ℝ) ≤ Real.log |(-13 / 80 : ℝ)| ∧ Real.log |(-13 / 80 : ℝ)| ≤ (-1817077276432507 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq19).1 (lq19).2

theorem fz73 : (36622004593622591 / 80000000000000000 : ℝ) ≤ Fx (-13 / 80 : ℝ) ∧ Fx (-13 / 80 : ℝ) ≤ (36622004613129039 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-13 / 80 : ℝ)) (by norm_num) (lz73).1 (lz73).2
  constructor <;> linarith [h.1, h.2]

theorem lz74 : (-464074497771463 / 250000000000000 : ℝ) ≤ Real.log |(-5 / 32 : ℝ)| ∧ Real.log |(-5 / 32 : ℝ)| ≤ (-185629798958579 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq18).1 (lq18).2

theorem fz74 : (285629798958579 / 640000000000000 : ℝ) ≤ Fx (-5 / 32 : ℝ) ∧ Fx (-5 / 32 : ℝ) ≤ (714074497771463 / 1600000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-5 / 32 : ℝ)) (by norm_num) (lz74).1 (lz74).2
  constructor <;> linarith [h.1, h.2]

theorem lz75 : (-37942399712121 / 20000000000000 : ℝ) ≤ Real.log |(-3 / 20 : ℝ)| ∧ Real.log |(-3 / 20 : ℝ)| ≤ (-379423996821209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq17).1 (lq17).2

theorem fz75 : (1738271990463627 / 4000000000000000 : ℝ) ≤ Fx (-3 / 20 : ℝ) ∧ Fx (-3 / 20 : ℝ) ≤ (173827199136363 / 400000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 20 : ℝ)) (by norm_num) (lz75).1 (lz75).2
  constructor <;> linarith [h.1, h.2]

theorem lz76 : (-496032840648919 / 250000000000000 : ℝ) ≤ Real.log |(-11 / 80 : ℝ)| ∧ Real.log |(-11 / 80 : ℝ)| ≤ (-79365254443827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq16).1 (lq16).2

theorem fz76 : (1313017798882097 / 3200000000000000 : ℝ) ≤ Fx (-11 / 80 : ℝ) ∧ Fx (-11 / 80 : ℝ) ≤ (8206361247138109 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-11 / 80 : ℝ)) (by norm_num) (lz76).1 (lz76).2
  constructor <;> linarith [h.1, h.2]

theorem lz77 : (-324912741 / 156250000 : ℝ) ≤ Real.log |(-1 / 8 : ℝ)| ∧ Real.log |(-1 / 8 : ℝ)| ≤ (-20794415409 / 10000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq15).1 (lq15).2

theorem fz77 : (30794415409 / 80000000000 : ℝ) ≤ Fx (-1 / 8 : ℝ) ∧ Fx (-1 / 8 : ℝ) ≤ (481162741 / 1250000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 8 : ℝ)) (by norm_num) (lz77).1 (lz77).2
  constructor <;> linarith [h.1, h.2]

theorem lz78 : (-266341859827139 / 125000000000000 : ℝ) ≤ Real.log |(-19 / 160 : ℝ)| ∧ Real.log |(-19 / 160 : ℝ)| ≤ (-2130734834442829 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq14).1 (lq14).2

theorem fz78 : (59483961854413751 / 160000000000000000 : ℝ) ≤ Fx (-19 / 160 : ℝ) ∧ Fx (-19 / 160 : ℝ) ≤ (7435495336715641 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-19 / 160 : ℝ)) (by norm_num) (lz78).1 (lz78).2
  constructor <;> linarith [h.1, h.2]

theorem lz79 : (-1092401036148709 / 500000000000000 : ℝ) ≤ Real.log |(-9 / 80 : ℝ)| ∧ Real.log |(-9 / 80 : ℝ)| ≤ (-2184802056133427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq13).1 (lq13).2

theorem fz79 : (28663218505200843 / 80000000000000000 : ℝ) ≤ Fx (-9 / 80 : ℝ) ∧ Fx (-9 / 80 : ℝ) ≤ (14331609325338381 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-9 / 80 : ℝ)) (by norm_num) (lz79).1 (lz79).2
  constructor <;> linarith [h.1, h.2]

theorem lz80 : (-2241960476043791 / 1000000000000000 : ℝ) ≤ Real.log |(-17 / 160 : ℝ)| ∧ Real.log |(-17 / 160 : ℝ)| ≤ (-2241960470100571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq12).1 (lq12).2

theorem fz80 : (55113327991709707 / 160000000000000000 : ℝ) ≤ Fx (-17 / 160 : ℝ) ∧ Fx (-17 / 160 : ℝ) ≤ (55113328092744447 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-17 / 160 : ℝ)) (by norm_num) (lz80).1 (lz80).2
  constructor <;> linarith [h.1, h.2]

theorem lz81 : (-2302585094803327 / 1000000000000000 : ℝ) ≤ Real.log |(-1 / 10 : ℝ)| ∧ Real.log |(-1 / 10 : ℝ)| ≤ (-575646272986983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq11).1 (lq11).2

theorem fz81 : (825646272986983 / 2500000000000000 : ℝ) ≤ Fx (-1 / 10 : ℝ) ∧ Fx (-1 / 10 : ℝ) ≤ (3302585094803327 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 10 : ℝ)) (by norm_num) (lz81).1 (lz81).2
  constructor <;> linarith [h.1, h.2]

theorem lz82 : (-1218058243295429 / 500000000000000 : ℝ) ≤ Real.log |(-7 / 80 : ℝ)| ∧ Real.log |(-7 / 80 : ℝ)| ≤ (-2436116484578741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq10).1 (lq10).2

theorem fz82 : (24052815392051187 / 80000000000000000 : ℝ) ≤ Fx (-7 / 80 : ℝ) ∧ Fx (-7 / 80 : ℝ) ≤ (12026407703068003 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-7 / 80 : ℝ)) (by norm_num) (lz82).1 (lz82).2
  constructor <;> linarith [h.1, h.2]

theorem lz83 : (-51805343328121 / 20000000000000 : ℝ) ≤ Real.log |(-3 / 40 : ℝ)| ∧ Real.log |(-3 / 40 : ℝ)| ≤ (-518053432881209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq9).1 (lq9).2

theorem fz83 : (2154160298643627 / 8000000000000000 : ℝ) ≤ Fx (-3 / 40 : ℝ) ∧ Fx (-3 / 40 : ℝ) ≤ (215416029984363 / 800000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 40 : ℝ)) (by norm_num) (lz83).1 (lz83).2
  constructor <;> linarith [h.1, h.2]

theorem lz84 : (-669319635848919 / 250000000000000 : ℝ) ≤ Real.log |(-11 / 160 : ℝ)| ∧ Real.log |(-11 / 160 : ℝ)| ≤ (-107091141655827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq8).1 (lq8).2

theorem fz84 : (1618002558214097 / 6400000000000000 : ℝ) ≤ Fx (-11 / 160 : ℝ) ∧ Fx (-11 / 160 : ℝ) ≤ (10112515994338109 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-11 / 160 : ℝ)) (by norm_num) (lz84).1 (lz84).2
  constructor <;> linarith [h.1, h.2]

theorem lz85 : (-108304247 / 39062500 : ℝ) ≤ Real.log |(-1 / 16 : ℝ)| ∧ Real.log |(-1 / 16 : ℝ)| ≤ (-6931471803 / 2500000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq7).1 (lq7).2

theorem fz85 : (9431471803 / 40000000000 : ℝ) ≤ Fx (-1 / 16 : ℝ) ∧ Fx (-1 / 16 : ℝ) ≤ (147366747 / 625000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 16 : ℝ)) (by norm_num) (lz85).1 (lz85).2
  constructor <;> linarith [h.1, h.2]

theorem lz86 : (-1438974626548709 / 500000000000000 : ℝ) ≤ Real.log |(-9 / 160 : ℝ)| ∧ Real.log |(-9 / 160 : ℝ)| ≤ (-2877949236433427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq6).1 (lq6).2

theorem fz86 : (34901543127900843 / 160000000000000000 : ℝ) ≤ Fx (-9 / 160 : ℝ) ∧ Fx (-9 / 160 : ℝ) ≤ (17450771638938381 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-9 / 160 : ℝ)) (by norm_num) (lz86).1 (lz86).2
  constructor <;> linarith [h.1, h.2]

theorem lz87 : (-2995732275603327 / 1000000000000000 : ℝ) ≤ Real.log |(-1 / 20 : ℝ)| ∧ Real.log |(-1 / 20 : ℝ)| ≤ (-748933068061983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq5).1 (lq5).2

theorem fz87 : (998933068061983 / 5000000000000000 : ℝ) ≤ Fx (-1 / 20 : ℝ) ∧ Fx (-1 / 20 : ℝ) ≤ (3995732275603327 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 20 : ℝ)) (by norm_num) (lz87).1 (lz87).2
  constructor <;> linarith [h.1, h.2]

theorem lz88 : (-65668286944121 / 20000000000000 : ℝ) ≤ Real.log |(-3 / 80 : ℝ)| ∧ Real.log |(-3 / 80 : ℝ)| ≤ (-656682868941209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq4).1 (lq4).2

theorem fz88 : (2570048606823627 / 16000000000000000 : ℝ) ≤ Fx (-3 / 80 : ℝ) ∧ Fx (-3 / 80 : ℝ) ≤ (257004860832363 / 1600000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 80 : ℝ)) (by norm_num) (lz88).1 (lz88).2
  constructor <;> linarith [h.1, h.2]

theorem lz89 : (-3688879456403327 / 1000000000000000 : ℝ) ≤ Real.log |(-1 / 40 : ℝ)| ∧ Real.log |(-1 / 40 : ℝ)| ≤ (-922219863136983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq3).1 (lq3).2

theorem fz89 : (1172219863136983 / 10000000000000000 : ℝ) ≤ Fx (-1 / 40 : ℝ) ∧ Fx (-1 / 40 : ℝ) ≤ (4688879456403327 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 40 : ℝ)) (by norm_num) (lz89).1 (lz89).2
  constructor <;> linarith [h.1, h.2]

theorem lz90 : (-79531230560121 / 20000000000000 : ℝ) ≤ Real.log |(-3 / 160 : ℝ)| ∧ Real.log |(-3 / 160 : ℝ)| ≤ (-795312305001209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq2).1 (lq2).2

theorem fz90 : (2985936915003627 / 32000000000000000 : ℝ) ≤ Fx (-3 / 160 : ℝ) ∧ Fx (-3 / 160 : ℝ) ≤ (298593691680363 / 3200000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-3 / 160 : ℝ)) (by norm_num) (lz90).1 (lz90).2
  constructor <;> linarith [h.1, h.2]

theorem lz91 : (-4382026637203327 / 1000000000000000 : ℝ) ≤ Real.log |(-1 / 80 : ℝ)| ∧ Real.log |(-1 / 80 : ℝ)| ≤ (-1095506658211983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq1).1 (lq1).2

theorem fz91 : (1345506658211983 / 20000000000000000 : ℝ) ≤ Fx (-1 / 80 : ℝ) ∧ Fx (-1 / 80 : ℝ) ≤ (5382026637203327 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 80 : ℝ)) (by norm_num) (lz91).1 (lz91).2
  constructor <;> linarith [h.1, h.2]

theorem lz92 : (-5075173818003327 / 1000000000000000 : ℝ) ≤ Real.log |(-1 / 160 : ℝ)| ∧ Real.log |(-1 / 160 : ℝ)| ≤ (-1268793453286983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq0).1 (lq0).2

theorem fz92 : (1518793453286983 / 40000000000000000 : ℝ) ≤ Fx (-1 / 160 : ℝ) ∧ Fx (-1 / 160 : ℝ) ≤ (6075173818003327 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_neg (z := (-1 / 160 : ℝ)) (by norm_num) (lz92).1 (lz92).2
  constructor <;> linarith [h.1, h.2]

theorem lz93 : (-5075173818003327 / 1000000000000000 : ℝ) ≤ Real.log |(1 / 160 : ℝ)| ∧ Real.log |(1 / 160 : ℝ)| ≤ (-1268793453286983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq0).1 (lq0).2

theorem fz93 : (-6075173818003327 / 160000000000000000 : ℝ) ≤ Fx (1 / 160 : ℝ) ∧ Fx (1 / 160 : ℝ) ≤ (-1518793453286983 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 160 : ℝ)) (by norm_num) (lz93).1 (lz93).2
  constructor <;> linarith [h.1, h.2]

theorem lz94 : (-4382026637203327 / 1000000000000000 : ℝ) ≤ Real.log |(1 / 80 : ℝ)| ∧ Real.log |(1 / 80 : ℝ)| ≤ (-1095506658211983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq1).1 (lq1).2

theorem fz94 : (-5382026637203327 / 80000000000000000 : ℝ) ≤ Fx (1 / 80 : ℝ) ∧ Fx (1 / 80 : ℝ) ≤ (-1345506658211983 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 80 : ℝ)) (by norm_num) (lz94).1 (lz94).2
  constructor <;> linarith [h.1, h.2]

theorem lz95 : (-79531230560121 / 20000000000000 : ℝ) ≤ Real.log |(3 / 160 : ℝ)| ∧ Real.log |(3 / 160 : ℝ)| ≤ (-795312305001209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq2).1 (lq2).2

theorem fz95 : (-298593691680363 / 3200000000000000 : ℝ) ≤ Fx (3 / 160 : ℝ) ∧ Fx (3 / 160 : ℝ) ≤ (-2985936915003627 / 32000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 160 : ℝ)) (by norm_num) (lz95).1 (lz95).2
  constructor <;> linarith [h.1, h.2]

theorem lz96 : (-3688879456403327 / 1000000000000000 : ℝ) ≤ Real.log |(1 / 40 : ℝ)| ∧ Real.log |(1 / 40 : ℝ)| ≤ (-922219863136983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq3).1 (lq3).2

theorem fz96 : (-4688879456403327 / 40000000000000000 : ℝ) ≤ Fx (1 / 40 : ℝ) ∧ Fx (1 / 40 : ℝ) ≤ (-1172219863136983 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 40 : ℝ)) (by norm_num) (lz96).1 (lz96).2
  constructor <;> linarith [h.1, h.2]

theorem lz97 : (-65668286944121 / 20000000000000 : ℝ) ≤ Real.log |(3 / 80 : ℝ)| ∧ Real.log |(3 / 80 : ℝ)| ≤ (-656682868941209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq4).1 (lq4).2

theorem fz97 : (-257004860832363 / 1600000000000000 : ℝ) ≤ Fx (3 / 80 : ℝ) ∧ Fx (3 / 80 : ℝ) ≤ (-2570048606823627 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 80 : ℝ)) (by norm_num) (lz97).1 (lz97).2
  constructor <;> linarith [h.1, h.2]

theorem lz98 : (-2995732275603327 / 1000000000000000 : ℝ) ≤ Real.log |(1 / 20 : ℝ)| ∧ Real.log |(1 / 20 : ℝ)| ≤ (-748933068061983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq5).1 (lq5).2

theorem fz98 : (-3995732275603327 / 20000000000000000 : ℝ) ≤ Fx (1 / 20 : ℝ) ∧ Fx (1 / 20 : ℝ) ≤ (-998933068061983 / 5000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 20 : ℝ)) (by norm_num) (lz98).1 (lz98).2
  constructor <;> linarith [h.1, h.2]

theorem lz99 : (-1438974626548709 / 500000000000000 : ℝ) ≤ Real.log |(9 / 160 : ℝ)| ∧ Real.log |(9 / 160 : ℝ)| ≤ (-2877949236433427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq6).1 (lq6).2

theorem fz99 : (-17450771638938381 / 80000000000000000 : ℝ) ≤ Fx (9 / 160 : ℝ) ∧ Fx (9 / 160 : ℝ) ≤ (-34901543127900843 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (9 / 160 : ℝ)) (by norm_num) (lz99).1 (lz99).2
  constructor <;> linarith [h.1, h.2]

theorem lz100 : (-108304247 / 39062500 : ℝ) ≤ Real.log |(1 / 16 : ℝ)| ∧ Real.log |(1 / 16 : ℝ)| ≤ (-6931471803 / 2500000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq7).1 (lq7).2

theorem fz100 : (-147366747 / 625000000 : ℝ) ≤ Fx (1 / 16 : ℝ) ∧ Fx (1 / 16 : ℝ) ≤ (-9431471803 / 40000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 16 : ℝ)) (by norm_num) (lz100).1 (lz100).2
  constructor <;> linarith [h.1, h.2]

theorem lz101 : (-669319635848919 / 250000000000000 : ℝ) ≤ Real.log |(11 / 160 : ℝ)| ∧ Real.log |(11 / 160 : ℝ)| ≤ (-107091141655827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq8).1 (lq8).2

theorem fz101 : (-10112515994338109 / 40000000000000000 : ℝ) ≤ Fx (11 / 160 : ℝ) ∧ Fx (11 / 160 : ℝ) ≤ (-1618002558214097 / 6400000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (11 / 160 : ℝ)) (by norm_num) (lz101).1 (lz101).2
  constructor <;> linarith [h.1, h.2]

theorem lz102 : (-51805343328121 / 20000000000000 : ℝ) ≤ Real.log |(3 / 40 : ℝ)| ∧ Real.log |(3 / 40 : ℝ)| ≤ (-518053432881209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq9).1 (lq9).2

theorem fz102 : (-215416029984363 / 800000000000000 : ℝ) ≤ Fx (3 / 40 : ℝ) ∧ Fx (3 / 40 : ℝ) ≤ (-2154160298643627 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 40 : ℝ)) (by norm_num) (lz102).1 (lz102).2
  constructor <;> linarith [h.1, h.2]

theorem lz103 : (-1218058243295429 / 500000000000000 : ℝ) ≤ Real.log |(7 / 80 : ℝ)| ∧ Real.log |(7 / 80 : ℝ)| ≤ (-2436116484578741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq10).1 (lq10).2

theorem fz103 : (-12026407703068003 / 40000000000000000 : ℝ) ≤ Fx (7 / 80 : ℝ) ∧ Fx (7 / 80 : ℝ) ≤ (-24052815392051187 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (7 / 80 : ℝ)) (by norm_num) (lz103).1 (lz103).2
  constructor <;> linarith [h.1, h.2]

theorem lz104 : (-2302585094803327 / 1000000000000000 : ℝ) ≤ Real.log |(1 / 10 : ℝ)| ∧ Real.log |(1 / 10 : ℝ)| ≤ (-575646272986983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq11).1 (lq11).2

theorem fz104 : (-3302585094803327 / 10000000000000000 : ℝ) ≤ Fx (1 / 10 : ℝ) ∧ Fx (1 / 10 : ℝ) ≤ (-825646272986983 / 2500000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 10 : ℝ)) (by norm_num) (lz104).1 (lz104).2
  constructor <;> linarith [h.1, h.2]

theorem lz105 : (-2241960476043791 / 1000000000000000 : ℝ) ≤ Real.log |(17 / 160 : ℝ)| ∧ Real.log |(17 / 160 : ℝ)| ≤ (-2241960470100571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq12).1 (lq12).2

theorem fz105 : (-55113328092744447 / 160000000000000000 : ℝ) ≤ Fx (17 / 160 : ℝ) ∧ Fx (17 / 160 : ℝ) ≤ (-55113327991709707 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (17 / 160 : ℝ)) (by norm_num) (lz105).1 (lz105).2
  constructor <;> linarith [h.1, h.2]

theorem lz106 : (-1092401036148709 / 500000000000000 : ℝ) ≤ Real.log |(9 / 80 : ℝ)| ∧ Real.log |(9 / 80 : ℝ)| ≤ (-2184802056133427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq13).1 (lq13).2

theorem fz106 : (-14331609325338381 / 40000000000000000 : ℝ) ≤ Fx (9 / 80 : ℝ) ∧ Fx (9 / 80 : ℝ) ≤ (-28663218505200843 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (9 / 80 : ℝ)) (by norm_num) (lz106).1 (lz106).2
  constructor <;> linarith [h.1, h.2]

theorem lz107 : (-266341859827139 / 125000000000000 : ℝ) ≤ Real.log |(19 / 160 : ℝ)| ∧ Real.log |(19 / 160 : ℝ)| ≤ (-2130734834442829 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq14).1 (lq14).2

theorem fz107 : (-7435495336715641 / 20000000000000000 : ℝ) ≤ Fx (19 / 160 : ℝ) ∧ Fx (19 / 160 : ℝ) ≤ (-59483961854413751 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (19 / 160 : ℝ)) (by norm_num) (lz107).1 (lz107).2
  constructor <;> linarith [h.1, h.2]

theorem lz108 : (-324912741 / 156250000 : ℝ) ≤ Real.log |(1 / 8 : ℝ)| ∧ Real.log |(1 / 8 : ℝ)| ≤ (-20794415409 / 10000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq15).1 (lq15).2

theorem fz108 : (-481162741 / 1250000000 : ℝ) ≤ Fx (1 / 8 : ℝ) ∧ Fx (1 / 8 : ℝ) ≤ (-30794415409 / 80000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 8 : ℝ)) (by norm_num) (lz108).1 (lz108).2
  constructor <;> linarith [h.1, h.2]

theorem lz109 : (-496032840648919 / 250000000000000 : ℝ) ≤ Real.log |(11 / 80 : ℝ)| ∧ Real.log |(11 / 80 : ℝ)| ≤ (-79365254443827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq16).1 (lq16).2

theorem fz109 : (-8206361247138109 / 20000000000000000 : ℝ) ≤ Fx (11 / 80 : ℝ) ∧ Fx (11 / 80 : ℝ) ≤ (-1313017798882097 / 3200000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (11 / 80 : ℝ)) (by norm_num) (lz109).1 (lz109).2
  constructor <;> linarith [h.1, h.2]

theorem lz110 : (-37942399712121 / 20000000000000 : ℝ) ≤ Real.log |(3 / 20 : ℝ)| ∧ Real.log |(3 / 20 : ℝ)| ≤ (-379423996821209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq17).1 (lq17).2

theorem fz110 : (-173827199136363 / 400000000000000 : ℝ) ≤ Fx (3 / 20 : ℝ) ∧ Fx (3 / 20 : ℝ) ≤ (-1738271990463627 / 4000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 20 : ℝ)) (by norm_num) (lz110).1 (lz110).2
  constructor <;> linarith [h.1, h.2]

theorem lz111 : (-464074497771463 / 250000000000000 : ℝ) ≤ Real.log |(5 / 32 : ℝ)| ∧ Real.log |(5 / 32 : ℝ)| ≤ (-185629798958579 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq18).1 (lq18).2

theorem fz111 : (-714074497771463 / 1600000000000000 : ℝ) ≤ Fx (5 / 32 : ℝ) ∧ Fx (5 / 32 : ℝ) ≤ (-285629798958579 / 640000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (5 / 32 : ℝ)) (by norm_num) (lz111).1 (lz111).2
  constructor <;> linarith [h.1, h.2]

theorem lz112 : (-1817077277933003 / 1000000000000000 : ℝ) ≤ Real.log |(13 / 80 : ℝ)| ∧ Real.log |(13 / 80 : ℝ)| ≤ (-1817077276432507 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq19).1 (lq19).2

theorem fz112 : (-36622004613129039 / 80000000000000000 : ℝ) ≤ Fx (13 / 80 : ℝ) ∧ Fx (13 / 80 : ℝ) ≤ (-36622004593622591 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (13 / 80 : ℝ)) (by norm_num) (lz112).1 (lz112).2
  constructor <;> linarith [h.1, h.2]

theorem lz113 : (-355867389990489 / 200000000000000 : ℝ) ≤ Real.log |(27 / 160 : ℝ)| ∧ Real.log |(27 / 160 : ℝ)| ≤ (-1779336948449653 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq20).1 (lq20).2

theorem fz113 : (-15008419529743203 / 32000000000000000 : ℝ) ≤ Fx (27 / 160 : ℝ) ∧ Fx (27 / 160 : ℝ) ≤ (-75042097608140631 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (27 / 160 : ℝ)) (by norm_num) (lz113).1 (lz113).2
  constructor <;> linarith [h.1, h.2]

theorem lz114 : (-871484652895429 / 500000000000000 : ℝ) ≤ Real.log |(7 / 40 : ℝ)| ∧ Real.log |(7 / 40 : ℝ)| ≤ (-1742969304278741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq21).1 (lq21).2

theorem fz114 : (-9600392570268003 / 20000000000000000 : ℝ) ≤ Fx (7 / 40 : ℝ) ∧ Fx (7 / 40 : ℝ) ≤ (-19200785129951187 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (7 / 40 : ℝ)) (by norm_num) (lz114).1 (lz114).2
  constructor <;> linarith [h.1, h.2]

theorem lz115 : (-418494108605599 / 250000000000000 : ℝ) ≤ Real.log |(3 / 16 : ℝ)| ∧ Real.log |(3 / 16 : ℝ)| ≤ (-1673976432791113 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq22).1 (lq22).2

theorem fz115 : (-2005482325816797 / 4000000000000000 : ℝ) ≤ Fx (3 / 16 : ℝ) ∧ Fx (3 / 16 : ℝ) ≤ (-8021929298373339 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 16 : ℝ)) (by norm_num) (lz115).1 (lz115).2
  constructor <;> linarith [h.1, h.2]

theorem lz116 : (-1609437914003327 / 1000000000000000 : ℝ) ≤ Real.log |(1 / 5 : ℝ)| ∧ Real.log |(1 / 5 : ℝ)| ≤ (-402359477911983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq23).1 (lq23).2

theorem fz116 : (-2609437914003327 / 5000000000000000 : ℝ) ≤ Fx (1 / 5 : ℝ) ∧ Fx (1 / 5 : ℝ) ≤ (-652359477911983 / 1250000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 5 : ℝ)) (by norm_num) (lz116).1 (lz116).2
  constructor <;> linarith [h.1, h.2]

theorem lz117 : (-315733251275139 / 200000000000000 : ℝ) ≤ Real.log |(33 / 160 : ℝ)| ∧ Real.log |(33 / 160 : ℝ)| ≤ (-1578666252971497 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq24).1 (lq24).2

theorem fz117 : (-17019197292079587 / 32000000000000000 : ℝ) ≤ Fx (33 / 160 : ℝ) ∧ Fx (33 / 160 : ℝ) ≤ (-85095986348059401 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (33 / 160 : ℝ)) (by norm_num) (lz117).1 (lz117).2
  constructor <;> linarith [h.1, h.2]

theorem lz118 : (-1548813295243791 / 1000000000000000 : ℝ) ≤ Real.log |(17 / 80 : ℝ)| ∧ Real.log |(17 / 80 : ℝ)| ≤ (-1548813289800571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq25).1 (lq25).2

theorem fz118 : (-43329826019144447 / 80000000000000000 : ℝ) ≤ Fx (17 / 80 : ℝ) ∧ Fx (17 / 80 : ℝ) ≤ (-43329825926609707 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (17 / 80 : ℝ)) (by norm_num) (lz118).1 (lz118).2
  constructor <;> linarith [h.1, h.2]

theorem lz119 : (-379956440514921 / 250000000000000 : ℝ) ≤ Real.log |(7 / 32 : ℝ)| ∧ Real.log |(7 / 32 : ℝ)| ≤ (-379956438220963 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq26).1 (lq26).2

theorem fz119 : (-4409695083604447 / 8000000000000000 : ℝ) ≤ Fx (7 / 32 : ℝ) ∧ Fx (7 / 32 : ℝ) ≤ (-4409695067546741 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (7 / 32 : ℝ)) (by norm_num) (lz119).1 (lz119).2
  constructor <;> linarith [h.1, h.2]

theorem lz120 : (-745827445748709 / 500000000000000 : ℝ) ≤ Real.log |(9 / 40 : ℝ)| ∧ Real.log |(9 / 40 : ℝ)| ≤ (-1491654875833427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq27).1 (lq27).2

theorem fz120 : (-11212447011738381 / 20000000000000000 : ℝ) ≤ Fx (9 / 40 : ℝ) ∧ Fx (9 / 40 : ℝ) ≤ (-22424893882500843 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (9 / 40 : ℝ)) (by norm_num) (lz120).1 (lz120).2
  constructor <;> linarith [h.1, h.2]

theorem lz121 : (-179698462227139 / 125000000000000 : ℝ) ≤ Real.log |(19 / 80 : ℝ)| ∧ Real.log |(19 / 80 : ℝ)| ≤ (-1437587654142829 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq28).1 (lq28).2

theorem fz121 : (-5789270782315641 / 10000000000000000 : ℝ) ≤ Fx (19 / 80 : ℝ) ∧ Fx (19 / 80 : ℝ) ≤ (-46314165428713751 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (19 / 80 : ℝ)) (by norm_num) (lz121).1 (lz121).2
  constructor <;> linarith [h.1, h.2]

theorem lz122 : (-108304247 / 78125000 : ℝ) ≤ Real.log |(1 / 4 : ℝ)| ∧ Real.log |(1 / 4 : ℝ)| ≤ (-6931471803 / 5000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq29).1 (lq29).2

theorem fz122 : (-186429247 / 312500000 : ℝ) ≤ Fx (1 / 4 : ℝ) ∧ Fx (1 / 4 : ℝ) ≤ (-11931471803 / 20000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 4 : ℝ)) (by norm_num) (lz122).1 (lz122).2
  constructor <;> linarith [h.1, h.2]

theorem lz123 : (-167188024678821 / 125000000000000 : ℝ) ≤ Real.log |(21 / 80 : ℝ)| ∧ Real.log |(21 / 80 : ℝ)| ≤ (-1337504196430567 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq30).1 (lq30).2

theorem fz123 : (-6135948518255241 / 10000000000000000 : ℝ) ≤ Fx (21 / 80 : ℝ) ∧ Fx (21 / 80 : ℝ) ≤ (-49087588125041907 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (21 / 80 : ℝ)) (by norm_num) (lz123).1 (lz123).2
  constructor <;> linarith [h.1, h.2]

theorem lz124 : (-322746045448919 / 250000000000000 : ℝ) ≤ Real.log |(11 / 40 : ℝ)| ∧ Real.log |(11 / 40 : ℝ)| ≤ (-51639367231827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq31).1 (lq31).2

theorem fz124 : (-6300206499938109 / 10000000000000000 : ℝ) ≤ Fx (11 / 40 : ℝ) ∧ Fx (11 / 40 : ℝ) ≤ (-1008033039550097 / 1600000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (11 / 40 : ℝ)) (by norm_num) (lz124).1 (lz124).2
  constructor <;> linarith [h.1, h.2]

theorem lz125 : (-623266209612421 / 500000000000000 : ℝ) ≤ Real.log |(23 / 80 : ℝ)| ∧ Real.log |(23 / 80 : ℝ)| ≤ (-1246532418224841 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq32).1 (lq32).2

theorem fz125 : (-25835122821085683 / 40000000000000000 : ℝ) ≤ Fx (23 / 80 : ℝ) ∧ Fx (23 / 80 : ℝ) ≤ (-51670245619171343 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (23 / 80 : ℝ)) (by norm_num) (lz125).1 (lz125).2
  constructor <;> linarith [h.1, h.2]

theorem lz126 : (-24079456096121 / 20000000000000 : ℝ) ≤ Real.log |(3 / 10 : ℝ)| ∧ Real.log |(3 / 10 : ℝ)| ≤ (-240794560761209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq33).1 (lq33).2

theorem fz126 : (-132238368288363 / 200000000000000 : ℝ) ≤ Fx (3 / 10 : ℝ) ∧ Fx (3 / 10 : ℝ) ≤ (-1322383682283627 / 2000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 10 : ℝ)) (by norm_num) (lz126).1 (lz126).2
  constructor <;> linarith [h.1, h.2]

theorem lz127 : (-290787702571463 / 250000000000000 : ℝ) ≤ Real.log |(5 / 16 : ℝ)| ∧ Real.log |(5 / 16 : ℝ)| ≤ (-116315080928579 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq34).1 (lq34).2

theorem fz127 : (-540787702571463 / 800000000000000 : ℝ) ≤ Fx (5 / 16 : ℝ) ∧ Fx (5 / 16 : ℝ) ≤ (-216315080928579 / 320000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (5 / 16 : ℝ)) (by norm_num) (lz127).1 (lz127).2
  constructor <;> linarith [h.1, h.2]

theorem lz128 : (-1123930097133003 / 1000000000000000 : ℝ) ≤ Real.log |(13 / 40 : ℝ)| ∧ Real.log |(13 / 40 : ℝ)| ≤ (-1123930096132507 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq35).1 (lq35).2

theorem fz128 : (-27611091262729039 / 40000000000000000 : ℝ) ≤ Fx (13 / 40 : ℝ) ∧ Fx (13 / 40 : ℝ) ≤ (-27611091249722591 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (13 / 40 : ℝ)) (by norm_num) (lz128).1 (lz128).2
  constructor <;> linarith [h.1, h.2]

theorem lz129 : (-217237953830489 / 200000000000000 : ℝ) ≤ Real.log |(27 / 80 : ℝ)| ∧ Real.log |(27 / 80 : ℝ)| ≤ (-1086189768149653 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq36).1 (lq36).2

theorem fz129 : (-11265424753423203 / 16000000000000000 : ℝ) ≤ Fx (27 / 80 : ℝ) ∧ Fx (27 / 80 : ℝ) ≤ (-56327123740040631 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (27 / 80 : ℝ)) (by norm_num) (lz129).1 (lz129).2
  constructor <;> linarith [h.1, h.2]

theorem lz130 : (-524911062495429 / 500000000000000 : ℝ) ≤ Real.log |(7 / 20 : ℝ)| ∧ Real.log |(7 / 20 : ℝ)| ≤ (-1049822123978741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq37).1 (lq37).2

theorem fz130 : (-7174377437468003 / 10000000000000000 : ℝ) ≤ Fx (7 / 20 : ℝ) ∧ Fx (7 / 20 : ℝ) ≤ (-14348754867851187 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (7 / 20 : ℝ)) (by norm_num) (lz130).1 (lz130).2
  constructor <;> linarith [h.1, h.2]

theorem lz131 : (-101473080521043 / 100000000000000 : ℝ) ≤ Real.log |(29 / 80 : ℝ)| ∧ Real.log |(29 / 80 : ℝ)| ≤ (-1014730804167317 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq38).1 (lq38).2

theorem fz131 : (-5842719335110247 / 8000000000000000 : ℝ) ≤ Fx (29 / 80 : ℝ) ∧ Fx (29 / 80 : ℝ) ≤ (-58427193320852193 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (29 / 80 : ℝ)) (by norm_num) (lz131).1 (lz131).2
  constructor <;> linarith [h.1, h.2]

theorem lz132 : (-245207313405599 / 250000000000000 : ℝ) ≤ Real.log |(3 / 8 : ℝ)| ∧ Real.log |(3 / 8 : ℝ)| ≤ (-980829252491113 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq39).1 (lq39).2

theorem fz132 : (-1485621940216797 / 2000000000000000 : ℝ) ≤ Fx (3 / 8 : ℝ) ∧ Fx (3 / 8 : ℝ) ≤ (-5942487757473339 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 8 : ℝ)) (by norm_num) (lz132).1 (lz132).2
  constructor <;> linarith [h.1, h.2]

theorem lz133 : (-948039431019327 / 1000000000000000 : ℝ) ≤ Real.log |(31 / 80 : ℝ)| ∧ Real.log |(31 / 80 : ℝ)| ≤ (-37921577186663 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq40).1 (lq40).2

theorem fz133 : (-60389222361599137 / 80000000000000000 : ℝ) ≤ Fx (31 / 80 : ℝ) ∧ Fx (31 / 80 : ℝ) ≤ (-2415568892786553 / 3200000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (31 / 80 : ℝ)) (by norm_num) (lz133).1 (lz133).2
  constructor <;> linarith [h.1, h.2]

theorem lz134 : (-916290733203327 / 1000000000000000 : ℝ) ≤ Real.log |(2 / 5 : ℝ)| ∧ Real.log |(2 / 5 : ℝ)| ≤ (-229072682836983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq41).1 (lq41).2

theorem fz134 : (-1916290733203327 / 2500000000000000 : ℝ) ≤ Fx (2 / 5 : ℝ) ∧ Fx (2 / 5 : ℝ) ≤ (-479072682836983 / 625000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (2 / 5 : ℝ)) (by norm_num) (lz134).1 (lz134).2
  constructor <;> linarith [h.1, h.2]

theorem lz135 : (-177103815115139 / 200000000000000 : ℝ) ≤ Real.log |(33 / 80 : ℝ)| ∧ Real.log |(33 / 80 : ℝ)| ≤ (-885519072671497 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq42).1 (lq42).2

theorem fz135 : (-12444425898799587 / 16000000000000000 : ℝ) ≤ Fx (33 / 80 : ℝ) ∧ Fx (33 / 80 : ℝ) ≤ (-62222129398159401 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (33 / 80 : ℝ)) (by norm_num) (lz135).1 (lz135).2
  constructor <;> linarith [h.1, h.2]

theorem lz136 : (-855666114443791 / 1000000000000000 : ℝ) ≤ Real.log |(17 / 40 : ℝ)| ∧ Real.log |(17 / 40 : ℝ)| ≤ (-855666109500571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq43).1 (lq43).2

theorem fz136 : (-31546323945544447 / 40000000000000000 : ℝ) ≤ Fx (17 / 40 : ℝ) ∧ Fx (17 / 40 : ℝ) ≤ (-31546323861509707 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (17 / 40 : ℝ)) (by norm_num) (lz136).1 (lz136).2
  constructor <;> linarith [h.1, h.2]

theorem lz137 : (-206669645314921 / 250000000000000 : ℝ) ≤ Real.log |(7 / 16 : ℝ)| ∧ Real.log |(7 / 16 : ℝ)| ≤ (-206669643145963 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq44).1 (lq44).2

theorem fz137 : (-3196687517204447 / 4000000000000000 : ℝ) ≤ Fx (7 / 16 : ℝ) ∧ Fx (7 / 16 : ℝ) ≤ (-3196687502021741 / 4000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (7 / 16 : ℝ)) (by norm_num) (lz137).1 (lz137).2
  constructor <;> linarith [h.1, h.2]

theorem lz138 : (-399253855348709 / 500000000000000 : ℝ) ≤ Real.log |(9 / 20 : ℝ)| ∧ Real.log |(9 / 20 : ℝ)| ≤ (-798507695533427 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq45).1 (lq45).2

theorem fz138 : (-8093284698138381 / 10000000000000000 : ℝ) ≤ Fx (9 / 20 : ℝ) ∧ Fx (9 / 20 : ℝ) ≤ (-16186569259800843 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (9 / 20 : ℝ)) (by norm_num) (lz138).1 (lz138).2
  constructor <;> linarith [h.1, h.2]

theorem lz139 : (-771108747138631 / 1000000000000000 : ℝ) ≤ Real.log |(37 / 80 : ℝ)| ∧ Real.log |(37 / 80 : ℝ)| ≤ (-192777180298063 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq46).1 (lq46).2

theorem fz139 : (-65531023644129347 / 80000000000000000 : ℝ) ≤ Fx (37 / 80 : ℝ) ∧ Fx (37 / 80 : ℝ) ≤ (-16382755671028331 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (37 / 80 : ℝ)) (by norm_num) (lz139).1 (lz139).2
  constructor <;> linarith [h.1, h.2]

theorem lz140 : (-93055064627139 / 125000000000000 : ℝ) ≤ Real.log |(19 / 40 : ℝ)| ∧ Real.log |(19 / 40 : ℝ)| ≤ (-744440473842829 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq47).1 (lq47).2

theorem fz140 : (-4143046227915641 / 5000000000000000 : ℝ) ≤ Fx (19 / 40 : ℝ) ∧ Fx (19 / 40 : ℝ) ≤ (-33144369003013751 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (19 / 40 : ℝ)) (by norm_num) (lz140).1 (lz140).2
  constructor <;> linarith [h.1, h.2]

theorem lz141 : (-718465056754683 / 1000000000000000 : ℝ) ≤ Real.log |(39 / 80 : ℝ)| ∧ Real.log |(39 / 80 : ℝ)| ≤ (-359232493495689 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq48).1 (lq48).2

theorem fz141 : (-67020137213432637 / 80000000000000000 : ℝ) ≤ Fx (39 / 80 : ℝ) ∧ Fx (39 / 80 : ℝ) ≤ (-33510067246331871 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (39 / 80 : ℝ)) (by norm_num) (lz141).1 (lz141).2
  constructor <;> linarith [h.1, h.2]

theorem lz142 : (-108304247 / 156250000 : ℝ) ≤ Real.log |(1 / 2 : ℝ)| ∧ Real.log |(1 / 2 : ℝ)| ≤ (-6931471803 / 10000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq49).1 (lq49).2

theorem fz142 : (-264554247 / 312500000 : ℝ) ≤ Fx (1 / 2 : ℝ) ∧ Fx (1 / 2 : ℝ) ≤ (-16931471803 / 20000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (1 / 2 : ℝ)) (by norm_num) (lz142).1 (lz142).2
  constructor <;> linarith [h.1, h.2]

theorem lz143 : (-668454568209629 / 1000000000000000 : ℝ) ≤ Real.log |(41 / 80 : ℝ)| ∧ Real.log |(41 / 80 : ℝ)| ≤ (-167113641927407 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq50).1 (lq50).2

theorem fz143 : (-68406637296594789 / 80000000000000000 : ℝ) ≤ Fx (41 / 80 : ℝ) ∧ Fx (41 / 80 : ℝ) ≤ (-17101659319023687 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (41 / 80 : ℝ)) (by norm_num) (lz143).1 (lz143).2
  constructor <;> linarith [h.1, h.2]

theorem lz144 : (-80544627078821 / 125000000000000 : ℝ) ≤ Real.log |(21 / 40 : ℝ)| ∧ Real.log |(21 / 40 : ℝ)| ≤ (-644357016130567 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq51).1 (lq51).2

theorem fz144 : (-4316437168655241 / 5000000000000000 : ℝ) ≤ Fx (21 / 40 : ℝ) ∧ Fx (21 / 40 : ℝ) ≤ (-34531497338741907 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (21 / 40 : ℝ)) (by norm_num) (lz144).1 (lz144).2
  constructor <;> linarith [h.1, h.2]

theorem lz145 : (-310413259610187 / 500000000000000 : ℝ) ≤ Real.log |(43 / 80 : ℝ)| ∧ Real.log |(43 / 80 : ℝ)| ≤ (-620826518720373 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq52).1 (lq52).2

theorem fz145 : (-34847770163238041 / 40000000000000000 : ℝ) ≤ Fx (43 / 80 : ℝ) ∧ Fx (43 / 80 : ℝ) ≤ (-69695540304976039 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (43 / 80 : ℝ)) (by norm_num) (lz145).1 (lz145).2
  constructor <;> linarith [h.1, h.2]

theorem lz146 : (-149459250248919 / 250000000000000 : ℝ) ≤ Real.log |(11 / 20 : ℝ)| ∧ Real.log |(11 / 20 : ℝ)| ≤ (-23913480019827 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq53).1 (lq53).2

theorem fz146 : (-4394051752738109 / 5000000000000000 : ℝ) ≤ Fx (11 / 20 : ℝ) ∧ Fx (11 / 20 : ℝ) ≤ (-703048280218097 / 800000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (11 / 20 : ℝ)) (by norm_num) (lz146).1 (lz146).2
  constructor <;> linarith [h.1, h.2]

theorem lz147 : (-575364145143617 / 1000000000000000 : ℝ) ≤ Real.log |(9 / 16 : ℝ)| ∧ Real.log |(9 / 16 : ℝ)| ≤ (-17980129520113 / 31250000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq54).1 (lq54).2

theorem fz147 : (-14178277306292553 / 16000000000000000 : ℝ) ≤ Fx (9 / 16 : ℝ) ∧ Fx (9 / 16 : ℝ) ≤ (-443071165681017 / 500000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (9 / 16 : ℝ)) (by norm_num) (lz147).1 (lz147).2
  constructor <;> linarith [h.1, h.2]

theorem lz148 : (-276692619212421 / 500000000000000 : ℝ) ≤ Real.log |(23 / 40 : ℝ)| ∧ Real.log |(23 / 40 : ℝ)| ≤ (-553385237924841 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq55).1 (lq55).2

theorem fz148 : (-17863930241885683 / 20000000000000000 : ℝ) ≤ Fx (23 / 40 : ℝ) ∧ Fx (23 / 40 : ℝ) ≤ (-35727860472271343 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (23 / 40 : ℝ)) (by norm_num) (lz148).1 (lz148).2
  constructor <;> linarith [h.1, h.2]

theorem lz149 : (-531879033203879 / 1000000000000000 : ℝ) ≤ Real.log |(47 / 80 : ℝ)| ∧ Real.log |(47 / 80 : ℝ)| ≤ (-531879032703877 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq56).1 (lq56).2

theorem fz149 : (-71998314560582313 / 80000000000000000 : ℝ) ≤ Fx (47 / 80 : ℝ) ∧ Fx (47 / 80 : ℝ) ≤ (-71998314537082219 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (47 / 80 : ℝ)) (by norm_num) (lz149).1 (lz149).2
  constructor <;> linarith [h.1, h.2]

theorem lz150 : (-10216512480121 / 20000000000000 : ℝ) ≤ Real.log |(3 / 5 : ℝ)| ∧ Real.log |(3 / 5 : ℝ)| ≤ (-102165124701209 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq57).1 (lq57).2

theorem fz150 : (-90649537440363 / 100000000000000 : ℝ) ≤ Fx (3 / 5 : ℝ) ∧ Fx (3 / 5 : ℝ) ≤ (-906495374103627 / 1000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 5 : ℝ)) (by norm_num) (lz150).1 (lz150).2
  constructor <;> linarith [h.1, h.2]

theorem lz151 : (-957434251569 / 1953125000000 : ℝ) ≤ Real.log |(49 / 80 : ℝ)| ∧ Real.log |(49 / 80 : ℝ)| ≤ (-490206336303309 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq58).1 (lq58).2

theorem fz151 : (-142617403326881 / 156250000000000 : ℝ) ≤ Fx (49 / 80 : ℝ) ∧ Fx (49 / 80 : ℝ) ≤ (-73020110478862141 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (49 / 80 : ℝ)) (by norm_num) (lz151).1 (lz151).2
  constructor <;> linarith [h.1, h.2]

theorem lz152 : (-117500907371463 / 250000000000000 : ℝ) ≤ Real.log |(5 / 8 : ℝ)| ∧ Real.log |(5 / 8 : ℝ)| ≤ (-47000362898579 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq59).1 (lq59).2

theorem fz152 : (-367500907371463 / 400000000000000 : ℝ) ≤ Fx (5 / 8 : ℝ) ∧ Fx (5 / 8 : ℝ) ≤ (-147000362898579 / 160000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (5 / 8 : ℝ)) (by norm_num) (lz152).1 (lz152).2
  constructor <;> linarith [h.1, h.2]

theorem lz153 : (-225100501094897 / 500000000000000 : ℝ) ≤ Real.log |(51 / 80 : ℝ)| ∧ Real.log |(51 / 80 : ℝ)| ≤ (-45020100168961 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq60).1 (lq60).2

theorem fz153 : (-36980125555839747 / 40000000000000000 : ℝ) ≤ Fx (51 / 80 : ℝ) ∧ Fx (51 / 80 : ℝ) ≤ (-7396025108617011 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (51 / 80 : ℝ)) (by norm_num) (lz153).1 (lz153).2
  constructor <;> linarith [h.1, h.2]

theorem lz154 : (-430782916333003 / 1000000000000000 : ℝ) ≤ Real.log |(13 / 20 : ℝ)| ∧ Real.log |(13 / 20 : ℝ)| ≤ (-430782915832507 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq61).1 (lq61).2

theorem fz154 : (-18600177912329039 / 20000000000000000 : ℝ) ≤ Fx (13 / 20 : ℝ) ∧ Fx (13 / 20 : ℝ) ≤ (-18600177905822591 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (13 / 20 : ℝ)) (by norm_num) (lz154).1 (lz154).2
  constructor <;> linarith [h.1, h.2]

theorem lz155 : (-411734721363033 / 1000000000000000 : ℝ) ≤ Real.log |(53 / 80 : ℝ)| ∧ Real.log |(53 / 80 : ℝ)| ≤ (-411734720861811 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq62).1 (lq62).2

theorem fz155 : (-74821940232240749 / 80000000000000000 : ℝ) ≤ Fx (53 / 80 : ℝ) ∧ Fx (53 / 80 : ℝ) ≤ (-74821940205675983 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (53 / 80 : ℝ)) (by norm_num) (lz155).1 (lz155).2
  constructor <;> linarith [h.1, h.2]

theorem lz156 : (-78608517670489 / 200000000000000 : ℝ) ≤ Real.log |(27 / 40 : ℝ)| ∧ Real.log |(27 / 40 : ℝ)| ≤ (-393042587849653 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq63).1 (lq63).2

theorem fz156 : (-7522429977103203 / 8000000000000000 : ℝ) ≤ Fx (27 / 40 : ℝ) ∧ Fx (27 / 40 : ℝ) ≤ (-37612149871940631 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (27 / 40 : ℝ)) (by norm_num) (lz156).1 (lz156).2
  constructor <;> linarith [h.1, h.2]

theorem lz157 : (-374693449687427 / 1000000000000000 : ℝ) ≤ Real.log |(11 / 16 : ℝ)| ∧ Real.log |(11 / 16 : ℝ)| ≤ (-74938689836289 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq64).1 (lq64).2

theorem fz157 : (-15121627946561697 / 16000000000000000 : ℝ) ≤ Fx (11 / 16 : ℝ) ∧ Fx (11 / 16 : ℝ) ≤ (-3024325588199179 / 3200000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (11 / 16 : ℝ)) (by norm_num) (lz157).1 (lz157).2
  constructor <;> linarith [h.1, h.2]

theorem lz158 : (-178337472095429 / 500000000000000 : ℝ) ≤ Real.log |(7 / 10 : ℝ)| ∧ Real.log |(7 / 10 : ℝ)| ≤ (-356674943678741 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq65).1 (lq65).2

theorem fz158 : (-4748362304668003 / 5000000000000000 : ℝ) ≤ Fx (7 / 10 : ℝ) ∧ Fx (7 / 10 : ℝ) ≤ (-9496724605751187 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (7 / 10 : ℝ)) (by norm_num) (lz158).1 (lz158).2
  constructor <;> linarith [h.1, h.2]

theorem lz159 : (-338975367102647 / 1000000000000000 : ℝ) ≤ Real.log |(57 / 80 : ℝ)| ∧ Real.log |(57 / 80 : ℝ)| ≤ (-42371920822411 / 125000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq66).1 (lq66).2

theorem fz159 : (-76321595924850879 / 80000000000000000 : ℝ) ≤ Fx (57 / 80 : ℝ) ∧ Fx (57 / 80 : ℝ) ≤ (-9540199486877427 / 10000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (57 / 80 : ℝ)) (by norm_num) (lz159).1 (lz159).2
  constructor <;> linarith [h.1, h.2]

theorem lz160 : (-32158362441043 / 100000000000000 : ℝ) ≤ Real.log |(29 / 40 : ℝ)| ∧ Real.log |(29 / 40 : ℝ)| ≤ (-321583623867317 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq67).1 (lq67).2

theorem fz160 : (-3832592510790247 / 4000000000000000 : ℝ) ≤ Fx (29 / 40 : ℝ) ∧ Fx (29 / 40 : ℝ) ≤ (-38325925092152193 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (29 / 40 : ℝ)) (by norm_num) (lz160).1 (lz160).2
  constructor <;> linarith [h.1, h.2]

theorem lz161 : (-78249970183389 / 250000000000000 : ℝ) ≤ Real.log |(117 / 160 : ℝ)| ∧ Real.log |(117 / 160 : ℝ)| ≤ (-156499940087923 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq68).1 (lq68).2

theorem fz161 : (-38405246511456513 / 40000000000000000 : ℝ) ≤ Fx (117 / 160 : ℝ) ∧ Fx (117 / 160 : ℝ) ≤ (-76810492990286991 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (117 / 160 : ℝ)) (by norm_num) (lz161).1 (lz161).2
  constructor <;> linarith [h.1, h.2]

theorem lz162 : (-304489191084377 / 1000000000000000 : ℝ) ≤ Real.log |(59 / 80 : ℝ)| ∧ Real.log |(59 / 80 : ℝ)| ≤ (-30448919050783 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq69).1 (lq69).2

theorem fz162 : (-76964862273978243 / 80000000000000000 : ℝ) ≤ Fx (59 / 80 : ℝ) ∧ Fx (59 / 80 : ℝ) ≤ (-7696486223996197 / 8000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (59 / 80 : ℝ)) (by norm_num) (lz162).1 (lz162).2
  constructor <;> linarith [h.1, h.2]

theorem lz163 : (-296050322462479 / 1000000000000000 : ℝ) ≤ Real.log |(119 / 160 : ℝ)| ∧ Real.log |(119 / 160 : ℝ)| ≤ (-296050321861821 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq70).1 (lq70).2

theorem fz163 : (-154229988373035001 / 160000000000000000 : ℝ) ≤ Fx (119 / 160 : ℝ) ∧ Fx (119 / 160 : ℝ) ≤ (-154229988301556699 / 160000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (119 / 160 : ℝ)) (by norm_num) (lz163).1 (lz163).2
  constructor <;> linarith [h.1, h.2]

theorem lz164 : (-71920518205599 / 250000000000000 : ℝ) ≤ Real.log |(3 / 4 : ℝ)| ∧ Real.log |(3 / 4 : ℝ)| ≤ (-287682072191113 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq71).1 (lq71).2

theorem fz164 : (-965761554616797 / 1000000000000000 : ℝ) ≤ Fx (3 / 4 : ℝ) ∧ Fx (3 / 4 : ℝ) ≤ (-3863046216573339 / 4000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (3 / 4 : ℝ)) (by norm_num) (lz164).1 (lz164).2
  constructor <;> linarith [h.1, h.2]

theorem lz165 : (-135576385478787 / 500000000000000 : ℝ) ≤ Real.log |(61 / 80 : ℝ)| ∧ Real.log |(61 / 80 : ℝ)| ≤ (-271152770239323 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq72).1 (lq72).2

theorem fz165 : (-38770159514206007 / 40000000000000000 : ℝ) ≤ Fx (61 / 80 : ℝ) ∧ Fx (61 / 80 : ℝ) ≤ (-77540318984598703 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (61 / 80 : ℝ)) (by norm_num) (lz165).1 (lz165).2
  constructor <;> linarith [h.1, h.2]

theorem lz166 : (-254892250219327 / 1000000000000000 : ℝ) ≤ Real.log |(31 / 40 : ℝ)| ∧ Real.log |(31 / 40 : ℝ)| ≤ (-10195689974663 / 40000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq73).1 (lq73).2

theorem fz166 : (-38901659756799137 / 40000000000000000 : ℝ) ≤ Fx (31 / 40 : ℝ) ∧ Fx (31 / 40 : ℝ) ≤ (-1556066389214553 / 1600000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (31 / 40 : ℝ)) (by norm_num) (lz166).1 (lz166).2
  constructor <;> linarith [h.1, h.2]

theorem lz167 : (-49372015722547 / 200000000000000 : ℝ) ≤ Real.log |(25 / 32 : ℝ)| ∧ Real.log |(25 / 32 : ℝ)| ≤ (-246860077668617 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq74).1 (lq74).2

theorem fz167 : (-249372015722547 / 256000000000000 : ℝ) ≤ Fx (25 / 32 : ℝ) ∧ Fx (25 / 32 : ℝ) ≤ (-1246860077668617 / 1280000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (25 / 32 : ℝ)) (by norm_num) (lz167).1 (lz167).2
  constructor <;> linarith [h.1, h.2]

theorem lz168 : (-238891909074311 / 1000000000000000 : ℝ) ≤ Real.log |(63 / 80 : ℝ)| ∧ Real.log |(63 / 80 : ℝ)| ≤ (-119445954009281 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq75).1 (lq75).2

theorem fz168 : (-78050190271681593 / 80000000000000000 : ℝ) ≤ Fx (63 / 80 : ℝ) ∧ Fx (63 / 80 : ℝ) ≤ (-39025095102584703 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (63 / 80 : ℝ)) (by norm_num) (lz168).1 (lz168).2
  constructor <;> linarith [h.1, h.2]

theorem lz169 : (-115493364850873 / 500000000000000 : ℝ) ≤ Real.log |(127 / 160 : ℝ)| ∧ Real.log |(127 / 160 : ℝ)| ≤ (-115493364255171 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq76).1 (lq76).2

theorem fz169 : (-78167657336060871 / 80000000000000000 : ℝ) ≤ Fx (127 / 160 : ℝ) ∧ Fx (127 / 160 : ℝ) ≤ (-78167657260406717 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (127 / 160 : ℝ)) (by norm_num) (lz169).1 (lz169).2
  constructor <;> linarith [h.1, h.2]

theorem lz170 : (-223143552403327 / 1000000000000000 : ℝ) ≤ Real.log |(4 / 5 : ℝ)| ∧ Real.log |(4 / 5 : ℝ)| ≤ (-55785887761983 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq77).1 (lq77).2

theorem fz170 : (-1223143552403327 / 1250000000000000 : ℝ) ≤ Fx (4 / 5 : ℝ) ∧ Fx (4 / 5 : ℝ) ≤ (-305785887761983 / 312500000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (4 / 5 : ℝ)) (by norm_num) (lz170).1 (lz170).2
  constructor <;> linarith [h.1, h.2]

theorem lz171 : (-207639366296933 / 1000000000000000 : ℝ) ≤ Real.log |(13 / 16 : ℝ)| ∧ Real.log |(13 / 16 : ℝ)| ≤ (-41527872901623 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq78).1 (lq78).2

theorem fz171 : (-15699311761860129 / 16000000000000000 : ℝ) ≤ Fx (13 / 16 : ℝ) ∧ Fx (13 / 16 : ℝ) ≤ (-3139862347721099 / 3200000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (13 / 16 : ℝ)) (by norm_num) (lz171).1 (lz171).2
  constructor <;> linarith [h.1, h.2]

theorem lz172 : (-38474378955139 / 200000000000000 : ℝ) ≤ Real.log |(33 / 40 : ℝ)| ∧ Real.log |(33 / 40 : ℝ)| ≤ (-192371892371497 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq79).1 (lq79).2

theorem fz172 : (-7869654505519587 / 8000000000000000 : ℝ) ≤ Fx (33 / 40 : ℝ) ∧ Fx (33 / 40 : ℝ) ≤ (-39348272448259401 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (33 / 40 : ℝ)) (by norm_num) (lz172).1 (lz172).2
  constructor <;> linarith [h.1, h.2]

theorem lz173 : (-92412344765489 / 500000000000000 : ℝ) ≤ Real.log |(133 / 160 : ℝ)| ∧ Real.log |(133 / 160 : ℝ)| ≤ (-92412343366103 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq80).1 (lq80).2

theorem fz173 : (-78790841853810037 / 80000000000000000 : ℝ) ≤ Fx (133 / 160 : ℝ) ∧ Fx (133 / 160 : ℝ) ≤ (-78790841667691699 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (133 / 160 : ℝ)) (by norm_num) (lz173).1 (lz173).2
  constructor <;> linarith [h.1, h.2]

theorem lz174 : (-88667009130713 / 500000000000000 : ℝ) ≤ Real.log |(67 / 80 : ℝ)| ∧ Real.log |(67 / 80 : ℝ)| ≤ (-177334014998309 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq81).1 (lq81).2

theorem fz174 : (-39440689611757771 / 40000000000000000 : ℝ) ≤ Fx (67 / 80 : ℝ) ∧ Fx (67 / 80 : ℝ) ≤ (-78881379004886703 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (67 / 80 : ℝ)) (by norm_num) (lz174).1 (lz174).2
  constructor <;> linarith [h.1, h.2]

theorem lz175 : (-42474760078133 / 250000000000000 : ℝ) ≤ Real.log |(27 / 32 : ℝ)| ∧ Real.log |(27 / 32 : ℝ)| ≤ (-16989903650507 / 100000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq82).1 (lq82).2

theorem fz175 : (-7896818522109591 / 8000000000000000 : ℝ) ≤ Fx (27 / 32 : ℝ) ∧ Fx (27 / 32 : ℝ) ≤ (-3158727398563689 / 3200000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (27 / 32 : ℝ)) (by norm_num) (lz175).1 (lz175).2
  constructor <;> linarith [h.1, h.2]

theorem lz176 : (-162518933643791 / 1000000000000000 : ℝ) ≤ Real.log |(17 / 20 : ℝ)| ∧ Real.log |(17 / 20 : ℝ)| ≤ (-162518929200571 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq83).1 (lq83).2

theorem fz176 : (-19762821871944447 / 20000000000000000 : ℝ) ≤ Fx (17 / 20 : ℝ) ∧ Fx (17 / 20 : ℝ) ≤ (-19762821796409707 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (17 / 20 : ℝ)) (by norm_num) (lz176).1 (lz176).2
  constructor <;> linarith [h.1, h.2]

theorem lz177 : (-147920135802533 / 1000000000000000 : ℝ) ≤ Real.log |(69 / 80 : ℝ)| ∧ Real.log |(69 / 80 : ℝ)| ≤ (-7396006488069 / 50000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq84).1 (lq84).2

theorem fz177 : (-79206489370374777 / 80000000000000000 : ℝ) ≤ Fx (69 / 80 : ℝ) ∧ Fx (69 / 80 : ℝ) ≤ (-3960324447676761 / 4000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (69 / 80 : ℝ)) (by norm_num) (lz177).1 (lz177).2
  constructor <;> linarith [h.1, h.2]

theorem lz178 : (-33382850114921 / 250000000000000 : ℝ) ≤ Real.log |(7 / 8 : ℝ)| ∧ Real.log |(7 / 8 : ℝ)| ≤ (-33382848070963 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq85).1 (lq85).2

theorem fz178 : (-1983679950804447 / 2000000000000000 : ℝ) ≤ Fx (7 / 8 : ℝ) ∧ Fx (7 / 8 : ℝ) ≤ (-1983679936496741 / 2000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (7 / 8 : ℝ)) (by norm_num) (lz178).1 (lz178).2
  constructor <;> linarith [h.1, h.2]

theorem lz179 : (-7900870874207 / 62500000000000 : ℝ) ≤ Real.log |(141 / 160 : ℝ)| ∧ Real.log |(141 / 160 : ℝ)| ≤ (-25282784899749 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq86).1 (lq86).2

theorem fz179 : (-9926522793263187 / 10000000000000000 : ℝ) ≤ Fx (141 / 160 : ℝ) ∧ Fx (141 / 160 : ℝ) ≤ (-31764872670864609 / 32000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (141 / 160 : ℝ)) (by norm_num) (lz179).1 (lz179).2
  constructor <;> linarith [h.1, h.2]

theorem lz180 : (-29836692062139 / 250000000000000 : ℝ) ≤ Real.log |(71 / 80 : ℝ)| ∧ Real.log |(71 / 80 : ℝ)| ≤ (-29836689314143 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq87).1 (lq87).2

theorem fz180 : (-19868405136411869 / 20000000000000000 : ℝ) ≤ Fx (71 / 80 : ℝ) ∧ Fx (71 / 80 : ℝ) ≤ (-19868404941304153 / 20000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (71 / 80 : ℝ)) (by norm_num) (lz180).1 (lz180).2
  constructor <;> linarith [h.1, h.2]

theorem lz181 : (-4493167891377 / 40000000000000 : ℝ) ≤ Real.log |(143 / 160 : ℝ)| ∧ Real.log |(143 / 160 : ℝ)| ≤ (-28082296143897 / 250000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq88).1 (lq88).2

theorem fz181 : (-6362523008466911 / 6400000000000000 : ℝ) ≤ Fx (143 / 160 : ℝ) ∧ Fx (143 / 160 : ℝ) ≤ (-39765768348577271 / 40000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (143 / 160 : ℝ)) (by norm_num) (lz181).1 (lz181).2
  constructor <;> linarith [h.1, h.2]

theorem lz182 : (-91567212435613 / 1000000000000000 : ℝ) ≤ Real.log |(73 / 80 : ℝ)| ∧ Real.log |(73 / 80 : ℝ)| ≤ (-91567193035597 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq89).1 (lq89).2

theorem fz182 : (-79684406507799749 / 80000000000000000 : ℝ) ≤ Fx (73 / 80 : ℝ) ∧ Fx (73 / 80 : ℝ) ≤ (-79684405091598581 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (73 / 80 : ℝ)) (by norm_num) (lz182).1 (lz182).2
  constructor <;> linarith [h.1, h.2]

theorem lz183 : (-64538553536539 / 1000000000000000 : ℝ) ≤ Real.log |(15 / 16 : ℝ)| ∧ Real.log |(15 / 16 : ℝ)| ≤ (-32269260222167 / 500000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq90).1 (lq90).2

theorem fz183 : (-3193615660609617 / 3200000000000000 : ℝ) ≤ Fx (15 / 16 : ℝ) ∧ Fx (15 / 16 : ℝ) ≤ (-1596807780666501 / 1600000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (15 / 16 : ℝ)) (by norm_num) (lz183).1 (lz183).2
  constructor <;> linarith [h.1, h.2]

theorem lz184 : (-9555316590339 / 250000000000000 : ℝ) ≤ Real.log |(77 / 80 : ℝ)| ∧ Real.log |(77 / 80 : ℝ)| ≤ (-7644242355843 / 200000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq91).1 (lq91).2

theorem fz184 : (-19985759377456103 / 20000000000000000 : ℝ) ≤ Fx (77 / 80 : ℝ) ∧ Fx (77 / 80 : ℝ) ≤ (-15988606661399911 / 16000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (77 / 80 : ℝ)) (by norm_num) (lz184).1 (lz184).2
  constructor <;> linarith [h.1, h.2]

theorem lz185 : (-1257886782209 / 100000000000000 : ℝ) ≤ Real.log |(79 / 80 : ℝ)| ∧ Real.log |(79 / 80 : ℝ)| ≤ (-12578780593379 / 1000000000000000 : ℝ) :=
  logabs_bounds (by norm_num) (lq92).1 (lq92).2

theorem fz185 : (-7999373055794511 / 8000000000000000 : ℝ) ≤ Fx (79 / 80 : ℝ) ∧ Fx (79 / 80 : ℝ) ≤ (-79993723666876941 / 80000000000000000 : ℝ) := by
  have h := Fx_bounds_pos (z := (79 / 80 : ℝ)) (by norm_num) (lz185).1 (lz185).2
  constructor <;> linarith [h.1, h.2]

/-! ## The boxes (generated) -/

set_option maxHeartbeats 4000000 in
theorem box0 (κ : ℝ) (ha : (0 : ℝ) ≤ κ) (hb : κ ≤ (1 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (-2 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (27 / 40 : ℝ) + (1 : ℝ) * Fx (29 / 40 : ℝ) + (1 : ℝ) * Fx (31 / 40 : ℝ) + (2 : ℝ) * Fx (33 / 40 : ℝ) + (-1 : ℝ) * (Fx (67 / 80 : ℝ) + Real.log |(67 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 8 : ℝ) + (-1 : ℝ) * (Fx (71 / 80 : ℝ) + Real.log |(71 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (15 / 16 : ℝ) + Real.log |(15 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (79 / 80 : ℝ) + Real.log |(79 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz166).1, (fz166).2, (fz170).1, (fz170).2, (fz172).1, (fz172).2, (fz174).1, (fz174).2, (lz174).1, (lz174).2, (fz176).1, (fz176).2, (fz178).1, (fz178).2, (fz180).1, (fz180).2, (lz180).1, (lz180).2, (fz183).1, (fz183).2, (lz183).1, (lz183).2, (fz185).1, (fz185).2, (lz185).1, (lz185).2]
  have hEb : (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (-2 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (1 : ℝ) * Fx (7 / 10 : ℝ) + (1 : ℝ) * Fx (3 / 4 : ℝ) + (2 : ℝ) * Fx (4 / 5 : ℝ) + (-1 : ℝ) * (Fx (67 / 80 : ℝ) + Real.log |(67 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (17 / 20 : ℝ) + (-1 : ℝ) * (Fx (71 / 80 : ℝ) + Real.log |(71 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (15 / 16 : ℝ) + Real.log |(15 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (79 / 80 : ℝ) + Real.log |(79 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz166).1, (fz166).2, (fz170).1, (fz170).2, (fz172).1, (fz172).2, (fz174).1, (fz174).2, (lz174).1, (lz174).2, (fz176).1, (fz176).2, (fz178).1, (fz178).2, (fz180).1, (fz180).2, (lz180).1, (lz180).2, (fz183).1, (fz183).2, (lz183).1, (lz183).2, (fz185).1, (fz185).2, (lz185).1, (lz185).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (0 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (2 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t2 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 40 : ℝ)) (z := (4 : ℝ) / 40 - κ) (z2 := (1 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t3 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 80 : ℝ)) (z := (5 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t4 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 8 : ℝ)) (z := (6 : ℝ) / 40 - κ) (z2 := (3 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (13 / 80 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 80 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (21 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (5 / 16 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 20 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (27 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 10 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (29 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 4 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (31 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (4 / 5 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (33 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (67 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (17 / 20 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (7 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (71 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (15 / 16 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (79 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box1 (κ : ℝ) (ha : (1 / 40 : ℝ) ≤ κ) (hb : κ ≤ (1 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (-2 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (1 : ℝ) * Fx (7 / 10 : ℝ) + (1 : ℝ) * Fx (3 / 4 : ℝ) + (2 : ℝ) * Fx (4 / 5 : ℝ) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (17 / 20 : ℝ) + (-1 : ℝ) * (Fx (69 / 80 : ℝ) + Real.log |(69 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (73 / 80 : ℝ) + Real.log |(73 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (77 / 80 : ℝ) + Real.log |(77 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz166).1, (fz166).2, (fz170).1, (fz170).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2, (fz172).1, (fz172).2, (fz176).1, (fz176).2, (fz177).1, (fz177).2, (lz177).1, (lz177).2, (fz182).1, (fz182).2, (lz182).1, (lz182).2, (fz184).1, (fz184).2, (lz184).1, (lz184).2]
  have hEb : (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (0 : ℝ) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (-2 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (1 : ℝ) * Fx (27 / 40 : ℝ) + (1 : ℝ) * Fx (29 / 40 : ℝ) + (2 : ℝ) * Fx (31 / 40 : ℝ) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (33 / 40 : ℝ) + (-1 : ℝ) * (Fx (69 / 80 : ℝ) + Real.log |(69 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (73 / 80 : ℝ) + Real.log |(73 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (77 / 80 : ℝ) + Real.log |(77 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz166).1, (fz166).2, (fz170).1, (fz170).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2, (fz172).1, (fz172).2, (fz176).1, (fz176).2, (fz177).1, (fz177).2, (lz177).1, (lz177).2, (fz182).1, (fz182).2, (lz182).1, (lz182).2, (fz184).1, (fz184).2, (lz184).1, (lz184).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (1 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := chord_up_pos (w := (1 : ℝ)) (z1 := (0 : ℝ)) (z := (2 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t2 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 20 : ℝ)) (z := (4 : ℝ) / 40 - κ) (z2 := (3 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t3 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (5 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t4 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 10 : ℝ)) (z := (6 : ℝ) / 40 - κ) (z2 := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 16 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (23 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (5 / 8 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (13 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (27 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (7 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (29 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (31 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (4 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 16 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (33 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (17 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (69 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (73 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (77 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box2 (κ : ℝ) (ha : (1 / 20 : ℝ) ≤ κ) (hb : κ ≤ (3 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (-2 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (1 : ℝ) * Fx (27 / 40 : ℝ) + (1 : ℝ) * Fx (29 / 40 : ℝ) + (2 : ℝ) * Fx (31 / 40 : ℝ) + (-1 : ℝ) * (Fx (63 / 80 : ℝ) + Real.log |(63 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (33 / 40 : ℝ) + (-1 : ℝ) * (Fx (67 / 80 : ℝ) + Real.log |(67 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (71 / 80 : ℝ) + Real.log |(71 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (15 / 16 : ℝ) + Real.log |(15 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz166).1, (fz166).2, (fz168).1, (fz168).2, (lz168).1, (lz168).2, (fz170).1, (fz170).2, (fz172).1, (fz172).2, (fz174).1, (fz174).2, (lz174).1, (lz174).2, (fz180).1, (fz180).2, (lz180).1, (lz180).2, (fz183).1, (fz183).2, (lz183).1, (lz183).2]
  have hEb : (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (-2 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (1 : ℝ) * Fx (7 / 10 : ℝ) + (2 : ℝ) * Fx (3 / 4 : ℝ) + (-1 : ℝ) * (Fx (63 / 80 : ℝ) + Real.log |(63 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (4 / 5 : ℝ) + (-1 : ℝ) * (Fx (67 / 80 : ℝ) + Real.log |(67 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (71 / 80 : ℝ) + Real.log |(71 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (15 / 16 : ℝ) + Real.log |(15 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz166).1, (fz166).2, (fz168).1, (fz168).2, (lz168).1, (lz168).2, (fz170).1, (fz170).2, (fz172).1, (fz172).2, (fz174).1, (fz174).2, (lz174).1, (lz174).2, (fz180).1, (fz180).2, (lz180).1, (lz180).2, (fz183).1, (fz183).2, (lz183).1, (lz183).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (3 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (1 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (4 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t3 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 16 : ℝ)) (z := (5 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t4 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 40 : ℝ)) (z := (6 : ℝ) / 40 - κ) (z2 := (1 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (9 / 80 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 80 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (21 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 5 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (5 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 20 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (27 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 10 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (29 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (3 / 4 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (31 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (63 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (4 / 5 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (33 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (67 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (71 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (15 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box3 (κ : ℝ) (ha : (3 / 40 : ℝ) ≤ κ) (hb : κ ≤ (1 / 10 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (-2 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (1 : ℝ) * Fx (7 / 10 : ℝ) + (2 : ℝ) * Fx (3 / 4 : ℝ) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (4 / 5 : ℝ) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (69 / 80 : ℝ) + Real.log |(69 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (73 / 80 : ℝ) + Real.log |(73 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz166).1, (fz166).2, (fz170).1, (fz170).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2, (fz177).1, (fz177).2, (lz177).1, (lz177).2, (fz182).1, (fz182).2, (lz182).1, (lz182).2]
  have hEb : (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (-2 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (1 : ℝ) * Fx (27 / 40 : ℝ) + (2 : ℝ) * Fx (29 / 40 : ℝ) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (31 / 40 : ℝ) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (69 / 80 : ℝ) + Real.log |(69 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (73 / 80 : ℝ) + Real.log |(73 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz166).1, (fz166).2, (fz170).1, (fz170).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2, (fz177).1, (fz177).2, (lz177).1, (lz177).2, (fz182).1, (fz182).2, (lz182).1, (lz182).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 / 10 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (3 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := chord_up_pos (w := (1 : ℝ)) (z1 := (0 : ℝ)) (z := (4 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t3 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (5 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t4 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 20 : ℝ)) (z := (6 : ℝ) / 40 - κ) (z2 := (3 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 16 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (23 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (3 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (5 / 8 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (13 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (27 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (7 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (29 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (61 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (31 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (4 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 16 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (69 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (73 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box4 (κ : ℝ) (ha : (1 / 10 : ℝ) ≤ κ) (hb : κ ≤ (9 / 80 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-17 / 160 : ℝ) + Real.log |(-17 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-9 / 160 : ℝ) + Real.log |(-9 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-1 / 160 : ℝ) + Real.log |(-1 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (3 / 160 : ℝ) + Real.log |(3 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (-2 : ℝ) * (Fx (11 / 160 : ℝ) + Real.log |(11 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (19 / 160 : ℝ) + Real.log |(19 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (27 / 160 : ℝ) + Real.log |(27 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (7 / 32 : ℝ) + Real.log |(7 / 32 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (1 : ℝ) * Fx (27 / 40 : ℝ) + (2 : ℝ) * Fx (29 / 40 : ℝ) + (-1 : ℝ) * (Fx (119 / 160 : ℝ) + Real.log |(119 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * Fx (31 / 40 : ℝ) + (-1 : ℝ) * (Fx (127 / 160 : ℝ) + Real.log |(127 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (27 / 32 : ℝ) + Real.log |(27 / 32 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (143 / 160 : ℝ) + Real.log |(143 / 160 : ℝ)| * (1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz80).1, (fz80).2, (lz80).1, (lz80).2, (fz86).1, (fz86).2, (lz86).1, (lz86).2, (fz92).1, (fz92).2, (lz92).1, (lz92).2, (fz95).1, (fz95).2, (lz95).1, (lz95).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz98).1, (fz98).2, (fz101).1, (fz101).2, (lz101).1, (lz101).2, (fz107).1, (fz107).2, (lz107).1, (lz107).2, (fz113).1, (fz113).2, (lz113).1, (lz113).2, (fz119).1, (fz119).2, (lz119).1, (lz119).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz148).1, (fz148).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz152).1, (fz152).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz156).1, (fz156).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz160).1, (fz160).2, (fz163).1, (fz163).2, (lz163).1, (lz163).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz166).1, (fz166).2, (fz169).1, (fz169).2, (lz169).1, (lz169).2, (fz175).1, (fz175).2, (lz175).1, (lz175).2, (fz181).1, (fz181).2, (lz181).1, (lz181).2]
  have hEb : (1 : ℝ) * (Fx (-17 / 160 : ℝ) + Real.log |(-17 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-9 / 160 : ℝ) + Real.log |(-9 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-1 / 160 : ℝ) + Real.log |(-1 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (3 / 160 : ℝ) + Real.log |(3 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * Fx (3 / 80 : ℝ) + (-2 : ℝ) * (Fx (11 / 160 : ℝ) + Real.log |(11 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (19 / 160 : ℝ) + Real.log |(19 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (27 / 160 : ℝ) + Real.log |(27 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (7 / 32 : ℝ) + Real.log |(7 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * Fx (9 / 16 : ℝ) + (1 : ℝ) * Fx (49 / 80 : ℝ) + (1 : ℝ) * Fx (53 / 80 : ℝ) + (2 : ℝ) * Fx (57 / 80 : ℝ) + (-1 : ℝ) * (Fx (119 / 160 : ℝ) + Real.log |(119 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * Fx (61 / 80 : ℝ) + (-1 : ℝ) * (Fx (127 / 160 : ℝ) + Real.log |(127 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (27 / 32 : ℝ) + Real.log |(27 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (143 / 160 : ℝ) + Real.log |(143 / 160 : ℝ)| * (-1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz80).1, (fz80).2, (lz80).1, (lz80).2, (fz86).1, (fz86).2, (lz86).1, (lz86).2, (fz92).1, (fz92).2, (lz92).1, (lz92).2, (fz95).1, (fz95).2, (lz95).1, (lz95).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz98).1, (fz98).2, (fz101).1, (fz101).2, (lz101).1, (lz101).2, (fz107).1, (fz107).2, (lz107).1, (lz107).2, (fz113).1, (fz113).2, (lz113).1, (lz113).2, (fz119).1, (fz119).2, (lz119).1, (lz119).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz148).1, (fz148).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz152).1, (fz152).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz156).1, (fz156).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz160).1, (fz160).2, (fz163).1, (fz163).2, (lz163).1, (lz163).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz166).1, (fz166).2, (fz169).1, (fz169).2, (lz169).1, (lz169).2, (fz175).1, (fz175).2, (lz175).1, (lz175).2, (fz181).1, (fz181).2, (lz181).1, (lz181).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (9 / 80 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (1 / 10 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 160 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 160 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 160 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 160 : ℝ)) (z := (5 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t4 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (11 / 160 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 160 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (27 / 160 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 32 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 16 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (23 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (49 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (5 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (53 / 80 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (27 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (57 / 80 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (29 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (119 / 160 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (61 / 80 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (31 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (127 / 160 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (27 / 32 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (143 / 160 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box5 (κ : ℝ) (ha : (9 / 80 : ℝ) ≤ κ) (hb : κ ≤ (1 / 8 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-19 / 160 : ℝ) + Real.log |(-19 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-11 / 160 : ℝ) + Real.log |(-11 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-3 / 160 : ℝ) + Real.log |(-3 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (1 / 160 : ℝ) + Real.log |(1 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * Fx (3 / 80 : ℝ) + (-2 : ℝ) * (Fx (9 / 160 : ℝ) + Real.log |(9 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (17 / 160 : ℝ) + Real.log |(17 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (5 / 32 : ℝ) + Real.log |(5 / 32 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (33 / 160 : ℝ) + Real.log |(33 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * Fx (9 / 16 : ℝ) + (1 : ℝ) * Fx (49 / 80 : ℝ) + (1 : ℝ) * Fx (53 / 80 : ℝ) + (2 : ℝ) * Fx (57 / 80 : ℝ) + (-1 : ℝ) * (Fx (117 / 160 : ℝ) + Real.log |(117 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * Fx (61 / 80 : ℝ) + (-1 : ℝ) * (Fx (25 / 32 : ℝ) + Real.log |(25 / 32 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (133 / 160 : ℝ) + Real.log |(133 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (141 / 160 : ℝ) + Real.log |(141 / 160 : ℝ)| * (1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz78).1, (fz78).2, (lz78).1, (lz78).2, (fz84).1, (fz84).2, (lz84).1, (lz84).2, (fz90).1, (fz90).2, (lz90).1, (lz90).2, (fz93).1, (fz93).2, (lz93).1, (lz93).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz99).1, (fz99).2, (lz99).1, (lz99).2, (fz105).1, (fz105).2, (lz105).1, (lz105).2, (fz111).1, (fz111).2, (lz111).1, (lz111).2, (fz117).1, (fz117).2, (lz117).1, (lz117).2, (fz146).1, (fz146).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz150).1, (fz150).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz154).1, (fz154).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz158).1, (fz158).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz161).1, (fz161).2, (lz161).1, (lz161).2, (fz164).1, (fz164).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz167).1, (fz167).2, (lz167).1, (lz167).2, (fz173).1, (fz173).2, (lz173).1, (lz173).2, (fz179).1, (fz179).2, (lz179).1, (lz179).2]
  have hEb : (1 : ℝ) * (Fx (-19 / 160 : ℝ) + Real.log |(-19 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-11 / 160 : ℝ) + Real.log |(-11 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-3 / 160 : ℝ) + Real.log |(-3 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (1 / 160 : ℝ) + Real.log |(1 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (-2 : ℝ) * (Fx (9 / 160 : ℝ) + Real.log |(9 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (17 / 160 : ℝ) + Real.log |(17 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (5 / 32 : ℝ) + Real.log |(5 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (33 / 160 : ℝ) + Real.log |(33 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (2 : ℝ) * Fx (7 / 10 : ℝ) + (-1 : ℝ) * (Fx (117 / 160 : ℝ) + Real.log |(117 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * Fx (3 / 4 : ℝ) + (-1 : ℝ) * (Fx (25 / 32 : ℝ) + Real.log |(25 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (133 / 160 : ℝ) + Real.log |(133 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (141 / 160 : ℝ) + Real.log |(141 / 160 : ℝ)| * (-1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz78).1, (fz78).2, (lz78).1, (lz78).2, (fz84).1, (fz84).2, (lz84).1, (lz84).2, (fz90).1, (fz90).2, (lz90).1, (lz90).2, (fz93).1, (fz93).2, (lz93).1, (lz93).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz99).1, (fz99).2, (lz99).1, (lz99).2, (fz105).1, (fz105).2, (lz105).1, (lz105).2, (fz111).1, (fz111).2, (lz111).1, (lz111).2, (fz117).1, (fz117).2, (lz117).1, (lz117).2, (fz146).1, (fz146).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz150).1, (fz150).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz154).1, (fz154).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz158).1, (fz158).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz161).1, (fz161).2, (lz161).1, (lz161).2, (fz164).1, (fz164).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz167).1, (fz167).2, (lz167).1, (lz167).2, (fz173).1, (fz173).2, (lz173).1, (lz173).2, (fz179).1, (fz179).2, (lz179).1, (lz179).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 / 8 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (9 / 80 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 160 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 160 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 160 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 160 : ℝ)) (z := (5 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t4 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (6 : ℝ) / 40 - κ) (z2 := (3 / 80 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (9 / 160 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 160 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (5 / 32 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (33 / 160 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 20 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (9 / 16 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 5 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (49 / 80 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 20 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (53 / 80 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (7 / 10 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (57 / 80 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (117 / 160 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 4 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (61 / 80 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (25 / 32 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (133 / 160 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (141 / 160 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box6 (κ : ℝ) (ha : (1 / 8 : ℝ) ≤ κ) (hb : κ ≤ (3 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (0 : ℝ) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (-2 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (2 : ℝ) * Fx (7 / 10 : ℝ) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 4 : ℝ) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (69 / 80 : ℝ) + Real.log |(69 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2, (fz177).1, (fz177).2, (lz177).1, (lz177).2]
  have hEb : (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (1 : ℝ) * Fx (0 : ℝ) + (-2 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (2 : ℝ) * Fx (27 / 40 : ℝ) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (29 / 40 : ℝ) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (69 / 80 : ℝ) + Real.log |(69 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz160).1, (fz160).2, (fz164).1, (fz164).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2, (fz177).1, (fz177).2, (lz177).1, (lz177).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (3 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (1 / 8 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := chord_up_pos (w := (1 : ℝ)) (z1 := (0 : ℝ)) (z := (6 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 16 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (21 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (11 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (23 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (3 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (5 / 8 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (13 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (27 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (7 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (57 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (29 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (61 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 16 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (69 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box7 (κ : ℝ) (ha : (3 / 20 : ℝ) ≤ κ) (hb : κ ≤ (7 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (2 : ℝ) * Fx (27 / 40 : ℝ) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (29 / 40 : ℝ) + (-1 : ℝ) * (Fx (59 / 80 : ℝ) + Real.log |(59 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (63 / 80 : ℝ) + Real.log |(63 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (67 / 80 : ℝ) + Real.log |(67 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz162).1, (fz162).2, (lz162).1, (lz162).2, (fz168).1, (fz168).2, (lz168).1, (lz168).2, (fz174).1, (fz174).2, (lz174).1, (lz174).2]
  have hEb : (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (2 : ℝ) * Fx (13 / 20 : ℝ) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 10 : ℝ) + (-1 : ℝ) * (Fx (59 / 80 : ℝ) + Real.log |(59 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (63 / 80 : ℝ) + Real.log |(63 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (67 / 80 : ℝ) + Real.log |(67 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2, (fz158).1, (fz158).2, (fz160).1, (fz160).2, (fz162).1, (fz162).2, (lz162).1, (lz162).2, (fz168).1, (fz168).2, (lz168).1, (lz168).2, (fz174).1, (fz174).2, (lz174).1, (lz174).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (7 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (3 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 16 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := tangent_up_neg (w := (-2 : ℝ)) (z0 := (1 / 80 : ℝ)) (z := (7 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 16 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 2 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (21 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 20 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (23 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 5 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (5 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (13 / 20 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (27 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 16 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 10 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (29 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (59 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (63 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (67 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box8 (κ : ℝ) (ha : (7 / 40 : ℝ) ≤ κ) (hb : κ ≤ (1 / 5 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (2 : ℝ) * Fx (13 / 20 : ℝ) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 10 : ℝ) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2]
  have hEb : (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (2 : ℝ) * Fx (5 / 8 : ℝ) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (27 / 40 : ℝ) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 16 : ℝ) + Real.log |(13 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz156).1, (fz156).2, (fz158).1, (fz158).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2, (fz171).1, (fz171).2, (lz171).1, (lz171).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 / 5 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (7 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-1 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (19 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (21 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (11 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (23 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (3 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (5 / 8 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (13 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (53 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (27 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (7 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (57 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (61 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box9 (κ : ℝ) (ha : (1 / 5 : ℝ) ≤ κ) (hb : κ ≤ (9 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (2 : ℝ) * Fx (5 / 8 : ℝ) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (27 / 40 : ℝ) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (59 / 80 : ℝ) + Real.log |(59 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (63 / 80 : ℝ) + Real.log |(63 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2, (fz162).1, (fz162).2, (lz162).1, (lz162).2, (fz168).1, (fz168).2, (lz168).1, (lz168).2]
  have hEb : (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (2 : ℝ) * Fx (3 / 5 : ℝ) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (59 / 80 : ℝ) + Real.log |(59 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (63 / 80 : ℝ) + Real.log |(63 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2, (fz154).1, (fz154).2, (fz156).1, (fz156).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2, (fz162).1, (fz162).2, (lz162).1, (lz162).2, (fz168).1, (fz168).2, (lz168).1, (lz168).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (9 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (1 / 5 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 10 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-3 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 16 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 80 : ℝ)) (z := (9 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 16 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 20 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (19 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 2 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (21 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 20 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (23 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (3 / 5 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (5 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (51 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 20 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (27 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 16 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (59 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (63 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box10 (κ : ℝ) (ha : (9 / 40 : ℝ) ≤ κ) (hb : κ ≤ (1 / 4 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (2 : ℝ) * Fx (3 / 5 : ℝ) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (13 / 20 : ℝ) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2]
  have hEb : (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (2 : ℝ) * Fx (23 / 40 : ℝ) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (61 / 80 : ℝ) + Real.log |(61 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz152).1, (fz152).2, (fz154).1, (fz154).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2, (fz165).1, (fz165).2, (lz165).1, (lz165).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 / 4 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (9 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 16 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 8 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-1 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-3 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-1 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (17 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (9 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (19 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (21 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (11 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (23 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (3 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (49 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (5 / 8 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (13 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (53 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (57 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (61 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box11 (κ : ℝ) (ha : (1 / 4 : ℝ) ≤ κ) (hb : κ ≤ (11 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (2 : ℝ) * Fx (23 / 40 : ℝ) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (5 / 8 : ℝ) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (59 / 80 : ℝ) + Real.log |(59 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2, (fz162).1, (fz162).2, (lz162).1, (lz162).2]
  have hEb : (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (2 : ℝ) * Fx (11 / 20 : ℝ) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (59 / 80 : ℝ) + Real.log |(59 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2, (fz150).1, (fz150).2, (fz152).1, (fz152).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2, (fz162).1, (fz162).2, (lz162).1, (lz162).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (11 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (1 / 4 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-21 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 20 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-1 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-1 / 10 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-3 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 16 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (2 / 5 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (17 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 20 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (19 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 2 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (21 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (11 / 20 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (23 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (47 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 5 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (5 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (51 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 16 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (59 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box12 (κ : ℝ) (ha : (11 / 40 : ℝ) ≤ κ) (hb : κ ≤ (3 / 10 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (2 : ℝ) * Fx (11 / 20 : ℝ) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 5 : ℝ) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2]
  have hEb : (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 8 : ℝ) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (2 : ℝ) * Fx (21 / 40 : ℝ) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (57 / 80 : ℝ) + Real.log |(57 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz148).1, (fz148).2, (fz150).1, (fz150).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2, (fz159).1, (fz159).2, (lz159).1, (lz159).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (3 / 10 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (11 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-23 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 16 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-3 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-1 / 8 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-1 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-1 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 8 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (17 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (9 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (19 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (21 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (11 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 16 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (23 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (3 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (49 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (53 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (57 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box13 (κ : ℝ) (ha : (3 / 10 : ℝ) ≤ κ) (hb : κ ≤ (13 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 8 : ℝ) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (2 : ℝ) * Fx (21 / 40 : ℝ) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (23 / 40 : ℝ) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2]
  have hEb : (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (2 : ℝ) * Fx (1 / 2 : ℝ) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 16 : ℝ) + Real.log |(11 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2, (fz146).1, (fz146).2, (fz148).1, (fz148).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2, (fz157).1, (fz157).2, (lz157).1, (lz157).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (13 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (3 / 10 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-5 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-21 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 5 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-7 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-3 / 20 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-1 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 10 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-3 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 80 : ℝ)) (z := (13 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 20 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (3 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (2 / 5 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (17 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 20 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (19 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (1 / 2 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (21 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (43 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 20 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (23 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (47 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (51 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box14 (κ : ℝ) (ha : (13 / 40 : ℝ) ≤ κ) (hb : κ ≤ (7 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * Fx (0 : ℝ) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (2 : ℝ) * Fx (1 / 2 : ℝ) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (11 / 20 : ℝ) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2]
  have hEb : (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-7 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (2 : ℝ) * Fx (19 / 40 : ℝ) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (53 / 80 : ℝ) + Real.log |(53 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2, (fz144).1, (fz144).2, (fz146).1, (fz146).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2, (fz155).1, (fz155).2, (lz155).1, (lz155).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (7 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (13 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-27 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-23 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-1 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 16 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-7 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-3 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 8 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-1 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-1 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (7 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 8 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (17 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (9 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (19 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (41 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (21 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (11 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 16 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (49 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (53 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box15 (κ : ℝ) (ha : (7 / 20 : ℝ) ≤ κ) (hb : κ ≤ (3 / 8 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-7 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (2 : ℝ) * Fx (19 / 40 : ℝ) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (21 / 40 : ℝ) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2]
  have hEb : (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (2 : ℝ) * Fx (9 / 20 : ℝ) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (51 / 80 : ℝ) + Real.log |(51 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2, (fz142).1, (fz142).2, (fz144).1, (fz144).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2, (fz153).1, (fz153).2, (lz153).1, (lz153).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (3 / 8 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (7 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-29 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-5 / 16 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-21 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 4 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-9 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-1 / 5 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-7 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 20 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-1 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 10 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-3 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 10 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (13 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 20 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (3 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (2 / 5 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (17 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (9 / 20 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (19 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (39 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 2 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (21 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (43 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (47 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (51 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box16 (κ : ℝ) (ha : (3 / 8 : ℝ) ≤ κ) (hb : κ ≤ (2 / 5 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (2 : ℝ) * Fx (9 / 20 : ℝ) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 2 : ℝ) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2]
  have hEb : (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-9 / 40 : ℝ) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (2 : ℝ) * Fx (17 / 40 : ℝ) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (49 / 80 : ℝ) + Real.log |(49 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2, (fz140).1, (fz140).2, (fz142).1, (fz142).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2, (fz151).1, (fz151).2, (lz151).1, (lz151).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (2 / 5 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (3 / 8 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-31 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-27 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-23 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-1 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-9 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-1 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-3 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 8 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-1 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-1 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (3 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (7 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 8 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (17 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (9 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (37 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (19 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (41 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 16 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (49 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box17 (κ : ℝ) (ha : (2 / 5 : ℝ) ≤ κ) (hb : κ ≤ (17 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-9 / 40 : ℝ) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (2 : ℝ) * Fx (17 / 40 : ℝ) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (19 / 40 : ℝ) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2]
  have hEb : (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 4 : ℝ) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (2 : ℝ) * Fx (2 / 5 : ℝ) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (47 / 80 : ℝ) + Real.log |(47 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2, (fz138).1, (fz138).2, (fz140).1, (fz140).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2, (fz149).1, (fz149).2, (lz149).1, (lz149).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (17 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (2 / 5 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-33 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-29 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-5 / 16 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 10 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-11 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-21 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-1 / 4 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-9 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 5 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-7 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 20 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-1 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 10 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-3 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 4 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (11 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 10 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (13 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 20 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (3 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (2 / 5 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (17 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 16 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 20 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (19 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (39 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (43 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (47 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box18 (κ : ℝ) (ha : (17 / 40 : ℝ) ≤ κ) (hb : κ ≤ (9 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 4 : ℝ) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (2 : ℝ) * Fx (2 / 5 : ℝ) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (9 / 20 : ℝ) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2]
  have hEb : (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-11 / 40 : ℝ) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (2 : ℝ) * Fx (3 / 8 : ℝ) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 16 : ℝ) + Real.log |(9 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2, (fz136).1, (fz136).2, (fz138).1, (fz138).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2, (fz147).1, (fz147).2, (lz147).1, (lz147).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (9 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (17 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-31 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-27 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-3 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-23 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-11 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-1 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-1 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-3 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 8 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-1 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (3 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (7 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (3 / 8 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (33 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (17 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (9 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (37 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (41 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box19 (κ : ℝ) (ha : (9 / 20 : ℝ) ≤ κ) (hb : κ ≤ (19 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-11 / 40 : ℝ) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (2 : ℝ) * Fx (3 / 8 : ℝ) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (17 / 40 : ℝ) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2]
  have hEb : (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (2 : ℝ) * Fx (7 / 20 : ℝ) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (43 / 80 : ℝ) + Real.log |(43 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2, (fz134).1, (fz134).2, (fz136).1, (fz136).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2, (fz145).1, (fz145).2, (lz145).1, (lz145).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (19 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (9 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-37 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-33 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-29 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 20 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-13 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-5 / 16 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-3 / 10 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-11 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 4 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-9 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 5 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-7 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 20 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-1 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 5 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (9 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 4 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (11 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 10 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (13 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (7 / 20 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (3 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (31 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (2 / 5 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (17 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 16 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (39 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (43 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box20 (κ : ℝ) (ha : (19 / 40 : ℝ) ≤ κ) (hb : κ ≤ (1 / 2 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (2 : ℝ) * Fx (7 / 20 : ℝ) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (2 / 5 : ℝ) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2]
  have hEb : (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (1 : ℝ) * (Fx (-27 / 80 : ℝ) + Real.log |(-27 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-13 / 40 : ℝ) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (2 : ℝ) * Fx (13 / 40 : ℝ) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (41 / 80 : ℝ) + Real.log |(41 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz56).1, (fz56).2, (lz56).1, (lz56).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz75).1, (fz75).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2, (fz132).1, (fz132).2, (fz134).1, (fz134).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2, (fz143).1, (fz143).2, (lz143).1, (lz143).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 / 2 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (19 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-39 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 16 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-31 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 8 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-7 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-27 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-13 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-3 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-1 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-1 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-3 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (1 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (3 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (13 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (7 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (29 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 8 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (33 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (37 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (41 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box21 (κ : ℝ) (ha : (1 / 2 : ℝ) ≤ κ) (hb : κ ≤ (21 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-13 / 40 : ℝ) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (-1 : ℝ) * Fx (-7 / 40 : ℝ) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (2 : ℝ) * Fx (13 / 40 : ℝ) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 8 : ℝ) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2]
  have hEb : (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (1 : ℝ) * (Fx (-29 / 80 : ℝ) + Real.log |(-29 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-7 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (2 : ℝ) * Fx (3 / 10 : ℝ) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (39 / 80 : ℝ) + Real.log |(39 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz54).1, (fz54).2, (lz54).1, (lz54).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz71).1, (fz71).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2, (fz130).1, (fz130).2, (fz132).1, (fz132).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2, (fz141).1, (fz141).2, (lz141).1, (lz141).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (21 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (1 / 2 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-41 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-37 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-33 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-2 / 5 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-3 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-29 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-7 / 20 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-13 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 10 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-11 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 4 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-9 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 5 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-7 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 20 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (7 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 5 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (9 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 4 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (11 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (3 / 10 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (13 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (27 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 20 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (3 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (31 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 16 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (39 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box22 (κ : ℝ) (ha : (21 / 40 : ℝ) ≤ κ) (hb : κ ≤ (11 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-7 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (-1 : ℝ) * Fx (-1 / 5 : ℝ) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (2 : ℝ) * Fx (3 / 10 : ℝ) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 20 : ℝ) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2]
  have hEb : (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (1 : ℝ) * (Fx (-31 / 80 : ℝ) + Real.log |(-31 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 8 : ℝ) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (2 : ℝ) * Fx (11 / 40 : ℝ) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (37 / 80 : ℝ) + Real.log |(37 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz52).1, (fz52).2, (lz52).1, (lz52).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz69).1, (fz69).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz128).1, (fz128).2, (fz130).1, (fz130).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2, (fz139).1, (fz139).2, (lz139).1, (lz139).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (11 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (21 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-43 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-39 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 16 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-17 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-2 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-31 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-3 / 8 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-7 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-3 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-1 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-1 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 8 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (3 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (1 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (11 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (3 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (5 / 16 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (13 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (7 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (29 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (33 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (37 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box23 (κ : ℝ) (ha : (11 / 20 : ℝ) ≤ κ) (hb : κ ≤ (23 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 8 : ℝ) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (-1 : ℝ) * Fx (-9 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (2 : ℝ) * Fx (11 / 40 : ℝ) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (13 / 40 : ℝ) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2]
  have hEb : (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (1 : ℝ) * (Fx (-33 / 80 : ℝ) + Real.log |(-33 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-2 / 5 : ℝ) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (2 : ℝ) * Fx (1 / 4 : ℝ) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 16 : ℝ) + Real.log |(7 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz50).1, (fz50).2, (lz50).1, (lz50).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz65).1, (fz65).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz126).1, (fz126).2, (fz128).1, (fz128).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2, (fz137).1, (fz137).2, (lz137).1, (lz137).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (23 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (11 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-41 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-37 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 20 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-17 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-33 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-2 / 5 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-3 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 20 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-13 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 10 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-11 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 4 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-9 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 10 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 20 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (7 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 5 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (9 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (1 / 4 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (11 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (23 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 10 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (13 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (27 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (31 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box24 (κ : ℝ) (ha : (23 / 40 : ℝ) ≤ κ) (hb : κ ≤ (3 / 5 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-2 / 5 : ℝ) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 4 : ℝ) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (2 : ℝ) * Fx (1 / 4 : ℝ) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 10 : ℝ) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2]
  have hEb : (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (1 : ℝ) * (Fx (-7 / 16 : ℝ) + Real.log |(-7 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-17 / 40 : ℝ) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (2 : ℝ) * Fx (9 / 40 : ℝ) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (33 / 80 : ℝ) + Real.log |(33 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz48).1, (fz48).2, (lz48).1, (lz48).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz63).1, (fz63).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz124).1, (fz124).2, (fz126).1, (fz126).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2, (fz135).1, (fz135).2, (lz135).1, (lz135).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (3 / 5 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (23 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-47 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-43 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-39 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-19 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-9 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 16 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-17 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-2 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 8 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-7 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-3 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-1 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (1 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 8 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (3 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (1 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (9 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (21 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (11 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (3 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (5 / 16 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (29 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (33 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box25 (κ : ℝ) (ha : (3 / 5 : ℝ) ≤ κ) (hb : κ ≤ (5 / 8 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-17 / 40 : ℝ) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (-1 : ℝ) * Fx (-11 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (2 : ℝ) * Fx (9 / 40 : ℝ) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (11 / 40 : ℝ) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2]
  have hEb : (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (1 : ℝ) * (Fx (-37 / 80 : ℝ) + Real.log |(-37 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-9 / 20 : ℝ) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (2 : ℝ) * Fx (1 / 5 : ℝ) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (31 / 80 : ℝ) + Real.log |(31 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz46).1, (fz46).2, (lz46).1, (lz46).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz61).1, (fz61).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz122).1, (fz122).2, (fz124).1, (fz124).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2, (fz133).1, (fz133).2, (lz133).1, (lz133).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (5 / 8 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (3 / 5 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-49 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 16 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-41 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 2 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-19 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-37 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-9 / 20 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-17 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-2 / 5 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-3 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 20 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-13 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 10 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-11 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 20 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (3 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 10 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 20 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (7 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (1 / 5 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (9 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 4 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (11 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (23 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (27 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (31 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box26 (κ : ℝ) (ha : (5 / 8 : ℝ) ≤ κ) (hb : κ ≤ (13 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-9 / 20 : ℝ) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 10 : ℝ) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (2 : ℝ) * Fx (1 / 5 : ℝ) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 4 : ℝ) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2]
  have hEb : (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (1 : ℝ) * (Fx (-39 / 80 : ℝ) + Real.log |(-39 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-19 / 40 : ℝ) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (2 : ℝ) * Fx (7 / 40 : ℝ) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (29 / 80 : ℝ) + Real.log |(29 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz44).1, (fz44).2, (lz44).1, (lz44).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz59).1, (fz59).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz120).1, (fz120).2, (fz122).1, (fz122).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2, (fz131).1, (fz131).2, (lz131).1, (lz131).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (13 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (5 / 8 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-51 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-47 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-43 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-21 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-1 / 2 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-39 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-19 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-9 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-17 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-2 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 8 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-7 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-3 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (1 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 8 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (3 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (7 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (1 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (9 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (21 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (5 / 16 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (29 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box27 (κ : ℝ) (ha : (13 / 20 : ℝ) ≤ κ) (hb : κ ≤ (27 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-19 / 40 : ℝ) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (-1 : ℝ) * Fx (-13 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (2 : ℝ) * Fx (7 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (9 / 40 : ℝ) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2]
  have hEb : (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (1 : ℝ) * (Fx (-41 / 80 : ℝ) + Real.log |(-41 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 2 : ℝ) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (1 : ℝ) * Fx (0 : ℝ) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (2 : ℝ) * Fx (3 / 20 : ℝ) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (27 / 80 : ℝ) + Real.log |(27 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz42).1, (fz42).2, (lz42).1, (lz42).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz57).1, (fz57).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz116).1, (fz116).2, (fz120).1, (fz120).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2, (fz129).1, (fz129).2, (lz129).1, (lz129).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (27 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (13 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-53 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-49 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 16 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 20 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-21 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-41 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-1 / 2 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-19 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 20 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-17 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-2 / 5 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-3 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 20 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-13 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := chord_up_pos (w := (1 : ℝ)) (z1 := (0 : ℝ)) (z := (27 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 20 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (3 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 10 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (3 / 20 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (7 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 16 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 5 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (9 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (23 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (27 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box28 (κ : ℝ) (ha : (27 / 40 : ℝ) ≤ κ) (hb : κ ≤ (7 / 10 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-1 / 2 : ℝ) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (-1 : ℝ) * Fx (-7 / 20 : ℝ) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (2 : ℝ) * Fx (3 / 20 : ℝ) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 5 : ℝ) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2]
  have hEb : (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (1 : ℝ) * (Fx (-43 / 80 : ℝ) + Real.log |(-43 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-21 / 40 : ℝ) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (2 : ℝ) * Fx (1 / 8 : ℝ) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (5 / 16 : ℝ) + Real.log |(5 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz40).1, (fz40).2, (lz40).1, (lz40).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz55).1, (fz55).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz114).1, (fz114).2, (fz116).1, (fz116).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2, (fz127).1, (fz127).2, (lz127).1, (lz127).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (7 / 10 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (27 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-51 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-47 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-23 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-11 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-43 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-21 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-1 / 2 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-19 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-9 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-17 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-2 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 8 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-7 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (1 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (1 / 8 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (3 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (7 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (1 / 5 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (21 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (5 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box29 (κ : ℝ) (ha : (7 / 10 : ℝ) ≤ κ) (hb : κ ≤ (29 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-21 / 40 : ℝ) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (-1 : ℝ) * Fx (-3 / 8 : ℝ) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (2 : ℝ) * Fx (1 / 8 : ℝ) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (7 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2]
  have hEb : (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (1 : ℝ) * (Fx (-9 / 16 : ℝ) + Real.log |(-9 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-11 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (0 : ℝ) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (2 : ℝ) * Fx (1 / 10 : ℝ) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (23 / 80 : ℝ) + Real.log |(23 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz53).1, (fz53).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz110).1, (fz110).2, (fz114).1, (fz114).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2, (fz125).1, (fz125).2, (lz125).1, (lz125).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (29 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (7 / 10 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-57 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-53 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-49 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 5 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-23 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 16 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-11 / 20 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-21 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 2 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-19 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 20 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-17 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-2 / 5 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-3 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := chord_up_pos (w := (1 : ℝ)) (z1 := (0 : ℝ)) (z := (29 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 20 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (3 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (1 / 10 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 20 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (7 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 16 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (23 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box30 (κ : ℝ) (ha : (29 / 40 : ℝ) ≤ κ) (hb : κ ≤ (3 / 4 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-59 / 80 : ℝ) + Real.log |(-59 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-11 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (-1 : ℝ) * Fx (-2 / 5 : ℝ) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (2 : ℝ) * Fx (1 / 10 : ℝ) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 20 : ℝ) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz23).1, (fz23).2, (lz23).1, (lz23).2, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2]
  have hEb : (1 : ℝ) * (Fx (-59 / 80 : ℝ) + Real.log |(-59 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (1 : ℝ) * (Fx (-47 / 80 : ℝ) + Real.log |(-47 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-23 / 40 : ℝ) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (2 : ℝ) * Fx (3 / 40 : ℝ) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (21 / 80 : ℝ) + Real.log |(21 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz23).1, (fz23).2, (lz23).1, (lz23).2, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz36).1, (fz36).2, (lz36).1, (lz36).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz51).1, (fz51).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz108).1, (fz108).2, (fz110).1, (fz110).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2, (fz123).1, (fz123).2, (lz123).1, (lz123).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (3 / 4 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (29 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-59 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 16 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-51 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-5 / 8 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-3 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-47 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-23 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-11 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-21 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-1 / 2 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-19 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-9 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-17 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-2 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 16 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (3 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (1 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 8 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (3 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (21 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box31 (κ : ℝ) (ha : (3 / 4 : ℝ) ≤ κ) (hb : κ ≤ (31 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-23 / 40 : ℝ) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (-1 : ℝ) * Fx (-17 / 40 : ℝ) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (2 : ℝ) * Fx (3 / 40 : ℝ) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 8 : ℝ) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2]
  have hEb : (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (1 : ℝ) * (Fx (-49 / 80 : ℝ) + Real.log |(-49 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 5 : ℝ) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (0 : ℝ) + (2 : ℝ) * Fx (1 / 20 : ℝ) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (19 / 80 : ℝ) + Real.log |(19 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz49).1, (fz49).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz104).1, (fz104).2, (fz108).1, (fz108).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2, (fz121).1, (fz121).2, (lz121).1, (lz121).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (31 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (3 / 4 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-61 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-57 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-53 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 20 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-5 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-49 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-3 / 5 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-23 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 20 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-21 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 2 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-19 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 20 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-17 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := chord_up_pos (w := (1 : ℝ)) (z1 := (0 : ℝ)) (z := (31 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (1 / 20 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (3 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 10 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 16 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box32 (κ : ℝ) (ha : (31 / 40 : ℝ) ≤ κ) (hb : κ ≤ (4 / 5 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-63 / 80 : ℝ) + Real.log |(-63 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-59 / 80 : ℝ) + Real.log |(-59 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 5 : ℝ) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (-1 : ℝ) * Fx (-9 / 20 : ℝ) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * Fx (1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 10 : ℝ) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz17).1, (fz17).2, (lz17).1, (lz17).2, (fz23).1, (fz23).2, (lz23).1, (lz23).2, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2]
  have hEb : (1 : ℝ) * (Fx (-63 / 80 : ℝ) + Real.log |(-63 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-59 / 80 : ℝ) + Real.log |(-59 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-27 / 40 : ℝ) + (1 : ℝ) * (Fx (-51 / 80 : ℝ) + Real.log |(-51 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-5 / 8 : ℝ) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * Fx (1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (17 / 80 : ℝ) + Real.log |(17 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz17).1, (fz17).2, (lz17).1, (lz17).2, (fz23).1, (fz23).2, (lz23).1, (lz23).2, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz32).1, (fz32).2, (lz32).1, (lz32).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz47).1, (fz47).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz102).1, (fz102).2, (fz104).1, (fz104).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2, (fz118).1, (fz118).2, (lz118).1, (lz118).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (4 / 5 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (31 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-63 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-59 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 16 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-27 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-13 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-51 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-5 / 8 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-3 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-23 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-11 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-21 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-1 / 2 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-19 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-9 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 16 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 80 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 16 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (3 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (1 / 10 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box33 (κ : ℝ) (ha : (4 / 5 : ℝ) ≤ κ) (hb : κ ≤ (33 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-27 / 40 : ℝ) + (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-5 / 8 : ℝ) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (-1 : ℝ) * Fx (-19 / 40 : ℝ) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * Fx (1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (3 / 40 : ℝ) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2]
  have hEb : (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-7 / 10 : ℝ) + (1 : ℝ) * (Fx (-53 / 80 : ℝ) + Real.log |(-53 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-13 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (3 / 16 : ℝ) + Real.log |(3 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz45).1, (fz45).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz98).1, (fz98).2, (fz102).1, (fz102).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2, (fz115).1, (fz115).2, (lz115).1, (lz115).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (33 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (4 / 5 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-61 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-57 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 10 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-27 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-53 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-13 / 20 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-5 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 5 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-23 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 20 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-21 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 2 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-19 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := chord_up_pos (w := (2 : ℝ)) (z1 := (0 : ℝ)) (z := (33 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 20 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (3 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box34 (κ : ℝ) (ha : (33 / 40 : ℝ) ≤ κ) (hb : κ ≤ (17 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-67 / 80 : ℝ) + Real.log |(-67 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-63 / 80 : ℝ) + Real.log |(-63 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-59 / 80 : ℝ) + Real.log |(-59 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-7 / 10 : ℝ) + (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-13 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (-1 : ℝ) * Fx (-1 / 2 : ℝ) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz11).1, (fz11).2, (lz11).1, (lz11).2, (fz17).1, (fz17).2, (lz17).1, (lz17).2, (fz23).1, (fz23).2, (lz23).1, (lz23).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2]
  have hEb : (1 : ℝ) * (Fx (-67 / 80 : ℝ) + Real.log |(-67 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-63 / 80 : ℝ) + Real.log |(-63 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-59 / 80 : ℝ) + Real.log |(-59 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-29 / 40 : ℝ) + (1 : ℝ) * (Fx (-11 / 16 : ℝ) + Real.log |(-11 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-27 / 40 : ℝ) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-1 / 80 : ℝ) + Real.log |(-1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (9 / 80 : ℝ) + Real.log |(9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (13 / 80 : ℝ) + Real.log |(13 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz11).1, (fz11).2, (lz11).1, (lz11).2, (fz17).1, (fz17).2, (lz17).1, (lz17).2, (fz23).1, (fz23).2, (lz23).1, (lz23).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz28).1, (fz28).2, (lz28).1, (lz28).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz43).1, (fz43).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz91).1, (fz91).2, (lz91).1, (lz91).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz96).1, (fz96).2, (fz98).1, (fz98).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2, (fz106).1, (fz106).2, (lz106).1, (lz106).2, (fz112).1, (fz112).2, (lz112).1, (lz112).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (17 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (33 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-67 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-63 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-59 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-29 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-7 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 16 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-27 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-13 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-5 / 8 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-3 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-23 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-11 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-21 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-1 / 2 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 16 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-1 / 80 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (1 / 40 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (1 / 20 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 16 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (13 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box35 (κ : ℝ) (ha : (17 / 20 : ℝ) ≤ κ) (hb : κ ≤ (7 / 8 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-69 / 80 : ℝ) + Real.log |(-69 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-29 / 40 : ℝ) + (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-27 / 40 : ℝ) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (-1 : ℝ) * Fx (-21 / 40 : ℝ) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (0 : ℝ) + (1 : ℝ) * Fx (1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz8).1, (fz8).2, (lz8).1, (lz8).2, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2]
  have hEb : (1 : ℝ) * (Fx (-69 / 80 : ℝ) + Real.log |(-69 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 4 : ℝ) + (1 : ℝ) * (Fx (-57 / 80 : ℝ) + Real.log |(-57 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-7 / 10 : ℝ) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (1 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (11 / 80 : ℝ) + Real.log |(11 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz8).1, (fz8).2, (lz8).1, (lz8).2, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz39).1, (fz39).2, (fz41).1, (fz41).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz96).1, (fz96).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2, (fz109).1, (fz109).2, (lz109).1, (lz109).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (7 / 8 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (17 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-69 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 16 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-61 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 4 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-29 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-57 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-7 / 10 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-27 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 20 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-5 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 5 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-23 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-11 / 20 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-21 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 16 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (34 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t14 := chord_up_pos (w := (1 : ℝ)) (z1 := (0 : ℝ)) (z := (35 : ℝ) / 40 - κ) (z2 := (1 / 40 : ℝ)) (by norm_num) (by norm_num) (by linarith) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box36 (κ : ℝ) (ha : (7 / 8 : ℝ) ≤ κ) (hb : κ ≤ (71 / 80 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-141 / 160 : ℝ) + Real.log |(-141 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-133 / 160 : ℝ) + Real.log |(-133 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-25 / 32 : ℝ) + Real.log |(-25 / 32 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-3 / 4 : ℝ) + (1 : ℝ) * (Fx (-117 / 160 : ℝ) + Real.log |(-117 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-2 : ℝ) * Fx (-7 / 10 : ℝ) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (-1 : ℝ) * Fx (-11 / 20 : ℝ) + (1 : ℝ) * (Fx (-33 / 160 : ℝ) + Real.log |(-33 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-5 / 32 : ℝ) + Real.log |(-5 / 32 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-17 / 160 : ℝ) + Real.log |(-17 / 160 : ℝ)| * (1 / 160 : ℝ)) + (2 : ℝ) * (Fx (-9 / 160 : ℝ) + Real.log |(-9 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (1 : ℝ) * (Fx (-1 / 160 : ℝ) + Real.log |(-1 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (3 / 160 : ℝ) + Real.log |(3 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (11 / 160 : ℝ) + Real.log |(11 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (19 / 160 : ℝ) + Real.log |(19 / 160 : ℝ)| * (1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz6).1, (fz6).2, (lz6).1, (lz6).2, (fz12).1, (fz12).2, (lz12).1, (lz12).2, (fz18).1, (fz18).2, (lz18).1, (lz18).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz21).1, (fz21).2, (fz24).1, (fz24).2, (lz24).1, (lz24).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz27).1, (fz27).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz31).1, (fz31).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz35).1, (fz35).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz39).1, (fz39).2, (fz68).1, (fz68).2, (lz68).1, (lz68).2, (fz74).1, (fz74).2, (lz74).1, (lz74).2, (fz80).1, (fz80).2, (lz80).1, (lz80).2, (fz86).1, (fz86).2, (lz86).1, (lz86).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz92).1, (fz92).2, (lz92).1, (lz92).2, (fz95).1, (fz95).2, (lz95).1, (lz95).2, (fz101).1, (fz101).2, (lz101).1, (lz101).2, (fz107).1, (fz107).2, (lz107).1, (lz107).2]
  have hEb : (1 : ℝ) * (Fx (-141 / 160 : ℝ) + Real.log |(-141 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-133 / 160 : ℝ) + Real.log |(-133 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-25 / 32 : ℝ) + Real.log |(-25 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-61 / 80 : ℝ) + (1 : ℝ) * (Fx (-117 / 160 : ℝ) + Real.log |(-117 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-2 : ℝ) * Fx (-57 / 80 : ℝ) + (-1 : ℝ) * Fx (-53 / 80 : ℝ) + (-1 : ℝ) * Fx (-49 / 80 : ℝ) + (-1 : ℝ) * Fx (-9 / 16 : ℝ) + (1 : ℝ) * (Fx (-33 / 160 : ℝ) + Real.log |(-33 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-5 / 32 : ℝ) + Real.log |(-5 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-17 / 160 : ℝ) + Real.log |(-17 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (2 : ℝ) * (Fx (-9 / 160 : ℝ) + Real.log |(-9 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-3 / 80 : ℝ) + (1 : ℝ) * (Fx (-1 / 160 : ℝ) + Real.log |(-1 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (3 / 160 : ℝ) + Real.log |(3 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (11 / 160 : ℝ) + Real.log |(11 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (19 / 160 : ℝ) + Real.log |(19 / 160 : ℝ)| * (-1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz6).1, (fz6).2, (lz6).1, (lz6).2, (fz12).1, (fz12).2, (lz12).1, (lz12).2, (fz18).1, (fz18).2, (lz18).1, (lz18).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz21).1, (fz21).2, (fz24).1, (fz24).2, (lz24).1, (lz24).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz27).1, (fz27).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz31).1, (fz31).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz35).1, (fz35).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz39).1, (fz39).2, (fz68).1, (fz68).2, (lz68).1, (lz68).2, (fz74).1, (fz74).2, (lz74).1, (lz74).2, (fz80).1, (fz80).2, (lz80).1, (lz80).2, (fz86).1, (fz86).2, (lz86).1, (lz86).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz92).1, (fz92).2, (lz92).1, (lz92).2, (fz95).1, (fz95).2, (lz95).1, (lz95).2, (fz101).1, (fz101).2, (lz101).1, (lz101).2, (fz107).1, (fz107).2, (lz107).1, (lz107).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (71 / 80 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (7 / 8 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-141 / 160 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-133 / 160 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-25 / 32 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-61 / 80 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-3 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-117 / 160 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-57 / 80 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-7 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-53 / 80 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-13 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-49 / 80 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-3 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-9 / 16 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-11 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-33 / 160 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-5 / 32 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 160 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-9 / 160 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 80 : ℝ)) (z := (34 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t14 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 160 : ℝ)) (z := (35 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 160 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (11 / 160 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (19 / 160 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box37 (κ : ℝ) (ha : (71 / 80 : ℝ) ≤ κ) (hb : κ ≤ (9 / 10 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-143 / 160 : ℝ) + Real.log |(-143 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-27 / 32 : ℝ) + Real.log |(-27 / 32 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-127 / 160 : ℝ) + Real.log |(-127 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-61 / 80 : ℝ) + (1 : ℝ) * (Fx (-119 / 160 : ℝ) + Real.log |(-119 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-2 : ℝ) * Fx (-57 / 80 : ℝ) + (-1 : ℝ) * Fx (-53 / 80 : ℝ) + (-1 : ℝ) * Fx (-49 / 80 : ℝ) + (-1 : ℝ) * Fx (-9 / 16 : ℝ) + (1 : ℝ) * (Fx (-7 / 32 : ℝ) + Real.log |(-7 / 32 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-27 / 160 : ℝ) + Real.log |(-27 / 160 : ℝ)| * (1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-19 / 160 : ℝ) + Real.log |(-19 / 160 : ℝ)| * (1 / 160 : ℝ)) + (2 : ℝ) * (Fx (-11 / 160 : ℝ) + Real.log |(-11 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-3 / 80 : ℝ) + (1 : ℝ) * (Fx (-3 / 160 : ℝ) + Real.log |(-3 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (1 / 160 : ℝ) + Real.log |(1 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (9 / 160 : ℝ) + Real.log |(9 / 160 : ℝ)| * (1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (17 / 160 : ℝ) + Real.log |(17 / 160 : ℝ)| * (1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz4).1, (fz4).2, (lz4).1, (lz4).2, (fz10).1, (fz10).2, (lz10).1, (lz10).2, (fz16).1, (fz16).2, (lz16).1, (lz16).2, (fz19).1, (fz19).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz22).1, (fz22).2, (lz22).1, (lz22).2, (fz25).1, (fz25).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz29).1, (fz29).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz33).1, (fz33).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz37).1, (fz37).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz66).1, (fz66).2, (lz66).1, (lz66).2, (fz72).1, (fz72).2, (lz72).1, (lz72).2, (fz78).1, (fz78).2, (lz78).1, (lz78).2, (fz84).1, (fz84).2, (lz84).1, (lz84).2, (fz87).1, (fz87).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz90).1, (fz90).2, (lz90).1, (lz90).2, (fz93).1, (fz93).2, (lz93).1, (lz93).2, (fz99).1, (fz99).2, (lz99).1, (lz99).2, (fz105).1, (fz105).2, (lz105).1, (lz105).2]
  have hEb : (1 : ℝ) * (Fx (-143 / 160 : ℝ) + Real.log |(-143 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-27 / 32 : ℝ) + Real.log |(-27 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-127 / 160 : ℝ) + Real.log |(-127 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-31 / 40 : ℝ) + (1 : ℝ) * (Fx (-119 / 160 : ℝ) + Real.log |(-119 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-2 : ℝ) * Fx (-29 / 40 : ℝ) + (-1 : ℝ) * Fx (-27 / 40 : ℝ) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (1 : ℝ) * (Fx (-7 / 32 : ℝ) + Real.log |(-7 / 32 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-27 / 160 : ℝ) + Real.log |(-27 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (1 : ℝ) * (Fx (-19 / 160 : ℝ) + Real.log |(-19 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (2 : ℝ) * (Fx (-11 / 160 : ℝ) + Real.log |(-11 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (1 : ℝ) * (Fx (-3 / 160 : ℝ) + Real.log |(-3 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (1 / 160 : ℝ) + Real.log |(1 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (9 / 160 : ℝ) + Real.log |(9 / 160 : ℝ)| * (-1 / 160 : ℝ)) + (-1 : ℝ) * (Fx (17 / 160 : ℝ) + Real.log |(17 / 160 : ℝ)| * (-1 / 160 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz4).1, (fz4).2, (lz4).1, (lz4).2, (fz10).1, (fz10).2, (lz10).1, (lz10).2, (fz16).1, (fz16).2, (lz16).1, (lz16).2, (fz19).1, (fz19).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz22).1, (fz22).2, (lz22).1, (lz22).2, (fz25).1, (fz25).2, (fz26).1, (fz26).2, (lz26).1, (lz26).2, (fz29).1, (fz29).2, (fz30).1, (fz30).2, (lz30).1, (lz30).2, (fz33).1, (fz33).2, (fz34).1, (fz34).2, (lz34).1, (lz34).2, (fz37).1, (fz37).2, (fz38).1, (fz38).2, (lz38).1, (lz38).2, (fz66).1, (fz66).2, (lz66).1, (lz66).2, (fz72).1, (fz72).2, (lz72).1, (lz72).2, (fz78).1, (fz78).2, (lz78).1, (lz78).2, (fz84).1, (fz84).2, (lz84).1, (lz84).2, (fz87).1, (fz87).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz90).1, (fz90).2, (lz90).1, (lz90).2, (fz93).1, (fz93).2, (lz93).1, (lz93).2, (fz99).1, (fz99).2, (lz99).1, (lz99).2, (fz105).1, (fz105).2, (lz105).1, (lz105).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (9 / 10 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (71 / 80 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-143 / 160 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-27 / 32 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-127 / 160 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-31 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-61 / 80 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-119 / 160 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-29 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-57 / 80 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-27 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-53 / 80 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-5 / 8 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-49 / 80 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-23 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-9 / 16 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 32 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-27 / 160 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 160 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-11 / 160 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (34 : ℝ) / 40 - κ) (z2 := (-3 / 80 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t14 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 160 : ℝ)) (z := (35 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t15 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 160 : ℝ)) (z := (36 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (9 / 160 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (17 / 160 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box38 (κ : ℝ) (ha : (9 / 10 : ℝ) ≤ κ) (hb : κ ≤ (37 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-73 / 80 : ℝ) + Real.log |(-73 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-69 / 80 : ℝ) + Real.log |(-69 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-31 / 40 : ℝ) + (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-29 / 40 : ℝ) + (-1 : ℝ) * Fx (-27 / 40 : ℝ) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (-1 : ℝ) * Fx (-23 / 40 : ℝ) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz3).1, (fz3).2, (lz3).1, (lz3).2, (fz8).1, (fz8).2, (lz8).1, (lz8).2, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz15).1, (fz15).2, (fz19).1, (fz19).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2]
  have hEb : (1 : ℝ) * (Fx (-73 / 80 : ℝ) + Real.log |(-73 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-69 / 80 : ℝ) + Real.log |(-69 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-4 / 5 : ℝ) + (1 : ℝ) * (Fx (-61 / 80 : ℝ) + Real.log |(-61 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 4 : ℝ) + (-1 : ℝ) * Fx (-7 / 10 : ℝ) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (1 : ℝ) * (Fx (-3 / 80 : ℝ) + Real.log |(-3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (7 / 80 : ℝ) + Real.log |(7 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz3).1, (fz3).2, (lz3).1, (lz3).2, (fz8).1, (fz8).2, (lz8).1, (lz8).2, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz15).1, (fz15).2, (fz19).1, (fz19).2, (fz20).1, (fz20).2, (lz20).1, (lz20).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz37).1, (fz37).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz88).1, (fz88).2, (lz88).1, (lz88).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2, (fz103).1, (fz103).2, (lz103).1, (lz103).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (37 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (9 / 10 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-73 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-69 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 16 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-4 / 5 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-31 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-61 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-3 / 4 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-29 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 10 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-27 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 20 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-5 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 5 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-23 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 16 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 40 : ℝ)) (z := (34 : ℝ) / 40 - κ) (z2 := (-1 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t14 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 80 : ℝ)) (z := (35 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t15 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (36 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (7 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box39 (κ : ℝ) (ha : (37 / 40 : ℝ) ≤ κ) (hb : κ ≤ (19 / 20 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-15 / 16 : ℝ) + Real.log |(-15 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-71 / 80 : ℝ) + Real.log |(-71 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-67 / 80 : ℝ) + Real.log |(-67 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-4 / 5 : ℝ) + (1 : ℝ) * (Fx (-63 / 80 : ℝ) + Real.log |(-63 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-3 / 4 : ℝ) + (-1 : ℝ) * Fx (-7 / 10 : ℝ) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (-1 : ℝ) * Fx (-3 / 5 : ℝ) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz2).1, (fz2).2, (lz2).1, (lz2).2, (fz5).1, (fz5).2, (lz5).1, (lz5).2, (fz11).1, (fz11).2, (lz11).1, (lz11).2, (fz13).1, (fz13).2, (fz15).1, (fz15).2, (fz17).1, (fz17).2, (lz17).1, (lz17).2, (fz19).1, (fz19).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2]
  have hEb : (1 : ℝ) * (Fx (-15 / 16 : ℝ) + Real.log |(-15 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-71 / 80 : ℝ) + Real.log |(-71 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-67 / 80 : ℝ) + Real.log |(-67 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-33 / 40 : ℝ) + (1 : ℝ) * (Fx (-63 / 80 : ℝ) + Real.log |(-63 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-31 / 40 : ℝ) + (-1 : ℝ) * Fx (-29 / 40 : ℝ) + (-1 : ℝ) * Fx (-27 / 40 : ℝ) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (1 : ℝ) * (Fx (-1 / 16 : ℝ) + Real.log |(-1 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * (Fx (1 / 16 : ℝ) + Real.log |(1 / 16 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz2).1, (fz2).2, (lz2).1, (lz2).2, (fz5).1, (fz5).2, (lz5).1, (lz5).2, (fz11).1, (fz11).2, (lz11).1, (lz11).2, (fz13).1, (fz13).2, (fz15).1, (fz15).2, (fz17).1, (fz17).2, (lz17).1, (lz17).2, (fz19).1, (fz19).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz35).1, (fz35).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz85).1, (fz85).2, (lz85).1, (lz85).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2, (fz100).1, (fz100).2, (lz100).1, (lz100).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (19 / 20 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (37 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-15 / 16 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-71 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-67 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-33 / 40 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-4 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-63 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-31 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-3 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-29 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-7 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-27 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-13 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-5 / 8 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-3 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-21 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 80 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-9 / 80 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 10 : ℝ)) (z := (34 : ℝ) / 40 - κ) (z2 := (-3 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t14 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-1 / 16 : ℝ)) (z := (35 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t15 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (36 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t16 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 80 : ℝ)) (z := (38 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 16 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box40 (κ : ℝ) (ha : (19 / 20 : ℝ) ≤ κ) (hb : κ ≤ (39 / 40 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-77 / 80 : ℝ) + Real.log |(-77 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-73 / 80 : ℝ) + Real.log |(-73 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-69 / 80 : ℝ) + Real.log |(-69 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-33 / 40 : ℝ) + (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-31 / 40 : ℝ) + (-1 : ℝ) * Fx (-29 / 40 : ℝ) + (-1 : ℝ) * Fx (-27 / 40 : ℝ) + (-1 : ℝ) * Fx (-5 / 8 : ℝ) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * Fx (0 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz1).1, (fz1).2, (lz1).1, (lz1).2, (fz3).1, (fz3).2, (lz3).1, (lz3).2, (fz8).1, (fz8).2, (lz8).1, (lz8).2, (fz9).1, (fz9).2, (fz13).1, (fz13).2, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz15).1, (fz15).2, (fz19).1, (fz19).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2]
  have hEb : (1 : ℝ) * (Fx (-77 / 80 : ℝ) + Real.log |(-77 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-73 / 80 : ℝ) + Real.log |(-73 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-69 / 80 : ℝ) + Real.log |(-69 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-17 / 20 : ℝ) + (1 : ℝ) * (Fx (-13 / 16 : ℝ) + Real.log |(-13 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-4 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 4 : ℝ) + (-1 : ℝ) * Fx (-7 / 10 : ℝ) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (1 : ℝ) * (Fx (-23 / 80 : ℝ) + Real.log |(-23 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-19 / 80 : ℝ) + Real.log |(-19 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-3 / 16 : ℝ) + Real.log |(-3 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-11 / 80 : ℝ) + Real.log |(-11 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (1 : ℝ) * (Fx (-7 / 80 : ℝ) + Real.log |(-7 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (3 / 80 : ℝ) + Real.log |(3 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz1).1, (fz1).2, (lz1).1, (lz1).2, (fz3).1, (fz3).2, (lz3).1, (lz3).2, (fz8).1, (fz8).2, (lz8).1, (lz8).2, (fz9).1, (fz9).2, (fz13).1, (fz13).2, (fz14).1, (fz14).2, (lz14).1, (lz14).2, (fz15).1, (fz15).2, (fz19).1, (fz19).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz33).1, (fz33).2, (fz60).1, (fz60).2, (lz60).1, (lz60).2, (fz64).1, (fz64).2, (lz64).1, (lz64).2, (fz70).1, (fz70).2, (lz70).1, (lz70).2, (fz76).1, (fz76).2, (lz76).1, (lz76).2, (fz77).1, (fz77).2, (fz81).1, (fz81).2, (fz82).1, (fz82).2, (lz82).1, (lz82).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz97).1, (fz97).2, (lz97).1, (lz97).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (39 / 40 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (19 / 20 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-77 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-73 / 80 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-69 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-17 / 20 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-33 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-13 / 16 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-4 / 5 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-31 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 4 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-29 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 10 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-27 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-13 / 20 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-5 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-23 / 80 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-19 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-3 / 16 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-11 / 80 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 8 : ℝ)) (z := (34 : ℝ) / 40 - κ) (z2 := (-1 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t14 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-7 / 80 : ℝ)) (z := (35 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t15 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 40 : ℝ)) (z := (36 : ℝ) / 40 - κ) (z2 := (-1 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t16 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 40 : ℝ)) (z := (38 : ℝ) / 40 - κ) (z2 := (0 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (3 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

set_option maxHeartbeats 4000000 in
theorem box41 (κ : ℝ) (ha : (39 / 40 : ℝ) ≤ κ) (hb : κ ≤ (1 : ℝ)) : Upot κ ≤ 71 / 100 := by
  have hEa : (1 : ℝ) * (Fx (-79 / 80 : ℝ) + Real.log |(-79 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-15 / 16 : ℝ) + Real.log |(-15 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-71 / 80 : ℝ) + Real.log |(-71 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-17 / 20 : ℝ) + (1 : ℝ) * (Fx (-67 / 80 : ℝ) + Real.log |(-67 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-4 / 5 : ℝ) + (-1 : ℝ) * Fx (-3 / 4 : ℝ) + (-1 : ℝ) * Fx (-7 / 10 : ℝ) + (-1 : ℝ) * Fx (-13 / 20 : ℝ) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 8 : ℝ) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 40 : ℝ) + (-1 : ℝ) * Fx (-1 / 40 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz0).1, (fz0).2, (lz0).1, (lz0).2, (fz2).1, (fz2).2, (lz2).1, (lz2).2, (fz5).1, (fz5).2, (lz5).1, (lz5).2, (fz7).1, (fz7).2, (fz9).1, (fz9).2, (fz11).1, (fz11).2, (lz11).1, (lz11).2, (fz13).1, (fz13).2, (fz15).1, (fz15).2, (fz19).1, (fz19).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2]
  have hEb : (1 : ℝ) * (Fx (-79 / 80 : ℝ) + Real.log |(-79 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-15 / 16 : ℝ) + Real.log |(-15 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-71 / 80 : ℝ) + Real.log |(-71 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-7 / 8 : ℝ) + (1 : ℝ) * (Fx (-67 / 80 : ℝ) + Real.log |(-67 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-2 : ℝ) * Fx (-33 / 40 : ℝ) + (-1 : ℝ) * Fx (-31 / 40 : ℝ) + (-1 : ℝ) * Fx (-29 / 40 : ℝ) + (-1 : ℝ) * Fx (-27 / 40 : ℝ) + (1 : ℝ) * (Fx (-5 / 16 : ℝ) + Real.log |(-5 / 16 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-21 / 80 : ℝ) + Real.log |(-21 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (1 : ℝ) * (Fx (-17 / 80 : ℝ) + Real.log |(-17 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (2 : ℝ) * (Fx (-13 / 80 : ℝ) + Real.log |(-13 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-3 / 20 : ℝ) + (1 : ℝ) * (Fx (-9 / 80 : ℝ) + Real.log |(-9 / 80 : ℝ)| * (-1 / 80 : ℝ)) + (-1 : ℝ) * Fx (-1 / 10 : ℝ) + (-1 : ℝ) * Fx (-1 / 20 : ℝ) + (-1 : ℝ) * (Fx (1 / 80 : ℝ) + Real.log |(1 / 80 : ℝ)| * (-1 / 80 : ℝ)) ≤ 71 / 100 := by
    linarith [Fx_zero, (fz0).1, (fz0).2, (lz0).1, (lz0).2, (fz2).1, (fz2).2, (lz2).1, (lz2).2, (fz5).1, (fz5).2, (lz5).1, (lz5).2, (fz7).1, (fz7).2, (fz9).1, (fz9).2, (fz11).1, (fz11).2, (lz11).1, (lz11).2, (fz13).1, (fz13).2, (fz15).1, (fz15).2, (fz19).1, (fz19).2, (fz21).1, (fz21).2, (fz25).1, (fz25).2, (fz27).1, (fz27).2, (fz29).1, (fz29).2, (fz31).1, (fz31).2, (fz58).1, (fz58).2, (lz58).1, (lz58).2, (fz62).1, (fz62).2, (lz62).1, (lz62).2, (fz67).1, (fz67).2, (lz67).1, (lz67).2, (fz73).1, (fz73).2, (lz73).1, (lz73).2, (fz75).1, (fz75).2, (fz77).1, (fz77).2, (fz79).1, (fz79).2, (lz79).1, (lz79).2, (fz81).1, (fz81).2, (fz83).1, (fz83).2, (fz87).1, (fz87).2, (fz89).1, (fz89).2, (fz94).1, (fz94).2, (lz94).1, (lz94).2]
  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ (1 : ℝ) - κ)
  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - (39 / 40 : ℝ))
  have t0 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-79 / 80 : ℝ)) (z := (0 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t1 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-15 / 16 : ℝ)) (z := (2 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t2 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-71 / 80 : ℝ)) (z := (4 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t3 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-7 / 8 : ℝ)) (z := (5 : ℝ) / 40 - κ) (z2 := (-17 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t4 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-67 / 80 : ℝ)) (z := (6 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t5 := chord_up_neg (w := (-2 : ℝ)) (z1 := (-33 / 40 : ℝ)) (z := (7 : ℝ) / 40 - κ) (z2 := (-4 / 5 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t6 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-31 / 40 : ℝ)) (z := (9 : ℝ) / 40 - κ) (z2 := (-3 / 4 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t7 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-29 / 40 : ℝ)) (z := (11 : ℝ) / 40 - κ) (z2 := (-7 / 10 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t8 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-27 / 40 : ℝ)) (z := (13 : ℝ) / 40 - κ) (z2 := (-13 / 20 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t9 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-5 / 16 : ℝ)) (z := (27 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t10 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-21 / 80 : ℝ)) (z := (29 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t11 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-17 / 80 : ℝ)) (z := (31 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t12 := tangent_up_pos (w := (2 : ℝ)) (z0 := (-13 / 80 : ℝ)) (z := (33 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t13 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-3 / 20 : ℝ)) (z := (34 : ℝ) / 40 - κ) (z2 := (-1 / 8 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t14 := tangent_up_pos (w := (1 : ℝ)) (z0 := (-9 / 80 : ℝ)) (z := (35 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  have t15 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 10 : ℝ)) (z := (36 : ℝ) / 40 - κ) (z2 := (-3 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t16 := chord_up_neg (w := (-1 : ℝ)) (z1 := (-1 / 20 : ℝ)) (z := (38 : ℝ) / 40 - κ) (z2 := (-1 / 40 : ℝ)) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have t17 := tangent_up_neg (w := (-1 : ℝ)) (z0 := (1 / 80 : ℝ)) (z := (40 : ℝ) / 40 - κ) (by norm_num) (by norm_num) (by linarith)
  linarith [Upot_expand κ, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, P1, P2]

/-- `U ≤ 71/100` on `[0, 1]`: the 42 boxes cover `[0, 1]`. -/
theorem Upot_le (κ : ℝ) (h0 : 0 ≤ κ) (h1 : κ ≤ 1) : Upot κ ≤ 71 / 100 := by
  rcases le_or_gt κ (1 / 40 : ℝ) with h | hk0
  · exact box0 κ (by linarith) h
  rcases le_or_gt κ (1 / 20 : ℝ) with h | hk1
  · exact box1 κ hk0.le h
  rcases le_or_gt κ (3 / 40 : ℝ) with h | hk2
  · exact box2 κ hk1.le h
  rcases le_or_gt κ (1 / 10 : ℝ) with h | hk3
  · exact box3 κ hk2.le h
  rcases le_or_gt κ (9 / 80 : ℝ) with h | hk4
  · exact box4 κ hk3.le h
  rcases le_or_gt κ (1 / 8 : ℝ) with h | hk5
  · exact box5 κ hk4.le h
  rcases le_or_gt κ (3 / 20 : ℝ) with h | hk6
  · exact box6 κ hk5.le h
  rcases le_or_gt κ (7 / 40 : ℝ) with h | hk7
  · exact box7 κ hk6.le h
  rcases le_or_gt κ (1 / 5 : ℝ) with h | hk8
  · exact box8 κ hk7.le h
  rcases le_or_gt κ (9 / 40 : ℝ) with h | hk9
  · exact box9 κ hk8.le h
  rcases le_or_gt κ (1 / 4 : ℝ) with h | hk10
  · exact box10 κ hk9.le h
  rcases le_or_gt κ (11 / 40 : ℝ) with h | hk11
  · exact box11 κ hk10.le h
  rcases le_or_gt κ (3 / 10 : ℝ) with h | hk12
  · exact box12 κ hk11.le h
  rcases le_or_gt κ (13 / 40 : ℝ) with h | hk13
  · exact box13 κ hk12.le h
  rcases le_or_gt κ (7 / 20 : ℝ) with h | hk14
  · exact box14 κ hk13.le h
  rcases le_or_gt κ (3 / 8 : ℝ) with h | hk15
  · exact box15 κ hk14.le h
  rcases le_or_gt κ (2 / 5 : ℝ) with h | hk16
  · exact box16 κ hk15.le h
  rcases le_or_gt κ (17 / 40 : ℝ) with h | hk17
  · exact box17 κ hk16.le h
  rcases le_or_gt κ (9 / 20 : ℝ) with h | hk18
  · exact box18 κ hk17.le h
  rcases le_or_gt κ (19 / 40 : ℝ) with h | hk19
  · exact box19 κ hk18.le h
  rcases le_or_gt κ (1 / 2 : ℝ) with h | hk20
  · exact box20 κ hk19.le h
  rcases le_or_gt κ (21 / 40 : ℝ) with h | hk21
  · exact box21 κ hk20.le h
  rcases le_or_gt κ (11 / 20 : ℝ) with h | hk22
  · exact box22 κ hk21.le h
  rcases le_or_gt κ (23 / 40 : ℝ) with h | hk23
  · exact box23 κ hk22.le h
  rcases le_or_gt κ (3 / 5 : ℝ) with h | hk24
  · exact box24 κ hk23.le h
  rcases le_or_gt κ (5 / 8 : ℝ) with h | hk25
  · exact box25 κ hk24.le h
  rcases le_or_gt κ (13 / 20 : ℝ) with h | hk26
  · exact box26 κ hk25.le h
  rcases le_or_gt κ (27 / 40 : ℝ) with h | hk27
  · exact box27 κ hk26.le h
  rcases le_or_gt κ (7 / 10 : ℝ) with h | hk28
  · exact box28 κ hk27.le h
  rcases le_or_gt κ (29 / 40 : ℝ) with h | hk29
  · exact box29 κ hk28.le h
  rcases le_or_gt κ (3 / 4 : ℝ) with h | hk30
  · exact box30 κ hk29.le h
  rcases le_or_gt κ (31 / 40 : ℝ) with h | hk31
  · exact box31 κ hk30.le h
  rcases le_or_gt κ (4 / 5 : ℝ) with h | hk32
  · exact box32 κ hk31.le h
  rcases le_or_gt κ (33 / 40 : ℝ) with h | hk33
  · exact box33 κ hk32.le h
  rcases le_or_gt κ (17 / 20 : ℝ) with h | hk34
  · exact box34 κ hk33.le h
  rcases le_or_gt κ (7 / 8 : ℝ) with h | hk35
  · exact box35 κ hk34.le h
  rcases le_or_gt κ (71 / 80 : ℝ) with h | hk36
  · exact box36 κ hk35.le h
  rcases le_or_gt κ (9 / 10 : ℝ) with h | hk37
  · exact box37 κ hk36.le h
  rcases le_or_gt κ (37 / 40 : ℝ) with h | hk38
  · exact box38 κ hk37.le h
  rcases le_or_gt κ (19 / 20 : ℝ) with h | hk39
  · exact box39 κ hk38.le h
  rcases le_or_gt κ (39 / 40 : ℝ) with h | hk40
  · exact box40 κ hk39.le h
  exact box41 κ hk40.le (by linarith)

end MaxU7Cert

theorem MaxU7_proof : Stmt_MaxU7 g7 := by
  intro κ h0 h1
  unfold g7
  exact MaxU7Cert.Upot_le κ h0 h1

end Zeta2.Z7

end
