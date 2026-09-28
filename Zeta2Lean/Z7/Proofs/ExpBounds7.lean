module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# The prime-by-prime exponent bounds (combination)

gap: 'denominators' (combination).  Difficulty 2.  **Proved** (complete; the two table facts
`EB7.resRows7_tiles` and `EB7.resRows7_f_le` are checked by `decide +kernel`).

**Task.** Prove `Stmt_ExpBounds7` from `Stmt_ThmK7`, `Stmt_HeadCert7`, `Stmt_ResCert7`,
`Stmt_Emin7`, `Stmt_SmallPrimes7` and `Stmt_BigPrimes7`.

**Proof (field by field).**
* `big` = `Stmt_BigPrimes7`; `small` = `Stmt_SmallPrimes7`.
* The trivial kernel (`EB7.eq7_le_of_Emin`): if every class has `E ≥ 4 - f`, then `Stmt_ThmK7`
  with `(c₀, j, c) = (0, 1, 0)` and `T = -f` gives `e_q ≤ f`.  Both certificate hypotheses are
  vacuous: `LevGe τ 0 1 0 (5 - f)` needs `p` with `E + 1 ≤ p < 5 - f` (`EB7.levGe_of_le`), and
  `PoleLevAt τ w (-f)` needs `l` with `E - netE + f < l ≤ -netE - 1`, i.e. `E + f < -1`
  (`EB7.poleLevGe_of_le`).
* `crude`: `Stmt_Emin7` (`E ≥ -10`) and the trivial kernel with `f = 14`.
* `tail`: for `x = n/q ≥ 20` put `t = ⌊(x - 20)/40⌋`, so `x - 40t ∈ [20, 60)`; the rows of
  `resRows7` tile `[20, 60)` (`EB7.resRows7_tiles`, kernel-checked, with the covering lemma
  `EB7.tilesB_cover`), so `x ∈ [a + 40t, b + 40t)` for some row; `Stmt_ResCert7` gives
  `E ≥ 4 - f ≥ -6` (every residue row has `f ≤ 10`: `EB7.resRows7_f_le`, kernel-checked); then
  the trivial kernel with `f = 10`.
* `rows`: a row of `denTable7` is a head row (`Stmt_HeadCert7` gives exactly the certificate
  hypotheses of `Stmt_ThmK7` with `(c₀, j, c)` of the row and `T = -f`, `EB7.eq7_le_of_head`) or a
  residue row shifted by `40t`, `t ∈ {0, 1, 2}` (`Stmt_ResCert7` with that `t`, then the trivial
  kernel; `EB7.shift_a`/`EB7.shift_b` compute the shifted ends).  The side conditions come from
  `DenRow.sane` (`denTable7_sane`, `Z7/DenTable.lean`; unpacked by `EB7.sane_spec`): `1 ≤ j ≤ 4`,
  `c ≠ 0 → f + j ≥ 4`, positive denominators of the ends, and the denominators of `c₀`, `c`
  divide `41!^256`, so they are `q`-integral for every prime `q > 41` (`EB7.valGe_zero_of_den_dvd`).

**For `Denominators7`.** `EB7.denTable7_tiles` (the 3409 rows tile `[1, 140)`, kernel-checked) with
`EB7.tilesB_cover` puts every `x = n/q ∈ [1, 140)` in some row, so `rows` applies to every prime
`q > 1000`, `q ∤ u`, `q² > 2n + 3q` with `n/q < 140`; import this file to reuse them.

**Numerical check.** `python/z7_mirror.py`, section "ExpBounds7" (all five fields against the true
exponents at `n = 40 … 480` and sampled primes of larger `n`); `python/z7_audit.py` (the table
against 11,662 true exponents).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

namespace EB7

/-! ### Kernel-checked facts about the residue rows -/

/-- `tilesB l ln ld hn hd`: the rows of `l`, read left to right, tile `[ln/ld, hn/hd)`.  Every row
has positive denominators, its left end is the right end of the previous row (the first row starts
at `ln/ld`; ends compared by cross-multiplication), and the last right end is `hn/hd`. -/
def tilesB : List DenRow → ℕ → ℕ → ℕ → ℕ → Bool
  | [], ln, ld, hn, hd => decide (ln * hd = hn * ld)
  | r :: rs, ln, ld, hn, hd =>
      decide (0 < r.ad) && decide (0 < r.bd) && decide (r.an * ld = ln * r.ad) &&
        tilesB rs r.bn r.bd hn hd

/-- A list of rows that tiles `[ln/ld, hn/hd)` covers every point of it. -/
theorem tilesB_cover : ∀ (l : List DenRow) (ln ld hn hd : ℕ), 0 < ld → 0 < hd →
    tilesB l ln ld hn hd = true → ∀ x : ℚ, (ln : ℚ) / ld ≤ x → x < (hn : ℚ) / hd →
      ∃ r ∈ l, r.a ≤ x ∧ x < r.b := by
  intro l
  induction l with
  | nil =>
    intro ln ld hn hd hld hhd h x h1 h2
    simp only [tilesB, decide_eq_true_eq] at h
    have hld' : (ld : ℚ) ≠ 0 := by exact_mod_cast hld.ne'
    have hhd' : (hd : ℚ) ≠ 0 := by exact_mod_cast hhd.ne'
    have he : (ln : ℚ) / ld = (hn : ℚ) / hd := by
      rw [div_eq_div_iff hld' hhd']
      exact_mod_cast h
    linarith
  | cons r rs ih =>
    intro ln ld hn hd hld hhd h x h1 h2
    simp only [tilesB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨had, hbd⟩, hcross⟩, hrest⟩ := h
    have ha : r.a = (ln : ℚ) / ld := by
      have had' : (r.ad : ℚ) ≠ 0 := by exact_mod_cast had.ne'
      have hld' : (ld : ℚ) ≠ 0 := by exact_mod_cast hld.ne'
      rw [DenRow.a, div_eq_div_iff had' hld']
      exact_mod_cast hcross
    by_cases hx : x < r.b
    · refine ⟨r, List.mem_cons.mpr (Or.inl rfl), ?_, hx⟩
      rw [ha]
      exact h1
    · obtain ⟨r', hr', h'⟩ := ih r.bn r.bd hn hd hbd hhd hrest x (not_lt.mp hx) h2
      exact ⟨r', List.mem_cons.mpr (Or.inr hr'), h'⟩

/-- The residue rows tile one period `[20, 60)` (kernel-checked). -/
theorem resRows7_tiles : tilesB resRows7 20 1 60 1 = true := by
  decide +kernel

/-- Every residue row has `f ≤ 10` (kernel-checked). -/
theorem resRows7_f_le : resRows7.all (fun r => decide (r.f ≤ 10)) = true := by
  decide +kernel

/-- The whole table tiles `[1, 140)` (kernel-checked).  Not used here: provided for the analytic
part (`Denominators7`), where `tilesB_cover` then puts every `x = n/q ∈ [1, 140)` in a row. -/
theorem denTable7_tiles : tilesB denTable7 1 1 140 1 = true := by
  decide +kernel

/-! ### The sanity conditions of the table -/

/-- `DenRow.sane`, unpacked. -/
theorem sane_spec {r : DenRow} (h : r.sane = true) :
    0 < r.ad ∧ 0 < r.bd ∧ 1 ≤ r.j ∧ r.j ≤ 4 ∧ r.f ≤ 14 ∧ (r.c = 0 ∨ 4 ≤ r.f + r.j) ∧
      r.c0.den ∣ DenRow.denBound ∧ r.c.den ∣ DenRow.denBound := by
  simp only [DenRow.sane, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  exact h

/-- Every row of the table is sane. -/
theorem sane_of_mem {r : DenRow} (hr : r ∈ denTable7) : r.sane = true :=
  List.all_eq_true.mp denTable7_sane r hr

/-- The unshifted residue rows are rows of the table. -/
theorem mem_denTable7_of_res {r : DenRow} (hr : r ∈ resRows7) : r ∈ denTable7 := by
  simp only [denTable7, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hr))

/-- The left end of a row shifted by `40 s`. -/
theorem shift_a (s : ℕ) (r : DenRow) (h : 0 < r.ad) : (DenRow.shift s r).a = r.a + 40 * s := by
  have h' : (r.ad : ℚ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [DenRow.a, DenRow.shift]
  push_cast
  rw [add_div, mul_div_assoc, div_self h', mul_one]

/-- The right end of a row shifted by `40 s`. -/
theorem shift_b (s : ℕ) (r : DenRow) (h : 0 < r.bd) : (DenRow.shift s r).b = r.b + 40 * s := by
  have h' : (r.bd : ℚ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [DenRow.b, DenRow.shift]
  push_cast
  rw [add_div, mul_div_assoc, div_self h', mul_one]

/-! ### `q`-integrality of the kernel constants -/

/-- `v_q(0) ≥ 0`. -/
theorem valGe_zero_zero (q : ℕ) : ValGe q 0 0 := by
  simp [ValGe]

/-- A rational whose denominator divides `41!^256` is `q`-integral for every prime `q > 41`. -/
theorem valGe_zero_of_den_dvd {q : ℕ} (hq : q.Prime) (hq41 : 41 < q) {x : ℚ}
    (hx : x.den ∣ DenRow.denBound) : ValGe q 0 x := by
  have hnd : ¬ q ∣ x.den := by
    intro hdvd
    have h0 : q ∣ (Nat.factorial 41) ^ 256 := hdvd.trans hx
    have h1 : q ∣ Nat.factorial 41 := hq.dvd_of_dvd_pow h0
    have h2 : q ≤ 41 := (Nat.Prime.dvd_factorial hq).mp h1
    omega
  unfold ValGe
  rw [neg_zero, zpow_zero]
  by_cases hx0 : x = 0
  · rw [hx0, padicNorm.zero]
    exact zero_le_one
  · rw [padicNorm.eq_zpow_of_nonzero hx0]
    have hv : 0 ≤ padicValRat q x := by
      rw [padicValRat, padicValNat.eq_zero_of_not_dvd hnd]
      omega
    exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hq.one_lt.le) (by omega)

/-! ### Vacuous certificates -/

/-- `LevGe τ c₀ j c P` is vacuous when `P ≤ E + 1`. -/
theorem levGe_of_le {τ : LocalType} {c0 : ℚ} {j : ℕ} {c : ℚ} {P : ℤ} (h : P ≤ τ.E + 1) :
    LevGe τ c0 j c P := by
  intro p hp1 hp2
  exfalso
  omega

/-- `PoleLevGe τ T` is vacuous when `T ≤ E + 1`: `E - netE - T < l ≤ -netE - 1` is impossible. -/
theorem poleLevGe_of_le {τ : LocalType} {T : ℤ} (h : T ≤ τ.E + 1) : PoleLevGe τ T := by
  intro p _ l hl1 hl2
  exfalso
  omega

/-! ### The exponent bounds from Theorem K -/

/-- **Trivial kernel.**  If every class has `E ≥ 4 - f`, then `e_q ≤ f` (`Stmt_ThmK7` with
`κ = 0`, `T = -f`). -/
theorem eq7_le_of_Emin (hK : Stmt_ThmK7) {u q : ℕ} (f : ℕ) (hq : q.Prime) (hq29 : 29 ≤ q)
    (hadm : 80 * u + 3 * q < q ^ 2) (hE : ∀ k₀ < q, 4 - (f : ℤ) ≤ (localModel u q k₀).E) :
    eq7 u q ≤ f := by
  have h := hK u q 0 0 1 (-(f : ℤ)) hq hq29 hadm (by omega) le_rfl (by norm_num)
    (valGe_zero_zero q) (valGe_zero_zero q) (fun h0 => absurd rfl h0)
    (fun k₀ hk₀ => levGe_of_le (by have := hE k₀ hk₀; omega))
    (fun k₀ hk₀ => poleLevGe_of_le (by have := hE k₀ hk₀; omega))
  omega

/-- **Head rows.**  `Stmt_HeadCert7` supplies the certificate hypotheses of `Stmt_ThmK7` for the
row's kernel and `T = -f`. -/
theorem eq7_le_of_head (hK : Stmt_ThmK7) (hH : Stmt_HeadCert7) {row : DenRow}
    (hrow : row ∈ headRows7) (hsane : row.sane = true) {u q : ℕ} (hq : q.Prime)
    (hq1000 : 1000 < q) (hqu : ¬ q ∣ u) (hadm : 80 * u + 3 * q < q ^ 2)
    (ha : row.a ≤ ((40 * u : ℕ) : ℚ) / q) (hb : ((40 * u : ℕ) : ℚ) / q < row.b) :
    eq7 u q ≤ row.f := by
  obtain ⟨-, -, hj1, hj4, -, hcf, hc0, hc⟩ := sane_spec hsane
  obtain ⟨hLev, hPole⟩ := hH row hrow u q hq hq1000 hqu hadm ha hb
  have h := hK u q row.c0 row.c row.j (-(row.f : ℤ)) hq (by omega) hadm (by omega) hj1 hj4
    (valGe_zero_of_den_dvd hq (by omega) hc0) (valGe_zero_of_den_dvd hq (by omega) hc)
    (fun hne => hcf.elim (fun h0 => absurd h0 hne) (fun h4 => by omega))
    (fun k₀ hk₀ => by
      have e : -(row.f : ℤ) + 5 = 5 - row.f := by ring
      rw [e]
      exact hLev k₀ hk₀)
    hPole
  omega

/-- **Residue rows** (shifted by `40 t`).  `Stmt_ResCert7` gives `E ≥ 4 - f`; then the trivial
kernel. -/
theorem eq7_le_of_res (hK : Stmt_ThmK7) (hR : Stmt_ResCert7) {row : DenRow}
    (hrow : row ∈ resRows7) (t : ℕ) {u q : ℕ} (hq : q.Prime) (hq1000 : 1000 < q)
    (hqu : ¬ q ∣ u) (hadm : 80 * u + 3 * q < q ^ 2)
    (ha : row.a + 40 * t ≤ ((40 * u : ℕ) : ℚ) / q) (hb : ((40 * u : ℕ) : ℚ) / q < row.b + 40 * t) :
    eq7 u q ≤ row.f :=
  eq7_le_of_Emin hK row.f hq (by omega) hadm (hR row hrow t u q hq hq1000 hqu hadm ha hb)

end EB7

open EB7 in
theorem ExpBounds7_proof (hK : Stmt_ThmK7) (hH : Stmt_HeadCert7) (hR : Stmt_ResCert7)
    (hE : Stmt_Emin7) (hS : Stmt_SmallPrimes7) (hB : Stmt_BigPrimes7) : Stmt_ExpBounds7 := by
  refine ⟨hB, hS, fun u q hq hq29 hadm => ?_, fun u q hq hq1000 hqu hadm h20 => ?_,
    fun row hrow u q hq hq1000 hqu hadm ha hb => ?_⟩
  · -- crude: `E ≥ -10`
    exact eq7_le_of_Emin hK 14 hq hq29 hadm fun k₀ hk₀ => by
      have := hE u q k₀ hq (by omega) hk₀
      omega
  · -- tail: `x = n/q ≥ 20`, reduce to one period by `t = ⌊(x - 20)/40⌋`
    apply eq7_le_of_Emin hK 10 hq (by omega) hadm
    intro k₀ hk₀
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
    have hx20 : (20 : ℚ) ≤ ((40 * u : ℕ) : ℚ) / q := by
      rw [le_div_iff₀ hq0]
      exact_mod_cast h20
    obtain ⟨t, ht1, ht2⟩ : ∃ t : ℕ, (t : ℚ) ≤ (((40 * u : ℕ) : ℚ) / q - 20) / 40 ∧
        (((40 * u : ℕ) : ℚ) / q - 20) / 40 < t + 1 :=
      ⟨_, Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩
    obtain ⟨r, hr, hra, hrb⟩ := tilesB_cover resRows7 20 1 60 1 one_pos one_pos resRows7_tiles
      (((40 * u : ℕ) : ℚ) / q - 40 * t)
      (by simp only [Nat.cast_ofNat, Nat.cast_one, div_one]; linarith)
      (by simp only [Nat.cast_ofNat, Nat.cast_one, div_one]; linarith)
    have hEr := hR r hr t u q hq hq1000 hqu hadm (by linarith) (by linarith) k₀ hk₀
    have hf : r.f ≤ 10 := by
      have h := List.all_eq_true.mp resRows7_f_le r hr
      simpa using h
    omega
  · -- rows: head rows, and residue rows shifted by `0`, `40`, `80`
    have hsane := sane_of_mem hrow
    simp only [denTable7, List.mem_append, List.mem_map] at hrow
    rcases hrow with ((hhead | hres) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
    · exact eq7_le_of_head hK hH hhead hsane hq hq1000 hqu hadm ha hb
    · refine eq7_le_of_res hK hR hres 0 hq hq1000 hqu hadm ?_ ?_
      · rw [Nat.cast_zero, mul_zero, add_zero]
        exact ha
      · rw [Nat.cast_zero, mul_zero, add_zero]
        exact hb
    · obtain ⟨had, hbd, -⟩ := sane_spec (sane_of_mem (mem_denTable7_of_res hr))
      rw [shift_a 1 r had] at ha
      rw [shift_b 1 r hbd] at hb
      exact eq7_le_of_res hK hR hr 1 hq hq1000 hqu hadm ha hb
    · obtain ⟨had, hbd, -⟩ := sane_spec (sane_of_mem (mem_denTable7_of_res hr))
      rw [shift_a 2 r had] at ha
      rw [shift_b 2 r hbd] at hb
      exact eq7_le_of_res hK hR hr 2 hq hq1000 hqu hadm ha hb

end Zeta2.Z7

end
