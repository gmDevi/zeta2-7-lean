module

public import Zeta2Lean.Z7.Statements

@[expose] public section

/-!
# `E`-certificates: the floor-sum form of `E` and sweep certificates (helper of `ResCert7`)

Reusable by `HeadCert7` (it needs an `E` lower bound on all its rows too).  Documentation of the
encoding and of the data generator: `notes/ResCert7.md`.

## Line systems (`LineSys7`)

A line system is a list of `n` lines `ℓ_j(x) = (A_j x + B_j)/80` with weights `W_j`, each of floor
type (`C_j = false`) or ceiling type (`C_j = true`), and a constant `K`; its value is
`val x y = ∑_j W_j F_j(ℓ_j(x) - y) + K` (`F_j = ⌊·⌋` or `⌈·⌉`).

## Sweep certificates (`ECert7`)

A certificate for `[a, b) = [pa/qa, pb/qb)` is the claimed lower bound `sig` and the order `ord`
(a permutation of `0, …, n-1`) of the lines by their fractional parts `β_j(x) = ℓ_j(x) - N_j`,
`N_j` = integer part at the midpoint (recomputed, `ECert7.N`).  `ECert7.ok` checks (by kernel
reduction, `decide +kernel`) that `0 ≤ β_j ≤ 1` at both ends (`< 1` at `a` for floor lines), that
the order is weakly increasing at both ends (hence on `[a, b]`, by linearity), and that every prefix
sum `V₀ - ∑_{i<p} W_{ord i}` is `≥ sig`.  For `y ∈ [0, 1)` a floor line drops by `W_j` when
`β_j < y`, a ceiling line when `β_j ≤ y`; the dropped lines form a prefix of `ord` as long as no
floor line and no ceiling line are integral at the same `(x, y)` (`LineSys7.Real`).  Hence
`ECert7.ok_sound`: `sig ≤ val x y` for `x ∈ [a, b)`, `y ∈ [0, 1)` realizable.

## The `E`-system of cand3 (`sysE7`) and the dictionary

`sysE7` has 20 lines (in units of `x/80`):
* `j = 0..5`: numerator upper ends `(1 - η_m) x - 1/2` (floor, weight `+1`);
* `j = 6..11`: numerator lower ends `η_m x - 1/2` (floor, weight `-1`);
* `j = 12..15`: pole-level upper ends `(1 - ℓ/20) x`, `ℓ = 0..3` (floor, weight `-1`);
* `j = 16..19`: pole-level lower ends `(ℓ/20) x` (ceiling, weight `+1`); constant `K = -4`.

`localModel_E_eq_sysE7`: for odd `q` and `k₀ < q`,
`(localModel u q k₀).E = sysE7.val (40u/q) (k₀/q) + [q ∣ 2k₀ - 40u]` (the `δ`-zero).
`sysE7_real_disc`: for a prime `q > 40` with `q ∤ u` the point `(40u/q, k₀/q)` is realizable.
`sysE7_val_add_40`: `val` is `40`-periodic in `x` (proof Lemma 4.12).

## Interface

* `ECert7.E_ge`: a valid certificate `c` of `sysE7` on `[a, b)` gives `c.sig ≤ E_ξ` for every
  class of every prime `q > 40`, `q ∤ u` with `40u/q ∈ [a + 40t, b + 40t)` (`ResCert7`: `t` = the
  period shift; `HeadCert7`: `t = 0`, data in `ResCert7Head.lean`).
* `RC7.LevGe_of_E`, `RC7.PoleLevGe_of_E`: the certificate conditions of `ThmK7` are vacuous
  for large `E`.
-/

set_option linter.style.longLine false

open Finset

namespace Zeta2.Z7

/-! ## Line systems -/

/-- A system of `n` lines `ℓ_j(x) = (A_j x + B_j)/80`, weights `W_j`, ceiling flags `C_j` and a
constant `K` (lists are read with default `0`/`false`). -/
structure LineSys7 where
  /-- number of lines -/
  n : ℕ
  /-- slopes (times `80`) -/
  A : List ℤ
  /-- intercepts (times `80`) -/
  B : List ℤ
  /-- weights -/
  W : List ℤ
  /-- `true`: ceiling line, `false`: floor line -/
  C : List Bool
  /-- constant term -/
  K : ℤ

namespace LineSys7

variable (S : LineSys7)

/-- slope of line `j` (times `80`) -/
def la (j : ℕ) : ℤ := S.A.getD j 0

/-- intercept of line `j` (times `80`) -/
def lb (j : ℕ) : ℤ := S.B.getD j 0

/-- weight of line `j` -/
def lw (j : ℕ) : ℤ := S.W.getD j 0

/-- ceiling flag of line `j` -/
def lc (j : ℕ) : Bool := S.C.getD j false

/-- the line `ℓ_j(x) = (A_j x + B_j)/80` -/
def ell (j : ℕ) (x : ℚ) : ℚ := ((S.la j : ℚ) * x + S.lb j) / 80

/-- `⌈z⌉` for a ceiling line, `⌊z⌋` for a floor line -/
def fl (j : ℕ) (z : ℚ) : ℤ := if S.lc j then ⌈z⌉ else ⌊z⌋

/-- the value `∑_j W_j F_j(ℓ_j(x) - y) + K` -/
def val (x y : ℚ) : ℤ := (∑ j ∈ range S.n, S.lw j * S.fl j (S.ell j x - y)) + S.K

/-- Realizability: no floor line and no ceiling line are integral at the same point. -/
def Real (x y : ℚ) : Prop :=
  ∀ i < S.n, ∀ j < S.n, S.lc i = false → S.lc j = true → ∀ z z' : ℤ,
    S.ell i x - y = z → S.ell j x - y = z' → False

/-- the integer part of `ℓ_j` at the midpoint of `[pa/qa, pb/qb]` -/
def Nm (pa qa pb qb : ℤ) (j : ℕ) : ℤ :=
  (S.la j * (pa * qb + pb * qa) + S.lb j * (2 * qa * qb)) / (80 * (2 * qa * qb))

/-- `80 Q (ℓ_j(P/Q) - N)`, an integer -/
def sv (N : ℤ) (j : ℕ) (P Q : ℤ) : ℤ := S.la j * P + S.lb j * Q - 80 * Q * N

end LineSys7

/-! ## Sweep certificates -/

/-- A sweep certificate for `[pa/qa, pb/qb)`: the lower bound `sig` and the order `ord` of the
lines by their fractional parts. -/
structure ECert7 where
  /-- numerator of the left end -/
  pa : ℤ
  /-- denominator of the left end -/
  qa : ℤ
  /-- numerator of the right end -/
  pb : ℤ
  /-- denominator of the right end -/
  qb : ℤ
  /-- the claimed lower bound -/
  sig : ℤ
  /-- the order of the lines -/
  ord : List ℕ

namespace ECert7

variable (S : LineSys7) (c : ECert7)

/-- integer part of line `j` at the midpoint -/
def N (j : ℕ) : ℤ := S.Nm c.pa c.qa c.pb c.qb j

/-- `80 qa β_j(a)` -/
def sa (j : ℕ) : ℤ := S.sv (c.N S j) j c.pa c.qa

/-- `80 qb β_j(b)` -/
def sb (j : ℕ) : ℤ := S.sv (c.N S j) j c.pb c.qb

/-- the value before any line has dropped (`y` just above `0`, no ceiling line at `0`) -/
def V0 : ℤ :=
  ((List.range S.n).map fun j => S.lw j * (c.N S j + if S.lc j then 1 else 0)).sum + S.K

/-- `0 ≤ β_j ≤ 1` at both ends, `β_j(a) < 1` for a floor line -/
def lineOK (j : ℕ) : Bool :=
  decide (0 ≤ c.sa S j) && decide (c.sa S j ≤ 80 * c.qa) && decide (0 ≤ c.sb S j) &&
    decide (c.sb S j ≤ 80 * c.qb) && (S.lc j || decide (c.sa S j < 80 * c.qa))

/-- the order is weakly increasing at both ends -/
def chainOK : List ℕ → Bool
  | [] => true
  | [_] => true
  | r :: s :: rs =>
    decide (c.sa S r ≤ c.sa S s) && decide (c.sb S r ≤ c.sb S s) && chainOK (s :: rs)

end ECert7

/-- every prefix sum is `≥ σ` -/
def ECert7.prefOK (S : LineSys7) (σ : ℤ) : ℤ → List ℕ → Bool
  | acc, [] => decide (σ ≤ acc)
  | acc, r :: rs => decide (σ ≤ acc) && ECert7.prefOK S σ (acc - S.lw r) rs

/-- The certificate check (by kernel reduction). -/
def ECert7.ok (S : LineSys7) (c : ECert7) : Bool :=
  decide (0 < c.qa) && decide (0 < c.qb) && decide (c.pa * c.qb < c.pb * c.qa) &&
    c.ord.isPerm (List.range S.n) && c.ord.all (c.lineOK S) && c.chainOK S c.ord &&
    ECert7.prefOK S c.sig (c.V0 S) c.ord

/-! ### Soundness -/

lemma ECert7.prefOK_sound (S : LineSys7) (σ : ℤ) (P : ℕ → Prop) [DecidablePred P] :
    ∀ (rows : List ℕ) (acc : ℤ), ECert7.prefOK S σ acc rows = true →
      σ ≤ acc - ((rows.takeWhile (fun r => decide (P r))).map S.lw).sum
  | [], acc, h => by simpa [ECert7.prefOK] using h
  | r :: rs, acc, h => by
    simp only [ECert7.prefOK, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hr : P r
    · have := ECert7.prefOK_sound S σ P rs (acc - S.lw r) h.2
      have e : (r :: rs).takeWhile (fun r => decide (P r)) =
          r :: rs.takeWhile (fun r => decide (P r)) := by
        simp [hr]
      rw [e, List.map_cons, List.sum_cons]
      linarith
    · simp [hr, h.1]

lemma ECert7.chainOK_chain (S : LineSys7) (c : ECert7) : ∀ L : List ℕ, c.chainOK S L = true →
    L.IsChain (fun r s => c.sa S r ≤ c.sa S s ∧ c.sb S r ≤ c.sb S s)
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | r :: s :: rs, h => by
    simp only [ECert7.chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.IsChain.cons_cons ⟨h.1.1, h.1.2⟩ (ECert7.chainOK_chain S c (s :: rs) h.2)

lemma ECert7.not_of_chain {α : Type*} (Q : α → Prop) : ∀ (L : List α) (a : α),
    (a :: L).IsChain (fun a b => Q b → Q a) → ¬ Q a → ∀ b ∈ L, ¬ Q b
  | [], _, _, _, b, hb => by simp at hb
  | c :: L, a, h, ha, b, hb => by
    rw [List.isChain_cons_cons] at h
    have hc : ¬ Q c := fun hQ => ha (h.1 hQ)
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact hc
    · exact ECert7.not_of_chain Q L c h.2 hc b hb'

/-- Along a chain on which `Q` is inherited backwards, the sum of `f` over the elements
satisfying `Q` is the sum over the maximal initial segment. -/
lemma ECert7.sum_ite_eq_takeWhile {α : Type*} (Q : α → Prop) [DecidablePred Q] (f : α → ℤ) :
    ∀ L : List α, L.IsChain (fun a b => Q b → Q a) →
      (L.map (fun a => if Q a then f a else 0)).sum =
        ((L.takeWhile (fun a => decide (Q a))).map f).sum
  | [], _ => by simp
  | a :: L, h => by
    by_cases ha : Q a
    · have ih := ECert7.sum_ite_eq_takeWhile Q f L h.tail
      simp [ha, ih]
    · have hall : ∀ b ∈ a :: L, ¬ Q b := by
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact ha
        · exact ECert7.not_of_chain Q L a h ha b hb'
      have h0 : (List.map (fun a => if Q a then f a else 0) (a :: L)) =
          List.map (fun _ => (0 : ℤ)) (a :: L) := by
        apply List.map_congr_left
        intro b hb
        simp [hall b hb]
      rw [h0]
      simp [ha]

lemma ECert7.sum_range_eq_list (n : ℕ) (f : ℕ → ℤ) :
    ∑ j ∈ range n, f j = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

lemma LineSys7.sv_cast (S : LineSys7) (j : ℕ) (N P Q : ℤ) (hQ : (Q : ℚ) ≠ 0) :
    (S.sv N j P Q : ℚ) = 80 * Q * (S.ell j ((P : ℚ) / Q) - N) := by
  unfold LineSys7.sv LineSys7.ell
  push_cast
  field_simp

/-- Affine interpolation of `ℓ_j - N` between the endpoints. -/
lemma LineSys7.ell_interp (S : LineSys7) (j : ℕ) (a b x N : ℚ) :
    (b - a) * (S.ell j x - N) = (b - x) * (S.ell j a - N) + (x - a) * (S.ell j b - N) := by
  unfold LineSys7.ell
  ring

lemma ECert7.nonneg_of_pos_mul {c z : ℚ} (hc : 0 < c) (h : 0 ≤ c * z) : 0 ≤ z := by
  by_contra hz
  push Not at hz
  nlinarith

lemma ECert7.le_one_of_pos_mul {c z : ℚ} (hc : 0 < c) (h : c * z ≤ c) : z ≤ 1 := by
  by_contra hz
  push Not at hz
  nlinarith

lemma ECert7.lt_one_of_pos_mul {c z : ℚ} (hc : 0 < c) (h : c * z < c) : z < 1 := by
  by_contra hz
  push Not at hz
  nlinarith

/-- A floor line with `β ∈ [0, 1)` drops by one exactly when `β < y`. -/
lemma ECert7.floor_sweep (N : ℤ) (β y : ℚ) (h0 : 0 ≤ β) (h1 : β < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ⌊(N : ℚ) + β - y⌋ = N - (if β < y then 1 else 0) := by
  rw [Int.floor_eq_iff]
  split_ifs with h <;> push_cast <;> constructor <;> linarith

/-- A ceiling line with `β ∈ [0, 1]` drops by one exactly when `β ≤ y`. -/
lemma ECert7.ceil_sweep (N : ℤ) (β y : ℚ) (h0 : 0 ≤ β) (h1 : β ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ⌈(N : ℚ) + β - y⌉ = N + 1 - (if β ≤ y then 1 else 0) := by
  rw [Int.ceil_eq_iff]
  split_ifs with h <;> push_cast <;> constructor <;> linarith

/-- **Soundness of a sweep certificate**: `sig ≤ val x y` on `[a, b) × [0, 1)`, off the
non-realizable points. -/
theorem ECert7.ok_sound (S : LineSys7) (c : ECert7) (hc : c.ok S = true) (x y : ℚ)
    (hxa : (c.pa : ℚ) / c.qa ≤ x) (hxb : x < (c.pb : ℚ) / c.qb) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hR : S.Real x y) : c.sig ≤ S.val x y := by
  simp only [ECert7.ok, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hqa, hqb⟩, hab⟩, hperm⟩, hrows⟩, hchain⟩, hpref⟩ := hc
  rw [List.isPerm_iff] at hperm
  rw [List.all_eq_true] at hrows
  have hchain' := ECert7.chainOK_chain S c _ hchain
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
  have hV : S.val x y = c.V0 S - ∑ j ∈ range S.n, S.lw j * (if Dd j = true then 1 else 0) := by
    unfold LineSys7.val ECert7.V0
    rw [← ECert7.sum_range_eq_list]
    have h1 : ∀ j ∈ range S.n, S.lw j * S.fl j (S.ell j x - y) =
        S.lw j * (c.N S j + if S.lc j then 1 else 0) -
          S.lw j * (if Dd j = true then 1 else 0) := by
      intro j hj
      rw [hfl j ((hmem j).2 (mem_range.1 hj))]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
    ring
  have hsum : ∑ j ∈ range S.n, S.lw j * (if Dd j = true then 1 else 0) =
      (c.ord.map (fun j => if Dd j = true then S.lw j else 0)).sum := by
    rw [ECert7.sum_range_eq_list]
    have e2 := (hperm.map (fun j => S.lw j * (if Dd j = true then (1 : ℤ) else 0))).sum_eq
    rw [← e2]
    congr 1
    apply List.map_congr_left
    intro j _
    split_ifs <;> simp
  have hchainD : c.ord.IsChain (fun r s => Dd s = true → Dd r = true) := by
    have hsub : ∀ r ∈ c.ord, ∀ s ∈ c.ord, (c.sa S r ≤ c.sa S s ∧ c.sb S r ≤ c.sb S s) →
        (Dd s = true → Dd r = true) := by
      intro r hr s hs hle hsy
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
        exact hR r ((hmem r).1 hr) s ((hmem s).1 hs) hcr hcs (c.N S r) (c.N S s)
          (by simp only [hβ] at hr_eq; linarith) (by simp only [hβ] at hs_eq; linarith)
      · linarith
    exact List.IsChain.imp_of_mem_imp (fun r s hr hs hle => hsub r hr s hs hle) hchain'
  have hfin := ECert7.sum_ite_eq_takeWhile (fun j => Dd j = true) S.lw c.ord hchainD
  have hp := ECert7.prefOK_sound S c.sig (fun j => Dd j = true) c.ord (c.V0 S) hpref
  rw [hV, hsum, hfin]
  exact hp

/-! ## Periodicity in `x` -/

namespace LineSys7

/-- `ℓ_j(x + 40 t) = ℓ_j(x) + (A_j/2) t` for an even slope. -/
lemma ell_add_40 (S : LineSys7) (j : ℕ) (hj : S.la j % 2 = 0) (x : ℚ) (t : ℤ) :
    S.ell j (x + 40 * t) = S.ell j x + ((S.la j / 2 : ℤ) : ℚ) * t := by
  have hz : S.la j = 2 * (S.la j / 2) := by omega
  unfold ell
  generalize S.la j / 2 = z at hz ⊢
  rw [hz]
  push_cast
  ring

lemma fl_add_int (S : LineSys7) (j : ℕ) (z : ℚ) (m : ℤ) : S.fl j (z + m) = S.fl j z + m := by
  unfold fl
  split_ifs <;> simp [Int.floor_add_intCast, Int.ceil_add_intCast]

/-- `val` is `40`-periodic in `x` when all slopes are even and `∑_j W_j A_j/2 = 0`. -/
theorem val_add_40 (S : LineSys7) (hA : ∀ j < S.n, S.la j % 2 = 0)
    (hW : ∑ j ∈ range S.n, S.lw j * (S.la j / 2) = 0) (x y : ℚ) (t : ℤ) :
    S.val (x + 40 * t) y = S.val x y := by
  unfold val
  have h1 : ∀ j ∈ range S.n, S.lw j * S.fl j (S.ell j (x + 40 * t) - y) =
      S.lw j * S.fl j (S.ell j x - y) + S.lw j * (S.la j / 2) * t := by
    intro j hj
    rw [S.ell_add_40 j (hA j (mem_range.1 hj)),
      show S.ell j x + ((S.la j / 2 : ℤ) : ℚ) * t - y =
        (S.ell j x - y) + ((S.la j / 2 * t : ℤ) : ℚ) by push_cast; ring, fl_add_int]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, hW]
  ring

/-- Realizability is invariant under `x ↦ x + 40 t` (the lines move by integers). -/
theorem Real_add_40 (S : LineSys7) (hA : ∀ j < S.n, S.la j % 2 = 0) {x y : ℚ}
    (h : S.Real x y) (t : ℤ) : S.Real (x + 40 * t) y := by
  intro i hi j hj hci hcj z z' h1 h2
  rw [S.ell_add_40 i (hA i hi)] at h1
  rw [S.ell_add_40 j (hA j hj)] at h2
  exact h i hi j hj hci hcj (z - S.la i / 2 * t) (z' - S.la j / 2 * t)
    (by push_cast; linarith) (by push_cast; linarith)

end LineSys7

/-! ## The `E`-system of cand3 -/

/-- The 20 lines of the floor-sum form of `E` (proof Lemma 4.12), `ℓ_j(x) = (A_j x + B_j)/80`:
numerator upper ends `(1 - η_m) x - 1/2` (weight `+1`), numerator lower ends `η_m x - 1/2`
(`-1`), pole-level upper ends `(1 - ℓ/20) x`, `ℓ = 0..3` (`-1`), pole-level lower ends
`(ℓ/20) x` (ceiling lines, `+1`); constant `-4`. -/
def sysE7 : LineSys7 where
  n := 20
  A := [70, 66, 66, 62, 58, 54, 10, 14, 14, 18, 22, 26, 80, 76, 72, 68, 0, 4, 8, 12]
  B := [-40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, 0, 0, 0, 0, 0, 0]
  W := [1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1]
  C := [false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, true, true, true]
  K := -4

lemma sysE7_n : sysE7.n = 20 := rfl

lemma sysE7_even : ∀ j < sysE7.n, sysE7.la j % 2 = 0 := by decide

lemma sysE7_bal : ∑ j ∈ range sysE7.n, sysE7.lw j * (sysE7.la j / 2) = 0 := by decide

/-- `E` is `40`-periodic in `x` (proof Lemma 4.12). -/
theorem sysE7_val_add_40 (x y : ℚ) (t : ℤ) : sysE7.val (x + 40 * t) y = sysE7.val x y :=
  sysE7.val_add_40 sysE7_even sysE7_bal x y t

theorem sysE7_Real_add_40 {x y : ℚ} (h : sysE7.Real x y) (t : ℤ) :
    sysE7.Real (x + 40 * t) y :=
  sysE7.Real_add_40 sysE7_even h t

/-! ## The dictionary: `E` of a local model is a value of `sysE7` -/

/-- `RC7.zc q M = ⌊M/q - 1/2⌋ + 1` for odd `q` (`RC7.floor_half`). -/
def RC7.zc (q : ℕ) (M : ℤ) : ℤ := (M + ((q : ℤ) - 1) / 2) / q

lemma RC7.floor_half (q : ℕ) (hq : Odd q) (M : ℤ) : ⌊(M : ℚ) / q - 1 / 2⌋ = RC7.zc q M - 1 := by
  obtain ⟨s, hs⟩ := hq
  have hqz : (q : ℤ) = 2 * s + 1 := by exact_mod_cast hs
  have hq0 : (0 : ℤ) < q := by omega
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have e : (M : ℚ) / q - 1 / 2 = ((2 * M - q : ℤ) : ℚ) / ((2 * q : ℕ) : ℚ) := by
    push_cast
    field_simp
  rw [e, Rat.floor_intCast_div_natCast]
  unfold RC7.zc
  have hs2 : ((q : ℤ) - 1) / 2 = s := by omega
  rw [hs2]
  have h1 := Int.emod_add_mul_ediv (M + s) q
  have h2 := Int.emod_nonneg (M + s) hq0.ne'
  have h3 := Int.emod_lt_of_pos (M + s) hq0
  have h2q : (0 : ℤ) < ((2 * q : ℕ) : ℤ) := by push_cast; omega
  have key := (Int.ediv_emod_unique h2q).2
    (show 2 * ((M + s) % q) + 1 + ((2 * q : ℕ) : ℤ) * ((M + s) / q - 1) = 2 * M - q ∧
        0 ≤ 2 * ((M + s) % q) + 1 ∧ 2 * ((M + s) % q) + 1 < ((2 * q : ℕ) : ℤ) from
      ⟨by push_cast; linarith, by omega, by push_cast; omega⟩)
  exact key.1

lemma RC7.ceil_div (q : ℕ) (hq : 0 < q) (M : ℤ) : ⌈(M : ℚ) / q⌉ = (M - 1) / q + 1 := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have h1 := Int.emod_add_mul_ediv (M - 1) q
  have h2 := Int.emod_nonneg (M - 1) hq0.ne'
  have h3 := Int.emod_lt_of_pos (M - 1) hq0
  have i1 : ((M - 1) / q) * (q : ℤ) < M := by linarith
  have i2 : M ≤ ((M - 1) / q + 1) * (q : ℤ) := by linarith
  have i1' : (((M - 1) / q : ℤ) : ℚ) * q < M := by exact_mod_cast i1
  have i2' : (M : ℚ) ≤ ((((M - 1) / q + 1 : ℤ)) : ℚ) * q := by exact_mod_cast i2
  rw [Int.ceil_eq_iff]
  constructor
  · rw [lt_div_iff₀ hq']
    push_cast
    linarith
  · rw [div_le_iff₀ hq']
    exact i2'

lemma RC7.ell_disc (A B h : ℤ) (hA : A = 2 * h) (u q k₀ : ℕ) (hq : 0 < q) :
    ((A : ℚ) * (((40 * u : ℕ) : ℚ) / q) + B) / 80 - (k₀ : ℚ) / q =
      ((h * u - k₀ : ℤ) : ℚ) / q + (B : ℚ) / 80 := by
  subst hA
  have hq' : (q : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The value of line `j` of `sysE7` at a discrete point, `M = (A_j/2) u - k₀`. -/
def RC7.gv (q j : ℕ) (M : ℤ) : ℤ :=
  if j < 12 then RC7.zc q M - 1 else if j < 16 then M / q else (M - 1) / q + 1

lemma RC7.la_even (j : ℕ) (hj : j < 20) : sysE7.la j = 2 * (sysE7.la j / 2) := by
  have : sysE7.la j % 2 = 0 := sysE7_even j hj
  omega

lemma RC7.fl_disc (u q k₀ : ℕ) (hq : Odd q) (j : ℕ) (hj : j < 20) :
    sysE7.fl j (sysE7.ell j (((40 * u : ℕ) : ℚ) / q) - (k₀ : ℚ) / q) =
      RC7.gv q j (sysE7.la j / 2 * u - k₀) := by
  have hq0 : 0 < q := hq.pos
  unfold LineSys7.ell
  rw [RC7.ell_disc _ _ _ (RC7.la_even j hj) u q k₀ hq0]
  unfold LineSys7.fl RC7.gv
  by_cases h12 : j < 12
  · have hb : sysE7.lb j = -40 := by interval_cases j <;> rfl
    have hc : sysE7.lc j = false := by interval_cases j <;> rfl
    rw [hb, hc, ite_eq_left h12]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (((-40 : ℤ) : ℚ)) / 80 = -(1 / 2) by norm_num, ← sub_eq_add_neg, RC7.floor_half q hq]
  · have h12' : 12 ≤ j := by omega
    by_cases h16 : j < 16
    · have hb : sysE7.lb j = 0 := by interval_cases j <;> rfl
      have hc : sysE7.lc j = false := by interval_cases j <;> rfl
      rw [hb, hc, ite_eq_right h12, ite_eq_left h16]
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_zero, zero_div, add_zero]
      exact Rat.floor_intCast_div_natCast _ _
    · have h16' : 16 ≤ j := by omega
      have hb : sysE7.lb j = 0 := by interval_cases j <;> rfl
      have hc : sysE7.lc j = true := by interval_cases j <;> rfl
      rw [hb, hc, ite_eq_right h12, ite_eq_right h16]
      simp only [↓reduceIte, Int.cast_zero, zero_div, add_zero]
      exact RC7.ceil_div q hq0 _

/-- The value of `sysE7` at a discrete point, as integer divisions. -/
theorem RC7.val_disc (u q k₀ : ℕ) (hq : Odd q) :
    sysE7.val (((40 * u : ℕ) : ℚ) / q) ((k₀ : ℚ) / q) =
      ∑ m : Fin 6, (RC7.zc q (((40 - eta m : ℕ) : ℤ) * u - k₀) - RC7.zc q ((eta m : ℤ) * u - k₀)) -
      ((40 * u - k₀) / q - (-(k₀ : ℤ) - 1) / q + ((38 * u - k₀) / q - (2 * u - k₀ - 1) / q) +
        ((36 * u - k₀) / q - (4 * u - k₀ - 1) / q) +
        ((34 * u - k₀) / q - (6 * u - k₀ - 1) / q)) := by
  unfold LineSys7.val
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [RC7.fl_disc u q k₀ hq j (by simpa [sysE7_n] using mem_range.1 hj)])]
  simp only [sysE7_n, Finset.sum_range_succ, Finset.sum_range_zero, Fin.sum_univ_six]
  simp only [RC7.gv, sysE7, LineSys7.lw, LineSys7.la, eta]
  norm_num
  ring

/-! ### The local model side: counting poles and zeros in a residue class -/

/-- `∑_{j < M} [j q ≤ s] = ⌊s/q⌋ + 1` when `-q ≤ s` and `⌊s/q⌋ < M`. -/
lemma RC7.cnt_le (q M : ℕ) (hq : 0 < q) (s : ℤ) (h1 : -(q : ℤ) ≤ s) (h2 : s / q < M) :
    ∑ j ∈ range M, (if (j : ℤ) * q ≤ s then (1 : ℤ) else 0) = s / q + 1 := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hs : -1 ≤ s / q := by
    rw [Int.le_ediv_iff_mul_le hq']
    linarith
  rw [Finset.sum_boole]
  have e : (range M).filter (fun j : ℕ => (j : ℤ) * q ≤ s) = range (s / q + 1).toNat := by
    ext j
    simp only [mem_filter, mem_range]
    rw [← Int.le_ediv_iff_mul_le hq']
    generalize s / q = d at hs h2 ⊢
    omega
  rw [e, card_range]
  generalize s / q = d at hs ⊢
  omega

lemma RC7.ediv_lt_bound (n q : ℕ) (hq : 0 < q) (k s : ℤ) (hs : s ≤ (n : ℤ) + k * q) :
    s / q < ((n / q : ℕ) : ℤ) + k + 1 := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rw [Int.ediv_lt_iff_lt_mul hq']
  have h1 : (n : ℤ) = q * ((n / q : ℕ) : ℤ) + ((n % q : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod n q).symm
  have h2 : ((n % q : ℕ) : ℤ) < q := by exact_mod_cast Nat.mod_lt n hq
  nlinarith

/-- `a_k` as a sum of the four level indicators. -/
lemma RC7.apole_ind (u k : ℕ) (hk : k ≤ 40 * u) :
    ((apole u k : ℕ) : ℤ) = 1 + (if 2 * u ≤ k ∧ k ≤ 38 * u then 1 else 0) +
      (if 4 * u ≤ k ∧ k ≤ 36 * u then 1 else 0) + (if 6 * u ≤ k ∧ k ≤ 34 * u then 1 else 0) := by
  unfold apole
  split_ifs <;> omega

lemma RC7.ind_split (A B k₀ P : ℕ) (hAB : A ≤ B + 1) :
    (if A ≤ k₀ + P ∧ k₀ + P ≤ B then (1 : ℤ) else 0) =
      (if (P : ℤ) ≤ (B : ℤ) - k₀ then 1 else 0) - (if (P : ℤ) ≤ (A : ℤ) - k₀ - 1 then 1 else 0) := by
  split_ifs <;> omega

lemma RC7.pole_term (u q k₀ j : ℕ) :
    (if k₀ + j * q ≤ 40 * u then -((apole u (k₀ + j * q) : ℕ) : ℤ) else 0) =
      -((if (j : ℤ) * q ≤ 40 * u - k₀ then 1 else 0) -
          (if (j : ℤ) * q ≤ -(k₀ : ℤ) - 1 then 1 else 0) +
        ((if (j : ℤ) * q ≤ 38 * u - k₀ then 1 else 0) -
          (if (j : ℤ) * q ≤ 2 * u - k₀ - 1 then 1 else 0)) +
        ((if (j : ℤ) * q ≤ 36 * u - k₀ then 1 else 0) -
          (if (j : ℤ) * q ≤ 4 * u - k₀ - 1 then 1 else 0)) +
        ((if (j : ℤ) * q ≤ 34 * u - k₀ then 1 else 0) -
          (if (j : ℤ) * q ≤ 6 * u - k₀ - 1 then 1 else 0))) := by
  have hP : (j : ℤ) * q = ((j * q : ℕ) : ℤ) := by push_cast; ring
  rw [hP]
  generalize j * q = P
  by_cases hk : k₀ + P ≤ 40 * u
  · rw [ite_eq_left hk, RC7.apole_ind u _ hk, RC7.ind_split (2 * u) (38 * u) k₀ P (by omega),
      RC7.ind_split (4 * u) (36 * u) k₀ P (by omega), RC7.ind_split (6 * u) (34 * u) k₀ P (by omega)]
    have e1 : (P : ℤ) ≤ 40 * u - k₀ := by omega
    have e2 : ¬ ((P : ℤ) ≤ -(k₀ : ℤ) - 1) := by omega
    simp only [e1, e2, ↓reduceIte]
    push_cast
    ring
  · rw [ite_eq_right hk]
    have e1 : ¬ ((P : ℤ) ≤ 40 * u - k₀) := by omega
    have e2 : ¬ ((P : ℤ) ≤ -(k₀ : ℤ) - 1) := by omega
    have e3 : ¬ ((P : ℤ) ≤ 38 * u - k₀) := by omega
    have e4 : ¬ ((P : ℤ) ≤ 2 * u - k₀ - 1) := by omega
    have e5 : ¬ ((P : ℤ) ≤ 36 * u - k₀) := by omega
    have e6 : ¬ ((P : ℤ) ≤ 4 * u - k₀ - 1) := by omega
    have e7 : ¬ ((P : ℤ) ≤ 34 * u - k₀) := by omega
    have e8 : ¬ ((P : ℤ) ≤ 6 * u - k₀ - 1) := by omega
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, ↓reduceIte]
    ring

lemma RC7.poles_sum (u q k₀ : ℕ) (hq : 0 < q) (hk : k₀ < q) :
    ∑ j ∈ range (40 * u / q + 1),
        (if k₀ + j * q ≤ 40 * u then -((apole u (k₀ + j * q) : ℕ) : ℤ) else 0) =
      -((40 * u - k₀) / q - (-(k₀ : ℤ) - 1) / q + ((38 * u - k₀) / q - (2 * u - k₀ - 1) / q) +
        ((36 * u - k₀) / q - (4 * u - k₀ - 1) / q) +
        ((34 * u - k₀) / q - (6 * u - k₀ - 1) / q)) := by
  rw [Finset.sum_congr rfl (fun j _ => RC7.pole_term u q k₀ j)]
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hc : ∀ s : ℤ, -(q : ℤ) ≤ s → s ≤ 40 * u →
      ∑ j ∈ range (40 * u / q + 1), (if (j : ℤ) * q ≤ s then (1 : ℤ) else 0) = s / q + 1 := by
    intro s h1 h2
    apply RC7.cnt_le q _ hq s h1
    have := RC7.ediv_lt_bound (40 * u) q hq 0 s (by push_cast; linarith)
    push_cast at this ⊢
    linarith
  rw [hc (40 * u - k₀) (by omega) (by omega), hc (-(k₀ : ℤ) - 1) (by omega) (by omega),
    hc (38 * u - k₀) (by omega) (by omega), hc (2 * u - k₀ - 1) (by omega) (by omega),
    hc (36 * u - k₀) (by omega) (by omega), hc (4 * u - k₀ - 1) (by omega) (by omega),
    hc (34 * u - k₀) (by omega) (by omega), hc (6 * u - k₀ - 1) (by omega) (by omega)]
  ring

lemma RC7.eta_le (m : Fin 6) : eta m ≤ 13 := by
  fin_cases m <;> decide

lemma RC7.mu_ind (u c : ℕ) : ((mu u c : ℕ) : ℤ) =
    ∑ m : Fin 6, (if eta m * u ≤ c ∧ c < 40 * u - eta m * u then (1 : ℤ) else 0) := by
  unfold mu
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  simp [block, Finset.mem_Ico]

lemma RC7.zero_term (u q k₀ t : ℕ) (hq : Odd q) :
    (if 0 ≤ (k₀ : ℤ) + t * q - (q + 1) / 2 ∧ (k₀ : ℤ) + t * q - (q + 1) / 2 < 40 * u ∧
        mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat ≠ 0 then
      ((mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat : ℕ) : ℤ) else 0) =
    ∑ m : Fin 6,
      ((if (t : ℤ) * q ≤ ((40 - eta m : ℕ) : ℤ) * u - k₀ + ((q : ℤ) - 1) / 2 then 1 else 0) -
        (if (t : ℤ) * q ≤ (eta m : ℤ) * u - k₀ + ((q : ℤ) - 1) / 2 then 1 else 0)) := by
  obtain ⟨s, hs⟩ := hq
  have hqz : (q : ℤ) = 2 * s + 1 := by exact_mod_cast hs
  have hh1 : ((q : ℤ) + 1) / 2 = s + 1 := by omega
  have hh2 : ((q : ℤ) - 1) / 2 = s := by omega
  rw [hh1, hh2]
  have hP : (t : ℤ) * q = ((t * q : ℕ) : ℤ) := by push_cast; ring
  rw [hP]
  generalize t * q = P
  -- each block: `[c < F] - [c < E] = [E ≤ c < F]`, `c = k₀ + P - (s + 1)`
  have key : ∀ m : Fin 6,
      ((if (P : ℤ) ≤ ((40 - eta m : ℕ) : ℤ) * u - k₀ + s then (1 : ℤ) else 0) -
        (if (P : ℤ) ≤ (eta m : ℤ) * u - k₀ + s then 1 else 0)) =
      (if (eta m : ℤ) * u ≤ (k₀ : ℤ) + P - (s + 1) ∧
          (k₀ : ℤ) + P - (s + 1) < ((40 - eta m : ℕ) : ℤ) * u then 1 else 0) := by
    intro m
    have he := RC7.eta_le m
    have hEF : ((40 - eta m : ℕ) : ℤ) * u = 40 * u - (eta m : ℤ) * u := by
      push_cast [Nat.cast_sub (by omega : eta m ≤ 40)]
      ring
    have hE0 : 0 ≤ (eta m : ℤ) * u := by positivity
    have hE1 : (eta m : ℤ) * u ≤ 20 * u := by
      have : (eta m : ℤ) ≤ 20 := by exact_mod_cast (by omega : eta m ≤ 20)
      nlinarith
    rw [hEF]
    generalize (eta m : ℤ) * u = E at hE0 hE1 ⊢
    split_ifs <;> omega
  simp only [key]
  by_cases hc : 0 ≤ (k₀ : ℤ) + P - (s + 1) ∧ (k₀ : ℤ) + P - (s + 1) < 40 * u
  · have hlhs : (if 0 ≤ (k₀ : ℤ) + P - (s + 1) ∧ (k₀ : ℤ) + P - (s + 1) < 40 * u ∧
          mu u ((k₀ : ℤ) + P - (s + 1)).toNat ≠ 0 then
        ((mu u ((k₀ : ℤ) + P - (s + 1)).toNat : ℕ) : ℤ) else 0) =
        ((mu u ((k₀ : ℤ) + P - (s + 1)).toNat : ℕ) : ℤ) := by
      split_ifs with h
      · rfl
      · push Not at h
        rw [h hc.1 hc.2]
        rfl
    rw [hlhs, RC7.mu_ind]
    apply Finset.sum_congr rfl
    intro m _
    have he := RC7.eta_le m
    have hEF : ((40 - eta m : ℕ) : ℤ) * u = 40 * u - (eta m : ℤ) * u := by
      push_cast [Nat.cast_sub (by omega : eta m ≤ 40)]
      ring
    have hct : (((k₀ : ℤ) + P - (s + 1)).toNat : ℤ) = (k₀ : ℤ) + P - (s + 1) :=
      Int.toNat_of_nonneg hc.1
    have hiff : (eta m * u ≤ ((k₀ : ℤ) + P - (s + 1)).toNat ∧
        ((k₀ : ℤ) + P - (s + 1)).toNat < 40 * u - eta m * u) ↔
        ((eta m : ℤ) * u ≤ (k₀ : ℤ) + P - (s + 1) ∧
          (k₀ : ℤ) + P - (s + 1) < ((40 - eta m : ℕ) : ℤ) * u) := by
      rw [hEF, ← hct]
      have h1 : eta m * u ≤ 40 * u := by nlinarith
      constructor
      · rintro ⟨a1, a2⟩
        refine ⟨by exact_mod_cast a1, ?_⟩
        have : ((((k₀ : ℤ) + P - (s + 1)).toNat : ℕ) : ℤ) < ((40 * u - eta m * u : ℕ) : ℤ) := by
          exact_mod_cast a2
        push_cast [Nat.cast_sub h1] at this
        linarith
      · rintro ⟨a1, a2⟩
        refine ⟨by exact_mod_cast a1, ?_⟩
        have : ((((k₀ : ℤ) + P - (s + 1)).toNat : ℕ) : ℤ) < ((40 * u - eta m * u : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub h1]
          linarith
        exact_mod_cast this
    simp only [hiff]
  · rw [ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩)]
    symm
    apply Finset.sum_eq_zero
    intro m _
    have he := RC7.eta_le m
    have hEF : ((40 - eta m : ℕ) : ℤ) * u = 40 * u - (eta m : ℤ) * u := by
      push_cast [Nat.cast_sub (by omega : eta m ≤ 40)]
      ring
    have hE0 : 0 ≤ (eta m : ℤ) * u := by positivity
    rw [ite_eq_right]
    rw [hEF]
    intro h
    exact hc ⟨by linarith, by linarith⟩

lemma RC7.zeros_sum (u q k₀ : ℕ) (hq : Odd q) (hk : k₀ < q) :
    ∑ t ∈ range (40 * u / q + 2),
      (if 0 ≤ (k₀ : ℤ) + t * q - (q + 1) / 2 ∧ (k₀ : ℤ) + t * q - (q + 1) / 2 < 40 * u ∧
          mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat ≠ 0 then
        ((mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat : ℕ) : ℤ) else 0) =
      ∑ m : Fin 6, (RC7.zc q (((40 - eta m : ℕ) : ℤ) * u - k₀) - RC7.zc q ((eta m : ℤ) * u - k₀)) := by
  have hq0 := hq.pos
  rw [Finset.sum_congr rfl (fun t _ => RC7.zero_term u q k₀ t hq), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  have he := RC7.eta_le m
  obtain ⟨s, hs⟩ := hq
  have hqz : (q : ℤ) = 2 * s + 1 := by exact_mod_cast hs
  have hh2 : ((q : ℤ) - 1) / 2 = s := by omega
  have hEF : ((40 - eta m : ℕ) : ℤ) * u = 40 * u - (eta m : ℤ) * u := by
    push_cast [Nat.cast_sub (by omega : eta m ≤ 40)]
    ring
  have hE0 : 0 ≤ (eta m : ℤ) * u := by positivity
  have hE1 : (eta m : ℤ) * u ≤ 20 * u := by
    have : (eta m : ℤ) ≤ 20 := by exact_mod_cast (by omega : eta m ≤ 20)
    nlinarith
  have hc : ∀ s' : ℤ, -(q : ℤ) ≤ s' → s' ≤ 40 * u + q →
      ∑ t ∈ range (40 * u / q + 2), (if (t : ℤ) * q ≤ s' then (1 : ℤ) else 0) = s' / q + 1 := by
    intro s' h1 h2
    apply RC7.cnt_le q _ hq0 s' h1
    have := RC7.ediv_lt_bound (40 * u) q hq0 1 s' (by push_cast; linarith)
    push_cast at this ⊢
    linarith
  rw [Finset.sum_sub_distrib, hh2, hc _ (by rw [hEF]; omega) (by rw [hEF]; omega),
    hc _ (by omega) (by omega)]
  unfold RC7.zc
  rw [hh2]
  ring

lemma RC7.sum_snd_filterMap {α β : Type*} (L : List α) (f : α → Option (β × ℤ)) :
    ((L.filterMap f).map Prod.snd).sum = (L.map fun a => ((f a).map Prod.snd).getD 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.filterMap_cons]
    cases h : f a with
    | none => simp [ih, h]
    | some p => simp [ih, h]

lemma RC7.sum_map_coe_range (n : ℕ) (F : ℤ → ℤ) :
    (((List.range n : List ℕ) : List ℤ).map F).sum = ∑ t ∈ range n, F t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [List.range_succ]

lemma RC7.getD_map_ite {β : Type*} (p : Prop) [Decidable p] (v : β × ℤ) :
    ((if p then some v else none).map Prod.snd).getD 0 = if p then v.2 else 0 := by
  split_ifs <;> rfl

/-- **The floor-sum form of `E`** (proof Lemma 4.12): for odd `q` and `k₀ < q`,
`E_ξ = sysE7.val (40u/q) (k₀/q) + [q ∣ 2k₀ - 40u]` (the last term is the `δ`-zero). -/
theorem localModel_E_eq_sysE7 (u q k₀ : ℕ) (hq : Odd q) (hk : k₀ < q) :
    (localModel u q k₀).E = sysE7.val (((40 * u : ℕ) : ℚ) / q) ((k₀ : ℚ) / q) +
      (if (2 * (k₀ : ℤ) - 40 * u) % q = 0 then 1 else 0) := by
  have hq0 := hq.pos
  have hL : (localModel u q k₀).E =
      ∑ j ∈ range (40 * u / q + 1),
        (if k₀ + j * q ≤ 40 * u then -((apole u (k₀ + j * q) : ℕ) : ℤ) else 0) +
      ∑ t ∈ range (40 * u / q + 2),
        (if 0 ≤ (k₀ : ℤ) + t * q - (q + 1) / 2 ∧ (k₀ : ℤ) + t * q - (q + 1) / 2 < 40 * u ∧
            mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat ≠ 0 then
          ((mu u ((k₀ : ℤ) + t * q - (q + 1) / 2).toNat : ℕ) : ℤ) else 0) +
      (if (2 * (k₀ : ℤ) - 40 * u) % q = 0 then 1 else 0) := by
    unfold LocalType.E localModel
    simp only [List.map_append, List.sum_append, RC7.sum_snd_filterMap, RC7.getD_map_ite,
      RC7.sum_map_coe_range]
    rw [← ECert7.sum_range_eq_list]
    congr 1
    split_ifs <;> simp
  rw [hL, RC7.poles_sum u q k₀ hq0 hk, RC7.zeros_sum u q k₀ hq hk, RC7.val_disc u q k₀ hq]
  ring

/-- `E_ξ ≥ sysE7.val (40u/q) (k₀/q)` (the `δ`-zero only raises `E`). -/
theorem localModel_E_ge_sysE7 (u q k₀ : ℕ) (hq : Odd q) (hk : k₀ < q) :
    sysE7.val (((40 * u : ℕ) : ℚ) / q) ((k₀ : ℚ) / q) ≤ (localModel u q k₀).E := by
  rw [localModel_E_eq_sysE7 u q k₀ hq hk]
  split_ifs <;> omega

/-! ## Realizability of the discrete points -/

/-- A discrete point `(40u/q, k₀/q)` with `q > 40` prime and `q ∤ u` is realizable: a numerator
line is never integral (`q` odd), and a pole-level upper line (`A/2 ∈ {40, 38, 36, 34}`) and a
pole-level lower line (`A'/2 ∈ {0, 2, 4, 6}`) are integral together only if
`q ∣ (A/2 - A'/2) u` with `28 ≤ A/2 - A'/2 ≤ 40 < q`, i.e. `q ∣ u`. -/
theorem sysE7_real_disc (u q k₀ : ℕ) (hq : q.Prime) (h40 : 40 < q) (hqu : ¬ q ∣ u) :
    sysE7.Real (((40 * u : ℕ) : ℚ) / q) ((k₀ : ℚ) / q) := by
  have hq0 : 0 < q := hq.pos
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  have hqQ : (q : ℚ) ≠ 0 := by positivity
  intro i hi j hj hci hcj z z' h1 h2
  rw [sysE7_n] at hi hj
  unfold LineSys7.ell at h1 h2
  rw [RC7.ell_disc _ _ _ (RC7.la_even i hi) u q k₀ hq0] at h1
  rw [RC7.ell_disc _ _ _ (RC7.la_even j hj) u q k₀ hq0] at h2
  have hj16 : 16 ≤ j := by
    by_contra hlt
    push Not at hlt
    revert hcj
    interval_cases j <;> decide
  have hbj : sysE7.lb j = 0 := by interval_cases j <;> rfl
  have hAj : 0 ≤ sysE7.la j / 2 ∧ sysE7.la j / 2 ≤ 6 := by interval_cases j <;> decide
  rw [hbj] at h2
  have h2a : ((sysE7.la j / 2 * u - k₀ : ℤ) : ℚ) / q = z' := by simpa using h2
  have h2b : ((sysE7.la j / 2 * u - k₀ : ℤ) : ℚ) = (q : ℚ) * (z' : ℚ) := by
    rw [← h2a]
    field_simp
  have h2' : sysE7.la j / 2 * u - k₀ = q * z' := by exact_mod_cast h2b
  by_cases hi12 : i < 12
  · have hbi : sysE7.lb i = -40 := by interval_cases i <;> rfl
    rw [hbi] at h1
    have h1a : ((sysE7.la i / 2 * u - k₀ : ℤ) : ℚ) / q - 1 / 2 = z := by
      rw [← h1]
      push_cast
      ring
    have h1b : ((2 * (sysE7.la i / 2 * u - k₀) - q : ℤ) : ℚ) = ((2 * (q * z) : ℤ) : ℚ) := by
      have e : ((2 * (sysE7.la i / 2 * u - k₀) - q : ℤ) : ℚ) =
          2 * q * (((sysE7.la i / 2 * u - k₀ : ℤ) : ℚ) / q - 1 / 2) := by
        push_cast
        field_simp
      rw [e, h1a]
      push_cast
      ring
    have h1' : 2 * (sysE7.la i / 2 * u - k₀) - q = 2 * (q * z) := by exact_mod_cast h1b
    obtain ⟨s, hs⟩ := hodd
    have hqz : (q : ℤ) = 2 * s + 1 := by exact_mod_cast hs
    generalize sysE7.la i / 2 * (u : ℤ) = X at h1'
    generalize (q : ℤ) * z = w at h1'
    omega
  · have hi16 : i < 16 := by
      by_contra hge
      push Not at hge
      revert hci
      interval_cases i <;> decide
    have hi12' : 12 ≤ i := by omega
    have hbi : sysE7.lb i = 0 := by interval_cases i <;> rfl
    have hAi : 34 ≤ sysE7.la i / 2 ∧ sysE7.la i / 2 ≤ 40 := by interval_cases i <;> decide
    rw [hbi] at h1
    have h1a : ((sysE7.la i / 2 * u - k₀ : ℤ) : ℚ) / q = z := by simpa using h1
    have h1b : ((sysE7.la i / 2 * u - k₀ : ℤ) : ℚ) = (q : ℚ) * (z : ℚ) := by
      rw [← h1a]
      field_simp
    have h1' : sysE7.la i / 2 * u - k₀ = q * z := by exact_mod_cast h1b
    have hd : (sysE7.la i / 2 - sysE7.la j / 2) * (u : ℤ) = q * (z - z') := by
      linear_combination h1' - h2'
    have hdvd : (q : ℤ) ∣ (sysE7.la i / 2 - sysE7.la j / 2) * u := ⟨z - z', hd⟩
    have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    rcases hprime.dvd_or_dvd hdvd with h | h
    · have := Int.le_of_dvd (by omega) h
      omega
    · exact hqu (Int.natCast_dvd_natCast.mp h)

/-! ## `E` lower bounds from certificates -/

/-- **`E` lower bound from a sweep certificate** (used by `ResCert7`, reusable by `HeadCert7`
with `t = 0`): if `c` is a valid certificate of `sysE7` on `[a, b)`, then for every prime `q > 40`
with `q ∤ u` and `40u/q ∈ [a + 40t, b + 40t)`, every class `k₀ < q` has `E_ξ ≥ sig`. -/
theorem ECert7.E_ge (c : ECert7) (hc : c.ok sysE7 = true) (t : ℤ) (u q : ℕ) (hq : q.Prime)
    (h40 : 40 < q) (hqu : ¬ q ∣ u)
    (hxa : (c.pa : ℚ) / c.qa + 40 * t ≤ ((40 * u : ℕ) : ℚ) / q)
    (hxb : ((40 * u : ℕ) : ℚ) / q < (c.pb : ℚ) / c.qb + 40 * t) (k₀ : ℕ) (hk : k₀ < q) :
    c.sig ≤ (localModel u q k₀).E := by
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hR := sysE7_real_disc u q k₀ hq h40 hqu
  have hR' := sysE7_Real_add_40 hR (-t)
  have hy0 : (0 : ℚ) ≤ (k₀ : ℚ) / q := by positivity
  have hy1 : (k₀ : ℚ) / q < 1 := by
    rw [div_lt_one hq0]
    exact_mod_cast hk
  have hs := c.ok_sound sysE7 hc _ _ (by rw [Int.cast_neg]; linarith)
    (by rw [Int.cast_neg]; linarith) hy0 hy1 hR'
  rw [sysE7_val_add_40] at hs
  exact hs.trans (localModel_E_ge_sysE7 u q k₀ hodd hk)

/-! ## Vacuous certificate conditions (for `HeadCert7`) -/

/-- `LevGe τ c0 j c P` is vacuous when `P ≤ E + 1` (no index `E + 1 ≤ p < P`); e.g. `E ≥ 4 - f`
gives `LevGe … (5 - f)`. -/
theorem RC7.LevGe_of_E (τ : LocalType) (c0 : ℚ) (j : ℕ) (c : ℚ) (P : ℤ) (h : P ≤ τ.E + 1) :
    LevGe τ c0 j c P := by
  intro p hp1 hp2
  exfalso
  omega

/-- `PoleLevGe τ T` is vacuous when `T ≤ E + 1` (no index `E - netE - T < l ≤ -netE - 1`); e.g.
`E ≥ -f - 1` gives `PoleLevGe … (-f)`. -/
theorem RC7.PoleLevGe_of_E (τ : LocalType) (T : ℤ) (h : T ≤ τ.E + 1) : PoleLevGe τ T := by
  intro p _ l hl1 hl2
  exfalso
  omega

end Zeta2.Z7
