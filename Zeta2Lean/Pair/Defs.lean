module

public import Zeta2Lean.Defs

@[expose] public section

/-!
# Zeta2Lean.Pair.Defs — definitions for the pair `{ζ₂(7), ζ₂(9)}`

*In this repository.* This file is the pair repository's (https://github.com/gmDevi/zeta2-7-9-lean),
unchanged apart from this paragraph and the module-system header.
It is imported by `Zeta2Lean/Pair/Statements.lean`, which the pair proof files reused by the
`ζ₂(7)` proof import; the `ζ₂(7)` proof uses none of its definitions.
Its references to documents, scripts and pair files that are not included here (such as
`BLUEPRINT_PAIR.md`, `docs/proof.md`, `python/pair_mirror.py` or `Pair/Main.lean`) are to
that repository.

Target: **at least one of `ζ₂(7)`, `ζ₂(9)` is irrational** (map of statements: `BLUEPRINT_PAIR.md`).
This file only adds the *pair-specific* objects.  The Volkenborn infrastructure (`volkenbornSum`,
`HasVolkenborn`, `volkenborn`, `halfPow`, `J`, `zeta2`, `Ahalf`, `dn`, the `HasVolkenborn` API) is
reused from `Zeta2Lean/Defs.lean` (namespace `Zeta2`).  Everything here lives in the namespace
`Zeta2.Pair`; inside it, short names such as `rcoef`, `rho0`, `Z7` refer to the pair versions
(Lean resolves the innermost namespace first), outside write `Pair.rcoef` etc.

## The family (shifted well-poised / Rhin–Viola-type deformation of the LSZ half-shift family)

For `n : ℕ` and a shift vector `h : Fin 6 → ℤ`,
```
R_n(t) = (2t + n) · ∏_{m<6} (t + 1/2 - h_m)_{n + 2 h_m} / (t)_{n+1}^6 ,
(t + 1/2 - h)_{n+2h} = ∏_{u ∈ [-h, n+h)} (t + 1/2 + u)          (offsets n h),
```
with `h` **admissible** (`Admissible n h`): `∑ h_m = 0`, every length `n + 2h_m ≥ 0`, and at least
`j + 2 = 5` of the `h_m` are `≥ 0` (the critical-zero condition used by the denominator argument).
Then `deg R_n = 1 + 6n - 6(n+1) = -5`, the poles are `t = 0, -1, …, -n` (order `≤ 6`) and
`R_n(-t-n) = -R_n(t)`.  **No power of 2 is built in** (unlike the `{7,9,11}` project, which uses
`2^{16n}`): all numerical data of the exploration are in this unnormalised form.  Powers of 2 are
neutral for the criterion (`|a|_∞ · |L|_2` is invariant); the assembly therefore bounds the *odd
part* `D · ‖D‖₂` of the common denominator.

Partial fractions: `R_n(t) = ∑_{i=1}^{6} ∑_{k=0}^{n} r_{i,k} (t+k)^{-i}` with the explicit Taylor
formula `r_{6-μ,k} = [ε^μ] G_k(ε)`, `G_k(ε) = ε^6 R_n(-k+ε)`:
```
G_k(ε) = (n - 2k + 2ε) · ∏_m ∏_{u ∈ [-h_m, n+h_m)} (u - k + 1/2 + ε)
                       · ∏_{j ≤ n, j ≠ k} (j - k + ε)^{-6}
```
computed in `PowerSeries ℚ` (the inverted product has non-zero constant term, so `⁻¹` is the honest
inverse).  `Stmt_PF` links these coefficients with the product form of `R_n`.

The linear form: `S_n = -∫_{ℤ₂} R_n'''(t + 1/2) dt = ∫ integrand`, with
`integrand n h x = ∑_{i,k} (i)₃ r_{i,k} (x + k + 1/2)^{-i-3}`, and (`Stmt_L1`)
```
S_n = ρ₀ + 60 c₃ J₆ + 210 c₅ J₈ = ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9),
Z₇ = (3)₄ 2^7 c₃ = 46080 c₃,  Z₉ = (5)₄ 2^9 c₅ = 860160 c₅,
```
(`c₁ = 0` by degree, `c₂ = c₄ = c₆ = 0` by the parity lemma).  The exploration's `lfam.py` uses
`S = +∫ R''' (t+1/2) dt`, so its `(rho0, C[6], C[8])` are `-(ρ₀, Z₇, Z₉)` here.

The linear-form machinery is stated **generically** (`genIntegrand`, `genRho0`, `genCsum` for an
arbitrary coefficient array `r : ℕ → ℕ → ℚ` and pole order `a`), so that its proof
(`Stmt_GenLinearForm`) is independent of the family and could be reused for other
configurations/families.

## Configurations

A `Config` is a sequence of degrees `cfg.n m → ∞` with admissible shift vectors `cfg.h m`.
Configuration **E** (the numerically best pair configuration): `h/n = (-0.425, 0.025, 0.05, 0.075,
0.125, 0.15)`, i.e. `n = 40 m`, `h = m · (-17, 1, 2, 3, 5, 6)` (`configE`).

## Target constants

`gE = -0.72` (coefficient growth, measured `≈ -0.79`) and `deltaE = 9` (log of the odd part of the
provable common denominator per `n`, estimated `10 - R_∞ ≈ 8.91`); `gE + deltaE = 8.28 < 12 log 2 =
8.3178` (`marginE`, in `Pair/Assembly.lean`).  The main theorem is also available for arbitrary
`(g, δ)` with `g + δ < 12 log 2` (`Pair/Main.lean`).
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

/-! ## Shift vectors -/

/-- Admissible shift vector `h` for degree `n`: `∑_m h_m = 0`, all lengths `n + 2 h_m ≥ 0`, and at
least five of the six shifts are `≥ 0` (critical-zero condition: every factor with `h_m ≥ 0` has
offsets `[-h_m, n + h_m) ⊇ [0, n)`, so `R_n` vanishes to order `≥ 5 = j + 2` at every critical
point `-1/2 - c`, `0 ≤ c < n`). -/
def Admissible (n : ℕ) (h : Fin 6 → ℤ) : Prop :=
  ∑ m, h m = 0 ∧ (∀ m, 0 ≤ (n : ℤ) + 2 * h m) ∧ 5 ≤ (univ.filter fun m => 0 ≤ h m).card

/-- The offsets `u ∈ [-h, n+h)` of the numerator factor
`(t + 1/2 - h)_{n+2h} = ∏_{u ∈ [-h, n+h)} (t + 1/2 + u)`. -/
def offsets (n : ℕ) (h : ℤ) : Finset ℤ :=
  Ico (-h) ((n : ℤ) + h)

/-- Taylor expansion `ε ↦ ∏_m (y + ε + 1/2 - h_m)_{n + 2h_m}` of the numerator at `t = y`. -/
def numSer (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ) : PowerSeries ℚ :=
  ∏ m : Fin 6, ∏ u ∈ offsets n (h m), (C (y + 1 / 2 + (u : ℚ)) + X)

/-- `G_k(ε) = ε^6 R_n(-k+ε) = (n - 2k + 2ε) · numSer n h (-k) · ∏_{j ≤ n, j ≠ k} (j - k + ε)^{-6}`.
-/
def Gser (n : ℕ) (h : Fin 6 → ℤ) (k : ℕ) : PowerSeries ℚ :=
  (C ((n : ℚ) - 2 * k) + C 2 * X) * numSer n h (-(k : ℚ)) *
    (∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹

/-- Partial-fraction coefficient `r_{i,k}` of `R_n` (`1 ≤ i ≤ 6`, `0 ≤ k ≤ n`), `0` otherwise:
`r_{6-μ,k} = [ε^μ] G_k(ε)`. -/
def rcoef (n : ℕ) (h : Fin 6 → ℤ) (i k : ℕ) : ℚ :=
  if 1 ≤ i ∧ i ≤ 6 ∧ k ≤ n then coeff (6 - i) (Gser n h k) else 0

/-! ## Generic linear forms (any coefficient array `r`, any pole order `a`) -/

/-- `∑_{i=1}^{a} ∑_{k=0}^{n} (i)₃ r_{i,k} (x + k + 1/2)^{-(i+3)}`: for `r` the partial-fraction
coefficients of a rational function `R = ∑ r_{i,k} (t+k)^{-i}` this is `-R'''(x + 1/2)`. -/
def genIntegrand (a n : ℕ) (r : ℕ → ℕ → ℚ) (x : ℕ) : ℚ :=
  ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
    ((i : ℚ) * (i + 1) * (i + 2)) * r i k * ((((x + k : ℕ) : ℚ) + 1 / 2)⁻¹) ^ (i + 3)

/-- `c_i = ∑_{k=0}^{n} r_{i,k}`. -/
def genCsum (n : ℕ) (r : ℕ → ℕ → ℚ) (i : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), r i k

/-- `ρ₀ = -∑_{i=1}^{a} ∑_{k=0}^{n} (i)₄ r_{i,k} A_k^{(i+4)}`, `A_k^{(s)} = ∑_{ℓ<k} (ℓ+1/2)^{-s}`
(`Zeta2.Ahalf`). -/
def genRho0 (a n : ℕ) (r : ℕ → ℕ → ℚ) : ℚ :=
  -∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
      ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * r i k * Ahalf k (i + 4)

/-! ## The linear form of the pair family -/

/-- `c_i = ∑_k r_{i,k}` for the pair family. -/
def csum (n : ℕ) (h : Fin 6 → ℤ) (i : ℕ) : ℚ :=
  genCsum n (rcoef n h) i

/-- The rational part `ρ₀` of `S_n`. -/
def rho0 (n : ℕ) (h : Fin 6 → ℤ) : ℚ :=
  genRho0 6 n (rcoef n h)

/-- `Z₇ = (3)₄ 2^7 c₃ = 46080 c₃`, the coefficient of `ζ₂(7)`. -/
def Z7 (n : ℕ) (h : Fin 6 → ℤ) : ℚ :=
  46080 * csum n h 3

/-- `Z₉ = (5)₄ 2^9 c₅ = 860160 c₅`, the coefficient of `ζ₂(9)`. -/
def Z9 (n : ℕ) (h : Fin 6 → ℤ) : ℚ :=
  860160 * csum n h 5

/-- The integrand `-R_n'''(x + 1/2) = ∑_{i,k} (i)₃ r_{i,k} (x + k + 1/2)^{-i-3}`
(values at `x ∈ ℕ`). -/
def integrand (n : ℕ) (h : Fin 6 → ℤ) (x : ℕ) : ℚ :=
  genIntegrand 6 n (rcoef n h) x

/-- `S_n = -∫_{ℤ₂} R_n'''(t + 1/2) dt` (only a name; statements use `HasVolkenborn`
certificates). -/
def Sn (n : ℕ) (h : Fin 6 → ℤ) : ℚ_[2] :=
  volkenborn (fun x => ((integrand n h x : ℚ) : ℚ_[2]))

/-- The linear form `ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9)` (the value of `S_n`, by `Stmt_L1`). -/
def Lform (n : ℕ) (h : Fin 6 → ℤ) : ℚ_[2] :=
  (rho0 n h : ℚ_[2]) + (Z7 n h : ℚ_[2]) * zeta2 7 + (Z9 n h : ℚ_[2]) * zeta2 9

/-! ## Product form of `R_n` (for `Stmt_PF`) -/

/-- Numerator `(2t + n) ∏_m (t + 1/2 - h_m)_{n+2h_m}` of `R_n` as a polynomial in `t`. -/
def Rnum (n : ℕ) (h : Fin 6 → ℤ) : Polynomial ℚ :=
  (Polynomial.C 2 * Polynomial.X + Polynomial.C (n : ℚ)) *
    ∏ m : Fin 6, ∏ u ∈ offsets n (h m), (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))

/-- `(t)_{n+1}^6 · ∑_{i,k} r_{i,k} (t+k)^{-i}` as a polynomial in `t`. -/
def PFpoly (n : ℕ) (h : Fin 6 → ℤ) : Polynomial ℚ :=
  ∑ i ∈ Icc (1 : ℕ) 6, ∑ k ∈ range (n + 1),
    Polynomial.C (rcoef n h i k) * (Polynomial.X + Polynomial.C (k : ℚ)) ^ (6 - i) *
      ∏ j ∈ (range (n + 1)).erase k, (Polynomial.X + Polynomial.C (j : ℚ)) ^ 6

/-- The Taylor expansion `ε ↦ R_n(y + ε)` (meaningful when `y ∉ {0, -1, …, -n}`). -/
def Rser (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ) : PowerSeries ℚ :=
  (C (2 * y + n) + C 2 * X) * numSer n h y * ((∏ j ∈ range (n + 1), (C (y + j) + X)) ^ 6)⁻¹

/-! ## Denominators -/

/-- `d` is a positive integer clearing the denominators of `ρ₀`, `Z₇`, `Z₉`. -/
def ClearsDen (d n : ℕ) (h : Fin 6 → ℤ) : Prop :=
  0 < d ∧ (∃ z : ℤ, (d : ℚ) * rho0 n h = z) ∧ (∃ z : ℤ, (d : ℚ) * Z7 n h = z) ∧
    ∃ z : ℤ, (d : ℚ) * Z9 n h = z

/-- The crude (certainly valid, useless for the margin) common denominator
`2^{6n} · n!^6 · d_{2n}^{10}` (`Stmt_CrudeInt`). -/
def Dcrude (n : ℕ) : ℕ :=
  2 ^ (6 * n) * n.factorial ^ 6 * dn (2 * n) ^ 10

/-! ## Configurations -/

/-- A configuration: degrees `n m → ∞` with admissible shift vectors `h m`
(`m` = sequence index). -/
structure Config where
  /-- the degree at step `m` -/
  n : ℕ → ℕ
  /-- the shift vector at step `m` -/
  h : ℕ → Fin 6 → ℤ
  adm : ∀ m, Admissible (n m) (h m)
  tendsto : Tendsto n atTop atTop

/-- Shift pattern of configuration E in units of `n/40`: `(-17, 1, 2, 3, 5, 6)`. -/
def hE : Fin 6 → ℤ :=
  ![-17, 1, 2, 3, 5, 6]

theorem admissible_E (m : ℕ) : Admissible (40 * m) (fun i => (m : ℤ) * hE i) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hE]
    simp
    ring
  · intro i
    fin_cases i <;> simp [hE] <;> omega
  · have hsub : ({1, 2, 3, 4, 5} : Finset (Fin 6)) ⊆ univ.filter (fun i => 0 ≤ (m : ℤ) * hE i) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [hE]
    exact le_trans (by decide) (Finset.card_le_card hsub)

/-- **Configuration E**: `n = 40 m`, `h = m · (-17, 1, 2, 3, 5, 6)`, i.e.
`h/n = (-0.425, 0.025, 0.05, 0.075, 0.125, 0.15)`. -/
def configE : Config where
  n m := 40 * m
  h m i := (m : ℤ) * hE i
  adm := admissible_E
  tendsto := Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩

/-- Target coefficient growth rate for configuration E (measured: `≈ -0.79`). -/
def gE : ℝ :=
  -18 / 25

/-- Target denominator rate (log of the odd part of `D_n`, per `n`) for configuration E
(residue-level estimate: `10 - R_∞ ≈ 8.91`). -/
def deltaE : ℝ :=
  9

/-! ## Basic API -/

theorem Dcrude_pos (n : ℕ) : 0 < Dcrude n := by
  unfold Dcrude
  have := Nat.lcmUpto_pos (2 * n)
  have := Nat.factorial_pos n
  unfold dn
  positivity

theorem Admissible.sum_eq {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h) : ∑ m, h m = 0 :=
  hh.1

theorem Admissible.len_nonneg {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h) (m : Fin 6) :
    0 ≤ (n : ℤ) + 2 * h m :=
  hh.2.1 m

theorem configE_n (m : ℕ) : configE.n m = 40 * m :=
  rfl

theorem configE_h (m : ℕ) (i : Fin 6) : configE.h m i = (m : ℤ) * hE i :=
  rfl

end Zeta2.Pair

end
