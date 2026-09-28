module

public import Mathlib

@[expose] public section

/-!
# Zeta2Lean.Defs — the Volkenborn integral, the 2-adic zeta values and the Δ-calculus

The shared definitions of the development, as in the pair repository
(https://github.com/gmDevi/zeta2-7-9-lean, file of the same name), which took them from the
`{7,9,11}` repository (https://github.com/gmDevi/zeta2-7-9-11-lean) without the definitions of
that project's construction.  The `ζ₂(7)` construction is in `Zeta2Lean/Z7/Defs.lean`.
"proof.md" is the informal proof `docs/proof.md` (the tools (P1)–(P3) of its §1).

* The first six definitions, `volkenbornSum`, `HasVolkenborn`, `volkenborn`, `halfPow`, `J` and
  `zeta2`, are the **trusted definitions**: they are the only project definitions in the statement
  of the main theorem, and `Challenge.lean` contains verbatim copies of them.  They are identical
  to those of the `{7,9,11}` and pair repositories.
* `Ahalf` and `dn` are used by the pair's linear form and denominators (`Zeta2Lean/Pair/`), not
  by the `ζ₂(7)` proof.
* `DeltaGe`, `DeltaAll`, `IntValued` and `hcoef` are the objects of the 2-adic Δ-calculus
  (`Stmt_Delta`, `Stmt_DeltaFun` in `Zeta2Lean/Statements.lean`).
* The file ends with the basic API of the Volkenborn Riemann sums.

Conventions.
* `ℚ_[2]` is Mathlib's field of 2-adic numbers; `‖·‖` its norm (`‖2‖ = 1/2`).
* The Volkenborn integral (proof.md P1) is *not* in Mathlib.  We use Riemann sums
  `volkenbornSum f N = 2^{-N} ∑_{x<2^N} f x` and the predicate `HasVolkenborn f I`
  (`volkenbornSum f N → I`).  `volkenborn f = limUnder …` is only a name for the limit; every
  statement that uses a value comes with a `HasVolkenborn` certificate.
* `J s = ∫_{ℤ₂} (t+1/2)^{-s} dt` and `zeta2 s = J (s-1) / ((s-1) 2^s)`.  The identification of
  `zeta2 s` with the Kubota–Leopoldt value `L₂(s, ω^{1-s})` is LSZ Lemma 2.8 (cited, not
  formalised).  Irrationality is invariant under the non-zero rational factor `(s-1) 2^s`, so a
  theorem about `J 6` *is* a theorem about `ζ₂(7)`.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ## Volkenborn integral via Riemann sums (proof.md P1, P2) -/

/-- Riemann sum `2^{-N} ∑_{x < 2^N} f x` of the Volkenborn integral. -/
def volkenbornSum (f : ℕ → ℚ_[2]) (N : ℕ) : ℚ_[2] :=
  ((2 : ℚ_[2]) ^ N)⁻¹ * ∑ x ∈ range (2 ^ N), f x

/-- `f` is Volkenborn integrable with integral `I`: the Riemann sums converge 2-adically to `I`. -/
def HasVolkenborn (f : ℕ → ℚ_[2]) (I : ℚ_[2]) : Prop :=
  Tendsto (volkenbornSum f) atTop (𝓝 I)

/-- The Volkenborn integral.  Only ever used together with a `HasVolkenborn` certificate
(`Stmt_JConv` proves convergence for every `J s`). -/
def volkenborn (f : ℕ → ℚ_[2]) : ℚ_[2] :=
  limUnder atTop (volkenbornSum f)

/-- `halfPow s x = (x + 1/2)^{-s}`, an element of `ℚ_[2]` (a 2-adic integer times `2^s`). -/
def halfPow (s x : ℕ) : ℚ_[2] :=
  ((x : ℚ_[2]) + 2⁻¹)⁻¹ ^ s

/-- `J s = ∫_{ℤ₂} (t + 1/2)^{-s} dt` (proof.md P2). -/
def J (s : ℕ) : ℚ_[2] :=
  volkenborn (halfPow s)

/-- The 2-adic zeta value, normalised by LSZ Lemma 2.8: `J_{s-1} = (s-1) 2^s ζ₂(s)` (`s ≥ 2`).
E.g. `zeta2 7 = J 6 / 768`, `zeta2 9 = J 8 / 4096`, `zeta2 11 = J 10 / 20480`. -/
def zeta2 (s : ℕ) : ℚ_[2] :=
  J (s - 1) / (((s : ℚ_[2]) - 1) * 2 ^ s)

/-! ## Finite sums and `lcm(1, …, n)` -/

/-- `A_k^{(s)} = ∑_{ℓ=0}^{k-1} (ℓ + 1/2)^{-s} = ∑_{ℓ=1}^{k} (ℓ - 1/2)^{-s}`. -/
def Ahalf (k s : ℕ) : ℚ :=
  ∑ l ∈ range k, (((l : ℚ) + 1 / 2)⁻¹) ^ s

/-- `d_n = lcm(1, …, n)` (Mathlib's `Nat.lcmUpto`). -/
def dn (n : ℕ) : ℕ := Nat.lcmUpto n

/-! ## 2-adic Δ-calculus (proof.md P3; Lai Def. 2.3) -/

/-- Lai's `Δ_m(f) ≥ c`: for every `k ≥ 2^m`, `v₂(f(k) - f(k₋)) ≥ c + v₂(k - k₋)`, where
`k₋ = k - 2^{⌊log₂ k⌋}` is `k` with its leading binary digit removed (so `k - k₋ = 2^{⌊log₂ k⌋}`). -/
def DeltaGe (m : ℕ) (c : ℤ) (f : ℕ → ℚ_[2]) : Prop :=
  ∀ k : ℕ, 2 ^ m ≤ k →
    ‖f k - f (k - 2 ^ Nat.log 2 k)‖ ≤ (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ)))

/-- Lai's `Δ(f) ≥ c`: `Δ₀(f) ≥ c` and `v₂(f 0) ≥ c - 1`. -/
def DeltaAll (c : ℤ) (f : ℕ → ℚ_[2]) : Prop :=
  DeltaGe 0 c f ∧ ‖f 0‖ ≤ (2 : ℝ) ^ (1 - c)

/-- `f` takes values in `ℤ₂`. -/
def IntValued (f : ℕ → ℚ_[2]) : Prop :=
  ∀ k, ‖f k‖ ≤ 1

/-- `h_β(x) = [δ^β] ∏_{k=0}^{n} (2x+2k+1+δ)^{-8}`, i.e. `h^{(β)}(x) / (β! 2^β)` for
`h(t) = ∏_{k=0}^{n} (2t+2k+1)^{-8}`.  (A function of the `{7,9,11}` construction.  It occurs here
only in the fields `hcoefInt`, `hcoefDelta` of the shared statement `Stmt_DeltaFun`, which the
`ζ₂(7)` proof does not use.) -/
def hcoef (n β x : ℕ) : ℚ :=
  coeff β (∏ k ∈ range (n + 1), ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8)⁻¹)

/-! ## Basic API (proved here, available to every proof file) -/

theorem volkenbornSum_add (f g : ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => f x + g x) N = volkenbornSum f N + volkenbornSum g N := by
  unfold volkenbornSum
  rw [Finset.sum_add_distrib, mul_add]

theorem volkenbornSum_const_mul (a : ℚ_[2]) (f : ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => a * f x) N = a * volkenbornSum f N := by
  unfold volkenbornSum
  rw [← Finset.mul_sum]
  ring

theorem volkenbornSum_sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => ∑ i ∈ s, F i x) N = ∑ i ∈ s, volkenbornSum (F i) N := by
  unfold volkenbornSum
  rw [Finset.sum_comm, Finset.mul_sum]

theorem HasVolkenborn.add {f g : ℕ → ℚ_[2]} {I I' : ℚ_[2]} (hf : HasVolkenborn f I)
    (hg : HasVolkenborn g I') : HasVolkenborn (fun x => f x + g x) (I + I') := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => f x + g x) = fun N => volkenbornSum f N + volkenbornSum g N
    from funext (volkenbornSum_add f g)]
  exact hf.add hg

theorem HasVolkenborn.const_mul {f : ℕ → ℚ_[2]} {I : ℚ_[2]} (a : ℚ_[2]) (hf : HasVolkenborn f I) :
    HasVolkenborn (fun x => a * f x) (a * I) := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => a * f x) = fun N => a * volkenbornSum f N
    from funext (volkenbornSum_const_mul a f)]
  exact hf.const_mul a

theorem HasVolkenborn.sum {ι : Type*} (s : Finset ι) {F : ι → ℕ → ℚ_[2]} {I : ι → ℚ_[2]}
    (h : ∀ i ∈ s, HasVolkenborn (F i) (I i)) :
    HasVolkenborn (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, I i) := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => ∑ i ∈ s, F i x) = fun N => ∑ i ∈ s, volkenbornSum (F i) N
    from funext (volkenbornSum_sum s F)]
  exact tendsto_finsetSum s h

theorem HasVolkenborn.unique {f : ℕ → ℚ_[2]} {I I' : ℚ_[2]} (h : HasVolkenborn f I)
    (h' : HasVolkenborn f I') : I = I' :=
  tendsto_nhds_unique h h'

theorem HasVolkenborn.volkenborn_eq {f : ℕ → ℚ_[2]} {I : ℚ_[2]} (h : HasVolkenborn f I) :
    volkenborn f = I :=
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨I, h⟩) h

/-- The rational `(x + 1/2)^{-s}` maps to `halfPow s x`. -/
theorem halfPow_eq_cast (s x : ℕ) :
    halfPow s x = (((((x : ℚ) + 1 / 2)⁻¹) ^ s : ℚ) : ℚ_[2]) := by
  simp [halfPow, one_div]

end Zeta2

end
