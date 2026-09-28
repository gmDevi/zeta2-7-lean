module

public import Zeta2Lean.Z7.Statements
public import Zeta2Lean.Z7.Proofs.ResCert7Data

@[expose] public section

/-!
# Residue-level certificates on one period `[20, 60)` and 40-periodicity (proof Lemma 4.12)

gap: 'denominators' (computer-assisted, pair-style).  Difficulty 4.  No dependencies.

**Status: proved** (complete; the certificates are checked by the kernel, `decide +kernel`).

**Statement.** `Stmt_ResCert7`: for each of the 980 rows `[a, b) × f` of `resRows7` and each
`t ∈ ℕ`, every class of a prime `q > 1000`, `q ∤ u`, `q² > 2n + 3q` with `x = n/q ∈ [a + 40t,
b + 40t)` has `E_ξ ≥ 4 - f` (so `E_ξ ≥ -6` for all `x ≥ 20`).

**Proof** (helpers `ResCert7Floor.lean`, data `ResCert7Data.lean`; encoding: `notes/ResCert7.md`).
* *Floor-sum form of `E`* (`localModel_E_eq_sysE7`): for odd `q` and `k₀ < q`, with `x = 40u/q`,
  `y = k₀/q`,
  `E_ξ = ∑_m [⌊(1-η_m)x - y - 1/2⌋ - ⌊η_m x - y - 1/2⌋]
         - ∑_{ℓ=0}^{3} [⌊(1 - ℓ/20)x - y⌋ - ⌈(ℓ/20)x - y⌉ + 1] + [q ∣ 2k₀ - n]`,
  i.e. `sysE7.val x y + δ` for the 20-line system `sysE7`; the counts of zeros and poles in the
  residue class are counted with `RC7.cnt_le`.
* *Periodicity* (`sysE7_val_add_40`): all slopes `A_j/80` have `A_j/2 ∈ ℤ`, and
  `∑_j W_j A_j/2 = 0` (`∑_m (1 - 2η_m) = 3.4 = ∑_ℓ |I_ℓ|`).
* *Realizability* (`sysE7_real_disc`, uses `q > 40` prime and `q ∤ u`): at a discrete point no
  floor line and no ceiling line are integral together, so the lines dropped at `y` form a
  prefix of the order of the fractional parts.
* *Certificates* (`resECerts7`, `ECert7.ok_sound`): on each row the order of the 20 lines by their
  fractional parts, checked at both ends, and all prefix sums `≥ 4 - f`; the kernel checks all
  980 (`resECerts7_ok`) and that they are the rows' own intervals and bounds (`resRows7_keys`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

theorem ResCert7_proof : Stmt_ResCert7 := by
  intro row hrow t u q hq hq1000 hqu _ ha hb k₀ hk
  obtain ⟨c, -, hok, hpa, hqa, hpb, hqb, hsig⟩ := resRows7_cert row hrow
  have h := ECert7.E_ge c hok (t : ℤ) u q hq (by omega) hqu ?_ ?_ k₀ hk
  · rw [hsig] at h
    exact h
  · rw [hpa, hqa]
    push_cast
    simpa [DenRow.a] using ha
  · rw [hpb, hqb]
    push_cast
    simpa [DenRow.b] using hb

end Zeta2.Z7

end
