module

public import Zeta2Lean.Z7.Proofs.HeadCert7Rows

@[expose] public section

/-!
# Kernel-level certificates on `[1, 20)`: continuum types + certified levels (proof §4.8)

gap: 'denominators' (the main computer-assisted step).  Difficulty 5.  No dependencies.

**Statement.** `Stmt_HeadCert7`: for each of the 469 rows `[a, b) × (f, κ)` of `headRows7` and
each prime `q > 1000` with `q ∤ u`, `q² > 2n + 3q` and `x = n/q ∈ [a, b)`, every class `k₀ < q`
satisfies `LevGe (localModel u q k₀) c₀ j c (5 - f)` and `PoleLevGe (localModel u q k₀) (-f)`.

**Informal proof** (proof Lemmas 4.10–4.11 + the certified data of the denominator computation).  With
`y = k₀/q` the local model is a function of `(x, y)`; it changes only when `y` crosses an event
line `γ x + e` (`γ ∈ (1/40)ℤ`, `e ∈ ½ℤ`); on a candidate interval the order of the event lines is
fixed, so finitely many types occur, and each is checked.

**Lean proof** (notes: `notes/HeadCert7.md`; generator: `HeadCert7_gen.py`).
1. *Dictionary* (`HeadCert7Dict.lean`): 23 lines `HC7.sysH` = the 20 lines of the floor-sum form
   of `E` (`sysE7`, `ResCert7Floor.lean`) + `x/2` (floor and ceiling) + `x/2 + 1/2`.  The literal
   `localModel u q k₀` is a function `HC7.cmodF` of the 23 floor values at `(x, y)` (poles, pole
   orders, zero multiplicities, the `δ`-zero, the bad pairs), for every odd `q`
   (`HC7.localModel_eq_cmodF`); `E = HC7.EF` of the floor values (`HC7.localModel_E_eq_EF`).
2. *Sweep* (`HC7.sweep`, a variant of `ECert7.ok_sound`): on a row, for a realizable point
   (`HC7.sysH_real_disc`: `q > 40` prime, `q ∤ u`), the floor vector is one of the 24 prefix
   states of the certificate's order of the lines by their fractional parts.
3. *Certificates* (`HeadCert7Row.lean`, data `HeadCert7Data*.lean`): `HC7.rowOK` checks, for every
   consistent state, `E ≥ 4 - f` (vacuous `LevGe`), or `κ = 0` without bad pairs, or a job of the
   table `HC7.levJobs`; and `E ≥ -1 - f` or a job of `HC7.poleJobs` (`HC7.rowOK_sound`).
4. *Series* (`HeadCert7Series.lean`, tables `HeadCert7Lev*.lean`, `HeadCert7Pole.lean`): the 76
   `LevGe` jobs (63 local types) and 9 `PoleLevGe` jobs (4 types) are checked by exact rational
   arithmetic on truncated series (`HC7.levChk_sound`, `HC7.poleChk_sound`).
Only `q > 40`, `q` prime and `q ∤ u` are used (not `q > 1000` or `q² > 2n + 3q`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Z7

theorem HeadCert7_proof : Stmt_HeadCert7 := by
  intro row hrow u q hq h1000 hqu _ ha hb
  obtain ⟨h, hh, rfl⟩ := HC7.aligned_sound headRows7 HC7.hrows7 HC7.hrows7_aligned row hrow
  have hok := List.all_eq_true.1 HC7.hrows7_ok h hh
  exact ⟨fun k₀ hk => (HC7.rowOK_sound h hok u q hq (by omega) hqu ha hb k₀ hk).1,
    fun k₀ hk => (HC7.rowOK_sound h hok u q hq (by omega) hqu ha hb k₀ hk).2⟩

end Zeta2.Z7

end
