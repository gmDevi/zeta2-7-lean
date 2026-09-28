# HeadCert7 — prover notes (round 4)

Target: `Zeta2Lean/Z7/Proofs/HeadCert7.lean`, `theorem HeadCert7_proof : Stmt_HeadCert7`.

## Status: PROVED

`#print axioms Zeta2.Z7.HeadCert7_proof` = `[propext, Classical.choice, Quot.sound]`.
`bash scripts/build.sh Zeta2Lean.Z7.Main`: green (9000 jobs, 2026-09-28).  `scripts/audit.sh`: no
sorry, no forbidden construct in the HeadCert7 files.  `leanchecker` replay of the 23 HeadCert7
modules, one at a time: fail=0 (2026-09-28).  No statement, `Defs`, `Statements`,
`DenTable`, `Assembly`, `Main` or `ResCert7*` change (only `ResCert7Floor` is imported; the head
`E`-certificates of `ResCert7Head.lean` are not needed: the new 23-line sweep subsumes them).

## Files (all `Zeta2Lean/Z7/Proofs/`, namespace `Zeta2.Z7.HC7`)

| file | content | build |
|---|---|---|
| `HeadCert7Dict.lean` | 23-line system `sysH`, `cmodF`, dictionary `localModel_eq_cmodF`, `hF_spec`, `EF`, `localModel_E_eq_EF`, `sweep`, `sysH_real_disc` | 7 s |
| `HeadCert7Series.lean` | truncated series (`cf`, `tmul`, `tprod`, `bserL`), `coeff_rSer`, `coeff_taylorAt`, `coeff_gSer`, `coeff_ASer`, `levChk_sound`, `poleChk_sound`, `LevGe_zero_of_nopairs`, the check by pole groups (`grp`, `grpC`, `ASerC_eq_grp`, `grpR`/`grpT`, `grpT_split`, `levChkV`, `LevJob.ok_of_vals1..4`), compact encoding `mkT`, `LevJob`, `PoleJob` | 10 s |
| `HeadCert7Lev0..7.lean` (generated) | the 76 `LevGe` jobs `levJob*_*`, each checked in pieces (237 `decide +kernel` in all), `levJobs*_ok` | 11-16 s each |
| `HeadCert7Pole.lean` (generated) | the 9 `PoleLevGe` jobs, `poleJobs_ok` | 3 s |
| `HeadCert7Tab.lean` (generated) | `levJobs`, `poleJobs`, `levJobs_sound`, `poleJobs_sound` | 3 s |
| `HeadCert7Row.lean` | `HRow`, `rowOK` (certificate + all consistent prefix states), `rowOK_sound`, `aligned` | 3 s |
| `HeadCert7Data0..7.lean` (generated) | the 469 row certificates in 243 chunks `hrows7_*_*` (one `decide +kernel` each), `hrows7_*_ok` | 15-30 s each |
| `HeadCert7Rows.lean` (generated) | `hrows7`, `hrows7_ok`, `hrows7_aligned` | 3 s |
| `HeadCert7.lean` | `HeadCert7_proof` (6 lines) | 3 s |
| `HeadCert7_gen.py` | generator (`--audit`: mirror checks vs `python/z7_audit.py`; `--check`) | – |

The 16 generated parts build one after the other (each imports the previous one) in about
4 min (at most about 4 GB of memory each, mostly the imported environment).

**Kernel memory** (2026-09-28).  Palomar's comparator also replays the proof with con-ron, 16 declarations
at a time; con-ron keeps a declaration's intermediate terms until that declaration is checked (roughly
0.1-0.25 GB per second of checking).  Each part used to be a single `decide +kernel` (33-134 s and 5-15 GB
in con-ron with one worker), and the 16 parts are adjacent in the export: con-ron's 16 workers needed far
more than 32 GB.  The generator now cuts the work into small kernel checks:
* a `LevGe` job is checked in pieces: its bad pairs are grouped by pole, so that each pole's Taylor series
  is computed once per group instead of once per pair (3-6 times less con-ron time), a piece
  `grpR τ lo hi m` / `grpT τ lo m` is the contribution of consecutive pole groups to `[y^m] ASer τ` (its
  value is computed by the generator and checked by one `decide +kernel`), and `LevJob.ok_of_vals*` checks
  the rest of `levChk` from the sum of the pieces;
* a `Data` part is checked in chunks of rows, one `decide +kernel` each.
Pieces and chunks are cut by a cost estimate (`HC7_BUDGET`, default 1200, about 1 ms of con-ron time per
unit): every check takes at most about 2 s in con-ron (one worker) and 1.1 s in Lean's kernel.  The checks
are `have`s inside `levJob*_*_ok` / `hrows7_*_ok`, not theorems of their own: con-ron re-reduces the
statement of a theorem proved by `decide +kernel` (whose proof is the auxiliary lemma), at about a quarter
of the cost of the check.  Regenerate / re-check the data:
```
HC7_NLEV=8 python3 Zeta2Lean/Z7/Proofs/HeadCert7_gen.py            # writes only changed files
HC7_NLEV=8 python3 Zeta2Lean/Z7/Proofs/HeadCert7_gen.py --check --audit
```

## The proof

1. **Dictionary** (Lemma 4.11): `HC7.sysH` = `sysE7` (20 lines) + `x/2` floor (20), `x/2` ceiling
   (21), `x/2 + 1/2` floor (22), weights 0.  `localModel u q k₀ = cmodF (40u/q) (hF u q k₀)` for
   every odd `q`; `hF j = sysH.fl j (sysH.ell j x - y)` for `j < 23`.  In `cmodF`: pole `j` iff
   `j ≤ F₁₂`, order `1 + ∑_{l=1}^3 [F_{16+l} ≤ j ≤ F_{12+l}]`; zero `w = -(2t-1)` with
   multiplicity `∑_m [t ≤ F_m + 1] - [t ≤ F_{m+6} + 1]`; `δ`-zero iff `F₂₁ = F₂₀`, at `-2F₂₀`;
   pole `j` has `max(0, j - F₂₂)` pairs of sign `+` if `F₂₀ < j`, else `max(0, F₂₂ - j)` of sign
   `-` (none at the centre `j = F₂₀` when `δ`).  `E = EF F` (the `sysE7` floor sum + `δ`).
2. **Sweep** (`HC7.sweep`): like `ECert7.ok_sound`, but it returns the state: the floor vector is
   `stF S c p` (the first `p` lines of `ord` dropped) for some `p ≤ n`.  Realizability is
   generalized (`Real'`: a floor and a ceiling line integral together must be identical; the check
   `noFC` forbids an identical floor line directly before its ceiling copy — lines 20/21 are sorted
   ceiling first).  `sysH_real_disc`: discrete points with `q > 40` prime, `q ∤ u` are `Real'`.
3. **Row check** `HC7.rowOK`: `okS` + interval = row + `X ≤ a`, `b ≤ X + 1` (so `40u/q = X`) +
   for every consistent state `p ∈ [0, 23]` (identical lines 1,2 and 7,8 together; states that
   split them are not realizable and are skipped): `levOK` (vacuous by `EF`, or `κ = 0` and no
   bad pairs, or a table job) and `poleOK` (vacuous or a table job).
4. **Series**: `levChk`/`poleChk` compute the needed coefficients of `ASer`, `rSer`, `taylorAt`
   exactly (ℚ arithmetic under `decide +kernel` works well here; the heaviest types have 90 pairs
   and 35 items; closed subterms are cached by the kernel).  `levChk` is evaluated by pole groups
   and in pieces (`HC7.ASerC_eq_grp`, `HC7.grpT_split`, `HC7.levChk_of_V`), see above.

Numbers: 10318 consistent states, 247 rows with exceptional states (799 incidences), 76 `LevGe`
jobs on 63 types, 9 `PoleLevGe` jobs on 4 types (= the audit's counts).  The generator's mirror
(`--audit`) agrees with `python/z7_audit.py`'s independent `LType` on all jobs; `cmodF` agrees with
the audit's `cont_model` at every realizable state (prototype check).

## Math remarks (no issue found)

* The dictionary of the docstring (proof §4.8) is exactly right for the Lean `localModel`, for
  every odd `q` (no size condition); only realizability needs `q > 40` prime and `q ∤ u`.
* `Stmt_HeadCert7`'s hypotheses `q > 1000` and `80u + 3q < q²` are not used (only `q > 40`).
* The 9 non-vacuous `PoleLevGe` jobs are on types with at most 2 items (rows `[1, 20/17)`); they
  hold (a pole with only zeros around has a polynomial Taylor factor).

## Pitfalls

* `fun j => … (j : ℤ) …` over `List.range` elaborates `j : ℤ` and coerces the list: write
  `fun j : ℕ => …`.
* `rw` of an `↔` inside `if`: use `if_congr h rfl rfl`.
* The coerced range `((List.range N : List ℕ) : List ℤ)` is `List.flatMap (fun a => [↑a])`:
  `HC7.coe_range` rewrites it to a `map`.
* Big literal lists of tuples time out in elaboration: types are encoded as flat `List ℤ`
  (`HC7.mkT`, bad pairs run-length encoded).
* A local hypothesis named `hF` shadows the function `HC7.hF` (silently becomes `sorry`).
* The kernel's work counts toward the heartbeats of the declaration being elaborated: the
  `have … := by decide +kernel` chunks of one `hrows7_*_ok` share one budget, hence
  `set_option maxHeartbeats 1000000` there (the default 200000 stopped part 7 part-way).
