# MaxU7 (Lemma G7, `Stmt_MaxU7 g7`) — handoff notes

Status: **proved** (round 3), no sorry. `Zeta2Lean/Z7/Proofs/MaxU7.lean` (~3100 lines, elaborates in
~5.5 min; each box theorem carries `set_option maxHeartbeats 4000000 in`).

## Method (chords and tangents, not the monotone box bound)
* `F(z) = z log|z| - z`, `F'' = 1/z`: convex on `[0, ∞)`, concave on `(-∞, 0]`.
  Hand-written lemmas: `tangent_pos/neg`, `chord_pos/neg` (via `Real.one_sub_inv_le_log_of_pos`),
  packaged per summand as `chord_up_pos/neg` and `tangent_up_pos/neg`.
* 42 boxes `[a, b]` (endpoints in `(1/80)ℤ`, refining the `1/40` breakpoint grid). Per summand
  `w F(p - κ)`: convex in `κ` → chord through `κ = a, b`; concave → tangent at the midpoint.
  The majorant is affine in `κ`; `hEa`/`hEb` bound it at `κ = a, b` (linarith on certified
  `log` values), `P1 = (b-κ)·hEa`, `P2 = (κ-a)·hEb`, and a final `linarith` with `Upot_expand`.
* Log enclosures: `lq*` (93 rationals `q = |z|`, denominators ≤ 160) via
  `Pair/Proofs/Landscape/Numerics.lean` (`log_le_of_le_mul`, `le_log_of_mul_le`, ...), exact
  `z = (r-1)/(r+1)`, rounded to `1e-15`; `lz*` (log |z|), `fz*` (F(z)) for 186 grid points.
* Worst exact box bound 0.708146 (margin 0.00185 to 0.71).

## Regenerating
`python3 Zeta2Lean/Z7/Proofs/MaxU7_gen.py Zeta2Lean/Z7/Proofs/MaxU7.lean OUT.lean [maxboxes]`
keeps the hand-written top of the file (everything before
"/-! ## Certified values of `log`") and regenerates the rest; it re-verifies every box exactly
(Fraction) with the same rational bounds that Lean uses.

## Pitfalls met
* `le_or_lt` no longer exists in this Mathlib: use `le_or_gt`.
* Box theorems exceed the default 200000 heartbeats (~7 s each); 4000000 is ample.
* Keep numerals textually identical between `t*` facts, `hEa/hEb` and the `fz/lz` lemmas
  (linarith atoms `Fx (a / b : ℝ)`, `Real.log |(a / b : ℝ)|`).
