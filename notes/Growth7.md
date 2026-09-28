# Growth7 (Theorem G) -- DONE (round 3)

`Zeta2Lean/Z7/Proofs/Growth7.lean`: `Growth7_proof : Stmt_MaxU7 g7 -> Stmt_ResidueBound7 -> Stmt_Growth7 g7`
is sorry-free; `#print axioms` = `propext, Classical.choice, Quot.sound`. Elaborates in ~26 s.

Proof (namespace `Growth7Aux` for helpers):
* `abs_AhalfZ_le : |AhalfZ d s| <= |d| * 2^s` (each term has `|h| >= 1/2`).
* residues: `|r_{i,k}| <= |C| (u+1)^B e^{0.71 * 40u}` for `k <= 40u` (ResidueBound7 + MaxU7 at `k/(40u)`).
* `|rho| <= 4 (40u+1) * 840 M (40u+1) 256`, `|Z| <= 46080 (40u+1) M`; `40u+1 <= 41u`, `(u+1)^B <= 2^B u^B`.
* `eventually_poly_le_exp` (copy of the pair's, exponent `N` general) absorbs `A u^(B+2)` into `e^{40 eps u}`.
