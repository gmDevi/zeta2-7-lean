# ThmK7 (Stmt_ThmK7, Theorem K) -- DONE (round 3)

`Zeta2Lean/Z7/Proofs/ThmK7.lean`: `ThmK7_proof` is sorry-free; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`. Elaborates in ~5 s (`scripts/check.sh`).

Helpers (namespace `Zeta2.Z7.ThmK7`, all proved):
* `AhalfZ_eq`: `AhalfZ d s = sgn(d) * sum_{o in oddBetween d} (2/o)^s`.
* `rho_eq`: `rho u = -rhoP u`; `rhoP_split`: `rhoP u = sum_{k0<q} classBad + goodPart` (q > 0).
* `pole_mem`: `(-2*(k/q), -a_k)` is an item of `localModel u q (k % q)` for `k <= 40u`.
* `ValGe` calculus (with `[Fact q.Prime]`): `valGe_zero/neg/add/sub/sum/mul/mono/int/pow/poch`,
  `valGe_two_div` (`q >= 3`, `q` does not divide `o`), `den_le` (`ValGe q T x`, `T <= 0` gives
  `padicValNat q x.den <= -T`).

Proof: per-pole `v_q(r_{i,k}) >= T` (PerPole7 + PoleLevGe at `pole_mem`) gives Z and the good
part; bad part = sum [classBad - 24 q^-5 kerRes] - sum 24 q^-5 c q^j farRes (KernelIdentity7),
ClassLemma7 with P = T+5, FarPart7 (its `j+1 <= q+E` from Emin7, q >= 29, j <= 4) then monotonicity
`j-4 >= T`; `c = 0` terms vanish. No math issue found.
