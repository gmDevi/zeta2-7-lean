# Denominators7 (Stmt_Denominators7 delta7, Theorem A) -- DONE (round 4)

`Zeta2Lean/Z7/Proofs/Denominators7.lean`: `Denominators7_proof (hX : Stmt_ExpBounds7)` is proved,
no `sorry`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. Elaborates in ~10 s
(`scripts/check.sh`); `scripts/build.sh Zeta2Lean.Z7.Proofs.Denominators7` builds with no warnings.

New import: `Zeta2Lean.Pair.Proofs.Denominators` (already built; only its PNT-side analytic lemmas
in `Zeta2.Pair.Den` are used). All new names live in `Zeta2.Z7.Den7` (no clashes, checked by grep).

Construction:
- `D u = Dodd7 u = prod_{q <= 40u odd prime} q^(eq7 u q)`, `e u = e7 u = v2(den rho) + v2(den Z)`.
- Integrality for every `u` (`den_dvd`, `int_of_den_dvd`): `den x | 2^e D` prime by prime via
  `Nat.factorization_prime_le_iff_dvd` + `padicValNat_dvd_iff_le`; odd `p > n` uses `hX.big`.

Size (`log_sum_bound7`, delta = eps/400000), split of the odd primes `q <= n = 40u`:
1. `q <= 1000` or `q^2 <= 80u + 3q`: `hX.small`, `q <= 1000 + sqrt(200u)`, total
   `<= 38038 (sqrt(80u)+1) log(80u)`;
2. `q > 1000`, `q^2 > 80u+3q`, `q | u`: `hX.crude` (14), total `<= 14 log u` (`Nat.prod_primeFactors_dvd`);
3. same, `q` not dividing `u`, `140 q <= 40u`: `hX.tail` (10), total `<= 10 theta(n/140)`;
4. same, `40u < 140 q`: `hX.rows` through `chain7_sum` over `denTable7` (kernel facts
   `denTable7_chain` (tiles [1,140) with exact endpoint pairs), `denTable7_rowOK`
   (`0<ad, 0<bd, a<b, a>=1, b<=140, f<=14`), `denTable7_length = 3409`), then PNT per row
   (`Pair.Den.theta_eventually`) and `table_integral` (`sum f(1/a-1/b) + 10/140 <= 3.99`, derived
   from `denTable7_integral_fixed` via `Uterm7_ge`).
Terms 1+2 are absorbed with `Pair.Den.small_term_eventually (4*38052/eps)`.

Math: no issue found; the formal proof follows the architect's five-range plan exactly.
Pitfalls met: `Σ'` is not a valid identifier; `if_pos` is deprecated in this toolchain (used
`split_ifs`); `push_cast` pushes casts into `Real.log`/products, so state cast forms explicitly.
