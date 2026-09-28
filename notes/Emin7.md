# Emin7 (Stmt_Emin7) -- DONE

`Zeta2Lean/Z7/Proofs/Emin7.lean` is sorry-free; `#print axioms Zeta2.Z7.Emin7_proof` =
[propext, Classical.choice, Quot.sound]. Elaborates in ~5 s.

Proof structure (namespace `Zeta2.Z7.Emin7Aux`):
1. `sum_filterMap_range`, `sum_filterMap_range_int` (the zero list is `do a <- List.range N; pure (a:Z)`),
   `getD_ite`: turn the three `filterMap` blocks of `localModel` into Finset sums S1 + S2 + S3; S3 >= 0.
2. `pole_bound`: `[k <= n] apole k = sum_{l<4} [2lu <= k /\ k + 2lu <= n]`, each count bounded by
   `card_mul_le` (min'/max' argument): `q * S1 >= -(136u + 4q)`.
3. `zero_bound`: termwise `S2`-summand >= `#{m : eta_m u + h <= k0 + tq < (40-eta_m)u + h}`, h = (q+1)/2,
   counts bounded below by `card_mul_ge` (explicit run t0 + i): `q * S2 >= 136u - 6q`.
4. nlinarith: E >= -10 (in fact E > -10 - ... gives E >= -10 with q >= 5; only q > 0 and k0 < q are used).