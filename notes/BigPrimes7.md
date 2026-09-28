# BigPrimes7 (Stmt_BigPrimes7, Theorem C) -- DONE

Status: proved, sorry-free, no warnings. `#print axioms BigPrimes7_proof` =
[propext, Classical.choice, Quot.sound]. Self-contained (imports only Z7.Statements).

Route (simpler than the informal "absorption" argument, which is not needed here):
- `PI q F` := all coefficients have padicNorm <= 1; closed under mul/prod/pow.
- numerator factors `C(c - k + 1/2) + X` and the linear factor `C(n-2k) + C 2 * X` are PI (q != 2);
- pole product inverted factor by factor (`prod_inv'`, `PowerSeries.inv_pow`, `inv_C_add_X`),
  each `j - k` a q-unit since 0 < |j-k| <= n < q (`pn_int_unit`);
- so `Gser_int`, `rcoef_int`; `AhalfZ_int` (|2l+1| <= n-1 < q, uses q odd); `rho_int`, `Zc_int`;
- `den_val_zero`: padicNorm <= 1 implies padicValNat q den = 0.
