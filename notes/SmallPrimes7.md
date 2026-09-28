# SmallPrimes7 (Stmt_SmallPrimes7, Lemma 4.9) -- DONE

`Zeta2Lean/Z7/Proofs/SmallPrimes7.lean` has no sorry and no warnings.
`#print axioms Zeta2.Z7.SmallPrimes7_proof` gives [propext, Classical.choice, Quot.sound].
It elaborates in about 6 s and imports only `Z7.Statements`. The helpers are in namespace
`Zeta2.Z7.SmallPrimes7`.

The proof gives `eq7 u q <= 18 M` with `M = Nat.log q (80u+1)`, for every odd prime, `q = 3`
included; the statement needs `19 M`. No factorials or Kummer are used, only per-level counting:
- `PSV q M L F`: coefficient `r` of `F` has `v_q >= L - M r`. It is closed under `mul`, `prod`
  and `pow`; see also `lin` and `inv`.
- `Gser_PSV`: `PSV q M (Wk u q M k) (Gser u k)`, taken factor by factor:
  - the linear factor has `L = 0`, so the centre `k = 20u` needs no special case;
  - a numerator factor has `L = cnt(2(c-k)+1)`;
  - an inverted pole factor has `L = -cnt(j-k)`.
  Here `cnt z = #{e in [1,M] : q^e | z}`, and `cnt = v_q` on the poles because `|j-k| < q^(M+1)`.
- `Wk_eq`: `Wk = sum_{e=1..M} Lev u (q^e) k`.
- `Lev_ge`: `Lev >= -10` for odd `Q`. Two counts give it:
  - `card_odd_ge`: `Q * #(multiples in block m) >= L_m - Q`;
  - `card_dvd_le`: `Q * #(multiples in pole level l) <= (n - 4lu) + Q`, using
    `a_j = sum_{l<4} [2lu <= j <= n-2lu]`.
  Both sums of lengths are `136u`.
- `rcoef_val`: `v_q(r_{i,k}) >= M i - 14 M`.
- `AhalfZ_val`: `v_q(AhalfZ d s) >= -s M`.
- `rho_val` gives `v_q(rho) >= -18 M`; `Zc_val` gives `v_q(Zc) >= -11 M`.
- `den_le` (copied from ThmK7) finishes the proof.

Pitfall: inside a filter, the set-builder notation `{c ∈ s | (Q:ℤ) ∣ 2*((c:ℤ) - k) + 1}` gives
the binder `c` the type `ℤ`, so `Ico a b` silently becomes an interval of integers. Use
`s.filter (fun c : ℕ => ...)` instead.
