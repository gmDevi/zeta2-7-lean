"""Common definitions for the cand3 family (and generic symmetric 'nested ramp' configurations).

Configuration g = dict(Q=40, etas=[...] (block offsets in units of n/Q), acells=[...] (Q/2 pole-order cells, left half)).
For n divisible by Q:
  blocks  C_m = [eta_m n/Q, n - eta_m n/Q - 1]            (numerator (t+1/2+eta_m n/Q)_{(Q-2 eta_m) n/Q})
  a_k     = acells[floor(Q k / n)] for 2k < n,  acells[min(floor(Q (n-k)/n), Q/2-1)] for 2k >= n  (symmetric)
  R_n(t)  = (2t+n)^delta prod_m prod_{c in C_m} (t+1/2+c) / prod_k (t+k)^{a_k},  delta = 1 (N + sum a even)
  S_n     = int_{Z_2} R_n'''(t + 1/2 - n/2) dt = rho_n + Z_n zeta_2(7)
Continuum:  U(kappa) = sum_m int_{eta_m/Q}^{1-eta_m/Q} log|z-kappa| dz - int_0^1 a(z) log|z-kappa| dz,
            with a(z) = full[floor(Q z)], full = acells + reversed(acells).
"""
from fractions import Fraction as Fr

CAND3 = dict(Q=40, etas=[5, 7, 7, 9, 11, 13], acells=[1, 1, 2, 2, 3, 3] + [4] * 14)
CAND2 = dict(Q=40, etas=[5, 6, 7, 8, 10, 11], acells=[1, 2, 3, 3] + [4] * 16)   # from cand2_bign.jsonl
CAND1 = dict(Q=40, etas=[5, 6, 7, 8, 9, 10], acells=[2, 2, 3] + [4] * 17)       # from cand1_bign.jsonl
# configurations from the denominators-search track (evoprov1.jsonl / prov_top60.jsonl, 2026-09-26), for genericity tests
EVOP1 = dict(Q=40, etas=[3, 6, 8, 10, 12, 13], acells=[1, 1, 2, 2, 3, 3] + [4] * 14)   # evoprov1 gen-0..4 leader
PROV2 = dict(Q=40, etas=[6, 7, 8, 9, 10, 11], acells=[0, 1, 2, 3, 3] + [4] * 15)      # prov_top60 #2 (a_0 = 0)
PROV5 = dict(Q=40, etas=[4, 7, 8, 9, 11, 12], acells=[1, 1, 2, 2, 3] + [4] * 15)      # prov_top60 #5
EVOP7 = dict(Q=40, etas=[5, 7, 7, 10, 12, 15, 16], acells=[1, 1, 2, 2, 3, 3] + [4] * 14)  # 7 blocks (not covered)


def blocks(g, n):
    Q = g['Q']
    assert n % Q == 0
    out = []
    for e in g['etas']:
        lo = e * n // Q
        hi = n - e * n // Q - 1
        out.append((lo, hi))
    return out


def ak(g, n):
    Q = g['Q']; ac = g['acells']; H = Q // 2
    a = []
    for k in range(n + 1):
        if 2 * k < n:
            a.append(ac[min(Q * k // n, H - 1)])
        else:
            a.append(ac[min(Q * (n - k) // n, H - 1)])
    return a


def params(g, n):
    bl = blocks(g, n); a = ak(g, n)
    N = sum(hi - lo + 1 for lo, hi in bl); SA = sum(a)
    delta = 1 if (N + SA) % 2 == 0 else 0
    return bl, a, N, SA, delta


def continuum_terms(g):
    """U(kappa) = sum_j w_j F(p_j - kappa), F(x) = x log|x| - x.  Returns list of (w_j, p_j) with p_j Fractions."""
    Q = g['Q']; ac = g['acells']
    full = list(ac) + list(ac[::-1])
    terms = {}
    def add(p, w):
        terms[p] = terms.get(p, 0) + w
    for e in g['etas']:
        add(Fr(Q - e, Q), 1); add(Fr(e, Q), -1)
    for i, a in enumerate(full):
        if a:
            add(Fr(i + 1, Q), -a); add(Fr(i, Q), a)
    return sorted((w, p) for p, w in terms.items() if w != 0)


def U_float(g, kappa):
    from math import log
    s = 0.0
    for w, p in continuum_terms(g):
        x = float(p) - kappa
        if x != 0:
            s += w * (x * log(abs(x)) - x)
    return s
