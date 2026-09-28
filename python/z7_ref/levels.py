"""Class levels from a local model (exact rationals).  Shared by the discrete checker and the continuum code.

Local model of a residue class (coordinate v = (t - xihat)/q):
  items = [(v_w, e_w)]   poles v = -j (e = -a), zeros v = -s/2 (e = mu), delta zero
  pairs = [(v_k, v_e, sgn)]  bad pairs of the centred rational part (pole v_k, evaluation point v_e)
Levels (lower bounds for q-adic valuations, valid for q > C(local data)):
  La : direct class bound for beta_xi (bad sum of the class)           = -5 + min{p >= E+1 : [y^p](A s^-E) != 0}
  Lb : subtracted class bound for T_xi = beta_xi - 24 q^-5 oint R        = -5 + min{p >= E+1 : [y^p]((A-RR) s^-E) != 0}
  LG : good-part bound  min over poles of level(r_{1,k})  (only poles with d != 0 carry good terms; we take all)
  L3 : c_3 class bound  min over poles of level(r_{3,k})
"""
from fractions import Fraction as Fr
from kernel import ser_mul, ser_inv, binom_series

INF = 10 ** 6

def _A_series(items, pairs, M):
    aser = [Fr(0)] * (M + 1)
    for vk, ve, sg in pairs:
        a = -sum(e for v, e in items if v == vk)
        if a <= 0: continue
        tay = [Fr(1)] + [Fr(0)] * (a - 1)
        const = Fr(1)
        for v, e in items:
            if v == vk: continue
            b = vk - v
            const *= b ** e
            tay = ser_mul(tay, binom_series(1 / b, e, a), a)
        b = ve - vk
        const *= b ** (-5)
        tay = ser_mul(tay, binom_series(-1 / b, -5, a), a)
        for i in range(1, a + 1):
            gi = const * tay[a - i]
            if gi == 0: continue
            ex = binom_series(-vk, -i, M + 1)
            for l in range(M + 1 - i):
                aser[i + l] += sg * gi * ex[l]
    return aser

def _R_series(items, M):
    rser = [Fr(1)] + [Fr(0)] * (M - 1)
    for v, e in items:
        if v != 0: rser = ser_mul(rser, binom_series(-v, e, M), M)
    return rser

def class_levels_local(items, pairs, M=12):
    E = sum(e for _, e in items)
    valid = M + min(E, 0)
    rser = _R_series(items, M)
    La = INF; Lb = INF
    if pairs:
        aser = _A_series(items, pairs, M)
        dA = {}
        for i, c in enumerate(aser):
            if c: dA[i + E] = dA.get(i + E, Fr(0)) + c
        ps = [p for p in sorted(dA) if p >= E + 1 and dA[p] != 0 and p < valid]
        La = -5 + (ps[0] if ps else valid)
        dB = dict(dA)
    else:
        dB = {}
    for i, c in enumerate(rser):
        if c: dB[i] = dB.get(i, Fr(0)) - c
    ps = [p for p in sorted(dB) if p >= E + 1 and dB[p] != 0 and p < valid]
    Lb = -5 + (ps[0] if ps else valid)
    # data for the one-step kernel improvement: D coefficients (p >= E+1) and b coefficients of RR s^-E
    Dco = {p: c for p, c in dB.items() if p >= E + 1 and p < valid}
    bco = {i: c for i, c in enumerate(rser)}
    # per-pole Laurent levels
    LG = INF; L3 = INF
    for vk in sorted(set(v for v, e in items)):
        a = -sum(e for v, e in items if v == vk)
        if a <= 0: continue
        # tau(w) = w^a RR(vk + w) = prod_{v != vk} (vk - v + w)^e  (Taylor, up to w^{a-1})
        tau = [Fr(1)] + [Fr(0)] * (a - 1)
        for v, e in items:
            if v == vk: continue
            b = vk - v
            tau = ser_mul(tau, binom_series(1 / b, e, a), a)
        def lev(i):
            if i > a: return INF
            lmax = max([l for l in range(0, a - i + 1) if tau[l] != 0] + [-1])
            if lmax < 0: return INF
            return E + a - lmax
        LG = min(LG, lev(1), lev(2), lev(3), lev(4))
        L3 = min(L3, lev(3))
    return dict(E=E, La=La, Lb=Lb, LG=LG, L3=L3, D=Dco, b=bco, valid=valid, exposed=bool(pairs))

def kernel_step_bound(types):
    """types: list of level dicts (one per realized local type at this x).
    Plain subtracted bound P0 = min Lb.  One-step kernel K = 1 + c q^j sum_{k0'} (t+k0')^{-j} with j = P0 + 5:
    admissible iff every type with E + 1 <= j has the same D coefficient d_j = c; then each type's new first
    nonzero index of d_p - c b_{p-j} gives its level, and the far part costs level j - 4 = P0 + 1.
    Returns the kernel bound (or P0 if not admissible) and c."""
    P0 = min(t['Lb'] for t in types)
    j = P0 + 5
    # FIX (restart 2026-09-26): j < 0 would be a POLYNOMIAL kernel: deg(R Psi) may be >= -1 (residue at infinity
    # no longer 0) and the far part is not q-divisible.  Only j >= 0 is admissible (j = 0: Psi = 1 + c constant,
    # no far part; j >= 1: far part costs j - 4 by the power-sum congruence).  The attempt-1 code allowed j < 0 and
    # produced bounds BELOW the truth at x ~ 7, 9.5, 17, 21, 22, 30 (disc_bound.py found the violations).
    if j < 0:
        return P0, None
    vals = set()
    for t in types:
        if t['E'] + 1 <= j:
            vals.add(t['D'].get(j, Fr(0)))
    if len(vals) != 1:
        return P0, None
    c = vals.pop()
    if c == 0:
        return P0, None
    best = INF
    for t in types:
        E = t['E']
        if E + 1 > j:
            best = min(best, t['Lb']); continue
        newp = None
        for p in range(E + 1, t['valid']):
            dp = t['D'].get(p, Fr(0)) - (c * t['b'].get(p - j, Fr(0)) if p - j >= 0 else 0)
            if dp != 0:
                newp = p; break
        lev = -5 + (newp if newp is not None else t['valid'])
        best = min(best, lev)
    return min(best, j - 4), c
