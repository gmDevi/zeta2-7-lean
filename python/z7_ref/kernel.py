"""Local kernel machinery for the collective (cross-class) cancellation theorem.

For a residue class xi (base point xihat = -k0), local coordinate v = (t - xihat)/q:
  local model  RR(v) = prod_{w in D_xi} (v - v_w)^{e_w}          (poles v_k = -j order a; zeros v = -s/2 mult mu; delta)
  A(s)  = sum_{bad pairs (k,e)} sgn_k * PP_{v_k}[ RR(v) (v_e - v)^{-5} ](s)
  K(s)  = A(s)/RR(s)   expanded at s = infinity in y = 1/s.
THEOREM (to be proved in proof.md):  B = 24 q^{-5} sum_xi  oint_{D_xi} R(t) (K_xi((t-xihat)/q) - 1) dt  exactly, hence
  v_q(B) >= -5 + min_xi max(E_xi + 1, j_xi),   j_xi = ord_{y=0}(K_xi - 1)  (non-exposed classes: K = 0, j = 0).
All arithmetic exact (Fractions).
"""
from fractions import Fraction as Fr
from math import comb

def ser_mul(a, b, M):
    c = [Fr(0)] * M
    for i, x in enumerate(a[:M]):
        if x == 0: continue
        for j, z in enumerate(b[:M - i]):
            if z: c[i + j] += x * z
    return c

def ser_inv(a, M):
    assert a[0] != 0
    b = [Fr(0)] * M; b[0] = 1 / a[0]
    for i in range(1, M):
        s = Fr(0)
        for j in range(1, i + 1):
            if j < len(a) and a[j]: s += a[j] * b[i - j]
        b[i] = -s / a[0]
    return b

def binom_series(c, e, M):
    """(1 + c u)^e as series in u, e integer (any sign)"""
    out = [Fr(0)] * M; coef = Fr(1)
    out[0] = Fr(1)
    for i in range(1, M):
        coef = coef * (e - i + 1) / i
        out[i] = coef * c ** i
    return out

def local_items(n, mu, ak, delta, q, k0):
    """returns list of (v, e) for the local model, the base point -k0, plus bad pairs [(v_k, v_e, sgn)] and E"""
    items = []
    j = 0
    while k0 + j * q <= n:
        k = k0 + j * q
        if ak[k]: items.append((Fr(-j), -ak[k]))
        j += 1
    smax = 2 * n // q + 3
    for s in range(-smax, smax + 1):
        if s % 2 == 0: continue
        num = s * q - 1
        if num % 2: continue
        c = k0 + num // 2
        m = mu.get(c, 0)
        if m: items.append((Fr(-s, 2), m))
    if delta and (2 * k0 - n) % q == 0:
        items.append((Fr(2 * k0 - n, 2 * q), delta))
    pairs = []
    j = 0
    while k0 + j * q <= n:
        k = k0 + j * q
        if ak[k]:
            d = k - n // 2
            if d != 0:
                sg = 1 if d > 0 else -1
                sig = 1
                while sig * q < 2 * abs(d):
                    pairs.append((Fr(-j), Fr(-j) + Fr(sg * sig, 2), sg))
                    sig += 2
        j += 1
    E = sum(e for _, e in items)
    return items, pairs, E

def kernel_expansion(items, pairs, M=12):
    """Return (E, list of coefficients of K(s) - 1 in y = 1/s, as dict power->coef for powers from -?..M)"""
    E = sum(e for _, e in items)
    # RR at infinity: s^E * prod (1 - v y)^e
    rser = [Fr(1)] + [Fr(0)] * (M - 1)
    for v, e in items:
        if v != 0: rser = ser_mul(rser, binom_series(-v, e, M), M)
    # A at infinity: sum over pairs of sgn * sum_i g_{-i} (s - v_k)^{-i},  (s - vk)^{-i} = y^i (1 - vk y)^{-i}
    aser = [Fr(0)] * (M + 1)      # index = power of y
    for vk, ve, sg in pairs:
        a = -sum(e for v, e in items if v == vk)       # pole order at vk
        if a <= 0: continue
        # g(vk + u) = u^{-a} * prod_{v != vk} (vk - v + u)^e * (ve - vk - u)^{-5}
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
        # g_{-i} = const * tay[a - i]
        for i in range(1, a + 1):
            gi = const * tay[a - i]
            if gi == 0: continue
            ex = binom_series(-vk, -i, M + 1)       # (1 - vk y)^{-i}
            for l in range(M + 1 - i):
                aser[i + l] += sg * gi * ex[l]
    # K = A / RR = y^{E} * aser / rser   ;  K - 1 as dict
    rinv = ser_inv(rser, M + 1)
    kser = ser_mul(aser, rinv, M + 1)   # powers y^i, i>=0 (aser starts at y^1)
    out = {}
    for i, c in enumerate(kser):
        p = i + E
        if c: out[p] = out.get(p, Fr(0)) + c
    out[0] = out.get(0, Fr(0)) - 1
    return E, {p: c for p, c in out.items() if c != 0}

def D_expansion(items, pairs, M=12):
    """D(y) := (A(s) - RR(s)) * s^{-E}  as dict power -> coef  (powers of y = 1/s).
    Class term of the theorem = q^{E+1} sum_{m>=0} F_m q^m d_{E+m+1}; class level = -5 + min{p >= E+1 : d_p != 0}."""
    E = sum(e for _, e in items)
    rser = [Fr(1)] + [Fr(0)] * (M - 1)
    for v, e in items:
        if v != 0: rser = ser_mul(rser, binom_series(-v, e, M), M)
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
    # A s^{-E} = y^{E} * aser(y) ; RR s^{-E} = rser(y)
    out = {}
    for i, c in enumerate(aser):
        if c: out[i + E] = out.get(i + E, Fr(0)) + c
    for i, c in enumerate(rser):
        if c: out[i] = out.get(i, Fr(0)) - c
    return E, {p: c for p, c in out.items() if c != 0}, M + min(E, 0)

def refined_level(items, pairs, M=12):
    E, D, valid = D_expansion(items, pairs, M)
    ps = [p for p in sorted(D) if p >= E + 1 and p < valid]
    p = ps[0] if ps else valid
    return E, p, -5 + p, D

def jorder(Kminus1, M):
    ps = sorted(Kminus1)
    return ps[0] if ps else M   # M: vanishes to the computed order

def class_levels(n, cfg_blocks, ak, delta, q, M=12, refined=True):
    mu = {}
    for lo, hi, m in cfg_blocks:
        for c in range(lo, hi + 1): mu[c] = mu.get(c, 0) + m
    out = []
    cache = {}
    for k0 in range(q):
        items, pairs, E = local_items(n, mu, ak, delta, q, k0)
        key = (tuple(sorted(items)), tuple(sorted(pairs)))
        if key not in cache:
            if refined:
                E2, p, L, D = refined_level(items, pairs, M)
                cache[key] = (E, p, L, D)
            else:
                if pairs:
                    E2, km1 = kernel_expansion(items, pairs, M)
                    j = jorder(km1, M)
                else:
                    j = 0; km1 = {0: Fr(-1)}
                cache[key] = (E, j, -5 + max(E + 1, j), km1)
        E, j, L, km1 = cache[key]
        out.append((k0, E, j, L, key, km1))
    return out
