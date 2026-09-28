"""Independent re-implementation (adversarial verification) -- shared helpers.  Does NOT import genpole/verify_cand/lfam.

Candidate family (n divisible by 40, u = n/40):
    R_n(t) = (2t+n)^delta * prod_{e in etas} prod_{c = e*u}^{n - e*u - 1} (t + 1/2 + c)  /  prod_{k=0}^{n} (t+k)^{a_k}
    a_k    = acells[ min( floor(40*min(k, n-k)/n), 19 ) ]
    delta  chosen so that delta + N + sum(a) is odd   (=> R(-n-t) = -R(t))
    S_n    = int_{Z_2} R_n'''(t + 1/2 - n/2) dt   (Volkenborn integral)
"""
import sys, math
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr

CANDS = {
    'cand3': dict(acells=[1, 1, 2, 2, 3, 3] + [4] * 14, etas=[5, 7, 7, 9, 11, 13]),
    'cand2': dict(acells=[1, 2, 3, 3] + [4] * 16, etas=[5, 6, 7, 8, 10, 11]),
    'cand1': dict(acells=[2, 2, 3] + [4] * 17, etas=[5, 6, 7, 8, 9, 10]),
    'uniform': dict(acells=[4] * 20, etas=[0, 0, 0, 0]),
}


def build(cfg, n):
    assert n % 40 == 0
    u = n // 40
    blocks = [(e * u, n - e * u - 1) for e in cfg['etas']]
    ac = cfg['acells']
    a = [ac[min(40 * min(k, n - k) // n, 19)] for k in range(n + 1)]
    N = sum(hi - lo + 1 for lo, hi in blocks)
    SA = sum(a)
    delta = (1 + N + SA) % 2
    return blocks, a, N, SA, delta


def mu_map(blocks):
    mu = {}
    for lo, hi in blocks:
        for c in range(lo, hi + 1):
            mu[c] = mu.get(c, 0) + 1
    return mu


def runs_of(a):
    runs = []
    s = 0
    for k in range(1, len(a) + 1):
        if k == len(a) or a[k] != a[s]:
            runs.append((s, k - 1, a[s]))
            s = k
    return runs


def primes_upto(N):
    if N < 2:
        return []
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


def lcm_upto(X):
    r = 1
    for q in primes_upto(X):
        qq = q
        while qq * q <= X:
            qq *= q
        r *= qq
    return r


def v2int(x):
    x = abs(x)
    if x == 0:
        return 10 ** 9
    return (x & -x).bit_length() - 1


def vq(x, q):
    if isinstance(x, Fr):
        if x == 0:
            return 10 ** 9
        return vq(x.numerator, q) - vq(x.denominator, q)
    x = abs(x)
    if x == 0:
        return 10 ** 9
    if q == 2:
        return v2int(x)
    c = 0
    while x % q == 0:
        x //= q
        c += 1
    return c


def lnabs(x):
    x = Fr(x)
    if x == 0:
        return float('-inf')
    return math.log(abs(x.numerator)) - math.log(x.denominator)


def to_mod2(x, W):
    """2-integral rational x -> integer in [0, 2^W) congruent to x mod 2^W"""
    x = Fr(x)
    num, den = x.numerator, x.denominator
    assert den % 2 == 1, 'not 2-integral'
    M = 1 << W
    return (num % M) * pow(den, -1, M) % M


def v2_linear_form(rho, coef, Y, sh, K):
    """S = rho + coef * X  with X = Y * 2^(-sh), Y known modulo 2^K.
    Returns (v2(S) or None, precision_limit) ; None means S == 0 to the available precision."""
    rho = Fr(rho); coef = Fr(coef)
    vr = vq(rho, 2) if rho != 0 else 10 ** 9
    vz = vq(coef, 2)
    E = max(-vr if rho != 0 else 0, sh - vz, 0) + 1
    prec = K + (E - sh + vz)        # absolute precision of 2^E * coef * X
    W = prec
    a1 = to_mod2(rho * Fr(2) ** E, W) if rho != 0 else 0
    a2 = to_mod2(coef * Fr(2) ** (E - sh), W) * (Y % (1 << W)) % (1 << W)
    T = (a1 + a2) % (1 << W)
    if T == 0:
        return None, W - E
    return v2int(T) - E, W - E


def S_mod2(rho, coef, Y, sh, K, P):
    """(rho + coef*Y*2^-sh) * 1  as integer mod 2^P, requires the result to be 2-integral to that precision;
    returns (value mod 2^P', P') where P' = min(P, available precision)."""
    rho = Fr(rho); coef = Fr(coef)
    vr = vq(rho, 2) if rho != 0 else 10 ** 9
    vz = vq(coef, 2)
    E = max(-vr if rho != 0 else 0, sh - vz, 0) + 1
    W = K + (E - sh + vz)
    a1 = to_mod2(rho * Fr(2) ** E, W) if rho != 0 else 0
    a2 = to_mod2(coef * Fr(2) ** (E - sh), W) * (Y % (1 << W)) % (1 << W)
    T = (a1 + a2) % (1 << W)
    # S = T * 2^-E  (mod 2^(W-E))
    Pp = min(P, W - E)
    assert v2int(T) >= E or T == 0, 'S not 2-integral?'
    return (T >> E) % (1 << Pp), Pp
