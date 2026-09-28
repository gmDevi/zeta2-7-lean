#!/usr/bin/env python3
"""Exact-arithmetic mirror of Zeta2Lean/Z7/Defs.lean (+ DenTable.lean) and numerical checks of every
statement of Zeta2Lean/Z7/Statements.lean (zeta_2(7) alone, configuration cand3).  Pure standard library.

Every function in section 1 mirrors the Lean definition of the same name *literally* (rcoef is 0 outside
1 <= i <= a_k, k <= n; natural-number subtraction is truncated; localModel uses the same List ranges and
the same Int arithmetic; coeffD/LevGe/PoleLevGe use the same series).  Power series are truncated lists.

Reference engines (verbatim copies of the research code, python/z7_ref/):
  vc_engine.py + vc_common.py  (verify-candidate: independent exact engine for r_{i,k}, c_i, rho, Z)
  kernel.py + levels.py + cont.py  (denominators-theory: local models, class levels, continuum types)
  qeng.py  (denominators-theory: q-adic engine for r_{i,k} at large n)
  cand.py  (growth-nonvanishing: the potential U)
Sign conventions: the research code has S = +int R''' = rho_n + Z_n zeta_2(7), Z_n = -46080 c_3; the Lean
objects are rho u = -rho_n, Zc u = -Z_n (S = -int R''').

usage: python3 python/z7_mirror.py [--quick]      (quick ~3 min; full ~15 min)
The 2-adic values J_s are read from python/zeta2_K17000.json (17000 bits), J_odd = 0.
"""
import sys, os, json, math, random, time
from fractions import Fraction as F
from math import factorial, comb, log

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
REF = os.path.join(HERE, 'z7_ref')
sys.path.insert(0, REF)
sys.path.insert(0, HERE)
import vc_engine, vc_common, kernel, levels, cont, qeng, cand   # noqa: E402

QUICK = '--quick' in sys.argv
FAILS = []
NCHECK = [0]
T0 = time.time()
CAND3 = vc_common.CANDS['cand3']


def check(name, cond, info=''):
    NCHECK[0] += 1
    if not cond:
        FAILS.append((name, info))
        print('  FAIL:', name, info, flush=True)
    return cond


def section(t):
    print('\n== %s   [%.0fs]' % (t, time.time() - T0), flush=True)


# ================================================================================================
# 0. helpers
def s_mul(a, b, M):
    c = [F(0)] * M
    for i, x in enumerate(a[:M]):
        if x:
            for j, y in enumerate(b[:M - i]):
                if y:
                    c[i + j] += x * y
    return c


def s_inv(a, M):
    assert a[0] != 0
    b = [F(0)] * M
    b[0] = 1 / F(a[0])
    for i in range(1, M):
        s = F(0)
        for j in range(1, i + 1):
            if j < len(a) and a[j]:
                s += a[j] * b[i - j]
        b[i] = -s / a[0]
    return b


def s_pow(a, e, M):
    r = [F(1)] + [F(0)] * (M - 1)
    for _ in range(e):
        r = s_mul(r, a, M)
    return r


def vq(x, q):
    x = F(x)
    if x == 0:
        return 10 ** 9
    a, b, v = x.numerator, x.denominator, 0
    while a % q == 0:
        a //= q; v += 1
    while b % q == 0:
        b //= q; v -= 1
    return v


def v2int(x):
    x = abs(x)
    if x == 0:
        return 10 ** 9
    return (x & -x).bit_length() - 1


def primes_upto(N):
    if N < 2:
        return []
    s = bytearray([1]) * (N + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


def is_prime(p):
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


def lnabs(x):
    x = F(x)
    return math.log(abs(x.numerator)) - math.log(x.denominator) if x != 0 else float('-inf')


def natlog(b, n):          # Nat.log b n
    if n < b or b <= 1:
        return 0
    k, p = 0, 1
    while p * b <= n:
        p *= b; k += 1
    return k


# ================================================================================================
# 1. Lean-literal definitions (Zeta2Lean/Z7/Defs.lean)
ETA = [5, 7, 7, 9, 11, 13]


def nsub(a, b):                       # natural-number subtraction
    return a - b if a >= b else 0


def block(u, m):                      # Finset.Ico (eta m * u) (40u - eta m * u)
    return range(ETA[m] * u, nsub(40 * u, ETA[m] * u))


def mu(u, c):
    return sum(1 for m in range(6) if c in block(u, m))


def apole(u, k):
    mn = min(k, nsub(40 * u, k))
    if mn < 2 * u:
        return 1
    if mn < 4 * u:
        return 2
    if mn < 6 * u:
        return 3
    return 4


GCACHE = {}


def Gser(u, k, M=5):
    """coefficients 0..M-1 of G_k(eps) = (n - 2k + 2 eps) numSer u (-k) (prod_{j != k} (j-k+eps)^{a_j})^{-1}"""
    key = (u, k, M)
    if key in GCACHE:
        return GCACHE[key]
    n = 40 * u
    num = [F(1)] + [F(0)] * (M - 1)
    for m in range(6):
        for c in block(u, m):
            num = s_mul(num, [F(-k) + F(1, 2) + c, F(1)], M)
    den = [F(1)] + [F(0)] * (M - 1)
    for j in range(n + 1):
        if j != k:
            den = s_mul(den, s_pow([F(j - k), F(1)], apole(u, j), M), M)
    G = s_mul(s_mul([F(n - 2 * k), F(2)], num, M), s_inv(den, M), M)
    GCACHE[key] = G
    return G


def rcoef(u, i, k):
    if 1 <= i <= apole(u, k) and k <= 40 * u:
        return Gser(u, k)[apole(u, k) - i]
    return F(0)


def genCsum(n, r, i):
    return sum((r(i, k) for k in range(n + 1)), F(0))


def AhalfZ(d, s):
    if d >= 0:
        return sum((F(2, 2 * l + 1) ** s for l in range(d)), F(0))
    return -sum(((1 / (F(1, 2) - l)) ** s for l in range(1, -d + 1)), F(0))


def genRhoZ(a, n, m, r):
    return -sum((F(i * (i + 1) * (i + 2) * (i + 3)) * r(i, k) * AhalfZ(k - m, i + 4)
                 for i in range(1, a + 1) for k in range(n + 1)), F(0))


def genIntegrandZ(a, n, m, r, x):
    return sum((F(i * (i + 1) * (i + 2)) * r(i, k) * (1 / (F(x + k - m) + F(1, 2))) ** (i + 3)
                for i in range(1, a + 1) for k in range(n + 1)), F(0))


def rfun(u, table=None):
    if table is not None:
        return lambda i, k: table.get((i, k), F(0))
    return lambda i, k: rcoef(u, i, k)


def csum(u, i, r=None):
    return genCsum(40 * u, r or rfun(u), i)


def rho(u, r=None):
    return genRhoZ(4, 40 * u, 20 * u, r or rfun(u))


def Zc(u, r=None):
    return 46080 * csum(u, 3, r)


def integrand(u, x, r=None):
    return genIntegrandZ(4, 40 * u, 20 * u, r or rfun(u), x)


def Rser(u, y, M=5):
    """coefficients of R_n(y + eps) (y not a pole)"""
    n = 40 * u
    y = F(y)
    num = [F(1)] + [F(0)] * (M - 1)
    for m in range(6):
        for c in block(u, m):
            num = s_mul(num, [y + F(1, 2) + c, F(1)], M)
    den = [F(1)] + [F(0)] * (M - 1)
    for j in range(n + 1):
        den = s_mul(den, s_pow([y + j, F(1)], apole(u, j), M), M)
    return s_mul(s_mul([2 * y + n, F(2)], num, M), s_inv(den, M), M)


def Rnum_at(u, t):
    t = F(t)
    v = 2 * t + 40 * u
    for m in range(6):
        for c in block(u, m):
            v *= t + F(1, 2) + c
    return v


def PFpoly_at(u, t, r):
    t = F(t)
    n = 40 * u
    tot = F(0)
    for k in range(n + 1):
        for i in range(1, apole(u, k) + 1):
            term = r(i, k) * (t + k) ** (apole(u, k) - i)
            for j in range(n + 1):
                if j != k:
                    term *= (t + j) ** apole(u, j)
            tot += term
    return tot


def eq7(u, q, rho_u, Zc_u):
    return max(vq_den(rho_u, q), vq_den(Zc_u, q))


def vq_den(x, q):                     # padicValNat q x.den
    d = F(x).denominator
    v = 0
    while d % q == 0:
        d //= q; v += 1
    return v


# ---- local types -------------------------------------------------------------------------------
def gchoose(e, i):
    num = F(1)
    for t in range(i):
        num *= (e - t)
    return num / factorial(i)


def bser(c, e, M):
    c = F(c)
    return [gchoose(e, i) * c ** i for i in range(M)]


def localModel(u, q, k0):
    n = 40 * u
    items = []
    for j in range(n // q + 1):
        if k0 + j * q <= n:
            items.append((-2 * j, -apole(u, k0 + j * q)))
    for t in range(n // q + 2):
        c = k0 + t * q - (q + 1) // 2
        if 0 <= c < n and mu(u, c) != 0:
            items.append((-(2 * t - 1), mu(u, c)))
    if (2 * k0 - n) % q == 0:             # Int.emod, q > 0
        items.append(((2 * k0 - n) // q, 1))
    pairs = []
    for j in range(n // q + 1):
        d = k0 + j * q - 20 * u
        if k0 + j * q <= n and d != 0:
            sg = 1 if d > 0 else -1
            for t in range(abs(d) // q + 1):
                if (2 * t + 1) * q < 2 * abs(d):
                    pairs.append((-2 * j, -2 * j + sg * (2 * t + 1), sg))
    return tuple(items), tuple(pairs)


def E_(items):
    return sum(e for _, e in items)


def netE(items, w):
    return sum(e for (w2, e) in items if w2 == w)


def rSer(items, M):
    s = [F(1)] + [F(0)] * (M - 1)
    for (w, e) in items:
        s = s_mul(s, bser(F(-w, 2), e, M), M)
    return s


def taylorAt(items, wk, M):
    s = [F(1)] + [F(0)] * (M - 1)
    for (w, e) in items:
        if w == wk:
            continue
        b = F(wk - w, 2)
        s = s_mul(s, [x * b ** e for x in bser(1 / b, e, M)], M)
    return s


def gSer(items, wk, we, M):
    b = F(we - wk, 2)
    return s_mul(taylorAt(items, wk, M), [x * b ** (-5) for x in bser(-1 / b, -5, M)], M)


def ASer(items, pairs, M):
    out = [F(0)] * M
    for (wk, we, sg) in pairs:
        a = max(0, -netE(items, wk))
        if a == 0:
            continue
        g = gSer(items, wk, we, a)
        for i in range(1, a + 1):
            ex = bser(F(-wk, 2), -i, M)
            for l in range(M - i):
                out[i + l] += sg * g[a - i] * ex[l]
    return out


class LT:
    """a LocalType with the Lean functions E, coeffD, LevGe, PoleLevAt, PoleLevGe"""
    CACHE = {}

    def __init__(self, items, pairs, M=26):
        self.items, self.pairs, self.M = items, pairs, M
        self.E = E_(items)
        self._A = None
        self._r = None

    @classmethod
    def get(cls, items, pairs):
        key = (items, pairs)
        if key not in cls.CACHE:
            if len(cls.CACHE) > 20000:
                cls.CACHE.clear()
            cls.CACHE[key] = LT(items, pairs)
        return cls.CACHE[key]

    @property
    def A(self):
        if self._A is None:
            self._A = ASer(self.items, self.pairs, self.M)
        return self._A

    @property
    def r(self):
        if self._r is None:
            self._r = rSer(self.items, self.M)
        return self._r

    def cz(self, which, z):
        if z < 0:
            return F(0)
        f = self.A if which == 'A' else self.r
        assert z < len(f), 'series too short'
        return f[z]

    def coeffD(self, c0, j, c, p):
        return self.cz('A', p - self.E) - c0 * self.cz('r', p) - c * self.cz('r', p - j)

    def LevGe(self, c0, j, c, P):
        return all(self.coeffD(c0, j, c, p) == 0 for p in range(self.E + 1, P))

    def firstNZ(self, c0, j, c, cap):
        for p in range(self.E + 1, cap):
            if self.coeffD(c0, j, c, p) != 0:
                return p
        return cap

    def PoleLevAt(self, wk, T):
        a = -netE(self.items, wk)
        if a <= 0:
            return True
        tay = taylorAt(self.items, wk, a)
        return all(tay[l] == 0 for l in range(a) if self.E - netE(self.items, wk) - T < l)

    def PoleLevGe(self, T):
        return all(self.PoleLevAt(w, T) for (w, _) in self.items)


def negChoose(j, i):
    return (-1) ** i * comb(i + j - 1, i)


def Xk(r, k, o):
    return sum((F(i * (i + 1) * (i + 2) * (i + 3)) * r(i, k) * F(2, o) ** (i + 4) for i in range(1, 5)), F(0))


def oddBetween(d):
    return [2 * l + 1 for l in range(d)] if d >= 0 else [-(2 * l + 1) for l in range(-d)]


def sgn(d):
    return (d > 0) - (d < 0)


def rhoP(u, r):
    return sum((sgn(k - 20 * u) * sum((Xk(r, k, o) for o in oddBetween(k - 20 * u)), F(0))
                for k in range(40 * u + 1)), F(0))


def classBad(u, q, k0, r):
    tot = F(0)
    for k in range(40 * u + 1):
        if k % q == k0:
            d = k - 20 * u
            tot += sgn(d) * sum((Xk(r, k, o) for o in oddBetween(d) if o % q == 0), F(0))
    return tot


def goodPart(u, q, r):
    return sum((sgn(k - 20 * u) * sum((Xk(r, k, o) for o in oddBetween(k - 20 * u) if o % q != 0), F(0))
                for k in range(40 * u + 1)), F(0))


def kerRes(u, q, k0, c0, j, c, r):
    n = 40 * u
    cls = [k for k in range(n + 1) if k % q == k0]
    tot = c0 * sum((r(1, k) for k in cls), F(0))
    if c != 0:
        s1 = sum((r(i, k) * negChoose(j, i - 1) * F(1, k0 - k) ** (i + j - 1)
                  for k in cls if k != k0 for i in range(1, 5)), F(0))
        s2 = sum((r(i, k) * negChoose(i, j - 1) * F(1, k - k0) ** (i + j - 1)
                  for k in range(n + 1) if k != k0 for i in range(1, 5)), F(0))
        tot += c * F(q) ** j * (s1 + s2)
    return tot


def farRes(u, q, k0, j, r):
    n = 40 * u
    return sum((r(i, k) * sum((negChoose(j, i - 1) * F(1, ip - k) ** (i + j - 1) for ip in range(q) if ip != k0), F(0))
                for k in range(n + 1) if k % q == k0 for i in range(1, 5)), F(0))


# ---- the exponent table (DenTable.lean) and growth ----------------------------------------------
def load_table():
    import z7_den_table as zt
    H, _ = zt.head_rows()
    R = zt.res_rows()
    return H, R


def Fx(z):
    return z * math.log(abs(z)) - z if z != 0 else 0.0


UPOT = [(1, 0), (1, 2), (1, 4), (-1, 5), (1, 6), (-2, 7), (-1, 9), (-1, 11), (-1, 13), (1, 27),
        (1, 29), (1, 31), (2, 33), (-1, 34), (1, 35), (-1, 36), (-1, 38), (-1, 40)]


def Upot(kap):
    return sum(w * Fx(p / 40 - kap) for w, p in UPOT)


G7, DELTA7 = 0.71, 3.99


# ================================================================================================
# 2-adic helpers
def load_J(K=17000):
    d = json.load(open(os.path.join(HERE, 'zeta2_K17000.json')))
    J = {}
    for key, v in d.items():
        m = int(key); Z = int(v[0]); sh = int(v[1])
        s = m - 1
        e = v2int(s); so = s >> e
        assert e + m - sh == 0, (m, sh)
        J[s] = (Z * so) % (1 << K)
    for s in range(1, 14, 2):
        J[s] = 0
    return J


def scaled_mod(x, E, K):
    x = F(x)
    num, den = x.numerator, x.denominator
    vd = v2int(den)
    assert E - vd >= 0, (E, vd)
    return (num * pow(2, E - vd, 1 << K) * pow(den >> vd, -1, 1 << K)) % (1 << K)


def v2_lin(rho_, coefs, J, K):
    """v2 of rho + sum_s coefs[s] J_s (J_s mod 2^K); None if 0 to the available precision"""
    E = 0
    for x in [rho_] + list(coefs.values()):
        if x != 0:
            E = max(E, -vq(x, 2))
    MOD = 1 << K
    tot = scaled_mod(rho_, E, K) if rho_ != 0 else 0
    for s, c in coefs.items():
        if c != 0:
            tot = (tot + scaled_mod(c, E, K) * J[s]) % MOD
    if tot == 0:
        return None
    return v2int(tot) - E


def riemann_centred(u, r, N, J, K=3000):
    """v2(R_N - (rho + 60 c3 J6)) for the Lean integrand of cand3 at u, and v2 of the value."""
    n = 40 * u
    w = {}
    for i in range(1, 5):
        for k in range(n + 1):
            rv = r(i, k)
            if rv != 0:
                w[(i, k)] = F(i * (i + 1) * (i + 2)) * rv * F(2) ** (i + 3)
    rh, c3 = rho(u, r), csum(u, 3, r)
    E = max([0] + [-vq(x, 2) for x in list(w.values()) + [rh, c3] if x != 0]) + N
    MOD = 1 << K
    wm = {key: scaled_mod(val, E - N, K) for key, val in w.items()}
    tot = 0
    for x in range(2 ** N):
        for (i, k), val in wm.items():
            tot += val * pow(2 * (x + k - 20 * u) + 1, -(i + 3), MOD)
    tot %= MOD
    L = (scaled_mod(rh, E, K) + scaled_mod(60 * c3, E, K) * J[6]) % MOD
    d = (tot - L) % MOD
    return (None if d == 0 else v2int(d) - E), v2_lin(rh, {6: 60 * c3}, J, K)


def riemann_neg_shift(s, e, N, J, K=600):
    """v2( 2^-N sum_{x<2^N} halfPowZ s (x - e) - (J_s + s sum_{l=1}^e halfPowZ (s+1) (-l)) )"""
    MOD = 1 << K
    # halfPowZ s z = 2^s (2z+1)^-s ; scale everything by 2^(N) (and keep 2^s factors explicit)
    E = N + 5
    tot = 0
    for x in range(2 ** N):
        tot += pow(2 * (x - e) + 1, -s, MOD)
    tot = tot * pow(2, s + E - N, MOD) % MOD                  # 2^E * R_N
    lim = J[s] * pow(2, E, MOD)
    for l in range(1, e + 1):
        lim += s * pow(2, s + 1 + E, MOD) * pow(1 - 2 * l, -(s + 1), MOD)
    d = (tot - lim) % MOD
    return None if d == 0 else v2int(d) - E


# ================================================================================================
def exact_data(u):
    """exact rho_n, c_i (and r_{i,k} for n <= 200) from the reference engine vc_engine"""
    res = vc_engine.compute(CAND3, 40 * u)
    return res


def main():
    random.seed(20260926)
    print('z7_mirror: %s run' % ('quick' if QUICK else 'full'))
    J = load_J()

    # --------------------------------------------------------------------------------------------
    section('construction: blocks, pole orders, degree, symmetry (vs vc_common.build)')
    for u in range(0, 13):
        n = 40 * u
        Nb = sum(len(block(u, m)) for m in range(6))
        SA = sum(apole(u, k) for k in range(n + 1))
        check('N = 136u', Nb == 136 * u, (u, Nb))
        check('sum a = 136u + 4', SA == 136 * u + 4, (u, SA))
        check('apole symmetric', all(apole(u, n - k) == apole(u, k) for k in range(n + 1)))
        check('apole in 1..4', all(1 <= apole(u, k) <= 4 for k in range(n + 1)))
        for m in range(6):
            B = set(block(u, m))
            check('block symmetric', all((n - 1 - c) in B for c in B))
        if u >= 1:
            blocks, a, N, SAr, delta = vc_common.build(CAND3, n)
            check('apole = vc_common', [apole(u, k) for k in range(n + 1)] == a, u)
            mud = vc_common.mu_map(blocks)
            check('mu = vc_common', all(mu(u, c) == mud.get(c, 0) for c in range(-3, n + 3)), u)
            check('delta = 1', delta == 1)
    print('  blocks/profile ok for u = 0..12 (N = 3.4n, sum a = N + 4, deg R = -3)')

    # --------------------------------------------------------------------------------------------
    section('rcoef (Lean-literal Gser) vs vc_engine; PF7; CoeffVanish7; rho, Zc; rho = -rhoP')
    us_small = [1, 2] if QUICK else [1, 2, 3]
    EX = {}
    for u in us_small:
        n = 40 * u
        t0 = time.time()
        res = exact_data(u)
        EX[u] = res
        rv = res['rik']
        ok = all(rcoef(u, i, k) == rv.get((i, k), F(0)) for k in range(n + 1) for i in range(0, 6))
        check('rcoef = vc_engine rik', ok, u)
        r = rfun(u)
        c = [csum(u, i) for i in range(0, 7)]
        check('csum = vc_engine c', all(c[i] == res['c'][i] for i in range(1, 5)), u)
        check('c1 = 0', c[1] == 0); check('c2 = 0', c[2] == 0); check('c4 = 0', c[4] == 0)
        check('c_even = 0', c[0] == 0 and c[6] == 0)
        check('c3 != 0', c[3] != 0)
        check('symm', all(rcoef(u, i, n - k) == (-1) ** (i + 1) * rcoef(u, i, k)
                          for k in range(n + 1) for i in range(0, 6)), u)
        rh = rho(u)
        check('rho = -rho_n (vc_engine)', rh == -res['rho'], u)
        check('Zc = -Z_n (vc_engine)', Zc(u) == -res['Z'], u)
        check('rho = -rhoP', rh == -rhoP(u, r), u)
        # PF7.poly at random rational points (degree 136u+3 identity checked at 5 points; the
        # partial fractions themselves are exact since they come from the Taylor coefficients)
        for _ in range(3):
            t = F(random.randint(-300, 300), random.randint(1, 50))
            check('PF7.poly', Rnum_at(u, t) == PFpoly_at(u, t, r), (u, t))
        # PF7.series at random y
        for _ in range(2):
            y = F(random.randint(-500, 500), random.randint(1, 60))
            if any(y + j == 0 for j in range(n + 1)):
                continue
            lhs = Rser(u, y, 5)
            rhs = [F(0)] * 5
            for k in range(n + 1):
                for i in range(1, 5):
                    rk = rcoef(u, i, k)
                    if rk:
                        ser = s_inv(s_pow([y + k, F(1)], i, 5), 5)
                        rhs = [a + rk * b for a, b in zip(rhs, ser)]
            check('PF7.series', lhs == rhs, (u, y))
        # IntegrandTaylor7
        for x in range(0, 4):
            y = F(x) - 20 * u + F(1, 2)
            check('IntegrandTaylor7', integrand(u, x) == -6 * Rser(u, y, 5)[3], (u, x))
        print('  u=%d (n=%d): rcoef/csum/rho/Zc agree with vc_engine; PF7, CoeffVanish7, IntegrandTaylor7 ok (%.1fs)'
              % (u, n, time.time() - t0))

    # --------------------------------------------------------------------------------------------
    section('TranslationNeg / GenLinearFormZ / L7: 2-adic convergence of the Riemann sums')
    for s in (4, 5, 6, 7):
        for e in (1, 2, 5):
            vals = [riemann_neg_shift(s, e, N, J) for N in (6, 8, 10)]
            check('TranslationNeg convergence', all(v is None or v >= N - 2 for v, N in zip(vals, (6, 8, 10))),
                  (s, e, vals))
    print('  TranslationNeg: v2(R_N - value) >= N - 2 for s = 4..7, e = 1, 2, 5, N = 6, 8, 10')
    for u in ([1] if QUICK else [1, 2]):
        r = rfun(u)
        Ns = (5, 7, 9) if QUICK else (5, 8, 11)
        out = [riemann_centred(u, r, N, J) for N in Ns]
        vS = out[0][1]
        diffs = [o[0] for o in out]
        # convergence: v2(R_N - S) strictly increasing in N (about +2 per step of N)
        check('L7 convergence', None not in diffs and diffs[0] < diffs[1] < diffs[2]
              and diffs[2] - diffs[0] >= Ns[2] - Ns[0], (u, diffs, vS))
        print('  u=%d: v2(S) = %d, v2(R_N - S) = %s for N = %s' % (u, vS, diffs, Ns))

    # --------------------------------------------------------------------------------------------
    section('Valuation7 (Theorem V) and nonvanishing of S_n')
    us_val = list(range(1, 7)) if QUICK else list(range(1, 13))
    DATA = {}
    for u in us_val:
        res = EX.get(u) or exact_data(u)
        DATA[u] = (-res['rho'], -res['Z'], res['c'][3])
        rh, zc, c3 = DATA[u]
        v = v2_lin(rh, {6: F(zc) / 768}, J, 17000)       # S = rho + Zc zeta2(7) = rho + (Zc/768) J6
        lam = natlog(2, 30 * u) + 1
        bound = 272 * u + 7 - 10 * lam
        check('Valuation7 bound', v is not None and v >= bound, (u, v, bound))
        check('Valuation7 (Lean constants)', v is not None and 2.0 ** (-v + 272 * u) <= 4 * 30.0 ** 10 * (u + 1) ** 10)
        print('  n=%4d: v2(S_n) = %5d >= 272u + 7 - 10 lambda = %5d  (S_n != 0)' % (40 * u, v, bound))

    # --------------------------------------------------------------------------------------------
    section('AuxPrime7 (Theorem N) at u with 38u - 1 prime')
    us_aux = [u for u in range(1, 26 if not QUICK else 11) if is_prime(38 * u - 1)]
    for u in us_aux:
        if u in DATA:
            rh, zc, _ = DATA[u]
        else:
            res = exact_data(u)
            rh, zc = -res['rho'], -res['Z']
        l = 38 * u - 1
        vr, vz = vq(rh, l), vq(zc, l)
        check('v_l(rho) = -1', vr == -1, (u, vr))
        check('v_l(Zc) >= 0', vz >= 0, (u, vz))
        # leading term: l * rho = -(6864/7) u0 (mod l), u0 = r_{1,0}/l^4, r_{1,0} = n Num(0)/prod k^{a_k}
        n = 40 * u
        r10 = F(n)
        for m in range(6):
            for c in block(u, m):
                r10 *= F(2 * c + 1, 2)
        for k in range(1, n + 1):
            r10 /= F(k) ** apole(u, k)
        if u in EX:
            check('r_{1,0} formula', r10 == rcoef(u, 1, 0))
        u0 = r10 / F(l) ** 4
        check('u0 unit', vq(u0, l) == 0)
        lhs = F(l) * rh
        diff = lhs + F(6864, 7) * u0
        check('l rho = -(6864/7) u0 mod l', vq(diff, l) >= 1, u)
        print('  n=%4d, l=%4d: v_l(rho) = %d, v_l(Z) = %s, l rho = -(6864/7) u0 (mod l)' % (n, l, vr, vz))

    # --------------------------------------------------------------------------------------------
    section('MaxU7, ResidueBound7, Growth7')
    tm = cand.continuum_terms(cand.CAND3)
    check('upotTerms = cand.continuum_terms', sorted((w, int(p * 40)) for w, p in tm) == sorted(UPOT))
    best = max((Upot(i / 200000), i / 200000) for i in range(200001))
    check('max U <= g7', best[0] <= G7, best)
    check('max U = 0.70670222...', abs(best[0] - 0.7067022242) < 1e-8, best)
    print('  grid max U = %.10f at kappa = %.6f  (target g7 = %.2f)' % (best[0], best[1], G7))
    for u in ([1, 2] if QUICK else [1, 2, 3, 5]):
        n = 40 * u
        if u in EX:
            rv = EX[u]['rik']
        else:
            rv = exact_data(u)['rik']
        worst = max(lnabs(v) - n * Upot(k / n) for (i, k), v in rv.items() if v != 0)
        check('ResidueBound7', worst <= 15 * math.log(u + 1) + 38 + 15 * math.log(40), (u, worst))
        print('  n=%4d: max (log|r_ik| - n U(k/n)) = %.2f   (proved: <= log(n+1) + 14 log n + 37.44 = %.2f)'
              % (n, worst, math.log(n + 1) + 14 * math.log(n) + 37.44))
    for u in us_val:
        rh, zc, _ = DATA[u]
        g = max(lnabs(rh), lnabs(zc)) / (40 * u)
        check('Growth7 (finite n, proved form)', g <= 0.70670223 + (14 * math.log(40 * u) + 2 * math.log(40 * u + 1) + 47.5) / (40 * u), (u, g))
        print('  n=%4d: log max(|rho|, |Z|)/n = %.4f' % (40 * u, g))

    # --------------------------------------------------------------------------------------------
    section('BigPrimes7 / SmallPrimes7 / Emin7 (exact exponents)')
    for u in us_val:
        n = 40 * u
        rh, zc, _ = DATA[u]
        worst = 0.0
        for q in primes_upto(2 * n + 50):
            if q == 2:
                continue
            e = eq7(u, q, rh, zc)
            if q > n:
                check('BigPrimes7', e == 0, (u, q, e))
            lam = natlog(q, 80 * u + 1)
            check('SmallPrimes7', e <= 19 * lam, (u, q, e, lam))
            if lam:
                worst = max(worst, e / (19 * lam))
        for q in [p for p in primes_upto(n + 60) if p >= 5][: (12 if QUICK else 40)]:
            Em = min(E_(localModel(u, q, k0)[0]) for k0 in range(q))
            check('Emin7', Em >= -10, (u, q, Em))
        print('  n=%4d: no odd prime > n divides D; max e_q/(19 lambda) = %.3f; E >= -10 on sampled primes' % (n, worst))

    # --------------------------------------------------------------------------------------------
    section('local models, levels and per-pole data vs the research engines (kernel.py, levels.py)')
    for u in ([2] if QUICK else [2, 5]):
        n = 40 * u
        blocks, ak, N, SAr, delta = vc_common.build(CAND3, n)
        mud = vc_common.mu_map(blocks)
        nt = 0
        for q in [p for p in primes_upto(n) if p >= 5 and p * p > 2 * n + 2 * p]:
            for k0 in range(q):
                items, pairs = localModel(u, q, k0)
                it2, pr2, E2 = kernel.local_items(n, mud, ak, 1, q, k0)
                A1 = sorted((F(w, 2), e) for w, e in items)
                B1 = sorted((F(a, 2), F(b, 2), s) for a, b, s in pairs)
                check('localModel = kernel.local_items', A1 == sorted(it2) and B1 == sorted(pr2), (u, q, k0))
                lt = LT.get(items, pairs)
                L = levels.class_levels_local(it2, pr2, 12)
                valid = L['valid']
                check('coeffD = levels D', all(lt.coeffD(1, 1, 0, p) == L['D'].get(p, F(0))
                                               for p in range(lt.E + 1, valid)), (u, q, k0))
                if pairs:
                    check('La', -5 + lt.firstNZ(0, 1, 0, valid) == L['La'], (u, q, k0))
                check('Lb', -5 + lt.firstNZ(1, 1, 0, valid) == L['Lb'], (u, q, k0))
                if L['LG'] < 10 ** 5:
                    check('PoleLevGe = LG', lt.PoleLevGe(L['LG']) and not lt.PoleLevGe(L['LG'] + 1), (u, q, k0))
                nt += 1
        print('  n=%d: %d classes: localModel, coeffD, L_a, L_b, per-pole levels agree' % (n, nt))

    # --------------------------------------------------------------------------------------------
    section('ClassLemma7 / KernelIdentity7 / FarPart7 (exact, all classes)')
    KERNELS = [(F(0), 1, F(0)), (F(1), 1, F(0)), (F(1), 2, F(-5, 4)), (F(3, 7), 1, F(2))]
    for u in ([2] if QUICK else [2, 5]):
        n = 40 * u
        rv = (EX.get(u) or exact_data(u))['rik']
        r = rfun(u, rv)
        ncl = 0
        for q in [p for p in primes_upto(n) if p >= 5 and p * p > 2 * n + 2 * p]:
            # kernel identity (exact), two kernels
            for (c0, j, c) in [(F(2, 3), 1, F(5)), (F(1), 3, F(-7, 2))]:
                tot = sum((kerRes(u, q, k0, c0, j, c, r) + c * F(q) ** j * farRes(u, q, k0, j, r)
                           for k0 in range(q)), F(0))
                check('KernelIdentity7', tot == 0, (u, q, j))
            # splitting of rhoP
            check('rhoP = sum classBad + goodPart',
                  rhoP(u, r) == sum((classBad(u, q, k0, r) for k0 in range(q)), F(0)) + goodPart(u, q, r), (u, q))
            for k0 in range(q):
                items, pairs = localModel(u, q, k0)
                lt = LT.get(items, pairs)
                bad = classBad(u, q, k0, r)
                for (c0, j, c) in KERNELS:
                    if (c0 != 0 and vq(c0, q) < 0) or (c != 0 and vq(c, q) < 0):
                        continue
                    P = lt.firstNZ(c0, j, c, lt.E + 16)
                    val = bad - 24 * F(1, q ** 5) * kerRes(u, q, k0, c0, j, c, r)
                    check('ClassLemma7', val == 0 or vq(val, q) >= P - 5, (u, q, k0, (c0, j, c), vq(val, q), P - 5))
                    if c != 0 and j + 1 <= q + lt.E:
                        fv = 24 * F(1, q ** 5) * (c * F(q) ** j * farRes(u, q, k0, j, r))
                        check('FarPart7', fv == 0 or vq(fv, q) >= j - 4, (u, q, k0, vq(fv, q)))
                    ncl += 1
        print('  n=%d: %d (class, kernel) tests: class lemma, far part, kernel identity, rho splitting ok' % (n, ncl))

    # --------------------------------------------------------------------------------------------
    section('the exponent table (DenTable.lean): integral, sanity, ThmK7 / HeadCert7 at sample primes')
    H, R = load_table()
    import z7_den_table as zt
    txt = open(os.path.join(HERE, '..', 'Zeta2Lean', 'Z7', 'DenTable.lean'), encoding='utf-8').read()
    nrows = txt.count('\n  ⟨')
    check('DenTable.lean row count', nrows == len(H) + len(R), (nrows, len(H), len(R)))
    head = sum((f * (1 / a - 1 / b) for a, b, f, *_ in H), F(0))
    per = [sum((f * (1 / (a + 40 * t) - 1 / (b + 40 * t)) for a, b, f, *_ in R), F(0)) for t in range(3)]
    Etab = head + sum(per) + F(10, 140)
    check('table integral < delta7', Etab < F(399, 100), float(Etab))
    check('margin g7 + delta7 < 6.8 log 2', G7 + DELTA7 < 6.8 * math.log(2))
    print('  E = %.10f (< delta7 = 3.99); g7 + delta7 = %.2f < 6.8 log 2 = %.6f' % (float(Etab), G7 + DELTA7, 6.8 * math.log(2)))
    for (a, b, f, c0, j, c) in H + R:
        sane = (1 <= j <= 4 and f <= 14 and (c == 0 or f + j >= 4)
                and zt.smooth17(F(c0).denominator) and zt.smooth17(F(c).denominator))
        check('DenRow.sane', sane, (a, b))

    def row_of(x, rows, shift=0):
        for rw in rows:
            if rw[0] + shift <= x < rw[1] + shift:
                return rw
        return None

    # ThmK7 + HeadCert7 at sampled (n, q): all classes satisfy the row certificate; e_q <= f (true e_q)
    ns_head = [200, 960] if QUICK else [200, 960, 2000]
    for n in ns_head:
        u = n // 40
        res = EX.get(u) or exact_data(u)
        rh, zc = -res['rho'], -res['Z']
        nq = 0; eqf = 0
        qs = [p for p in primes_upto(n) if p > 40 and u % p != 0 and p * p > 2 * n + 3 * p and n < 20 * p]
        if QUICK:
            qs = qs[::3]
        for q in qs:
            x = F(n, q)
            rw = row_of(x, H)
            assert rw is not None
            a, b, f, c0, j, c = rw
            ok_lev = ok_pole = True
            for k0 in range(q):
                items, pairs = localModel(u, q, k0)
                lt = LT.get(items, pairs)
                ok_lev = ok_lev and lt.LevGe(c0, j, c, 5 - f)
                ok_pole = ok_pole and lt.PoleLevGe(-f)
            check('HeadCert7 (LevGe)', ok_lev, (n, q, f))
            check('HeadCert7 (PoleLevGe)', ok_pole, (n, q, f))
            e = eq7(u, q, rh, zc)
            check('ThmK7 conclusion (true e_q <= f)', e <= f, (n, q, e, f))
            nq += 1; eqf += (e == f)
        print('  n=%4d: %d primes with x in [1,20): every class satisfies its row certificate; e_q <= f (= at %d)'
              % (n, nq, eqf))

    # ResCert7 at sampled (n, q): E >= 4 - f on [20, 140) (rows shifted by 40 t) and E >= -6 beyond
    ns_res = [4000] if QUICK else [4000, 8000]
    for n in ns_res:
        u = n // 40
        qs = [p for p in primes_upto(n // 20) if p > 40 and u % p != 0 and p * p > 2 * n + 3 * p]
        if QUICK:
            qs = qs[::4]
        nq = 0
        for q in qs:
            x = F(n, q)
            t = max(0, int((x - 20) // 40))
            rw = row_of(x - 40 * t, R)
            assert rw is not None, (n, q)
            f = rw[2]
            Em = min(E_(localModel(u, q, k0)[0]) for k0 in range(q))
            check('ResCert7', Em >= 4 - f, (n, q, Em, f))
            check('tail E >= -6', Em >= -6, (n, q, Em))
            nq += 1
        print('  n=%4d: %d primes with x >= 20: E_min >= 4 - f0(x) (and >= -6)' % (n, nq))
    if not QUICK:
        # far out: n = 180000, x in [260, 300) (shift t = 6 of the period [20, 60)); E only
        u = 4500
        n = 40 * u
        nq = 0
        for q in [p for p in primes_upto(700) if p > 600 and u % p != 0 and p * p > 2 * n + 3 * p]:
            x = F(n, q)
            t = int((x - 20) // 40)
            rw = row_of(x - 40 * t, R)
            Em = min(sum(e for _, e in localModel(u, q, k0)[0]) for k0 in range(q))
            check('ResCert7 (far, periodicity)', Em >= 4 - rw[2], (n, q, Em, rw[2]))
            nq += 1
        print('  n=%d: %d primes with x in [260, 300) (shift t = 6): E_min >= 4 - f0(x - 240)' % (n, nq))

    # true exponents against ExpBounds7 (all fields that apply at these n, with q > 40 in place of 1000)
    section('ExpBounds7 against the true exponents, and log D_n / n')
    for u in us_val:
        n = 40 * u
        rh, zc, _ = DATA[u]
        logD = 0.0
        for q in primes_upto(n):
            if q == 2:
                continue
            e = eq7(u, q, rh, zc)
            logD += e * math.log(q)
            if q >= 29 and 2 * n + 3 * q < q * q:
                check('ExpBounds7.crude', e <= 14, (u, q, e))
                if q > 40 and u % q != 0:
                    x = F(n, q)
                    if x >= 20:
                        check('ExpBounds7.tail', e <= 10, (u, q, e))
                    rw = row_of(x, H) or (row_of(x - 40 * int((x - 20) // 40), R) if x >= 20 and x < 140 else None)
                    if rw is not None:
                        check('ExpBounds7.rows', e <= rw[2], (u, q, e, rw[2]))
        print('  n=%4d: log(odd D_n)/n = %.4f' % (n, logD / n))

    # --------------------------------------------------------------------------------------------
    print('\n%d checks, %d failures, %.0fs' % (NCHECK[0], len(FAILS), time.time() - T0))
    for f in FAILS[:30]:
        print('  ', f)
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
