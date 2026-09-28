"""q-adic engine for the CENTRED form of a nested-block / non-uniform-pole family (cand3 and relatives).

R(t) = (2t+n)^delta prod_blocks prod_{c=lo}^{hi} (t+1/2+c)^mult / prod_{k=0}^{n} (t+k)^{a_k}
S    = int_{Z_2} R^{(3)}(t + 1/2 - n/2) dt = rho + Z zeta_2(7),   Z = -46080 c_3.
rho  = sum_k sgn(d_k) Y_k,  d_k = k - n/2,  Y_k = sum_{h in H_k} X(k,h),
X(k,h) = sum_i r_{i,k} (i)_4 h^{-(i+4)} = 4! [eps^{a_k-1}] G_k(eps) (h-eps)^{-5},  G_k(eps) = eps^{a_k} R(-k+eps),
H_k = half-integers strictly between 0 and d_k.
Everything is computed q-adically: numbers are (v, u, rp) = q^v * u, u a unit known mod q^rp.
Only for primes q >= 5 (Newton identities divide by r <= 3).
"""
import sys
from math import comb

class Q:
    """q-adic number with explicit relative precision."""
    __slots__ = ('v', 'u', 'rp')
    q = 5; P = 60
    def __init__(self, v, u, rp):
        self.v = v; self.u = u; self.rp = rp
    @classmethod
    def setq(cls, q, P=60):
        cls.q = q; cls.P = P
    @classmethod
    def from_int(cls, x, P=None):
        q = cls.q; P = P or cls.P
        if x == 0: return cls(10 ** 6, 0, 0)
        v = 0
        while x % q == 0: x //= q; v += 1
        return cls(v, x % q ** max(P - v, 1), max(P - v, 1))
    @classmethod
    def from_frac(cls, a, b):
        A = cls.from_int(a); B = cls.from_int(b)
        return A / B
    def iszero(self): return self.u == 0
    def __mul__(self, o):
        if isinstance(o, int): o = Q.from_int(o)
        if self.u == 0 or o.u == 0: return Q(self.v + o.v if (self.u == 0 and o.u == 0) else (self.v + o.v), 0, 0)
        rp = min(self.rp, o.rp)
        return Q(self.v + o.v, (self.u * o.u) % Q.q ** rp, rp)
    __rmul__ = __mul__
    def inv(self):
        assert self.u != 0
        m = Q.q ** self.rp
        return Q(-self.v, pow(self.u, -1, m), self.rp)
    def __truediv__(self, o):
        if isinstance(o, int): o = Q.from_int(o)
        return self * o.inv()
    def __neg__(self):
        return Q(self.v, (-self.u) % Q.q ** self.rp if self.rp else 0, self.rp)
    def __add__(self, o):
        if isinstance(o, int): o = Q.from_int(o)
        q = Q.q
        # absolute precisions
        a1 = self.v + self.rp; a2 = o.v + o.rp
        if self.u == 0: a1 = self.v
        if o.u == 0: a2 = o.v
        ap = min(a1, a2)
        v = min(self.v if self.u else ap, o.v if o.u else ap)
        if v >= ap:
            return Q(ap, 0, 0)
        s = 0
        if self.u: s += self.u * q ** (self.v - v)
        if o.u: s += o.u * q ** (o.v - v)
        m = q ** (ap - v); s %= m
        if s == 0: return Q(ap, 0, 0)
        t = 0
        while s % q == 0: s //= q; t += 1
        return Q(v + t, s % q ** (ap - v - t), ap - v - t)
    __radd__ = __add__
    def __sub__(self, o):
        if isinstance(o, int): o = Q.from_int(o)
        return self + (-o)
    def val(self):
        return self.v if self.u else None   # None: zero to the known precision (>= self.v)
    def __repr__(self):
        return 'Q(v=%s,u=%s,rp=%d)' % (self.v, self.u % Q.q if self.u else 0, self.rp)

def vq(x, q):
    if x == 0: return 10 ** 6
    x = abs(x); c = 0
    while x % q == 0: x //= q; c += 1
    return c

def build(cfg, n):
    """cfg: dict(acells=[20 ints], etas=[ints in units of n/40]) -> blocks, ak, delta"""
    assert n % 40 == 0
    blocks = []
    for e in cfg['etas']:
        lo = e * n // 40; hi = n - e * n // 40 - 1
        blocks.append((lo, hi, 1))
    ac = cfg['acells']
    full = list(ac) + list(ac[::-1])
    ak = []
    for k in range(n + 1):
        if 2 * k == n: ak.append(ac[-1])
        elif 2 * k < n: ak.append(full[min(40 * k // n, 19)])
        else: ak.append(ac[min(40 * (n - k) // n, 19)])
    N = sum((hi - lo + 1) * m for lo, hi, m in blocks); SA = sum(ak)
    delta = 1 if (N + SA) % 2 == 0 else 0
    return blocks, ak, delta

CAND3 = dict(acells=[1, 1, 2, 2, 3, 3] + [4] * 14, etas=[5, 7, 7, 9, 11, 13])

class Engine:
    """Precomputes prefix data for a fixed (n, blocks, ak, delta, q)."""
    def __init__(self, n, blocks, ak, delta, q, P=40, F=None):
        Q.setq(q, P)
        self.n, self.blocks, self.ak, self.delta, self.q, self.P = n, blocks, ak, delta, q, P
        qP = q ** P; self.qP = qP
        lo_all = min(b[0] for b in blocks); hi_all = max(b[1] for b in blocks)
        # odd numbers o = 2(c-k)+1 range
        self.M = 2 * max(hi_all, n) + 2 * n + 3
        M = self.M
        Vmax = 0; x = 1
        while x * q <= M: x *= q; Vmax += 1
        self.Vmax = Vmax
        self.F = F if F is not None else 4 * Vmax + 2   # fixed-point shift for power sums (r <= 4)
        Fx = self.F
        # --- odd-number prefix data: index i <-> o = -M + 2i (M odd)
        if M % 2 == 0: M += 1; self.M = M
        L = M + 1
        self.oPS = [[0] * (L + 1) for _ in range(5)]   # r = 1..4: sum of (2/o)^r * q^F  (mod q^P)
        self.oPU = [1] * (L + 1)                          # prod of unit parts of o
        self.oPV = [0] * (L + 1)                          # sum of v_q(o)
        self.oPN = [0] * (L + 1)                          # count of negative o (sign)
        for i in range(L):
            o = -M + 2 * i
            v = vq(o, q); ou = abs(o) // q ** v
            for r in range(1, 5):
                # (2/o)^r q^F = 2^r q^{F - r v} / (sign*ou)^r
                t = pow(2, r, qP) * pow(q, Fx - r * v, qP) * pow((ou if o > 0 else -ou) ** r % qP, -1, qP)
                self.oPS[r][i + 1] = (self.oPS[r][i] + t) % qP
            self.oPU[i + 1] = self.oPU[i] * ou % qP
            self.oPV[i + 1] = self.oPV[i] + v
            self.oPN[i + 1] = self.oPN[i] + (1 if o < 0 else 0)
        # --- integer prefix data for l in [-n, n] \ {0}: index j <-> l = -n + j
        L2 = 2 * n + 1
        self.lPS = [[0] * (L2 + 1) for _ in range(5)]
        self.lPU = [1] * (L2 + 1); self.lPV = [0] * (L2 + 1); self.lPN = [0] * (L2 + 1)
        for j in range(L2):
            l = -n + j
            if l == 0:
                for r in range(1, 5): self.lPS[r][j + 1] = self.lPS[r][j]
                self.lPU[j + 1] = self.lPU[j]; self.lPV[j + 1] = self.lPV[j]; self.lPN[j + 1] = self.lPN[j]
                continue
            v = vq(l, q); lu = abs(l) // q ** v
            for r in range(1, 5):
                t = pow(q, Fx - r * v, qP) * pow((lu if l > 0 else -lu) ** r % qP, -1, qP)
                self.lPS[r][j + 1] = (self.lPS[r][j] + t) % qP
            self.lPU[j + 1] = self.lPU[j] * lu % qP
            self.lPV[j + 1] = self.lPV[j] + v
            self.lPN[j + 1] = self.lPN[j] + (1 if l < 0 else 0)
        # pole cells: maximal runs of constant a
        cells = []; k = 0
        while k <= n:
            k2 = k
            while k2 + 1 <= n and ak[k2 + 1] == ak[k]: k2 += 1
            cells.append((k, k2, ak[k])); k = k2 + 1
        self.cells = cells
        # half-integer good sums: HS[s][D] = sum_{o odd, 1<=o<=2D-1, q not | o} (2/o)^s mod q^P, s = 5..8
        Dm = n // 2 + n + 2
        self.HS = {s: [0] * (Dm + 1) for s in range(5, 9)}
        for s in range(5, 9):
            acc = 0
            for D in range(1, Dm + 1):
                o = 2 * D - 1
                if o % q != 0:
                    acc = (acc + pow(2, s, qP) * pow(pow(o, s, qP), -1, qP)) % qP
                self.HS[s][D] = acc

    def _orange(self, o1, o2):
        """indices for odd o in [o1, o2] (o1 <= o2 odd)"""
        return (o1 + self.M) // 2, (o2 + self.M) // 2 + 1

    def pole_data(self, k):
        """returns (A, z, C0 (Q), E list of Q (Taylor coeffs of Pi up to eps^{A-1}), s_k)"""
        n, q, qP, Fx = self.n, self.q, self.qP, self.F
        A = self.ak[k]
        if A == 0: return None
        ps = [0] * 5          # fixed-point power sums * q^F  (int mod q^P)
        cv = 0; cu = 1; cneg = 0; twos = 0
        for (lo, hi, mult) in self.blocks:
            o1 = 2 * (lo - k) + 1; o2 = 2 * (hi - k) + 1
            i1, i2 = self._orange(o1, o2)
            for r in range(1, A):
                ps[r] = (ps[r] + mult * (self.oPS[r][i2] - self.oPS[r][i1])) % qP
            cv += mult * (self.oPV[i2] - self.oPV[i1])
            cu = cu * pow(self.oPU[i2] * pow(self.oPU[i1], -1, qP) % qP, mult, qP) % qP
            cneg += mult * (self.oPN[i2] - self.oPN[i1])
            twos += mult * (hi - lo + 1)
        # poles
        for (k1, k2, a) in self.cells:
            if a == 0: continue
            j1 = k1 - k + n; j2 = k2 - k + n + 1       # l = k' - k in [k1-k, k2-k]
            for r in range(1, A):
                ps[r] = (ps[r] - a * (self.lPS[r][j2] - self.lPS[r][j1])) % qP
            cv -= a * (self.lPV[j2] - self.lPV[j1])
            cu = cu * pow(pow(self.lPU[j2] * pow(self.lPU[j1], -1, qP) % qP, a, qP), -1, qP) % qP
            cneg += a * (self.lPN[j2] - self.lPN[j1])   # sign of 1/l^a same parity as l^a
        z = 0
        if self.delta:
            if n == 2 * k:
                z = 1; cu = cu * 2 % qP
            else:
                d2 = n - 2 * k
                v = vq(d2, q); du = abs(d2) // q ** v
                cv += v; cu = cu * du % qP
                if d2 < 0: cneg += 1
                # factor (1 + eps/beta), beta = d2/2
                for r in range(1, A):
                    t = pow(2, r, qP) * pow(q, Fx - r * v, qP) * pow((du if d2 > 0 else -du) ** r % qP, -1, qP)
                    ps[r] = (ps[r] + t) % qP
        # constant C0 = prod beta^e ; numerator betas carry 1/2 each
        cu = cu * pow(pow(2, twos, qP), -1, qP) % qP
        if cneg % 2: cu = (-cu) % qP
        C0 = Q(cv, cu, self.P)
        # power sums as Q numbers: p_r = ps[r] / q^F
        p = [None] + [Q.from_int(ps[r]) * Q(-Fx, 1, self.P) if ps[r] else Q(10 ** 6, 0, 0) for r in range(1, 5)]
        # Newton: E_m = (1/m) sum_{r=1}^m (-1)^{r-1} p_r E_{m-r}
        E = [Q(0, 1, self.P)]
        for m in range(1, A):
            tot = None
            for r in range(1, m + 1):
                term = p[r] * E[m - r]
                if r % 2 == 0: term = -term
                tot = term if tot is None else tot + term
            E.append(tot / m)
        return A, z, C0, E, cv

    def r_coeffs(self, k):
        """Laurent coefficients r_{i,k} (i = 1..A) as Q numbers."""
        pdat = self.pole_data(k)
        if pdat is None: return {}
        A, z, C0, E, s = pdat
        out = {}
        for i in range(1, A + 1):
            idx = A - i - z
            out[i] = C0 * E[idx] if idx >= 0 else Q(10 ** 6, 0, 0)
        return out

    def X_bad(self, k, r, h2):
        """X(k,h) for h = h2/2 (h2 odd, possibly q-divisible), from Laurent coeffs r (dict i->Q)."""
        tot = None
        H = Q.from_int(h2) / 2
        hinv = H.inv()
        for i, rik in r.items():
            if rik.u == 0: continue
            poch = i * (i + 1) * (i + 2) * (i + 3)
            pw = Q(0, 1, self.P)
            for _ in range(i + 4): pw = pw * hinv
            term = rik * poch * pw
            tot = term if tot is None else tot + term
        return tot if tot is not None else Q(10 ** 6, 0, 0)

    def pole_terms(self, k, m=None):
        """returns dict with r, sgn, good (Q), bad list [(h2, Q)], total Y (Q)"""
        n, q = self.n, self.q
        if m is None: m = n // 2
        r = self.r_coeffs(k)
        d = k - m
        out = dict(k=k, r=r, d=d)
        if d == 0 or not r:
            out['sgn'] = 0; out['good'] = Q(10 ** 6, 0, 0); out['bad'] = []; out['Y'] = Q(10 ** 6, 0, 0)
            return out
        sg = 1 if d > 0 else -1; D = abs(d)
        good = None
        for i, rik in r.items():
            if rik.u == 0: continue
            s = i + 4
            hs = Q.from_int(self.HS[s][D])
            if sg < 0 and s % 2 == 1: hs = -hs
            poch = i * (i + 1) * (i + 2) * (i + 3)
            term = rik * poch * hs
            good = term if good is None else good + term
        if good is None: good = Q(10 ** 6, 0, 0)
        bad = []
        o = q
        while o <= 2 * D - 1:
            if o % 2 == 1:
                bad.append((sg * o, self.X_bad(k, r, sg * o)))
            o += q
        Y = good
        for _, xb in bad: Y = Y + xb
        out.update(sgn=sg, good=good, bad=bad, Y=Y)
        return out

def vstr(x):
    v = x.val()
    return ('>=%d' % x.v) if v is None else str(v)

def analyse(n, cfg, q, P=40, verbose=False):
    blocks, ak, delta = build(cfg, n)
    eng = Engine(n, blocks, ak, delta, q, P=P)
    rho = Q(10 ** 6, 0, 0); c3 = Q(10 ** 6, 0, 0)
    rows = []
    for k in range(n + 1):
        pt = eng.pole_terms(k)
        if pt['r'].get(3) is not None: c3 = c3 + pt['r'][3]
        if pt['sgn']:
            contrib = pt['Y'] if pt['sgn'] > 0 else -pt['Y']
            rho = rho + contrib
        rows.append(pt)
    return eng, rho, c3, rows

if __name__ == '__main__':
    n = int(sys.argv[1]); q = int(sys.argv[2])
    eng, rho, c3, rows = analyse(n, CAND3, q)
    print('n=%d q=%d x=%.4f  v(rho)=%s v(c3)=%s' % (n, q, n / q, vstr(rho), vstr(c3)))
