#!/usr/bin/env python3
"""z7_audit.py -- independent adversarial audit of Zeta2Lean/Z7/{Defs,Statements,DenTable}.lean.

Standard library only.  Shares NO code with python/z7_mirror.py; the research engines of python/z7_ref/ are
used only as a source of exact partial-fraction data (vc_engine) where stated.  Every Lean definition used
below is re-transcribed from Zeta2Lean/Z7/Defs.lean.

Sections (select with arguments; default: all):
  table   DenTable structure: rows chain [1,20) and [20,60); endpoints = the candidate set
          C = U_{d<=40} (20/d)Z; residue maximum f0 = 10; exact integral; the Lean fixed-point bound.
  cont    CONTINUUM verification of Stmt_HeadCert7 / Stmt_ResCert7 for ALL u: for every row [a,b) and three
          rational x in (a,b), all continuum local types T(x) (the type in every gap of a superset of the event
          points y = frac(b x/40 + e), b = 0..40, e in {0,1/2}, and the type AT every e = 0 event point, where
          discrete classes may sit) satisfy the row certificate (LevGe (5-f) with the row kernel, PoleLevGe (-f);
          residue rows: E >= 4 - f, also at x + 40t, t <= 3); T(x) is the same set at the three x (Lemma 4.10).
  disc    DISCRETE sampling in the statement's domain (q > 1000 prime, q not | u, q^2 > 80u + 3q): the literal
          localModel of every class equals the continuum model at (n/q, k0/q), lies in T(x_mid) of its row
          (Lemma 4.11), and satisfies the row certificate.
  exact   exact valuation tests at n = 80, 200, 280, 400 (every prime q >= 5 with q^2 > 2n + 2q):
          Stmt_PerPole7 (direct: largest T with PoleLevAt, then v_q(r_ik) >= T), Stmt_FarPart7 (j = 1..6),
          Stmt_ClassLemma7 (kernels 0, 1, 1 - (5/4)y^2 and 3 random q-integral kernels, at the LARGEST P
          allowed by LevGe), Stmt_ThmK7 as an implication (best T per kernel -> true e_q <= -T),
          rho = -rhoP and its class splitting.  r_{i,k} from an independent exact engine (own code, equal to
          vc_engine's), class sums evaluated q-adically (checked against exact Fractions at n = 80).
  emin    Stmt_Emin7 for all primes 5 <= q <= 2n+50 and all classes, u <= 60 (literal localModel).
  primes  n = 40 .. 800 (own exact engine): Stmt_BigPrimes7, Stmt_SmallPrimes7, ExpBounds7.crude/tail on the
          exact exponents; Stmt_CoeffVanish7 (symm, c1 = c2 = c4 = 0); Stmt_ResidueBound7 and Stmt_Growth7 in
          their proved per-n forms; Stmt_AuxPrime7 at l = 38u - 1 prime; upotTerms re-derived from the profile.
  truth   ExpBounds7.rows/tail/crude against the research verifier's TRUE exponents (q-adic, n <= 200000);
          needs VERIF_DIR = .../verify-denominators-theory/data (skipped otherwise).
  bigj    Stmt_ClassLemma7 with kernel orders j in {5, 6, 8, 11} (exact Fractions, n = 80, 200).

usage: python3 python/z7_audit.py [table] [cont] [disc] [exact] [emin] [primes] [truth] [bigj] [--jobs N] [--quick]
       [--exact-u 1,3,4,6]   (the u-list of the exact section; default 2,5,7,10)
Full run (2026-09-26, 30 jobs): python/z7_audit_full.log.
"""
import sys, os, math, random, time, json, itertools
from fractions import Fraction as Fr
from math import comb, factorial
from collections import defaultdict

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
FAILS = []
NCHK = [0]
T0 = time.time()
ARGS = [a for a in sys.argv[1:] if not a.startswith('--')]
QUICK = '--quick' in sys.argv
JOBS = 1
EXACT_U = None
for i, a in enumerate(sys.argv):
    if a == '--jobs':
        JOBS = int(sys.argv[i + 1])
        ARGS = [x for x in ARGS if x != sys.argv[i + 1]]
    if a == '--exact-u':
        EXACT_U = [int(z) for z in sys.argv[i + 1].split(',')]
        ARGS = [x for x in ARGS if x != sys.argv[i + 1]]


def check(name, cond, info=''):
    NCHK[0] += 1
    if not cond:
        FAILS.append((name, info))
        print('  ** FAIL:', name, info, flush=True)
    return cond


def section(t):
    print('\n== %s   [%.0fs]' % (t, time.time() - T0), flush=True)


def vq(x, q):
    x = Fr(x)
    if x == 0:
        return 10 ** 9
    a, b, v = abs(x.numerator), x.denominator, 0
    while a % q == 0:
        a //= q; v += 1
    while b % q == 0:
        b //= q; v -= 1
    return v


def sieve(N):
    if N < 2:
        return []
    s = bytearray([1]) * (N + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


def isprime(p):
    if p < 2:
        return False
    for d in (2, 3, 5, 7, 11, 13):
        if p % d == 0:
            return p == d
    d = 17
    while d * d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


# =====================================================================================================
# Lean definitions (Zeta2Lean/Z7/Defs.lean), re-transcribed
ETA = (5, 7, 7, 9, 11, 13)


def nsub(a, b):
    return a - b if a >= b else 0


def apole(u, k):
    m = min(k, nsub(40 * u, k))
    return 1 if m < 2 * u else 2 if m < 4 * u else 3 if m < 6 * u else 4


def in_block(u, m, c):                    # c in Finset.Ico (eta m * u) (40u - eta m * u)
    return ETA[m] * u <= c < nsub(40 * u, ETA[m] * u)


def mu(u, c):
    return sum(1 for m in range(6) if in_block(u, m, c))


def local_model(u, q, k0):
    """literal transcription of localModel u q k0 (items, pairs) as sorted tuples"""
    n = 40 * u
    items = []
    for j in range(n // q + 1):
        if k0 + j * q <= n:
            items.append((-2 * j, -apole(u, k0 + j * q)))
    for t in range(n // q + 2):
        c = k0 + t * q - (q + 1) // 2           # Int: (q+1)/2 exact (q odd)
        if 0 <= c < n and mu(u, c) != 0:
            items.append((-(2 * t - 1), mu(u, c)))
    if (2 * k0 - n) % q == 0:
        items.append(((2 * k0 - n) // q, 1))
    pairs = []
    for j in range(n // q + 1):
        d = k0 + j * q - 20 * u
        if k0 + j * q <= n and d != 0:
            sg = 1 if d > 0 else -1
            for t in range(abs(d) // q + 1):
                if (2 * t + 1) * q < 2 * abs(d):
                    pairs.append((-2 * j, -2 * j + sg * (2 * t + 1), sg))
    return tuple(sorted(items)), tuple(sorted(pairs))


def cont_model(x, y):
    """continuum local model at (x, y), y in [0,1) (proof section 4.8 dictionary, discrete conventions):
    poles j >= 0 with y + j <= x, order by min(y+j, x-y-j) < x/20, x/10, 3x/20 (else 4); zeros v = -s/2
    (s odd) with multiplicity #{m : eta_m x < y + s/2 < (1-eta_m) x}; delta at y = x/2 mod 1; bad pairs
    sigma odd < 2|y + j - x/2|."""
    x, y = Fr(x), Fr(y)
    items = []
    j = 0
    while y + j <= x:
        z = y + j
        m = min(z, x - z)
        a = 1 if 20 * m < x else 2 if 10 * m < x else 3 if 20 * m < 3 * x else 4
        items.append((-2 * j, -a))
        j += 1
    npoles = j
    s = -1
    while True:
        z = y + Fr(s, 2)
        if 40 * z >= (40 - ETA[0]) * x:
            break
        mult = sum(1 for e in ETA if e * x < 40 * z < (40 - e) * x)
        if mult:
            items.append((-s, mult))
        s += 2
    dc = x / 2 - y
    if dc.denominator == 1 and dc >= 0:
        items.append((-2 * int(dc), 1))
    pairs = []
    for j in range(npoles):
        d = y + j - x / 2
        if d != 0:
            sg = 1 if d > 0 else -1
            sig = 1
            while sig < 2 * abs(d):
                pairs.append((-2 * j, -2 * j + sg * sig, sg))
                sig += 2
    return tuple(sorted(items)), tuple(sorted(pairs))


# ---- series helpers (lists of Fractions, truncated) ------------------------------------------------
BINC = {}


def gbin(e, l):                            # generalised binomial C(e, l), e in Z
    key = (e, l)
    v = BINC.get(key)
    if v is None:
        num = 1
        for t in range(l):
            num *= (e - t)
        v = Fr(num, factorial(l))
        BINC[key] = v
    return v


def smul(a, b, M):
    c = [Fr(0)] * M
    for i in range(min(len(a), M)):
        ai = a[i]
        if ai:
            for j in range(min(len(b), M - i)):
                if b[j]:
                    c[i + j] += ai * b[j]
    return c


class LType:
    """a LocalType (items (w, e), pairs (wk, we, sg); doubled coordinates) with the Lean predicates"""

    def __init__(self, items, pairs):
        self.items, self.pairs = items, pairs
        self.E = sum(e for _, e in items)
        self.net = defaultdict(int)
        for w, e in items:
            self.net[w] += e
        self._r = {}
        self._A = {}
        self._tay = {}

    def r(self, M):                         # rSer: prod (1 - (w/2) y)^e
        if M not in self._r:
            s = [Fr(1)] + [Fr(0)] * (M - 1)
            for w, e in self.items:
                v = Fr(w, 2)
                s = smul(s, [gbin(e, l) * (-v) ** l for l in range(M)], M)
            self._r[M] = s
        return self._r[M]

    def taylor(self, wk, M):                # taylorAt: prod_{w != wk} ((wk - w)/2 + u)^e
        key = (wk, M)
        if key not in self._tay:
            s = [Fr(1)] + [Fr(0)] * (M - 1)
            for w, e in self.items:
                if w == wk:
                    continue
                b = Fr(wk - w, 2)
                be = b ** e
                s = smul(s, [be * gbin(e, l) * b ** (-l) for l in range(M)], M)
            self._tay[key] = s
        return self._tay[key]

    def A(self, M):                         # ASer = A_tau(1/y) as a series in y
        if M not in self._A:
            out = [Fr(0)] * M
            for wk, we, sg in self.pairs:
                a = -self.net[wk]
                if a <= 0:
                    continue
                tau = self.taylor(wk, a)
                b = Fr(we - wk, 2)
                h = [comb(r + 4, 4) * b ** (-5 - r) for r in range(a)]   # (b - u)^{-5}
                g = smul(tau, h, a)
                vk = Fr(wk, 2)
                for i in range(1, a + 1):
                    co = sg * g[a - i]
                    if co == 0:
                        continue
                    for l in range(0, M - i):
                        out[i + l] += co * comb(i + l - 1, l) * vk ** l
            self._A[M] = out
        return self._A[M]

    def coeffD(self, c0, j, c, p, M):
        def cz(f, z):
            return f[z] if z >= 0 else Fr(0)
        A, r = self.A(M), self.r(M)
        return cz(A, p - self.E) - c0 * cz(r, p) - c * cz(r, p - j)

    def levge(self, c0, j, c, P):
        lo = self.E + 1
        if P <= lo:
            return True
        M = max(P - self.E, P) + 1
        return all(self.coeffD(c0, j, c, p, M) == 0 for p in range(lo, P))

    def first_nz(self, c0, j, c, cap):
        M = max(cap - self.E, cap) + 1
        for p in range(self.E + 1, cap):
            if self.coeffD(c0, j, c, p, M) != 0:
                return p
        return cap

    def polelev_at(self, wk, T):
        a = -self.net[wk]
        if a <= 0:
            return True
        ls = [l for l in range(a) if self.E + a - T < l]
        if not ls:
            return True
        tau = self.taylor(wk, a)
        return all(tau[l] == 0 for l in ls)

    def polelevge(self, T):
        return all(self.polelev_at(w, T) for w, _ in self.items)

    def max_polelev(self, lo=-40):
        """largest T with PoleLevGe T (T in [lo, 40])"""
        T = lo
        while T < 40 and self.polelevge(T + 1):
            T += 1
        return T


LTC = {}


def ltype(items, pairs):
    key = (items, pairs)
    t = LTC.get(key)
    if t is None:
        if len(LTC) > 200000:
            LTC.clear()
        t = LType(items, pairs)
        LTC[key] = t
    return t


# ---- the table (python/z7_den_table.py is only used to read the Lean file's rows) ------------------
def parse_q(s):
    s = s.strip()
    if '/' in s:
        a, b = s.split('/')
        return Fr(int(a.strip()), int(b.strip()))
    return Fr(int(s))


def lean_rows():
    """parse headRows7 and resRows7 directly from Zeta2Lean/Z7/DenTable.lean"""
    txt = open(os.path.join(ROOT, 'Zeta2Lean', 'Z7', 'DenTable.lean'), encoding='utf-8').read()
    out = {}
    for name in ('headRows7', 'resRows7'):
        i = txt.index('def %s : List DenRow := [' % name)
        j = txt.index('\n]', i)
        rows = []
        for line in txt[i:j].split('\n')[1:]:
            line = line.strip().rstrip(',')
            if not line.startswith('⟨'):
                continue
            f = [z for z in line[1:-1].split(',')]
            an, ad, bn, bd, ff = (int(z) for z in f[:5])
            c0, jj, c = parse_q(f[5]), int(f[6]), parse_q(f[7])
            rows.append((Fr(an, ad), Fr(bn, bd), ff, c0, jj, c, (an, ad, bn, bd)))
        out[name] = rows
    return out['headRows7'], out['resRows7']


def cand_points(lo, hi):
    pts = set()
    for d in range(1, 41):
        m0 = math.ceil(Fr(lo) * d / 20)
        m = m0
        while Fr(20 * m, d) <= hi:
            pts.add(Fr(20 * m, d))
            m += 1
    return sorted(p for p in pts if lo <= p <= hi)


# =====================================================================================================
def sec_table():
    section('table: structure of DenTable.lean (independent parse), candidate set, integral')
    H, R = lean_rows()
    check('469 head rows', len(H) == 469, len(H))
    check('980 residue rows', len(R) == 980, len(R))
    for rows, lo, hi, nm in ((H, 1, 20, 'head'), (R, 20, 60, 'res')):
        check('%s chain start' % nm, rows[0][0] == lo)
        check('%s chain end' % nm, rows[-1][1] == hi)
        check('%s chain' % nm, all(r1[1] == r2[0] for r1, r2 in zip(rows, rows[1:])))
        check('%s a < b' % nm, all(r[0] < r[1] for r in rows))
        pts = cand_points(lo, hi)
        ends = [r[0] for r in rows] + [rows[-1][1]]
        check('%s endpoints = candidate set C' % nm, ends == pts, (len(ends), len(pts)))
    check('residue f0 max = 10', max(r[2] for r in R) == 10, max(r[2] for r in R))
    check('residue kernels trivial', all(r[3] == 0 and r[4] == 1 and r[5] == 0 for r in R))
    kinds = defaultdict(int)
    for r in H:
        kinds[(r[3] != 0, r[4], r[5] != 0)] += 1
    print('  head kernel kinds (c0 != 0, j, c != 0):', dict(kinds))
    # the kernel with c != 0: only j = 2, c = -5/4 on [2, 20/9)
    far = [r for r in H if r[5] != 0]
    check('far-part rows', all(r[4] == 2 and r[5] == Fr(-5, 4) and Fr(2) <= r[0] and r[1] <= Fr(20, 9)
                               for r in far) and len(far) == 6, len(far))
    # exact integral and the Lean fixed-point statement
    head = sum((r[2] * (1 / r[0] - 1 / r[1]) for r in H), Fr(0))
    res = sum((r[2] * (1 / (r[0] + 40 * t) - 1 / (r[1] + 40 * t)) for r in R for t in range(3)), Fr(0))
    E = head + res + Fr(10, 140)
    check('head integral = 51/20 + 2989163/2882880', head == Fr(51, 20) + Fr(2989163, 2882880))
    check('E < 3.99', E < Fr(399, 100), float(E))
    S = 10 ** 15
    rows_all = [r[6] for r in H] + [r[6] for r in R]
    rows_all += [(an + 40 * t * ad, ad, bn + 40 * t * bd, bd) for t in (1, 2) for (_, _, _, _, _, _, (an, ad, bn, bd)) in R]
    fs = [r[2] for r in H] + [r[2] for r in R] * 3
    U = sum(f * ((S * ad + an - 1) // an - (S * bd) // bn) for f, (an, ad, bn, bd) in zip(fs, rows_all))
    lhs = U + (10 * S + 139) // 140
    check('Lean denTable7_integral_fixed holds', lhs <= 399 * S // 100, (lhs, 399 * S // 100))
    print('  E = %.10f; fixed point lhs = %d <= %d; margin to 3.99: %.4f' % (float(E), lhs, 399 * S // 100,
                                                                                3.99 - float(E)))
    # E - with the table's own f: what if the far part (j=2 rows) were dropped (f+1) ?
    Ef = E + sum((1 / r[0] - 1 / r[1] for r in far), Fr(0))
    print('  without the far part (the six j = 2 rows at f + 1): E = %.10f' % float(Ef))


# ---- continuum ---------------------------------------------------------------------------------------
def frac(z):
    return z - math.floor(z)


def cont_types(x):
    """T(x): types in all gaps of the event superset and at all e = 0 event points (with labels)"""
    ev = set([Fr(0)])
    for b in range(41):
        ev.add(frac(Fr(b, 40) * x))
        ev.add(frac(Fr(b, 40) * x + Fr(1, 2)))
    ev = sorted(ev)
    types = {}
    for i, y in enumerate(ev):
        y2 = ev[i + 1] if i + 1 < len(ev) else Fr(1)
        ym = (y + y2) / 2
        types.setdefault(cont_model(x, ym), ('gap', ym))
    for b in range(41):
        y = frac(Fr(b, 40) * x)
        types.setdefault(cont_model(x, y), ('pt', b, y))
    return types


def interior_points(a, b):
    return [(a + b) / 2, a + (b - a) / 3, a + 2 * (b - a) / 3 + Fr(1, 10 ** 7)]


def head_row_job(args):
    idx, (a, b, f, c0, j, c, _) = args
    out = {'idx': idx, 'fails': [], 'ntypes': 0}
    sets = []
    for x in interior_points(a, b):
        T = cont_types(x)
        sets.append(set(T))
        for key, lab in T.items():
            t = ltype(*key)
            if not t.levge(c0, j, c, 5 - f):
                out['fails'].append(('LevGe', float(x), lab, f, str(c0), j, str(c)))
            if not t.polelevge(-f):
                out['fails'].append(('PoleLevGe', float(x), lab, f))
        out['ntypes'] = max(out['ntypes'], len(T))
    if not (sets[0] == sets[1] == sets[2]):
        out['fails'].append(('constancy', float(a), float(b), [len(s) for s in sets],
                             len(sets[0] ^ sets[1]), len(sets[0] ^ sets[2])))
    return out


def res_row_job(args):
    idx, (a, b, f, c0, j, c, _) = args
    out = {'idx': idx, 'fails': [], 'Emin': None}
    base = None
    for t in range(4):
        sets = []
        for x in interior_points(a + 40 * t, b + 40 * t):
            T = cont_types(x)
            Es = sorted(sum(e for _, e in key[0]) for key in T)
            sets.append(set(T))
            if Es[0] < 4 - f:
                out['fails'].append(('E >= 4 - f', float(x), Es[0], f))
            if base is None:
                base = Es[0]
                out['Emin'] = base
            elif Es[0] != base:
                out['fails'].append(('periodic Emin', float(x), Es[0], base))
        if not (sets[0] == sets[1] == sets[2]):
            out['fails'].append(('constancy', float(a + 40 * t), float(b + 40 * t)))
    if max(0, 4 - base) != f:
        out['fails'].append(('f0 = max(0, 4 - Emin)', float(a), base, f))
    return out


def run_jobs(fn, items):
    if JOBS > 1:
        from multiprocessing import Pool
        with Pool(JOBS) as pool:
            return pool.map(fn, items, chunksize=1)
    return [fn(it) for it in items]


def sec_cont():
    section('continuum verification of HeadCert7 (469 rows) and ResCert7 (980 rows x 4 shifts)')
    H, R = lean_rows()
    hr = H if not QUICK else H[::10]
    res = run_jobs(head_row_job, list(enumerate(hr)))
    nt = 0
    for o in res:
        nt = max(nt, o['ntypes'])
        for fl in o['fails']:
            check('HeadCert7 continuum', False, (o['idx'],) + fl)
    check('head rows verified', True)
    print('  head rows: %d rows x 3 points, max %d types per x, %d failures'
          % (len(hr), nt, sum(len(o['fails']) for o in res)))
    # fallback without the far part (Lemma 4.5): the six j = 2 rows with f + 1 and the kernel kappa = 1
    nfb = 0
    for (a, b, f, c0, j, c, _) in H:
        if c != 0:
            for x in interior_points(a, b):
                for key in cont_types(x):
                    t = ltype(*key)
                    check('fallback kappa = 1 at f + 1', t.levge(Fr(1), 1, Fr(0), 5 - (f + 1)) and t.polelevge(-(f + 1)),
                          (float(a), float(b), f))
                    nfb += 1
    print('  fallback without the far part: the six [2, 20/9) rows certify f + 1 with kappa = 1 (%d type checks)'
          % nfb)
    rr = R if not QUICK else R[::20]
    res = run_jobs(res_row_job, list(enumerate(rr)))
    for o in res:
        for fl in o['fails']:
            check('ResCert7 continuum', False, (o['idx'],) + fl)
    print('  residue rows: %d rows x 3 points x shifts t = 0..3, %d failures; Emin range %s'
          % (len(rr), sum(len(o['fails']) for o in res),
             (min(o['Emin'] for o in res), max(o['Emin'] for o in res))))


# ---- discrete sampling -----------------------------------------------------------------------------
def disc_job(args):
    kind, ridx, row, u, q, Tmid = args
    a, b, f, c0, j, c, _ = row
    x = Fr(40 * u, q)
    out = {'fails': [], 'ntypes': 0}
    seen = set()
    for k0 in range(q):
        key = local_model(u, q, k0)
        if key in seen:
            continue
        seen.add(key)
        ck = cont_model(x, Fr(k0, q))
        if ck != key:
            out['fails'].append(('localModel = cont_model', u, q, k0))
        if Tmid is not None and key not in Tmid:
            out['fails'].append(('discrete type in T(x_mid)', kind, ridx, u, q, k0))
        t = ltype(*key)
        if kind == 'head':
            if not t.levge(c0, j, c, 5 - f):
                out['fails'].append(('HeadCert7 LevGe', u, q, k0, f))
            if not t.polelevge(-f):
                out['fails'].append(('HeadCert7 PoleLevGe', u, q, k0, f))
        else:
            if t.E < 4 - f:
                out['fails'].append(('ResCert7', u, q, k0, t.E, f))
    out['ntypes'] = len(seen)
    return out


def pick_uq(a, b, rng, qlo, qhi, tries=4000):
    for _ in range(tries):
        q = rng.randrange(qlo, qhi) | 1
        if not isprime(q):
            continue
        ulo = math.ceil(a * q / 40)
        uhi = math.ceil(b * q / 40) - 1          # 40u/q < b
        if uhi < ulo:
            continue
        u = rng.randrange(ulo, uhi + 1)
        if u % q == 0 or 80 * u + 3 * q >= q * q:
            continue
        x = Fr(40 * u, q)
        if a <= x < b:
            return u, q
    return None


def sec_disc():
    section('discrete sampling in the statement domain (q > 1000, q not | u): Lemma 4.11 + certificates')
    rng = random.Random(20260926)
    H, R = lean_rows()
    jobs = []
    per = 1 if QUICK else 2
    for ridx, row in enumerate(H):
        a, b = row[0], row[1]
        Tmid = set(cont_types((a + b) / 2))
        for s in range(per):
            uq = pick_uq(a, b, rng, 1001, 4001 if s == 0 else 9001)
            if uq:
                jobs.append(('head', ridx, row, uq[0], uq[1], Tmid))
    nh = len(jobs)
    for ridx, row in enumerate(R):
        if QUICK and ridx % 5:
            continue
        a, b = row[0], row[1]
        t = rng.randrange(0, 3)
        Tmid = set(cont_types((a + b) / 2 + 40 * t))
        uq = pick_uq(a + 40 * t, b + 40 * t, rng, 1001, 3001)
        if uq:
            jobs.append(('res', ridx, row, uq[0], uq[1], Tmid))
    print('  %d head samples, %d residue samples' % (nh, len(jobs) - nh), flush=True)
    res = run_jobs(disc_job, jobs)
    nf = 0
    for o in res:
        for fl in o['fails']:
            nf += 1
            if nf < 40:
                check('discrete', False, fl)
    check('discrete sampling', nf == 0, nf)
    print('  %d (u, q) samples, all classes: %d failures; max distinct types per sample %d'
          % (len(res), nf, max(o['ntypes'] for o in res)))


# ---- exact engine (own code) --------------------------------------------------------------------------
def exact_r(u):
    """exact r_{i,k} (dict), rho (Lean sign), csum_3 for n = 40u: own implementation.
    G_k(eps) = G_k(0) exp(sum_r (-1)^{r+1} p_r eps^r / r),  p_r = sum_beta e_beta beta^{-r};
    at the centre k = 20u: G = 2 eps H(eps)."""
    n = 40 * u
    ap = [apole(u, k) for k in range(n + 1)]
    muc = [mu(u, c) for c in range(n)]
    L = 1
    for m in range(1, 2 * n + 2):
        L = L * m // math.gcd(L, m)
    # prefix power sums for odd o = 2(c-k)+1 in [-2n-1, 2n-1]: weight mu(c); and for pole offsets
    r_out = {}
    fact = [1] * (n + 2)
    for i in range(1, n + 2):
        fact[i] = fact[i - 1] * i
    for k in range(n + 1):
        centre = (2 * k == n)
        P = [0, 0, 0, 0]
        G0num, G0den = 1, 1
        # numerator factors (c - k + 1/2 + eps) = (o + 2 eps)/2, o = 2(c-k)+1 : beta = o/2, 1/beta = 2/o
        for c in range(n):
            m_ = muc[c]
            if m_:
                o = 2 * (c - k) + 1
                w = 2 * L // o
                pw = 1
                for rr in (1, 2, 3):
                    pw *= w
                    P[rr] += m_ * pw
                G0num *= o ** m_
                G0den *= 2 ** m_
        for jj in range(n + 1):
            if jj != k:
                w = L // (jj - k)
                pw = 1
                for rr in (1, 2, 3):
                    pw *= w
                    P[rr] -= ap[jj] * pw
                d = (jj - k) ** ap[jj]
                if d < 0:
                    G0num, d = -G0num, -d
                G0den *= d
        if not centre:
            w = 2 * L // (n - 2 * k)
            pw = 1
            for rr in (1, 2, 3):
                pw *= w
                P[rr] += pw
            G0num *= (n - 2 * k)
            lead = Fr(G0num, G0den)
        else:
            lead = Fr(2 * G0num, G0den)
        p = [None] + [Fr(P[rr], L ** rr) for rr in (1, 2, 3)]
        e = [Fr(1), p[1], (p[1] ** 2 - p[2]) / 2, (p[1] ** 3 - 3 * p[1] * p[2] + 2 * p[3]) / 6]
        a = ap[k]
        top = a - 1 if centre else a
        for i in range(1, top + 1):
            r_out[(i, k)] = lead * e[top - i]
    return r_out


def Xk(r, k, o):
    return sum((Fr(i * (i + 1) * (i + 2) * (i + 3)) * r.get((i, k), 0) * Fr(2, o) ** (i + 4) for i in range(1, 5)), Fr(0))


def odd_between(d):
    return [2 * l + 1 for l in range(d)] if d >= 0 else [-(2 * l + 1) for l in range(-d)]


def sgn(d):
    return (d > 0) - (d < 0)


def AhalfZ(d, s):
    if d >= 0:
        return sum((Fr(2, 2 * l + 1) ** s for l in range(d)), Fr(0))
    return -sum(((1 / (Fr(1, 2) - l)) ** s for l in range(1, -d + 1)), Fr(0))


def rho_lean(u, r):
    return -sum((Fr(i * (i + 1) * (i + 2) * (i + 3)) * r.get((i, k), 0) * AhalfZ(k - 20 * u, i + 4)
                 for i in range(1, 5) for k in range(40 * u + 1)), Fr(0))


def negChoose(j, i):
    return (-1) ** i * comb(i + j - 1, i)


def kerRes(u, q, k0, c0, j, c, r):
    n = 40 * u
    cls = [k for k in range(n + 1) if k % q == k0]
    tot = c0 * sum((r.get((1, k), 0) for k in cls), Fr(0))
    s1 = sum((r.get((i, k), 0) * negChoose(j, i - 1) * Fr(1, k0 - k) ** (i + j - 1)
              for k in cls if k != k0 for i in range(1, 5)), Fr(0))
    s2 = sum((r.get((i, k), 0) * negChoose(i, j - 1) * Fr(1, k - k0) ** (i + j - 1)
              for k in range(n + 1) if k != k0 for i in range(1, 5)), Fr(0))
    return tot + c * Fr(q) ** j * (s1 + s2)


def farRes(u, q, k0, j, r):
    n = 40 * u
    tot = Fr(0)
    for k in range(n + 1):
        if k % q != k0:
            continue
        for i in range(1, 5):
            rv = r.get((i, k), 0)
            if rv:
                tot += rv * sum((negChoose(j, i - 1) * Fr(1, ip - k) ** (i + j - 1) for ip in range(q) if ip != k0), Fr(0))
    return tot


def classBad(u, q, k0, r):
    tot = Fr(0)
    for k in range(40 * u + 1):
        if k % q == k0:
            d = k - 20 * u
            tot += sgn(d) * sum((Xk(r, k, o) for o in odd_between(d) if o % q == 0), Fr(0))
    return tot


def goodPart(u, q, r):
    return sum((sgn(k - 20 * u) * sum((Xk(r, k, o) for o in odd_between(k - 20 * u) if o % q != 0), Fr(0))
                for k in range(40 * u + 1)), Fr(0))


def eq7(rho_, zc, q):
    def vden(x):
        d, v = Fr(x).denominator, 0
        while d % q == 0:
            d //= q; v += 1
        return v
    return max(vden(rho_), vden(zc))


def rand_qint(rng, q):
    while True:
        x = Fr(rng.randint(-40, 40), rng.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 25, 27]))
        if vq(x, q) >= 0:
            return x


class QAdic:
    """exact rationals -> q-adic arithmetic with a global scale: an accumulator holds q^{-B} * value mod q^PREC
    (all terms have valuation >= B); v() recovers the valuation (exact when < B + PREC)."""

    def __init__(self, q, B=-90, PREC=200):
        self.q, self.B, self.PREC = q, B, PREC
        self.MOD = q ** PREC
        self.cache = {}
        self.qp = [q ** e for e in range(PREC)]

    def split(self, x):                     # x = q^v * m, m a unit mod MOD (x != 0)
        x = Fr(x)
        key = x
        s = self.cache.get(key)
        if s is None:
            q = self.q
            a, b, v = x.numerator, x.denominator, 0
            while a % q == 0:
                a //= q; v += 1
            while b % q == 0:
                b //= q; v -= 1
            s = (v, a * pow(b, -1, self.MOD) % self.MOD)
            if len(self.cache) < 400000:
                self.cache[key] = s
        return s

    def term(self, v, m):                   # q^v * m (m integer, any), scaled
        e = v - self.B
        assert e >= 0, (v, self.B)
        return m * self.qp[e] % self.MOD if e < self.PREC else 0

    def val(self, acc):
        acc %= self.MOD
        if acc == 0:
            return 10 ** 9
        v = 0
        while acc % self.q == 0:
            acc //= self.q; v += 1
        return v + self.B


def sec_exact():
    section('exact valuation tests: PerPole7, FarPart7, ClassLemma7, ThmK7 (own exact engine + q-adic sums)')
    sys.path.insert(0, os.path.join(HERE, 'z7_ref'))
    import vc_engine, vc_common
    rng = random.Random(7)
    for u in (EXACT_U or ([2] if QUICK else [2, 5, 7, 10])):
        t0 = time.time()
        n = 40 * u
        r = exact_r(u)
        # cross-check with vc_engine (r_ik stored for n <= 200; rho, c always)
        ref = vc_engine.compute(vc_common.CANDS['cand3'], n)
        if 'rik' in ref:
            check('own r_ik = vc_engine', all(r.get(key, 0) == v for key, v in ref['rik'].items())
                  and all(ref['rik'].get(key, 0) == v for key, v in r.items()), u)
        rho_ = rho_lean(u, r)
        c3 = sum((r.get((3, k), 0) for k in range(n + 1)), Fr(0))
        zc = 46080 * c3
        check('rho = -rho_n (vc_engine)', rho_ == -ref['rho'], u)
        check('Zc = -Z_n (vc_engine)', zc == -ref['Z'], u)
        c1 = sum((r.get((1, k), 0) for k in range(n + 1)), Fr(0))
        check('c1 = 0', c1 == 0)
        if u <= 5:
            rhoP = sum((sgn(k - 20 * u) * sum((Xk(r, k, o) for o in odd_between(k - 20 * u)), Fr(0))
                        for k in range(n + 1)), Fr(0))
            check('rho = -rhoP', rho_ == -rhoP, u)
        npp = nfar = ncl = nk = 0
        worst_pp = 99
        for q in sieve(n + 60):
            if q < 5 or not (80 * u + 2 * q < q * q):
                continue
            QA = QAdic(q, B=-60, PREC=120)
            rq = {key: QA.split(v) for key, v in r.items() if v != 0}
            # --- PerPole7: for every pole, the largest T with PoleLevAt gives v_q(r_ik) >= T
            for k in range(n + 1):
                t = ltype(*local_model(u, q, k % q))
                wk = -2 * (k // q)
                T = -40
                while T < 40 and t.polelev_at(wk, T + 1):
                    T += 1
                for i in range(0, 6):
                    if (i, k) in rq:
                        vr = rq[(i, k)][0]
                        check('PerPole7', vr >= T, (u, q, k, i, T, vr))
                        worst_pp = min(worst_pp, vr - T)
                npp += 1
            if u <= 2 and q <= n:
                check('rhoP = sum classBad + goodPart',
                      rhoP == sum((classBad(u, q, k0, r) for k0 in range(q)), Fr(0)) + goodPart(u, q, r), (u, q))
            # q-adic building blocks
            MOD = QA.MOD
            inv = {}
            for d in range(-n - q, q + n + 1):
                if d % q:
                    inv[d] = pow(d, -1, MOD)

            Sk = {}                          # Sk[k][s] = sum_{ip < q, ip != k mod q} (ip - k)^{-s}, s = 1..9

            def Sfun(k, s):
                if k not in Sk:
                    k0_ = k % q
                    pw = [0] * 10
                    for ip in range(q):
                        if ip != k0_:
                            z = inv[ip - k]
                            zz = 1
                            for ss in range(1, 10):
                                zz = zz * z % MOD
                                pw[ss] += zz
                    Sk[k] = [x % MOD for x in pw]
                return Sk[k][s]

            def acc_far(k0, j):              # q^{-B} farRes mod q^PREC
                acc = 0
                for k in range(k0, n + 1, q):
                    for i in range(1, 5):
                        if (i, k) in rq:
                            v, m = rq[(i, k)]
                            acc += QA.term(v, m * negChoose(j, i - 1) * Sfun(k, i + j - 1))
                return acc % MOD

            def acc_bad(k0):                 # q^{-B} classBad
                acc = 0
                for k in range(k0, n + 1, q):
                    d = k - 20 * u
                    for o in odd_between(d):
                        if o % q == 0:
                            sgo, sig = sgn(d), abs(o) // q
                            for i in range(1, 5):
                                if (i, k) in rq:
                                    v, m = rq[(i, k)]
                                    # (2/o)^{i+4} = q^{-(i+4)} (2/(sign(o) sig))^{i+4}
                                    uu = pow(2 * pow(sgn(o) * sig, -1, MOD), i + 4, MOD)
                                    acc += sgo * QA.term(v - (i + 4), m * (i * (i + 1) * (i + 2) * (i + 3)) * uu)
                return acc % MOD

            def acc_ker(k0, c0, j, c):       # q^{-B} kerRes  (c0, c q-integral)
                acc = 0
                v0, m0 = QA.split(c0) if c0 != 0 else (0, 0)
                vc, mc = QA.split(c) if c != 0 else (0, 0)
                if c0 != 0:
                    for k in range(k0, n + 1, q):
                        if (1, k) in rq:
                            v, m = rq[(1, k)]
                            acc += QA.term(v + v0, m * m0)
                if c != 0:
                    for k in range(n + 1):
                        if k == k0:
                            continue
                        dd = k - k0
                        same = (dd % q == 0)
                        for i in range(1, 5):
                            if (i, k) not in rq:
                                continue
                            v, m = rq[(i, k)]
                            s = i + j - 1
                            if same:               # both s1 (k0 - k) and s2 (k - k0) terms, dd = q * t
                                t_ = dd // q
                                ut = pow(t_, -1, MOD)
                                coef = (negChoose(j, i - 1) * pow(-ut, s, MOD) + negChoose(i, j - 1) * pow(ut, s, MOD))
                                acc += QA.term(v + vc + j - s, m * mc * coef)
                            else:
                                coef = negChoose(i, j - 1) * pow(inv[dd], s, MOD)
                                acc += QA.term(v + vc + j, m * mc * coef)
                return acc % MOD

            kers = [(Fr(0), 1, Fr(0)), (Fr(1), 1, Fr(0)), (Fr(1), 2, Fr(-5, 4))]
            for _ in range(3):
                kers.append((rand_qint(rng, q), rng.randint(1, 4), rand_qint(rng, q)))
            classes = list(range(q)) if (q <= 60 or not QUICK) else rng.sample(range(q), 30)
            if u >= 7 and q > 60:
                classes = rng.sample(range(q), 40)
            for k0 in classes:
                t = ltype(*local_model(u, q, k0))
                for jj in range(1, 7):
                    if jj + 1 <= q + t.E:
                        vf = QA.val(acc_far(k0, jj))
                        # v(24 q^{-5} q^j farRes) = j - 5 + v(farRes) >= j - 4
                        check('FarPart7', vf >= 1, (u, q, k0, jj, vf))
                        nfar += 1
                ab = acc_bad(k0)
                for (c0, jj, c) in kers:
                    if (c0 != 0 and vq(c0, q) < 0) or (c != 0 and vq(c, q) < 0):
                        continue
                    P = t.first_nz(c0, jj, c, t.E + 14)
                    # val = bad - 24 q^{-5} kerRes
                    ak = acc_ker(k0, c0, jj, c)
                    # 24 q^{-5} kerRes: shift valuation by -5 (multiply scaled acc by q^{-5}: rescale)
                    # compute q^{-B} * (24 q^{-5} kerRes) = 24 * (q^{-B} kerRes) / q^5 : need exact division
                    tot = (ab * q ** 5 - 24 * ak) % MOD    # = q^{-B+5} * val  (mod q^PREC)
                    vv = QA.val(tot) - 5 if tot % MOD else 10 ** 9
                    check('ClassLemma7', vv >= P - 5, (u, q, k0, (c0, jj, c), vv, P - 5))
                    ncl += 1
                    if u == 2 and rng.random() < 0.05:      # q-adic engine against exact Fractions
                        ex = classBad(u, q, k0, r) - 24 * Fr(1, q ** 5) * kerRes(u, q, k0, c0, jj, c, r)
                        check('q-adic = exact (class lemma value)', vq(ex, q) == vv or (ex == 0 and vv > 50),
                              (q, k0, vq(ex, q), vv))
                        ef = farRes(u, q, k0, 2, r)
                        check('q-adic = exact (far part)', vq(ef, q) == QA.val(acc_far(k0, 2))
                              or (ef == 0 and QA.val(acc_far(k0, 2)) > 50), (q, k0))
            # --- ThmK7 as an implication: best T for kernels 0, 1 and the far kernel -> e_q <= -T
            if q >= 29 and 80 * u + 3 * q < q * q:
                e = eq7(rho_, zc, q)
                types = [ltype(*local_model(u, q, k0)) for k0 in range(q)]
                for (c0, jj, c) in [(Fr(0), 1, Fr(0)), (Fr(1), 1, Fr(0)), (Fr(1), 2, Fr(-5, 4))]:
                    best = None
                    for T in range(0, -15, -1):
                        if c != 0 and not (T + 4 <= jj):
                            continue
                        if all(tt.levge(c0, jj, c, T + 5) for tt in types) and all(tt.polelevge(T) for tt in types):
                            best = T
                            break
                    if best is not None:
                        check('ThmK7 (e_q <= -T)', e <= -best, (u, q, (c0, jj, c), e, best))
                        nk += 1
        print('  n=%d: PerPole7 %d poles (min slack %d), FarPart7 %d, ClassLemma7 %d, ThmK7 %d  (%.0fs)'
              % (n, npp, worst_pp, nfar, ncl, nk, time.time() - t0), flush=True)


def sec_emin():
    section('Emin7: E >= -10 for all primes 5 <= q <= 2n + 50 and all classes, u <= 60')
    worst = 99
    us = list(range(0, 61)) if not QUICK else list(range(0, 21))
    for u in us:
        n = 40 * u
        for q in sieve(2 * n + 50):
            if q < 5:
                continue
            for k0 in range(q):
                items, _ = local_model(u, q, k0)
                E = sum(e for _, e in items)
                worst = min(worst, E)
                if E < -10:
                    check('Emin7', False, (u, q, k0, E))
    check('Emin7 overall', worst >= -10, worst)
    print('  min E over all (u, q, k0) = %d' % worst)


def Fx(z):
    return z * math.log(abs(z)) - z if z != 0 else 0.0


UPOT = [(1, 0), (1, 2), (1, 4), (-1, 5), (1, 6), (-2, 7), (-1, 9), (-1, 11), (-1, 13), (1, 27),
        (1, 29), (1, 31), (2, 33), (-1, 34), (1, 35), (-1, 36), (-1, 38), (-1, 40)]


def Upot(kap):
    return sum(w * Fx(p / 40 - kap) for w, p in UPOT)


def lnabs(x):
    x = Fr(x)
    return math.log(abs(x.numerator)) - math.log(x.denominator)


def sec_primes():
    section('BigPrimes7 / SmallPrimes7 / ExpBounds7 on exact exponents; CoeffVanish7, ResidueBound7, '
            'Growth7, AuxPrime7 at finite n (own engine)')
    # the potential U: an independent derivation of the 18 terms from the profile
    terms = defaultdict(int)
    for e in ETA:                        # + sum_m int_{eta}^{1-eta} log|z - k| = F(1-eta-k) - F(eta-k)
        terms[40 - e] += 1
        terms[e] -= 1
    for lo, hi in ((0, 40), (2, 38), (4, 36), (6, 34)):   # - int a(z) log|z-k| = -sum_l (F(b_l-k) - F(a_l-k))
        terms[hi] -= 1
        terms[lo] += 1
    check('upotTerms = derived potential', sorted((w, p) for p, w in terms.items() if w) == sorted(UPOT))
    us = list(range(1, 21)) if not QUICK else list(range(1, 7))
    for u in us:
        t0 = time.time()
        n = 40 * u
        r = exact_r(u)
        rho_ = rho_lean(u, r)
        zc = 46080 * sum((r.get((3, k), 0) for k in range(n + 1)), Fr(0))
        # CoeffVanish7 (symm, c1, c_even) on the own engine's data
        check('symm', all(r.get((i, n - k), 0) == (-1) ** (i + 1) * r.get((i, k), 0)
                          for k in range(n + 1) for i in range(1, 5)), u)
        cs = [sum((r.get((i, k), 0) for k in range(n + 1)), Fr(0)) for i in range(5)]
        check('c1 = c2 = c4 = 0, c3 != 0', cs[1] == 0 and cs[2] == 0 and cs[4] == 0 and cs[3] != 0, u)
        # ResidueBound7 (proved constants) and Growth7 at finite n
        wr = max(lnabs(v) - n * Upot(k / n) for (i, k), v in r.items() if v != 0)
        check('ResidueBound7 (proved per-n form)', wr <= math.log(n + 1) + 14 * math.log(n) + 37.44, (u, wr))
        g = max(lnabs(rho_), lnabs(zc)) / n
        check('Growth7 (per-n proved form)',
              g <= 0.70670223 + (14 * math.log(n) + 2 * math.log(n + 1) + 47.5) / n, (u, g))
        # AuxPrime7 at l = 38u - 1 prime
        ell = 38 * u - 1
        if isprime(ell):
            check('AuxPrime7 v_l(rho) = -1', vq(rho_, ell) == -1, (u, vq(rho_, ell)))
            check('AuxPrime7 v_l(Z) >= 0', vq(zc, ell) >= 0, (u, vq(zc, ell)))
        worst = 0.0
        for q in sieve(3 * n + 50):
            if q == 2:
                continue
            e = eq7(rho_, zc, q)
            if q > n:
                check('BigPrimes7', e == 0, (u, q, e))
            lam = 0
            p = q
            while p <= 80 * u + 1:
                lam += 1; p *= q
            check('SmallPrimes7', e <= 19 * lam, (u, q, e, lam))
            if lam:
                worst = max(worst, e / (19 * lam))
            if q >= 29 and 80 * u + 3 * q < q * q:
                check('ExpBounds7.crude', e <= 14, (u, q, e))
                x = Fr(n, q)
                if u % q and x >= 20:
                    check('ExpBounds7.tail (q > 40)', e <= 10, (u, q, e))
        print('  n=%4d: max e_q/(19 lambda) = %.3f; max(log|r| - nU) = %.2f; log max(|rho|,|Z|)/n = %.4f%s  (%.1fs)'
              % (n, worst, wr, g, '; l = %d: v_l(rho) = %d, v_l(Z) = %d' % (ell, vq(rho_, ell), vq(zc, ell))
                 if isprime(ell) else '', time.time() - t0), flush=True)


def sec_truth():
    """ExpBounds7 (rows / tail / crude) against the TRUE exponents e_q(n) of the research verifier
    (verify-denominators-theory/data/vb_*.jsonl, vd_*.jsonl: q-adic truth, n up to 200000).
    Set VERIF_DIR to that data folder; skipped otherwise."""
    section('ExpBounds7 against the verifier\'s TRUE exponents (VERIF_DIR)')
    vd = os.environ.get('VERIF_DIR', '')
    if not vd or not os.path.isdir(vd):
        print('  (VERIF_DIR not set; skipped)')
        return
    H, R = lean_rows()

    def row_f(x):
        if 1 <= x < 20:
            for rw in H:
                if rw[0] <= x < rw[1]:
                    return rw[2], 'head'
        if 20 <= x < 140:
            t = int((x - 20) // 40)
            for rw in R:
                if rw[0] + 40 * t <= x < rw[1] + 40 * t:
                    return rw[2], 'res'
        if x >= 20:
            return 10, 'tail'
        return None, None
    stats = defaultdict(int)
    for fn in sorted(os.listdir(vd)):
        if not (fn.endswith('.jsonl') and (fn.startswith('vb_') or fn.startswith('vd_'))):
            continue
        for line in open(os.path.join(vd, fn)):
            d = json.loads(line)
            n, q, e = d['n'], d['q'], d['e']
            if n % 40 or q < 29:
                continue
            u = n // 40
            if not (80 * u + 3 * q < q * q):
                continue
            check('crude e <= 14', e <= 14, (n, q, e))
            if q <= 40 or u % q == 0:
                continue
            x = Fr(n, q)
            f, kind = row_f(x)
            if f is None:
                continue
            ok = check('ExpBounds7.%s (true e <= f)' % kind, e <= f, (fn, n, q, float(x), e, f))
            stats[kind] += 1
            stats[kind + '_eq'] += (e == f)
            if x >= 20:
                check('ExpBounds7.tail (true e <= 10)', e <= 10, (n, q, e))
    print('  checked: %s' % dict(stats))


def sec_bigj():
    """Stmt_ClassLemma7 with large kernel orders j in {5, 6, 8, 11} (exact Fractions), n = 80, 200."""
    section('ClassLemma7 with kernel orders j in {5, 6, 8, 11} (exact)')
    rng = random.Random(99)
    for u in ([2] if QUICK else [2, 5]):
        n = 40 * u
        r = exact_r(u)
        nt = 0
        for q in sieve(n + 60):
            if q < 5 or not (80 * u + 2 * q < q * q):
                continue
            classes = range(q) if q < 60 else rng.sample(range(q), 25)
            for k0 in classes:
                t = ltype(*local_model(u, q, k0))
                bad = classBad(u, q, k0, r)
                for j in (5, 6, 8, 11):
                    c0, c = rand_qint(rng, q), rand_qint(rng, q)
                    P = t.first_nz(c0, j, c, t.E + 16)
                    val = bad - 24 * Fr(1, q ** 5) * kerRes(u, q, k0, c0, j, c, r)
                    check('ClassLemma7 (large j)', val == 0 or vq(val, q) >= P - 5, (u, q, k0, j, vq(val, q), P - 5))
                    nt += 1
        print('  n=%d: %d (class, kernel) tests' % (n, nt), flush=True)


def main():
    print('z7_audit: %s' % ' '.join(sys.argv[1:]))
    todo = ARGS or ['table', 'cont', 'disc', 'exact', 'emin', 'primes', 'truth', 'bigj']
    for s in todo:
        {'table': sec_table, 'cont': sec_cont, 'disc': sec_disc, 'exact': sec_exact, 'emin': sec_emin,
         'primes': sec_primes, 'truth': sec_truth, 'bigj': sec_bigj}[s]()
    print('\n%d checks, %d failures, %.0fs' % (NCHK[0], len(FAILS), time.time() - T0))
    for f in FAILS[:40]:
        print('  ', f)
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
