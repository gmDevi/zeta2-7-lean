#!/usr/bin/env python3
"""Generator of the certificate data of `HeadCert7` (see `notes/HeadCert7.md`).

  python3 Zeta2Lean/Z7/Proofs/HeadCert7_gen.py            write the generated Lean files
  python3 Zeta2Lean/Z7/Proofs/HeadCert7_gen.py --check    only compare with the files on disk
  python3 Zeta2Lean/Z7/Proofs/HeadCert7_gen.py --audit    also cross-check the types and the checks
                                                          against python/z7_audit.py (independent code)

Only the Lean kernel checks matter for soundness; this script documents where the data come from.
It mirrors the Lean definitions exactly:
* `HC7.sysH` (23 lines: `sysE7` + x/2 floor, x/2 ceiling, x/2 + 1/2 floor), `LineSys7.Nm`, `sv`;
* per row: the certificate `<pa, qa, pb, qb, 0, ord>` (`ord` sorted by (sa, sb, floor after
  ceiling)), `X = floor(a)`; the prefix states `HC7.stF` (p = 0..23), the consistent ones
  (identical lines 1,2 and 7,8 together), `HC7.EF`, `HC7.cmodF`;
* the exceptional states: `LevGe` needed when `EF < 4 - f` and not (kappa = 0 and no pairs);
  `PoleLevGe` needed when `EF < -1 - f`; the distinct jobs form the tables `HC7.levJobs`,
  `HC7.poleJobs`, checked by `HC7.levChk` / `HC7.poleChk` (mirrored here with exact fractions).

Kernel memory.  Palomar's checkers run `lake comparator`, whose con-ron kernel checks 16 declarations
at a time and keeps each declaration's intermediate terms until that declaration is done (roughly
0.1-0.25 GB per second of checking).  So every kernel check is kept small:
* a `LevGe` job is checked in pieces: its bad pairs grouped by pole (`HC7.grp`), a piece is the
  contribution `HC7.grpR` / `HC7.grpT` of consecutive pole groups to `[y^m] ASer` (value computed
  here, checked by one `decide +kernel`), and `HC7.LevJob.ok_of_vals*` checks the rest of
  `HC7.levChk` from the sum of the pieces;
* the rows of a `HeadCert7Data*` part are checked in chunks, one `decide +kernel` each.
The pieces and chunks are cut by an estimate of their con-ron time (`lev_cost`, `row_cost`, in units
of about 1 ms on the machine where they were calibrated) below `HC7_BUDGET` (default 1200).
"""
import os
import re
import sys
import math
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
DENTABLE = os.path.join(HERE, '..', 'DenTable.lean')

ETA = [5, 7, 7, 9, 11, 13]
LA = [2 * (40 - e) for e in ETA] + [2 * e for e in ETA] + [80, 76, 72, 68] + [0, 4, 8, 12] + [40, 40, 40]
LB = [-40] * 12 + [0] * 8 + [0, 0, 40]
LW = [1] * 6 + [-1] * 6 + [-1] * 4 + [1] * 4 + [0, 0, 0]
CEIL = [False] * 16 + [True] * 4 + [False, True, False]
NL = 23
K = -4
IDENT = [(1, 2), (7, 8)]


def ediv(a, b):          # Int.ediv for b > 0 (floor division)
    assert b > 0
    return a // b


# ---- the table rows -------------------------------------------------------------------------------
def parse_rows():
    txt = open(DENTABLE, encoding='utf-8').read()
    i = txt.index('def headRows7 : List DenRow := [')
    j = txt.index('\n]', i)
    rows = []
    for m in re.finditer(r'⟨(\d+), (\d+), (\d+), (\d+), (\d+), ([^,]+), (\d+), ([^⟩]+)⟩', txt[i:j]):
        an, ad, bn, bd, f = (int(m.group(k)) for k in range(1, 6))
        c0s, js, cs = m.group(6).strip(), int(m.group(7)), m.group(8).strip()
        rows.append(dict(an=an, ad=ad, bn=bn, bd=bd, f=f, c0s=c0s, j=js, cs=cs,
                         c0=parse_q(c0s), c=parse_q(cs), text=m.group(0)))
    assert len(rows) == 469, len(rows)
    return rows


def parse_q(s):
    s = s.replace(' ', '')
    if '/' in s:
        a, b = s.split('/')
        return Fr(int(a), int(b))
    return Fr(int(s))


# ---- certificates (mirror of LineSys7.Nm / sv / ECert7.lineOK / chainOK / HC7.noFC) --------------
def Nmid(pa, qa, pb, qb):
    P = pa * qb + pb * qa
    Q = 2 * qa * qb
    return [ediv(LA[j] * P + LB[j] * Q, 80 * Q) for j in range(NL)]


def sv(j, N, P, Q):
    return LA[j] * P + LB[j] * Q - 80 * Q * N[j]


def make_cert(pa, qa, pb, qb):
    assert qa > 0 and qb > 0 and pa * qb < pb * qa
    N = Nmid(pa, qa, pb, qb)
    sa = [sv(j, N, pa, qa) for j in range(NL)]
    sb = [sv(j, N, pb, qb) for j in range(NL)]
    for j in range(NL):
        assert 0 <= sa[j] <= 80 * qa and 0 <= sb[j] <= 80 * qb, (pa, qa, pb, qb, j)
        if not CEIL[j]:
            assert sa[j] < 80 * qa
    order = sorted(range(NL), key=lambda j: (sa[j], sb[j], 0 if CEIL[j] else 1))
    for i in range(NL - 1):
        r, s = order[i], order[i + 1]
        assert sa[r] <= sa[s] and sb[r] <= sb[s]
        assert not ((not CEIL[r]) and CEIL[s] and LA[r] == LA[s] and LB[r] == LB[s])
    return N, order


def stF(N, order, p):
    d = set(order[:p])
    return [N[j] + (1 if CEIL[j] else 0) - (1 if j in d else 0) for j in range(NL)]


def consistent(order, p):
    d = set(order[:p])
    return all((i in d) == (j in d) for (i, j) in IDENT)


def EF(F):
    return sum(LW[j] * F[j] for j in range(20)) + K + (1 if F[21] == F[20] else 0)


# ---- HC7.cmodF --------------------------------------------------------------------------------------
def apoleF(F, j):
    return 1 + sum(1 for l in (1, 2, 3) if F[16 + l] <= j <= F[12 + l])


def muF(F, t):
    ind = lambda Fv: 1 if t <= Fv + 1 else 0
    return sum(ind(F[m]) - ind(F[m + 6]) for m in range(6))


def cmodF(X, F):
    items = []
    for j in range(X + 1):
        if j <= F[12]:
            items.append((-(2 * j), -apoleF(F, j)))
    for t in range(X + 2):
        m = muF(F, t)
        if m != 0:
            items.append((-(2 * t - 1), m))
    if F[21] == F[20]:
        items.append((-(2 * F[20]), 1))
    pairs = []
    for j in range(X + 1):
        if j <= F[12] and not (F[21] == F[20] and j == F[20]):
            pos = F[20] < j
            sg = 1 if pos else -1
            T = max(0, j - F[22]) if pos else max(0, F[22] - j)
            for t in range(T):
                pairs.append((-(2 * j), -(2 * j) + sg * (2 * t + 1), sg))
    return tuple(items), tuple(pairs)


# ---- HC7.levChk / HC7.poleChk (exact) --------------------------------------------------------------
def gch(e, i):
    v = Fr(1)
    for t in range(i):
        v = v * (e - t) / (t + 1)
    return v


def cf(a, n):
    return a[n] if n < len(a) else Fr(0)


def tmul(M, a, b):
    return [sum((cf(a, i) * cf(b, n - i) for i in range(n + 1)), Fr(0)) for n in range(M)]


def tprod(M, L):
    acc = [Fr(1) if i == 0 else Fr(0) for i in range(M)]
    for a in reversed(L):
        acc = tmul(M, a, acc)
    return acc


def bserL(M, c, e):
    return [gch(e, i) * c ** i for i in range(M)]


def zpow(x, e):
    return x ** e


def netE(tau, w):
    return sum(e for (v, e) in tau[0] if v == w)


def Etau(tau):
    return sum(e for (_, e) in tau[0])


def tayL(M, tau, wk):
    L = []
    for (w, e) in tau[0]:
        if w != wk:
            k = zpow(Fr(wk - w, 2), e)
            L.append([k * v for v in bserL(M, Fr(2, wk - w), e)])
    return tprod(M, L)


def gL(M, tau, wk, we):
    k = zpow(Fr(we - wk, 2), -5)
    return tmul(M, tayL(M, tau, wk), [k * v for v in bserL(M, Fr(-2, we - wk), -5)])


def ASerC(tau, m, cache):
    tot = Fr(0)
    for (wk, we, sg) in tau[1]:
        a = max(0, -netE(tau, wk))
        key = (a, wk, we)
        if key not in cache:
            cache[key] = gL(a, tau, wk, we)
        g = cache[key]
        s = Fr(0)
        for ip in range(a):
            i = ip + 1
            if i <= m:
                s += cf(g, a - i) * (gch(-i, m - i) * Fr(-wk, 2) ** (m - i))
        tot += sg * s
    return tot


def levChk(tau, c0, j, c, P):
    E = Etau(tau)
    rS = tprod(max(P, 0), [bserL(max(P, 0), Fr(-w, 2), e) for (w, e) in tau[0]])
    czf = lambda f, z: f(z) if z >= 0 else Fr(0)
    cache = {}
    for i in range(max(P - E - 1, 0)):
        p = E + 1 + i
        v = ASerC(tau, i + 1, cache) - c0 * czf(lambda z: cf(rS, z), p) - c * czf(lambda z: cf(rS, z), p - j)
        if v != 0:
            return False
    return True


def poleChk(tau, T):
    E = Etau(tau)
    for (w, _) in tau[0]:
        a = -netE(tau, w)
        L = tayL(max(a, 0), tau, w) if a > 0 else []
        for l in range(max(a, 0)):
            if E - netE(tau, w) - T < l and cf(L, l) != 0:
                return False
    return True


# ---- HC7.grp / HC7.grpC / HC7.levChkV (exact): `levChk` by pole groups --------------------------------
def grp(pairs):
    """Maximal runs of consecutive bad pairs with the same pole: [(w, [pairs])]."""
    out = []
    for pr in pairs:
        if out and out[-1][0] == pr[0]:
            out[-1][1].append(pr)
        else:
            out.append((pr[0], [pr]))
    return out


def conv(a, b, n):
    return sum((cf(a, i) * cf(b, n - i) for i in range(n + 1)), Fr(0))


def pairCA(A, a, pr, m):
    wk, we, sg = pr
    k = zpow(Fr(we - wk, 2), -5)
    B = [k * v for v in bserL(a, Fr(-2, we - wk), -5)]
    s = Fr(0)
    for ip in range(a):
        if ip + 1 <= m:
            s += conv(A, B, a - (ip + 1)) * (gch(-(ip + 1), m - (ip + 1)) * Fr(-wk, 2) ** (m - (ip + 1)))
    return sg * s


def grpC(tau, wg, m):
    w, g = wg
    a = max(0, -netE(tau, w))
    A = tayL(a, tau, w)
    return sum((pairCA(A, a, pr, m) for pr in g), Fr(0))


def levChkV(tau, V, c0, j, c, P):
    E = Etau(tau)
    n = max(P - E - 1, 0)
    if n > len(V):
        return False
    rS = tprod(max(P, 0), [bserL(max(P, 0), Fr(-w, 2), e) for (w, e) in tau[0]])
    czf = lambda z: cf(rS, z) if z >= 0 else Fr(0)
    return all(V[i] - c0 * czf(E + 1 + i) - c * czf(E + 1 + i - j) == 0 for i in range(n))


# ---- kernel cost estimates (about 1 ms of con-ron time per unit) ----------------------------------------
BUDGET = int(os.environ.get('HC7_BUDGET', '1200'))


def lev_cost(tau, wg, m):
    """One pole group at `[y^m]`: the Taylor series (items x a) and the pairs (pairs x a x min(m, a))."""
    a = max(0, -netE(tau, wg[0]))
    return 3 * len(tau[0]) * a + 5 * len(wg[1]) * a * min(m, a)


def row_cost(nexc):
    """One row: the 24 prefix states, plus the table look-ups of its exceptional states."""
    return 270 + 110 * nexc


def cut(costs, budget):
    """Consecutive pieces with cost at most `budget` (a single item may exceed it): the cut points."""
    cuts, acc = [0], 0
    for k, x in enumerate(costs):
        if acc > 0 and acc + x > budget:
            cuts.append(k)
            acc = 0
        acc += x
    return cuts


# ---- the analysis --------------------------------------------------------------------------------
def analyse(rows):
    levjobs, polejobs = {}, {}
    hrows = []
    stats = dict(states=0, exc_rows=0, inc=0)
    for idx, r in enumerate(rows):
        an, ad, bn, bd, f = r['an'], r['ad'], r['bn'], r['bd'], r['f']
        N, order = make_cert(an, ad, bn, bd)
        X = an // ad
        assert X * ad <= an and bn <= (X + 1) * bd, idx
        kappa0 = (r['c0'] == 0 and r['c'] == 0)
        exc = False
        nexc = 0
        for p in range(NL + 1):
            if not consistent(order, p):
                continue
            stats['states'] += 1
            F = stF(N, order, p)
            E = EF(F)
            lev_vac = 5 - f <= E + 1
            pole_vac = -f <= E + 1
            if lev_vac and pole_vac:
                continue
            nexc += 1
            tau = cmodF(X, F)
            need_lev = (not lev_vac) and not (kappa0 and len(tau[1]) == 0)
            need_pole = not pole_vac
            if need_lev or need_pole:
                stats['inc'] += 1
                exc = True
            if need_lev:
                key = (tau, r['c0s'], r['j'], r['cs'], 5 - f)
                levjobs.setdefault(key, (r['c0'], r['c'], []))[2].append((idx, p))
            if need_pole:
                polejobs.setdefault((tau, -f), []).append((idx, p))
        stats['exc_rows'] += exc
        hrows.append((r, N, order, X, nexc))
    return hrows, levjobs, polejobs, stats


# ---- Lean output ------------------------------------------------------------------------------------
def lean_tau(tau):
    """`HC7.mkT I P`: items flattened, bad pairs run-length encoded as (w, sign, count)."""
    items = ', '.join('%d, %d' % it for it in tau[0])
    groups = []
    for (wk, we, sg) in tau[1]:
        if groups and groups[-1][0] == wk and groups[-1][1] == sg:
            groups[-1][2] += 1
        else:
            groups.append([wk, sg, 1])
    dec = tuple((w, w + s * (2 * t + 1), s) for (w, s, n) in groups for t in range(n))
    assert dec == tau[1]
    pairs = ', '.join('%d, %d, %d' % tuple(g) for g in groups)
    return 'mkT [%s] [%s]' % (items, pairs)


def lean_q(s):
    return '(%s : ℚ)' % s


def lean_fr(x):
    return '(%d : ℚ)' % x.numerator if x.denominator == 1 else '(%d / %d : ℚ)' % (x.numerator, x.denominator)


def sum_expr(vs):
    """`v₀ + (v₁ + (… + vₙ))`, the shape `grpT_split` leaves (parenthesized as an argument)."""
    e = lean_fr(vs[-1])
    for v in reversed(vs[:-1]):
        e = '%s + %s' % (lean_fr(v), e if ' + ' not in e else '(%s)' % e)
    return e if len(vs) == 1 else '(%s)' % e


LEV_HEADER = '''module

public import Zeta2Lean.Z7.Proofs.%s

@[expose] public section

/-!
# `HeadCert7`: exceptional `LevGe` jobs, part %d (generated by `HeadCert7_gen.py`)

`levJob%d_k = ⟨τ, c0, j, c, P⟩ : HC7.LevJob`: the local type `τ` of an exceptional sweep state of a
head row (`E < 4 - f`, not trivially vacuous) with the row's kernel `c0 + c y^j` and `P = 5 - f`.
`levJob%d_k_ok` checks `HC7.levChk` (exact rational arithmetic) in pieces: each `have` evaluates the
contribution `grpR τ lo hi m` (pole groups `lo ≤ k < hi`) or `grpT τ lo m` (groups `k ≥ lo`) to
`[y^m] ASer τ` by `decide +kernel`, and `LevJob.ok_of_vals*` checks the rest of `levChk` from their
sum.  The pieces are small so that every kernel check needs little memory (see the generator).
Each part imports the previous one (part 0 imports `HeadCert7Series`) to sequence the build.
-/

set_option linter.style.longLine false

namespace Zeta2.Z7

namespace HC7

'''

POLE_HEADER = '''module

public import Zeta2Lean.Z7.Proofs.HeadCert7Series

@[expose] public section

/-!
# `HeadCert7`: exceptional `PoleLevGe` jobs (generated by `HeadCert7_gen.py`)

`⟨τ, T⟩ : HC7.PoleJob` with `T = -f` for the exceptional states with `E < -1 - f`; the kernel
check `poleJobs_ok` evaluates `HC7.poleChk`.
-/

set_option linter.style.longLine false

namespace Zeta2.Z7

namespace HC7

'''

FOOTER = '''
end HC7

end Zeta2.Z7
'''


def cost(tau):
    return len(tau[1]) * len(tau[0])


def lev_job(name, key, c0, c):
    """The definition of one `LevGe` job and its check in pieces."""
    tau, c0s, j, cs, P = key
    gs = grp(tau[1])
    nm = max(P - Etau(tau) - 1, 0)
    assert 1 <= nm <= 4, nm
    cuts = cut([lev_cost(tau, wg, nm) for wg in gs], BUDGET)
    bounds = list(zip(cuts, cuts[1:] + [None]))
    vals = [[sum((grpC(tau, gs[k], m) for k in range(lo, len(gs) if hi is None else hi)), Fr(0))
             for m in range(1, nm + 1)] for (lo, hi) in bounds]
    V = [sum((v[m] for v in vals), Fr(0)) for m in range(nm)]
    assert V == [ASerC(tau, m, {}) for m in range(1, nm + 1)], name
    assert levChkV(tau, V, c0, j, c, P), name
    out = ['def %s : LevJob :=\n  ⟨%s,\n    %s, %d, %s, %d⟩\n\n' % (name, lean_tau(tau), lean_q(c0s), j, lean_q(cs), P)]
    out.append('theorem %s_ok : %s.ok = true := by\n' % (name, name))
    hn = lambda s, m: 'h%d' % s if nm == 1 else 'h%d_%d' % (s, m)
    for s, (lo, hi) in enumerate(bounds):
        for m in range(1, nm + 1):
            lhs = 'grpT %s.τ %d %d' % (name, lo, m) if hi is None else 'grpR %s.τ %d %d %d' % (name, lo, hi, m)
            out.append('  have %s : %s = %s := by decide +kernel\n' % (hn(s, m), lhs, lean_fr(vals[s][m - 1])))
    sums = [sum_expr([v[m] for v in vals]) for m in range(nm)]
    out.append('  exact LevJob.ok_of_vals%d %s %s\n' % (nm, name, ' '.join(sums)))
    for m in range(1, nm + 1):
        rws = ['ASerC_eq_grpT'] + ['grpT_split _ %d %d _ (by norm_num)' % (lo, hi) for (lo, hi) in bounds if hi is not None]
        rws += [hn(s, m) for s in range(len(bounds))]
        out.append('    (by rw [%s])\n' % ', '.join(rws))
    out.append('    (by decide +kernel)\n')
    return ''.join(out), len(bounds) * nm


def gen_lev_files(levjobs, nfiles):
    jobs = sorted(levjobs.items(), key=lambda kv: -cost(kv[0][0]))
    bins = [[] for _ in range(nfiles)]
    load = [0] * nfiles
    for kv in jobs:
        b = min(range(nfiles), key=lambda i: load[i])
        bins[b].append(kv)
        load[b] += cost(kv[0][0]) + 50
    out = []
    npieces = 0
    for b, jl in enumerate(bins):
        body = []
        names = []
        for k, (key, (c0, c, _)) in enumerate(jl):
            name = 'levJob%d_%d' % (b, k)
            names.append(name)
            text, n = lev_job(name, key, c0, c)
            npieces += n
            body.append('/-- Exceptional `LevGe` job %d of part %d. -/\n' % (k, b) + text + '\n')
        body.append('/-- Exceptional `LevGe` jobs, part %d. -/\ndef levJobs%d : List LevJob :=\n  [%s]\n\n'
                    % (b, b, ', '.join(names)))
        body.append('theorem levJobs%d_ok : levJobs%d.all LevJob.ok = true := by\n  simp only [levJobs%d, List.all_cons, '
                    'List.all_nil, %s, Bool.and_true]\n' % (b, b, b, ', '.join(n + '_ok' for n in names)))
        prev = 'HeadCert7Series' if b == 0 else 'HeadCert7Lev%d' % (b - 1)
        out.append(('HeadCert7Lev%d.lean' % b, LEV_HEADER % (prev, b, b, b) + ''.join(body) + FOOTER))
    return out, len(bins), npieces


def gen_pole_file(polejobs):
    body = ['/-- Exceptional `PoleLevGe` jobs. -/\ndef poleJobs : List PoleJob := [\n']
    body.append(',\n'.join('  ⟨%s, %d⟩' % (lean_tau(k[0]), k[1]) for k in polejobs))
    body.append(']\n\n')
    body.append('theorem poleJobs_ok : poleJobs.all PoleJob.ok = true := by\n  decide +kernel\n')
    return ('HeadCert7Pole.lean', POLE_HEADER + ''.join(body) + FOOTER)


TAB_HEADER = """module

%s

@[expose] public section

/-!
# `HeadCert7`: the table of exceptional jobs (generated by `HeadCert7_gen.py`)

`HC7.levJobs` (%d `LevGe` jobs on %d local types) and `HC7.poleJobs` (%d `PoleLevGe` jobs on %d
types): the exceptional sweep states of the head rows, with their kernel-checked certificates
(`HC7.levJobs_sound`, `HC7.poleJobs_sound`).
-/

set_option linter.style.longLine false

namespace Zeta2.Z7

namespace HC7

/-- All exceptional `LevGe` jobs. -/
def levJobs : List LevJob :=
  %s

theorem levJobs_ok : levJobs.all LevJob.ok = true := by
  simp only [levJobs, List.all_append, %s, Bool.and_self]

theorem levJobs_sound : ∀ e ∈ levJobs, LevGe e.τ e.c0 e.j e.c e.P := fun e he =>
  levChk_sound _ _ _ _ _ (List.all_eq_true.1 levJobs_ok e he)

theorem poleJobs_sound : ∀ e ∈ poleJobs, PoleLevGe e.τ e.T := fun e he =>
  poleChk_sound _ _ (List.all_eq_true.1 poleJobs_ok e he)
"""

DATA_HEADER = """module

public import Zeta2Lean.Z7.Proofs.%s

@[expose] public section

/-!
# `HeadCert7`: row certificates, part %d (generated by `HeadCert7_gen.py`)

`⟨row, ⟨pa, qa, pb, qb, 0, ord⟩, X⟩ : HC7.HRow` for rows %d..%d of `headRows7`: the sweep
certificate of the 23 lines of `HC7.sysH` on the row interval (`ord` = the lines sorted by their
fractional parts) and `X = ⌊a⌋`.  `hrows7_%d_ok` checks `HC7.rowOK` (certificate + every consistent
prefix state) by kernel reduction, one `decide +kernel` per chunk `hrows7_%d_c` of rows (the chunks
are small so that every kernel check needs little memory, see the generator).  Each part imports
the previous one (part 0 imports `HeadCert7Row`) to sequence the build.
-/

set_option linter.style.longLine false

namespace Zeta2.Z7

namespace HC7

"""

ROWS_HEADER = """module

%s

@[expose] public section

/-!
# `HeadCert7`: all row certificates (generated by `HeadCert7_gen.py`)

`HC7.hrows7` = the certificates of the %d rows of `headRows7`, in order (`hrows7_aligned`), all
valid (`hrows7_ok`).
-/

set_option linter.style.longLine false

namespace Zeta2.Z7

namespace HC7

/-- All row certificates. -/
def hrows7 : List HRow :=
  %s

theorem hrows7_ok : hrows7.all rowOK = true := by
  simp only [hrows7, List.all_append, %s, Bool.and_self]

theorem hrows7_aligned : aligned headRows7 hrows7 = true := by
  decide +kernel
"""


NL_ = chr(10)


def gen_tab(nlev, levjobs, polejobs):
    imports = NL_.join(['public import Zeta2Lean.Z7.Proofs.HeadCert7Lev%d' % i for i in range(nlev)]
                       + ['public import Zeta2Lean.Z7.Proofs.HeadCert7Pole'])
    names = ['levJobs%d' % i for i in range(nlev)]
    text = TAB_HEADER % (imports, len(levjobs), len(set(k[0] for k in levjobs)), len(polejobs),
                         len(set(k[0] for k in polejobs)), ' ++ '.join(names),
                         ', '.join(n + '_ok' for n in names)) + FOOTER
    return ('HeadCert7Tab.lean', text)


def gen_data(hrows, CH):
    outs = []
    parts = [hrows[i:i + CH] for i in range(0, len(hrows), CH)]
    nchunks = 0
    for ci, part in enumerate(parts):
        first = ci * CH
        cuts = cut([row_cost(h[4]) for h in part], BUDGET)
        bounds = list(zip(cuts, cuts[1:] + [len(part)]))
        nchunks += len(bounds)
        body = ''
        names = []
        for k, (lo, hi) in enumerate(bounds):
            lines = []
            for (r, N, order, X, _) in part[lo:hi]:
                lines.append('  ⟨%s,' % r['text'] + NL_ + '    ⟨%d, %d, %d, %d, 0, [%s]⟩, %d⟩' % (
                    r['an'], r['ad'], r['bn'], r['bd'], ', '.join(map(str, order)), X))
            name = 'hrows7_%d_%d' % (ci, k)
            names.append(name)
            body += ('/-- Row certificates %d..%d. -/' % (first + lo, first + hi - 1) + NL_
                     + 'def %s : List HRow := [' % name + NL_ + (',' + NL_).join(lines) + ']' + NL_ + NL_)
        body += ('/-- Row certificates %d..%d. -/' % (first, first + len(part) - 1) + NL_
                 + 'def hrows7_%d : List HRow :=' % ci + NL_ + '  ' + ' ++ '.join(names) + NL_ + NL_)
        body += ('set_option maxHeartbeats 1000000 in' + NL_
                 + '-- the kernel checks of all the chunks count toward the heartbeats of this one declaration' + NL_)
        body += 'theorem hrows7_%d_ok : hrows7_%d.all rowOK = true := by' % (ci, ci) + NL_
        for k, name in enumerate(names):
            body += '  have h%d : %s.all rowOK = true := by decide +kernel' % (k, name) + NL_
        hs = ', '.join('h%d' % k for k in range(len(names)))
        if len(names) == 1:
            body += '  simp only [hrows7_%d, h0]' % ci + NL_
        else:
            body += '  simp only [hrows7_%d, List.all_append, %s, Bool.and_self]' % (ci, hs) + NL_
        prev = 'HeadCert7Row' if ci == 0 else 'HeadCert7Data%d' % (ci - 1)
        outs.append(('HeadCert7Data%d.lean' % ci,
                     DATA_HEADER % (prev, ci, first, first + len(part) - 1, ci, ci) + body + FOOTER))
    n = len(parts)
    imports = NL_.join('public import Zeta2Lean.Z7.Proofs.HeadCert7Data%d' % i for i in range(n))
    names = ['hrows7_%d' % i for i in range(n)]
    outs.append(('HeadCert7Rows.lean', ROWS_HEADER % (imports, len(hrows), ' ++ '.join(names),
                                                     ', '.join(nm + '_ok' for nm in names)) + FOOTER))
    return outs, nchunks


def main():
    rows = parse_rows()
    hrows, levjobs, polejobs, stats = analyse(rows)
    print('states %d, rows with exceptional states %d, incidences %d' % (stats['states'], stats['exc_rows'], stats['inc']))
    print('LevGe jobs %d on %d types; PoleLevGe jobs %d on %d types' % (
        len(levjobs), len(set(k[0] for k in levjobs)), len(polejobs), len(set(k[0] for k in polejobs))))
    if '--audit' in sys.argv:
        bad = 0
        for k, (c0, c, _) in levjobs.items():
            if not levChk(k[0], c0, k[2], c, k[4]):
                bad += 1
                print('levChk FAILS', k[4], len(k[0][1]))
        for k in polejobs:
            if not poleChk(k[0], k[1]):
                bad += 1
                print('poleChk FAILS', k[1])
        print('mirror checks: %d failures' % bad)
    outs = []
    lev_files, nlev, npieces = gen_lev_files(levjobs, int(os.environ.get('HC7_NLEV', '8')))
    outs += lev_files
    outs.append(gen_pole_file(polejobs))
    outs.append(gen_tab(nlev, levjobs, polejobs))
    data_files, nchunks = gen_data(hrows, int(os.environ.get('HC7_CH', '60')))
    outs += data_files
    print('budget %d: %d LevGe pieces, %d row chunks' % (BUDGET, npieces, nchunks))
    for name, text in outs:
        path = os.path.join(HERE, name)
        if '--check' in sys.argv:
            old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
            print(name, 'up to date:', old == text)
        elif '--dry' not in sys.argv:
            old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
            if old == text:
                print('unchanged', name)
                continue
            with open(path, 'w', encoding='utf-8', newline='\n') as fh:
                fh.write(text)
            print('wrote', name)


if __name__ == '__main__':
    main()
