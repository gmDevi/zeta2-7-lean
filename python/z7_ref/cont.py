"""Continuum exponent function f(x) of the kernel theorem, for the cand3-type family (profiles in cells of 1/Qc).

For a large prime q with x = n/q, a residue class at y = k0/q in [0,1) has the local model
  poles  v = -j,  j = 0..floor(x - y),  order a((y+j)/x)
  zeros  v = -s/2 (s odd), multiplicity mu((y+s/2)/x)   [left-limit convention irrelevant: boundaries handled below]
  delta  v = y - x/2  if 2y - x in Z
  pairs  pole j with d = y + j - x/2 != 0:  sigma odd < 2|d|, eval point v = -j + sgn(d) sigma/2, sign sgn(d).
For fixed x the type is piecewise constant in y; at every breakpoint all 2^m combinations of the m events located
there are taken (conservative: covers every discrete interleaving).  Per x:
  B-bound = max(min_y La, min_y Lb);  G-bound = min_y LG;  c3-bound = min_y L3
  f(x) = max(0, -min(B-bound, G-bound), -c3-bound).
f is constant between consecutive points of the candidate set C = U_{d=1..Qc} (Qc/(2d)) Z  (slopes in (1/Qc)Z).
"""
import sys, os, json, itertools
from fractions import Fraction as Fr
from math import floor, ceil
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from levels import class_levels_local, kernel_step_bound, INF

class Profile:
    def __init__(self, acells, etas, Qc=40, delta=1):
        self.ac = list(acells); self.etas = [Fr(e, Qc) for e in etas]; self.Qc = Qc; self.delta = delta
        self.full = list(acells) + list(acells[::-1])
    def a_at(self, kap, side):
        """pole order at kappa; side = -1 (left limit) / +1 (right limit) / 0 (interior)"""
        Qc = self.Qc
        if kap < 0 or kap > 1: return 0
        # cell index for left half uses floor(Qc*kap); right half floor(Qc*(1-kap)) ; take one-sided limits
        eps = Fr(1, 10 ** 9) * side
        z = kap + eps
        if z < 0 or z > 1: return 0
        if z * 2 < 1: return self.ac[min(int(floor(Qc * z)), Qc // 2 - 1)]
        if z * 2 > 1: return self.ac[min(int(floor(Qc * (1 - z))), Qc // 2 - 1)]
        return self.ac[-1]
    def mu_at(self, gam, side):
        eps = Fr(1, 10 ** 9) * side
        z = gam + eps
        return sum(1 for e in self.etas if e <= z < 1 - e)

def events(prof, x):
    """y-positions in [0,1) of all type changes, as a sorted list of Fractions (plus 0)."""
    Qc = prof.Qc
    ys = set([Fr(0)])
    J = int(floor(x)) + 2
    S = int(2 * x) + 4
    def add(y):
        y = y - floor(y)
        ys.add(y)
    for j in range(0, J + 1):
        add(x - j)                                  # pole existence y + j <= x
        for b in range(0, Qc + 1): add(Fr(b, Qc) * x - j)   # pole-order cells
        # exposure: 2|y + j - x/2| = sigma  -> y = x/2 - j +- sigma/2
        for sg in range(1, S + 2, 2):
            add(x / 2 - j + Fr(sg, 2)); add(x / 2 - j - Fr(sg, 2))
        add(x / 2 - j)                              # d = 0
    for s in range(-S, S + 1):
        if s % 2 == 0: continue
        for e in prof.etas:
            add(e * x - Fr(s, 2)); add((1 - e) * x - Fr(s, 2))
    for m in range(-2 * S, 2 * S + 1):
        add((x + m) / 2)                            # delta points
    return sorted(ys)

def local_model(prof, x, y, st):
    """st: function(name) -> side (-1/+1/0) choosing the one-sided state of each event family at this y."""
    items = []; pairs = []
    j = 0
    while y + j <= x + (0 if st('exist', j) >= 0 else -Fr(1, 10 ** 12)):
        kap = (y + j) / x
        a = prof.a_at(kap, st('cell', j))
        if a: items.append((Fr(-j), -a))
        d = y + j - x / 2
        if d != 0:
            sg = 1 if d > 0 else -1
            sig = 1
            side = st('exp', j)
            while (sig < 2 * abs(d)) or (sig == 2 * abs(d) and side > 0):
                if a: pairs.append((Fr(-j), Fr(-j) + Fr(sg * sig, 2), sg))
                sig += 2
        j += 1
    S = int(2 * x) + 4
    for s in range(-S, S + 1):
        if s % 2 == 0: continue
        gam = (y + Fr(s, 2)) / x
        m = prof.mu_at(gam, st('zero', s))
        if m: items.append((Fr(-s, 2), m))
    if prof.delta and (2 * y - x).denominator == 1 and int(2 * y - x) % 2 == 0:
        items.append((y - x / 2, prof.delta))
    return items, pairs

def f_at(prof, x, M=12, cache=None, detail=False):
    """x must be generic (not in the candidate set): then every breakpoint y* carries the events of ONE line, all of
    which switch at the same discrete threshold; the realizable local types are exactly the open-interval types plus
    the point types at the delta/centre points 2y - x in 2Z (the class containing t = -n/2)."""
    if cache is None: cache = {}
    ys = events(prof, x)
    pts = []
    for i, y in enumerate(ys):
        y2 = ys[i + 1] if i + 1 < len(ys) else Fr(1)
        pts.append(('mid', (y + y2) / 2))
        if (2 * y - x).denominator == 1 and int(2 * y - x) % 2 == 0:
            pts.append(('pt', y))
    minLa = minLb = minLG = minL3 = INF
    worst = {}
    types = {}
    for kind, y in pts:
        states = [lambda name, arg: 0]
        for st in states:
            items, pairs = local_model(prof, x, y, st)
            key = (tuple(sorted(items)), tuple(sorted(pairs)))
            if key not in cache:
                cache[key] = class_levels_local(items, pairs, M)
            L = cache[key]
            types[key] = L
            if L['exposed'] and L['La'] < minLa: minLa = L['La']; worst['La'] = (y, key)
            if L['Lb'] < minLb: minLb = L['Lb']; worst['Lb'] = (y, key)
            minLG = min(minLG, L['LG']); minL3 = min(minL3, L['L3'])
    Kb, kc = kernel_step_bound(list(types.values()))
    Bb = max(minLa, minLb, Kb)
    f = max(0, -min(Bb, minLG), -minL3)
    if detail: return f, dict(La=minLa, Lb=minLb, K=Kb, c=str(kc) if kc is not None else None, LG=minLG, L3=minL3,
                              worst=worst, ntypes=len(types))
    return f

def f0_at(prof, x):
    """plain class bound (= residue level):  max(0, 4 - min E over classes with a bad pair); 40-periodic in x."""
    ys = events(prof, x)
    pts = []
    for i, y in enumerate(ys):
        y2 = ys[i + 1] if i + 1 < len(ys) else Fr(1)
        pts.append((y + y2) / 2)
        if (2 * y - x).denominator == 1 and int(2 * y - x) % 2 == 0: pts.append(y)
    Emin = INF
    for y in pts:
        items, pairs = local_model(prof, x, y, lambda name, arg: 0)
        if pairs:
            Emin = min(Emin, sum(e for _, e in items))
    return max(0, 4 - Emin)

def candidates(Qc, X0, X1):
    s = set()
    for d in range(1, Qc + 1):
        step = Fr(Qc, 2 * d)
        k0 = int(ceil(X0 / step))
        k = k0
        while k * step <= X1:
            if k * step >= X0: s.add(k * step)
            k += 1
    return sorted(s)

if __name__ == '__main__':
    prof = Profile([1, 1, 2, 2, 3, 3] + [4] * 14, [5, 7, 7, 9, 11, 13])
    for xs in sys.argv[1:]:
        x = Fr(xs)
        f, det = f_at(prof, x, detail=True)
        print('x=%s (%.4f) f=%d  La=%s Lb=%s LG=%s L3=%s' % (x, float(x), f, det['La'], det['Lb'], det['LG'], det['L3']))
