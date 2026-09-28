"""Residue-level certificates for GAP 2 (denominators) of the pair {zeta_2(7), zeta_2(9)}, config E.

Reproduces, verbatim, the certificate data `certs0 ... certs9` / `allCerts` of
`Zeta2Lean/Pair/Proofs/Denominators.lean` (only the Lean kernel check of the data matters for
soundness; this script documents where the data come from).

Setting (configuration E: n = 40 m, h = m * (-17, 1, 2, 3, 5, 6)).  For an odd prime q with
q^2 > 2n and x = n/q, y = k/q, the level-one residue count `Wlev n h q k` equals

    Vl(x, y) = sum_j LW[j] * floor(ell_j(x) - y) - 6 floor(y),   ell_j(x) = (LA[j] x + LB[j]) / 80,

with 13 lines: six numerator upper ends (1 + eta_m) x - 1/2, six numerator lower ends
-eta_m x - 1/2 and the pole line x (Lean: `Wlev_eq_Vl`).  A certificate for an interval [a, b)
records the integer parts N_j of the lines at the midpoint (recomputed in Lean, `CC.N`) and the
order `ord` of the fractional parts beta_j(x) = ell_j(x) - N_j, which must be the same (weakly) at
both end points; then for every x in [a, b) and every y in [0, 1) off the numerator break points,
Vl(x, y) >= sig = min of the prefix sums (Lean: `certOK_sound`).  Cells of the line arrangement on
[1, 41) (candidate break points (1/(2 d)) Z, d = |gamma - gamma'|) with the same N, order and sig
are merged, and every merged cell is re-validated.

Also prints K = sum over [1, 81) of (10 - sig)(1/a - 1/b) + 12/81 = 8.9607... (Lean: `margin_T`,
bound 8.97), the constant of the final estimate log(odd part of D) <= (K + eps) n.

usage: python pair_den_certs.py OUT.lean [CHUNK=80]
"""
from fractions import Fraction as F
import math
import sys

C = [-17, 1, 2, 3, 5, 6]
LA = [2 * (40 + c) for c in C] + [-2 * c for c in C] + [80]
LB = [-40] * 12 + [0]
LW = [1] * 6 + [-1] * 6 + [-6]


def sv(j, N, P, Q):
    """80 Q (ell_j(P/Q) - N_j), an integer."""
    return LA[j] * P + LB[j] * Q - 80 * Q * N[j]


def Nmid(pa, qa, pb, qb):
    """Integer parts of the 13 lines at the midpoint of [pa/qa, pb/qb] (as `CC.N` in Lean)."""
    P = pa * qb + pb * qa
    Q = 2 * qa * qb
    return [(LA[j] * P + LB[j] * Q) // (80 * Q) for j in range(13)]


def breakpoints(lo, hi):
    """Candidate break points of the arrangement in [lo, hi]."""
    gam = [F(LA[j], 80) for j in range(13)] + [F(0)]
    diffs = set()
    for g1 in gam:
        for g2 in gam:
            d = abs(g1 - g2)
            if d != 0:
                diffs.add(d)
    pts = set()
    for d in diffs:
        j0 = math.ceil(lo * 2 * d)
        j1 = math.floor(hi * 2 * d)
        for j in range(j0, j1 + 1):
            pts.add(F(j) / (2 * d))
    pts.add(F(lo))
    pts.add(F(hi))
    return sorted(p for p in pts if lo <= p <= hi)


def make(a, b):
    """Certificate for [a, b); asserts exactly the conditions checked by `certOK` in Lean."""
    pa, qa, pb, qb = a.numerator, a.denominator, b.numerator, b.denominator
    N = Nmid(pa, qa, pb, qb)
    u = [sv(j, N, pa, qa) for j in range(13)]
    w = [sv(j, N, pb, qb) for j in range(13)]
    for j in range(13):
        assert 0 <= u[j] <= 80 * qa and 0 <= w[j] <= 80 * qb, (a, b, j)
        assert not (u[j] == 80 * qa and w[j] == 80 * qb), (a, b, j)
        assert j < 12 or u[j] < 80 * qa, (a, b, j)
    order = sorted(range(13), key=lambda j: (u[j], w[j]))
    for i in range(12):
        j, j2 = order[i], order[i + 1]
        assert u[j] <= u[j2] and w[j] <= w[j2], ("cross", a, b)
    V0 = sum(LW[j] * N[j] for j in range(13))
    pref = [V0]
    for j in order:
        pref.append(pref[-1] - LW[j])
    return dict(pa=pa, qa=qa, pb=pb, qb=qb, sig=min(pref), order=order)


def Kconst(certs, T, tail):
    """sum over [1, 1 + 40 T) of (10 - sig)(1/a - 1/b) + tail/(1 + 40 T), exact."""
    tot = F(0)
    for t in range(T):
        for c in certs:
            a = F(c['pa'], c['qa']) + 40 * t
            b = F(c['pb'], c['qb']) + 40 * t
            tot += max(0, 10 - c['sig']) * (1 / a - 1 / b)
    return tot + F(tail, 1 + 40 * T)


def merged_certs():
    bps = breakpoints(F(1), F(41))
    certs = [make(bps[i], bps[i + 1]) for i in range(len(bps) - 1)]
    merged = []
    for c in certs:
        if merged:
            p = merged[-1]
            if (Nmid(p['pa'], p['qa'], p['pb'], p['qb']) == Nmid(c['pa'], c['qa'], c['pb'], c['qb'])
                    and p['order'] == c['order'] and p['sig'] == c['sig']):
                m = make(F(p['pa'], p['qa']), F(c['pb'], c['qb']))
                assert m['sig'] == p['sig'] and m['order'] == p['order']
                merged[-1] = m
                continue
        merged.append(c)
    assert F(merged[0]['pa'], merged[0]['qa']) == 1 and F(merged[-1]['pb'], merged[-1]['qb']) == 41
    for a, b in zip(merged, merged[1:]):
        assert (a['pb'], a['qb']) == (b['pa'], b['qa'])
    return merged


if __name__ == "__main__":
    merged = merged_certs()
    print("merged certs", len(merged), "sig range", min(c['sig'] for c in merged),
          max(c['sig'] for c in merged))
    print("K (intervals [1, 81), tail 12/81) =", float(Kconst(merged, 2, 12)))
    CH = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    lines = ["  ⟨%d, %d, %d, %d, %d, [%s]⟩" % (c['pa'], c['qa'], c['pb'], c['qb'], c['sig'],
             ", ".join(str(j) for j in c['order'])) for c in merged]
    chunks = [lines[i:i + CH] for i in range(0, len(lines), CH)]
    out = []
    for ci, ch in enumerate(chunks):
        out.append("def certs%d : List CC := [\n%s]\n" % (ci, ",\n".join(ch)))
    out.append("def allCerts : List CC :=\n  "
               + " ++ ".join("certs%d" % i for i in range(len(chunks))) + "\n")
    with open(sys.argv[1] if len(sys.argv) > 1 else "certdata.lean", "w", encoding="utf-8",
              newline="\n") as fh:
        fh.write("\n".join(out))
    print("chunks", len(chunks))
