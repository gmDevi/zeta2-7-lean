#!/usr/bin/env python3
"""Generator for Zeta2Lean/Z7/Proofs/MaxU7.lean (Lemma G7 certificate, U <= 71/100 on [0,1]).

usage (from the project root):
  python3 Zeta2Lean/Z7/Proofs/MaxU7_gen.py Zeta2Lean/Z7/Proofs/MaxU7.lean OUT.lean [maxboxes]
The hand-written top of the input file (imports, docstring, convexity lemmas, `Upot_expand`), up to
the generated-section marker "/-! ## Certified values of `log`", is kept verbatim; the rest is
regenerated (with `maxboxes`, only the first boxes and a `sorry` for `MaxU7_proof`).  Everything is exact `Fraction` arithmetic except the float
box search, whose output is re-verified exactly with the certified rational log enclosures.
"""
from fractions import Fraction as Fr
import math
import sys

T = [(1, 0), (1, 2), (1, 4), (-1, 5), (1, 6), (-2, 7), (-1, 9), (-1, 11), (-1, 13), (1, 27),
     (1, 29), (1, 31), (2, 33), (-1, 34), (1, 35), (-1, 36), (-1, 38), (-1, 40)]
TARGET = Fr(71, 100)
CHI = Fr(6931471808, 10**10)   # log 2 upper (Numerics.log_two_le_d9)
CLO = Fr(6931471803, 10**10)   # log 2 lower (Numerics.d9_le_log_two)
DEN = 10**15


def lit(x):
    x = Fr(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "(%d / %d : ℝ)" % (x.numerator, x.denominator)


def zexpr(p40):
    return "(%d : ℝ) / 40 - κ" % p40


def Fxf(z):
    z = float(z)
    return 0.0 if z == 0 else z * math.log(abs(z)) - z


def plan(a, b):
    """list of (kind, w, p40, data) on the box [a,b]; kind 'C' (chord: data = (z1, z2)) or
    'T' (tangent at the midpoint: data = z0)."""
    m = (a + b) / 2
    out = []
    for w, p40 in T:
        p = Fr(p40, 40)
        pos = p >= b
        assert pos or p <= a
        if (w > 0) == pos:
            out.append(('C', w, p40, (p - b, p - a)))
        else:
            out.append(('T', w, p40, p - m))
    return out


def fbound(a, b):
    ea = eb = 0.0
    for kind, w, p40, d in plan(a, b):
        p = Fr(p40, 40)
        if kind == 'C':
            z1, z2 = d
            ea += w * Fxf(z2)
            eb += w * Fxf(z1)
        else:
            z0 = d
            s = math.log(abs(float(z0)))
            ea += w * (Fxf(z0) + s * float(p - a - z0))
            eb += w * (Fxf(z0) + s * float(p - b - z0))
    return max(ea, eb)


def boxes(ftarget=0.7095):
    res = []
    stack = [(Fr(k, 40), Fr(k + 1, 40)) for k in range(39, -1, -1)]
    while stack:
        a, b = stack.pop()
        if fbound(a, b) <= ftarget:
            res.append((a, b))
        else:
            m = (a + b) / 2
            stack += [(m, b), (a, m)]
    res.sort()
    return res


# ---------- certified log enclosures (mirror of Numerics.lean) ----------
def Slog(z):
    return 2 * (z + z**3 / 3 + z**5 / 5 + z**7 / 7 + z**9 / 9 + z**11 / 11)


def Rlog(z):
    return 2 * z**13 / (13 * (1 - z**2))


def rdown(x):
    return Fr(math.floor(x * DEN), DEN)


def rup(x):
    return Fr(math.ceil(x * DEN), DEN)


def logcert(q):
    """(lo, hi, lean proof of lo <= log q, lean proof of log q <= hi), q > 0 rational."""
    q = Fr(q)
    if q >= 1:
        k = 0
        while q / 2**(k + 1) >= 1:
            k += 1
        r = q / 2**k
        z = (r - 1) / (r + 1)
        hi = rup(Slog(z) + Rlog(z) + k * CHI)
        lo = rdown(Slog(z) + k * CLO)
        ph = ("log_le_of_le_mul (q := %s) (z := %s) (U := %s) %d (by norm_num) (by norm_num) "
              "(by norm_num) (by norm_num) (by norm_num [Slog, Rlog])" % (lit(q), lit(z), lit(hi), k))
        pl = ("le_log_of_mul_le (q := %s) (z := %s) (L := %s) %d (by norm_num) (by norm_num) "
              "(by norm_num) (by norm_num [Slog])" % (lit(q), lit(z), lit(lo), k))
    else:
        k = 0
        while q * 2**k < 1:
            k += 1
        r = q * 2**k
        z = (r - 1) / (r + 1)
        hi = rup(Slog(z) + Rlog(z) - k * CLO)
        lo = rdown(Slog(z) - k * CHI)
        ph = ("log_le_of_mul_le (q := %s) (z := %s) (U := %s) %d (by norm_num) (by norm_num) "
              "(by norm_num) (by norm_num) (by norm_num [Slog, Rlog])" % (lit(q), lit(z), lit(hi), k))
        pl = ("le_log_of_le_mul (q := %s) (z := %s) (L := %s) %d (by norm_num) (by norm_num) "
              "(by norm_num) (by norm_num) (by norm_num [Slog])" % (lit(q), lit(z), lit(lo), k))
    assert lo <= hi and hi - lo < Fr(1, 10**6)
    lq = math.log(float(q))
    assert float(lo) - 1e-12 <= lq <= float(hi) + 1e-12
    return lo, hi, pl, ph


def main():
    hdr, out = sys.argv[1], sys.argv[2]
    maxb = int(sys.argv[3]) if len(sys.argv) > 3 else None
    B = boxes()
    assert B[0][0] == 0 and B[-1][1] == 1
    assert all(B[i][1] == B[i + 1][0] for i in range(len(B) - 1))
    full = maxb is None
    if maxb:
        B = B[:maxb]
    Zf = set()
    Zl = set()
    for a, b in B:
        for kind, w, p40, d in plan(a, b):
            if kind == 'C':
                for z in d:
                    if z != 0:
                        Zf.add(z)
            else:
                Zf.add(d)
                Zl.add(d)
    Q = sorted(set(abs(z) for z in Zf))
    H = open(hdr, encoding='utf-8').read()
    MARK = "/-! ## Certified values of `log`"
    if MARK in H:
        H = H[:H.index(MARK)]
    L = [H.rstrip('\n') + "\n"]
    L.append("/-! ## Certified values of `log` and `F` at the grid points (generated) -/\n")
    qid = {}
    lb = {}
    for i, q in enumerate(Q):
        lo, hi, pl, ph = logcert(q)
        qid[q] = i
        lb[q] = (lo, hi)
        L.append("theorem lq%d : %s ≤ Real.log %s ∧ Real.log %s ≤ %s :=\n  ⟨%s,\n   %s⟩\n"
                 % (i, lit(lo), lit(q), lit(q), lit(hi), pl, ph))
    Zs = sorted(Zf)
    zid = {}
    fb = {}
    for i, z in enumerate(Zs):
        zid[z] = i
        q = abs(z)
        lo, hi = lb[q]
        L.append("theorem lz%d : %s ≤ Real.log |%s| ∧ Real.log |%s| ≤ %s :=\n"
                 "  logabs_bounds (by norm_num) (lq%d).1 (lq%d).2\n"
                 % (i, lit(lo), lit(z), lit(z), lit(hi), qid[q], qid[q]))
        if z > 0:
            FL, FU = z * lo - z, z * hi - z
            lem = "Fx_bounds_pos"
        else:
            FL, FU = z * hi - z, z * lo - z
            lem = "Fx_bounds_neg"
        L.append("theorem fz%d : %s ≤ Fx %s ∧ Fx %s ≤ %s := by\n"
                 "  have h := %s (z := %s) (by norm_num) (lz%d).1 (lz%d).2\n"
                 "  constructor <;> linarith [h.1, h.2]\n"
                 % (i, lit(FL), lit(z), lit(z), lit(FU), lem, lit(z), i, i))
        fb[z] = (FL, FU)
    L.append("/-! ## The boxes (generated) -/\n")
    worst = Fr(-10)
    for bi, (a, b) in enumerate(B):
        P = plan(a, b)
        EA = []
        EB = []
        used = set()
        facts = []
        for j, (kind, w, p40, d) in enumerate(P):
            ze = zexpr(p40)
            p = Fr(p40, 40)
            if kind == 'C':
                z1, z2 = d
                if w > 0:
                    facts.append("  have t%d := chord_up_pos (w := %s) (z1 := %s) (z := %s) (z2 := %s) "
                                 "(by norm_num) (by norm_num) (by linarith) (by linarith)"
                                 % (j, lit(w), lit(z1), ze, lit(z2)))
                else:
                    facts.append("  have t%d := chord_up_neg (w := %s) (z1 := %s) (z := %s) (z2 := %s) "
                                 "(by norm_num) (by linarith) (by linarith) (by norm_num)"
                                 % (j, lit(w), lit(z1), ze, lit(z2)))
                EA.append("%s * Fx %s" % (lit(w), lit(z2)))
                EB.append("%s * Fx %s" % (lit(w), lit(z1)))
                used.add(z1)
                used.add(z2)
            else:
                z0 = d
                lem = "tangent_up_pos" if w > 0 else "tangent_up_neg"
                facts.append("  have t%d := %s (w := %s) (z0 := %s) (z := %s) (by norm_num) (by norm_num) "
                             "(by linarith)" % (j, lem, lit(w), lit(z0), ze))
                EA.append("%s * (Fx %s + Real.log |%s| * %s)" % (lit(w), lit(z0), lit(z0), lit(p - a - z0)))
                EB.append("%s * (Fx %s + Real.log |%s| * %s)" % (lit(w), lit(z0), lit(z0), lit(p - b - z0)))
                used.add(z0)

        def evalE(end):
            v = Fr(0)
            for kind, w, p40, d in P:
                p = Fr(p40, 40)
                if kind == 'C':
                    z1, z2 = d
                    z = z2 if end == 'a' else z1
                    if z != 0:
                        v += w * fb[z][1] if w > 0 else w * fb[z][0]
                else:
                    z0 = d
                    c = w * (p - (a if end == 'a' else b) - z0)
                    lo, hi = lb[abs(z0)]
                    v += (w * fb[z0][1] if w > 0 else w * fb[z0][0]) + (c * hi if c > 0 else c * lo)
            return v
        ea, eb = evalE('a'), evalE('b')
        assert ea <= TARGET and eb <= TARGET, (a, b, float(ea), float(eb))
        worst = max(worst, ea, eb)
        hyps = ["Fx_zero"]
        for z in sorted(used):
            if z == 0:
                continue
            hyps += ["(fz%d).1" % zid[z], "(fz%d).2" % zid[z]]
            if z in Zl:
                hyps += ["(lz%d).1" % zid[z], "(lz%d).2" % zid[z]]
        L.append("set_option maxHeartbeats 4000000 in")
        L.append("theorem box%d (κ : ℝ) (ha : %s ≤ κ) (hb : κ ≤ %s) : Upot κ ≤ 71 / 100 := by"
                 % (bi, lit(a), lit(b)))
        L.append("  have hEa : %s ≤ 71 / 100 := by\n    linarith [%s]" % (" + ".join(EA), ", ".join(hyps)))
        L.append("  have hEb : %s ≤ 71 / 100 := by\n    linarith [%s]" % (" + ".join(EB), ", ".join(hyps)))
        L.append("  have P1 := mul_le_mul_of_nonneg_left hEa (by linarith : (0 : ℝ) ≤ %s - κ)" % lit(b))
        L.append("  have P2 := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ κ - %s)" % lit(a))
        L += facts
        L.append("  linarith [Upot_expand κ, %s]\n"
                 % ", ".join(["t%d" % j for j in range(len(P))] + ["P1", "P2"]))
    if full:
        L.append("/-- `U ≤ 71/100` on `[0, 1]`: the %d boxes cover `[0, 1]`. -/" % len(B))
        L.append("theorem Upot_le (κ : ℝ) (h0 : 0 ≤ κ) (h1 : κ ≤ 1) : Upot κ ≤ 71 / 100 := by")
        n = len(B)
        for bi, (a, b) in enumerate(B):
            lo = "(by linarith)" if bi == 0 else "hk%d.le" % (bi - 1)
            if bi < n - 1:
                L.append("  rcases le_or_gt κ %s with h | hk%d" % (lit(b), bi))
                L.append("  · exact box%d κ %s h" % (bi, lo))
            else:
                L.append("  exact box%d κ %s (by linarith)" % (bi, lo))
        L.append("\nend MaxU7Cert\n")
        L.append("theorem MaxU7_proof : Stmt_MaxU7 g7 := by")
        L.append("  intro κ h0 h1")
        L.append("  unfold g7")
        L.append("  exact MaxU7Cert.Upot_le κ h0 h1\n")
    else:
        L.append("end MaxU7Cert\n")
        L.append("theorem MaxU7_proof : Stmt_MaxU7 g7 := by")
        L.append("  sorry\n")
    L.append("end Zeta2.Z7\n\nend\n")
    open(out, 'w', encoding='utf-8', newline='\n').write("\n".join(L))
    print("boxes", len(B), "logs", len(Q), "Fx points", len(Zs), "worst box bound", float(worst),
          "margin", float(TARGET - worst))


if __name__ == '__main__':
    main()
