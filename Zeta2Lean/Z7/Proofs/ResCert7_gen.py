#!/usr/bin/env python3
"""Generator of the E-certificate data of `ResCert7`.

  python3 Zeta2Lean/Z7/Proofs/ResCert7_gen.py            write ResCert7Data.lean
  python3 Zeta2Lean/Z7/Proofs/ResCert7_gen.py --check    only compare with the files on disk
  python3 Zeta2Lean/Z7/Proofs/ResCert7_gen.py --selftest also test the floor-sum formula of E
                                                         against the literal localModel (random u, q, k0)

Only the Lean kernel checks of the data matter for soundness (`resECerts7_ok`, `resRows7_keys`);
this script documents where the data come from.

The floor-sum form of E (Lean: `sysE7`, `LineSys7.val`, `localModel_E_eq_sysE7`), 20 lines
ell_j(x) = (LA[j] x + LB[j]) / 80:
  j = 0..5    numerator upper ends (1 - eta_m) x - 1/2      floor,   weight +1
  j = 6..11   numerator lower ends eta_m x - 1/2            floor,   weight -1
  j = 12..15  pole-level upper ends (1 - l/20) x, l = 0..3  floor,   weight -1
  j = 16..19  pole-level lower ends (l/20) x                ceiling, weight +1
  constant -4;   E(localModel u q k0) = val(40u/q, k0/q) + [q | 2 k0 - 40 u]   (q odd, k0 < q).
A certificate (Lean: `ECert7`) of [a, b) = [pa/qa, pb/qb) is <pa, qa, pb, qb, sig, ord>, where ord
is the order of the 20 lines by their fractional parts beta_j = ell_j - N_j (N_j = integer part at
the midpoint), sorted by (80 qa beta_j(a), 80 qb beta_j(b)); sig = min of the prefix sums
V0 - sum_{i<p} W[ord[i]], V0 = sum_j W_j (N_j + [j ceiling]) - 4.  `ECert7.ok` re-checks everything.
"""
import os
import random
import re
import sys
from fractions import Fraction as F
import math

HERE = os.path.dirname(os.path.abspath(__file__))
DENTABLE = os.path.join(HERE, '..', 'DenTable.lean')
OUT_RES = os.path.join(HERE, 'ResCert7Data.lean')

ETA = [5, 7, 7, 9, 11, 13]
LA = [2 * (40 - e) for e in ETA] + [2 * e for e in ETA] + [80, 76, 72, 68] + [0, 4, 8, 12]
LB = [-40] * 12 + [0] * 8
LW = [1] * 6 + [-1] * 6 + [-1] * 4 + [1] * 4
NL = 20
CEIL = [j >= 16 for j in range(NL)]


def ell(j, x):
    return (LA[j] * x + LB[j]) / F(80)


def Efl(x, y):
    s = -4
    for j in range(NL):
        z = ell(j, x) - y
        s += LW[j] * (math.ceil(z) if CEIL[j] else math.floor(z))
    return s


def Nmid(pa, qa, pb, qb):
    P = pa * qb + pb * qa
    Q = 2 * qa * qb
    return [(LA[j] * P + LB[j] * Q) // (80 * Q) for j in range(NL)]


def sv(j, N, P, Q):
    return LA[j] * P + LB[j] * Q - 80 * Q * N[j]


def make(pa, qa, pb, qb):
    """The certificate of [pa/qa, pb/qb); asserts the conditions checked by `ECert7.ok`."""
    assert qa > 0 and qb > 0 and pa * qb < pb * qa
    N = Nmid(pa, qa, pb, qb)
    u = [sv(j, N, pa, qa) for j in range(NL)]
    w = [sv(j, N, pb, qb) for j in range(NL)]
    for j in range(NL):
        assert 0 <= u[j] <= 80 * qa and 0 <= w[j] <= 80 * qb, (pa, qa, pb, qb, j)
        if not CEIL[j]:
            assert u[j] < 80 * qa, (pa, qa, pb, qb, j)
    order = sorted(range(NL), key=lambda j: (u[j], w[j]))
    for i in range(NL - 1):
        j, j2 = order[i], order[i + 1]
        assert u[j] <= u[j2] and w[j] <= w[j2], ("lines cross inside", pa, qa, pb, qb)
    V0 = sum(LW[j] * (N[j] + (1 if CEIL[j] else 0)) for j in range(NL)) - 4
    pref = [V0]
    for j in order:
        pref.append(pref[-1] - LW[j])
    return dict(sig=min(pref), order=order)


# ---- literal transcription of `localModel ... .E` (for --selftest) ----------------------------------
def apole(u, k):
    m = min(k, 40 * u - k)
    return 1 if m < 2 * u else 2 if m < 4 * u else 3 if m < 6 * u else 4


def mu(u, c):
    return sum(1 for e in ETA if e * u <= c < 40 * u - e * u)


def E_localModel(u, q, k0):
    n = 40 * u
    E = 0
    for j in range(n // q + 1):
        if k0 + j * q <= n:
            E -= apole(u, k0 + j * q)
    for t in range(n // q + 2):
        c = k0 + t * q - (q + 1) // 2
        if 0 <= c < n and mu(u, c) != 0:
            E += mu(u, c)
    if (2 * k0 - n) % q == 0:
        E += 1
    return E


def selftest(trials=3000, seed=1):
    rnd = random.Random(seed)
    odd = [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
           83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
    for _ in range(trials):
        u = rnd.randint(0, 60)
        q = rnd.choice(odd)
        k0 = rnd.randrange(q)
        d = 1 if (2 * k0 - 40 * u) % q == 0 else 0
        assert E_localModel(u, q, k0) == Efl(F(40 * u, q), F(k0, q)) + d, (u, q, k0)
    print('selftest: floor-sum formula = literal localModel E on %d random (u, q odd, k0)' % trials)


# ---- the table rows ------------------------------------------------------------------------------------
def parse_rows(path, name):
    txt = open(path, encoding='utf-8').read()
    i = txt.index('def %s : List DenRow := [' % name)
    j = txt.index('\n]', i)
    return [tuple(int(g) for g in m.groups())
            for m in re.finditer(r'⟨(\d+), (\d+), (\d+), (\d+), (\d+), ', txt[i:j])]


def cert_line(an, ad, bn, bd, sg, o):
    return '  ⟨%d, %d, %d, %d, %d, [%s]⟩' % (an, ad, bn, bd, sg, ', '.join(map(str, o)))


def chunked(prefix, certs, CH, what):
    out = []
    chunks = [certs[i:i + CH] for i in range(0, len(certs), CH)]
    for ci, ch in enumerate(chunks):
        out.append('/-- Certificates of rows %d..%d of `%s`. -/\ndef %s_%d : List ECert7 := [\n%s]\n'
                   % (ci * CH, ci * CH + len(ch) - 1, what, prefix, ci, ',\n'.join(cert_line(*c) for c in ch)))
    return out, len(chunks)


RES_HEADER = '''module

public import Zeta2Lean.Z7.Proofs.ResCert7Floor

@[expose] public section

/-!
# Sweep certificates for the residue rows `resRows7` (data of `ResCert7`, generated)

Generated by `Zeta2Lean/Z7/Proofs/ResCert7_gen.py` (see also `notes/ResCert7.md`): for every row
`[a, b) × f` of `resRows7` (one period `[20, 60)`), a certificate
`⟨an, ad, bn, bd, 4 - f, ord⟩ : ECert7` of the 20-line system `sysE7`, where `ord` is the order of
the lines by their fractional parts on `[a, b)`.  Only the kernel checks below matter for
soundness:
* `resECerts7_ok`: every certificate is valid (`ECert7.ok sysE7`, `decide +kernel`, %d chunks);
* `resRows7_keys`: the certificates are those of the rows, in order (same interval, `sig = 4 - f`).
The minimum of the prefix sums equals `4 - f` exactly on every row (`E_min = 4 - f⁰`).
-/

set_option linter.style.longLine false

namespace Zeta2.Z7
'''

RES_FOOTER = '''
/-- All residue certificates. -/
def resECerts7 : List ECert7 :=
  %s

/-- The key `(pa, qa, pb, qb, sig)` of a certificate. -/
def ECert7.key (c : ECert7) : ℤ × ℤ × ℤ × ℤ × ℤ := (c.pa, c.qa, c.pb, c.qb, c.sig)

/-- The key of a residue row: its interval and the bound `4 - f`. -/
def RC7.rowKey (r : DenRow) : ℤ × ℤ × ℤ × ℤ × ℤ := (r.an, r.ad, r.bn, r.bd, 4 - (r.f : ℤ))

%s
theorem resECerts7_ok : resECerts7.all (ECert7.ok sysE7) = true := by
  simp only [resECerts7, List.all_append, %s, Bool.and_self]

/-- The certificates are those of the rows of `resRows7`, in order. -/
theorem resRows7_keys : resRows7.map RC7.rowKey = resECerts7.map ECert7.key := by
  decide +kernel

/-- Every residue row has a valid certificate with its interval and `sig = 4 - f`. -/
theorem resRows7_cert (row : DenRow) (hrow : row ∈ resRows7) :
    ∃ c ∈ resECerts7, c.ok sysE7 = true ∧ c.pa = row.an ∧ c.qa = row.ad ∧ c.pb = row.bn ∧
      c.qb = row.bd ∧ c.sig = 4 - (row.f : ℤ) := by
  have hmem : RC7.rowKey row ∈ resECerts7.map ECert7.key := by
    rw [← resRows7_keys]
    exact List.mem_map_of_mem hrow
  obtain ⟨c, hc, hkey⟩ := List.mem_map.1 hmem
  refine ⟨c, hc, List.all_eq_true.1 resECerts7_ok c hc, ?_⟩
  simp only [ECert7.key, RC7.rowKey, Prod.mk.injEq] at hkey
  exact ⟨hkey.1, hkey.2.1, hkey.2.2.1, hkey.2.2.2.1, hkey.2.2.2.2⟩

end Zeta2.Z7
'''

def gen_res(den, CH=98):
    res = parse_rows(den, 'resRows7')
    assert len(res) == 980
    certs = []
    for (an, ad, bn, bd, f) in res:
        c = make(an, ad, bn, bd)
        assert c['sig'] == 4 - f, (an, ad, bn, bd, f, c['sig'])
        certs.append((an, ad, bn, bd, 4 - f, c['order']))
    parts, nch = chunked('resECerts7', certs, CH, 'resRows7')
    names = ['resECerts7_%d' % i for i in range(nch)]
    oks = ''.join('theorem %s_ok : %s.all (ECert7.ok sysE7) = true := by\n  decide +kernel\n\n' % (nm, nm)
                  for nm in names)
    text = (RES_HEADER % nch + '\n' + '\n'.join(parts)
            + RES_FOOTER % (' ++ '.join(names), oks, ', '.join(nm + '_ok' for nm in names)))
    return text


def main():
    if '--selftest' in sys.argv:
        selftest()
    outs = [(OUT_RES, gen_res(DENTABLE))]
    for path, text in outs:
        if '--check' in sys.argv:
            old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
            print(os.path.basename(path), 'up to date:', old == text)
        else:
            with open(path, 'w', encoding='utf-8', newline='\n') as fh:
                fh.write(text)
            print('wrote', os.path.normpath(path))


if __name__ == '__main__':
    main()
