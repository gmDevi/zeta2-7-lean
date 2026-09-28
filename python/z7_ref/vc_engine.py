"""Independent exact engine (own code): Laurent data of R_n at every pole, collapsed residues c_i, centred rational part.

R(-k+eps) = eps^{-a_k} Phi_k(eps),  r_{i,k} = [eps^{a_k-i}] Phi_k(eps)
Phi_k(0)  = (n-2k)^delta * prod_c (c-k+1/2)^{mu(c)} / prod_{k'!=k} (k'-k)^{a_k'}
          = g_k / (2^N (n!)^4),   g_k = (n-2k)^delta * O_k * C(n,k)^4 * prod_{k'!=k} (k'-k)^{4-a_k'}   (integer)
          (O_k = prod_c (2(c-k)+1)^{mu(c)}, signed);  at the centre k=n/2 with delta=1 the factor is 2*eps instead.
Phi_k(eps)/Phi_k(0) = exp(sum_r (-1)^{r+1} p_r eps^r / r),  p_r = sum_c mu/(c-k+1/2)^r + delta (2/(n-2k))^r - sum a_k'/(k'-k)^r
Scaled: P_r = Lam^r p_r (Lam = lcm(1..2n)),  E_s = s! Lam^s e_s:  E1 = P1, E2 = P1^2-P2, E3 = P1^3-3P1P2+2P3.
r_{i,k} = Rn_{i,k} / Q,  Q = 2^N (n!)^4 * 6 * Lam^3,  Rn = g_k E_s (6/s!) Lam^{3-s},  s = a_k - i (centre: a_k-1-i, g doubled).

S_m = int R'''(t+1/2-m) dt = sum_{i,k} r_{i,k} (-(i)_3) [ J_{i+3} + A_{k-m}(i+3) ],  J_s = int (t+1/2)^{-s} dt,
A_d(s) = -s sum_{l<d} (l+1/2)^{-s-1}  (d>0);  +s sum_{l=1}^{|d|} (1/2-l)^{-s-1} = s(-1)^{s+1} sum_{l<|d|} (2/(2l+1))^{s+1} (d<0).
J_odd = 0, so S = rho + (-6 c_1) J_4 + (-60 c_3) J_6 ;  J_6 = 768 zeta_2(7)  =>  Z = -46080 c_3.
"""
import sys, math, time, random
from fractions import Fraction as Fr
from vc_common import build, runs_of, mu_map, lcm_upto, primes_upto, vq

FACT_SMALL = [1, 1, 2, 6]


def compute(cfg, n, want_std=False, npts=3, seed=12345, verbose=False):
    t0 = time.time()
    blocks, a, N, SA, delta = build(cfg, n)
    m = n // 2
    assert max(a) <= 4
    runs = runs_of(a)
    Lam = lcm_upto(2 * n)
    Lo = lcm_upto(n)
    while Lo % 2 == 0:
        Lo //= 2
    fact = [1] * (n + 2)
    for i in range(1, n + 2):
        fact[i] = fact[i - 1] * i
    OF = [1] * (n + 2)
    for i in range(1, n + 2):
        OF[i] = OF[i - 1] * (2 * i - 1)

    def oddprod(x1, x2):
        """product of all odd integers in [x1, x2] (x1 <= x2 odd)"""
        if x1 > 0:
            return OF[(x2 + 1) // 2] // OF[(x1 - 1) // 2]
        if x2 < 0:
            cnt = (x2 - x1) // 2 + 1
            v = OF[(-x1 + 1) // 2] // OF[(-x2 - 1) // 2]
            return -v if cnt % 2 else v
        cnt = (-x1 + 1) // 2
        v = OF[cnt] * OF[(x2 + 1) // 2]
        return -v if cnt % 2 else v

    def intprod(w1, w2):
        """product of the nonzero integers in [w1, w2]"""
        if w1 > w2:
            return 1
        if w1 > 0:
            return fact[w2] // fact[w1 - 1]
        if w2 < 0:
            cnt = w2 - w1 + 1
            v = fact[-w1] // fact[-w2 - 1]
            return -v if cnt % 2 else v
        cnt = -w1
        v = fact[-w1] * fact[w2]
        return -v if cnt % 2 else v

    # prefix power sums over odd offsets v = 2u+1, u in [-n, n-1]: OPS[r][u+n] = sum_{u'=-n}^{u-1} (2Lam/v')^r
    OPS = [None] + [[0] * (2 * n + 1) for _ in range(3)]
    acc = [0, 0, 0, 0]
    for idx in range(2 * n + 1):
        for r in (1, 2, 3):
            OPS[r][idx] = acc[r]
        if idx == 2 * n:
            break
        u = idx - n
        v = 2 * u + 1
        assert (2 * Lam) % v == 0
        w = (2 * Lam) // v
        pw = 1
        for r in (1, 2, 3):
            pw *= w
            acc[r] += pw
    # prefix power sums over integer offsets w in [-n, n], w != 0: IPS[r][w+n] = sum_{w'=-n}^{w-1} (Lam/w')^r
    IPS = [None] + [[0] * (2 * n + 2) for _ in range(3)]
    acc = [0, 0, 0, 0]
    for idx in range(2 * n + 2):
        for r in (1, 2, 3):
            IPS[r][idx] = acc[r]
        if idx == 2 * n + 1:
            break
        w_ = idx - n
        if w_ == 0:
            continue
        w = Lam // w_
        assert Lam % w_ == 0
        pw = 1
        for r in (1, 2, 3):
            pw *= w
            acc[r] += pw
    # centred A-sum tables: Tt[q][D] = sum_{l<D} (Lo/(2l+1))^q, q = 5..8, D = 0..m
    Tt = {}
    for q in range(5, 9):
        T = [0] * (m + 1)
        s = 0
        for D in range(1, m + 1):
            v = 2 * (D - 1) + 1
            assert Lo % v == 0
            s += (Lo // v) ** q
            T[D] = s
        Tt[q] = T
    Lopow = [Lo ** e for e in range(9)]
    if want_std:
        Los = lcm_upto(2 * n)
        while Los % 2 == 0:
            Los //= 2
        Tts = {}
        for q in range(5, 9):
            T = [0] * (n + 1)
            s = 0
            for D in range(1, n + 1):
                s += (Los // (2 * D - 1)) ** q
                T[D] = s
            Tts[q] = T
        Lospow = [Los ** e for e in range(9)]
    Lpow = [1, Lam, Lam ** 2, Lam ** 3]
    Q = (1 << N) * fact[n] ** 4 * 6 * Lam ** 3
    # modular point-evaluation checks
    rng = random.Random(seed)
    Pmods = [(1 << 61) - 1, (1 << 89) - 1]
    pts = []
    for PM in Pmods:
        for _ in range(npts):
            t0m = rng.randrange(10 ** 6, PM - 10 ** 6)
            pts.append([PM, t0m, 0])
    if verbose:
        print('tables %.1fs' % (time.time() - t0), flush=True)
    cnum = [0] * 5
    rho_c = 0
    rho_s = 0
    rik_store = {} if n <= 200 else None
    for k in range(n + 1):
        A = a[k]
        if A == 0:
            continue
        centre = (delta == 1 and 2 * k == n)
        O = 1
        for lo, hi in blocks:
            O *= oddprod(2 * (lo - k) + 1, 2 * (hi - k) + 1)
        PP = (fact[n] // (fact[k] * fact[n - k])) ** 4
        for (u1, u2, av) in runs:
            if av < 4:
                PP *= intprod(u1 - k, u2 - k) ** (4 - av)
        if centre:
            g = 2 * O * PP
        elif delta:
            g = (n - 2 * k) * O * PP
        else:
            g = O * PP
        top = A - 1 if centre else A
        smax = top - 1
        P = [0, 0, 0, 0]
        for r in range(1, smax + 1):
            s = 0
            for lo, hi in blocks:
                s += OPS[r][hi - k + 1 + n] - OPS[r][lo - k + n]
            if delta and not centre:
                s += ((2 * Lam) // (n - 2 * k)) ** r
            for (u1, u2, av) in runs:
                s -= av * (IPS[r][u2 - k + 1 + n] - IPS[r][u1 - k + n])
            P[r] = s
        E = [1, P[1], 0, 0]
        if smax >= 2:
            E[2] = P[1] * P[1] - P[2]
        if smax >= 3:
            E[3] = P[1] ** 3 - 3 * P[1] * P[2] + 2 * P[3]
        d = k - m
        for i in range(1, top + 1):
            s = top - i
            Rn = g * E[s] * (6 // FACT_SMALL[s]) * Lpow[3 - s]
            cnum[i] += Rn
            if rik_store is not None:
                rik_store[(i, k)] = Rn
            w3 = -(i * (i + 1) * (i + 2)) * (i + 3)
            q = i + 4
            if d != 0:
                sig = -1 if d > 0 else (1 if i % 2 == 0 else -1)
                rho_c += Rn * (w3 * sig * (1 << q)) * Tt[q][abs(d)] * Lopow[8 - q]
            if want_std and k != 0:
                rho_s += Rn * (w3 * -1 * (1 << q)) * Tts[q][k] * Lospow[8 - q]
            for pt in pts:
                PM, tm = pt[0], pt[1]
                pt[2] = (pt[2] + (Rn % PM) * pow(tm + k, -i, PM)) % PM
        if verbose and k % 200 == 0:
            print('  k=%d %.1fs' % (k, time.time() - t0), flush=True)
    c = [Fr(0)] + [Fr(cnum[i], Q) for i in range(1, 5)]
    rho = Fr(rho_c, Q * Lopow[8])
    out = dict(n=n, N=N, SA=SA, delta=delta, rho=rho, c=c, Z=-46080 * c[3], coefJ6=-60 * c[3], coefJ4=-6 * c[1])
    if want_std:
        out['rho_std'] = Fr(rho_s, Q * Lospow[8])
    if rik_store is not None:
        out['rik'] = {key: Fr(v, Q) for key, v in rik_store.items()}
    # point checks: R(t0) from the product formula
    mu = mu_map(blocks)
    chk = []
    for PM, tm, acc_ in pts:
        pf = acc_ * pow(Q % PM, -1, PM) % PM
        half = pow(2, -1, PM)
        num = pow((2 * tm + n) % PM, delta, PM)
        for cc, mm in mu.items():
            num = num * pow((tm + half + cc) % PM, mm, PM) % PM
        den = 1
        for k in range(n + 1):
            den = den * pow((tm + k) % PM, a[k], PM) % PM
        direct = num * pow(den, -1, PM) % PM
        chk.append(pf == direct)
    out['pointcheck'] = chk
    out['secs'] = time.time() - t0
    return out


def R_deriv_at_halfint(cfg, n, c0, order):
    """R^{(order)}(-1/2 - c0) computed directly from the product formula (exact Fractions, small n only)."""
    blocks, a, N, SA, delta = build(cfg, n)
    mu = mu_map(blocks)
    x0 = Fr(-1, 2) - c0
    z = mu.get(c0, 0)         # zero of order z at x0
    if z > order:
        return Fr(0)
    # Psi(eps) = R(x0+eps)/eps^z ; log-derivative power sums
    Psi0 = Fr(1)
    lin = []                  # (root offset beta, multiplicity): factor (beta + eps)^mult
    if delta:
        lin.append((Fr(2) * x0 + n, 1, 'lin2'))
    for cc, mm in mu.items():
        if cc == c0:
            continue
        lin.append((x0 + Fr(1, 2) + cc, mm, 'num'))
    for k in range(n + 1):
        if a[k]:
            lin.append((x0 + k, -a[k], 'den'))
    L = order - z
    p = [Fr(0)] * (L + 1)
    for beta, mm, kind in lin:
        if kind == 'lin2':
            # (2 x0 + n + 2 eps) = beta (1 + 2 eps/beta)
            Psi0 *= beta ** mm
            for r in range(1, L + 1):
                p[r] += mm * (Fr(2) / beta) ** r
        else:
            Psi0 *= beta ** mm
            for r in range(1, L + 1):
                p[r] += mm * (1 / beta) ** r
    e = [Fr(1)] + [Fr(0)] * L
    for s in range(1, L + 1):
        tot = Fr(0)
        for r in range(1, s + 1):
            tot += (-1) ** (r + 1) * p[r] * e[s - r]
        e[s] = tot / s
    return math.factorial(order) * Psi0 * e[L]


if __name__ == '__main__':
    from vc_common import CANDS
    name = sys.argv[1]
    n = int(sys.argv[2])
    res = compute(CANDS[name], n, want_std=True, verbose=True)
    print('pointcheck', res['pointcheck'], 'secs %.1f' % res['secs'])
    print('c_i zero?', [res['c'][i] == 0 for i in range(1, 5)])
