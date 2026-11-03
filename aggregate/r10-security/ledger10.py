#!/usr/bin/env python3
"""Round-by-round security ledger of the hidden-u ML-DSA-87 archive certificate (round 10).

What this script does, in order:
  1. Functional checks of the arithmetization against the standard library (hashlib):
     the 72 Keccak layers of keccak.rs, the sponge layout of hidden.rs (src_of, upos_of,
     pad_block), the input-link and mask definitions, the d0/d15 region identities, and the
     false product-of-MLE counterexample.
  2. A port of hidden::build_table9 (with reg7::front, keccak::specs, p3-whir WhirShape) whose
     round counts, coin bytes, singleton counts and per-component element counts are asserted
     against the measured transcripts of RESULTS-r9-hidden-u.md and transcripts/r9-*.txt.
  3. The per-round knowledge errors kappa_i (one entry per registered round), plus the coin
     decoder distances delta_i, for any N and WHIR schedule.
  4. The compiled bounds: classical (CF24 Lemma 9.12 with Lemma 7.15) and quantum (CDHZ
     Theorem 11.3 with Theorem 6.10 and Theorem 8.3), and the parameter search for the
     quantum goal 2^-128 at Q = 2^64, E = 2^20.

No proving and no heavy computation. Usage: python3 ledger10.py [--quick]
"""
import hashlib
import math
import random
import sys
from decimal import Decimal as D, getcontext, ROUND_CEILING

getcontext().prec = 120
LN2 = D(2).ln()

p = 2**64 - 2**32 + 1
QK = D(p) ** 5          # |K|, K = F_p[X]/(X^5 - 3)
B = D(2) ** 319         # the ledger's conservative stand-in for |K| in WHIR terms (round 6)
q = 8380417
HALF = (p + 1) // 2


def bits(e):
    e = D(e)
    if e <= 0:
        return D('Infinity')
    return -e.ln() / LN2


def fmt(e):
    b = bits(e)
    return 'inf' if b == D('Infinity') else f'{b:.3f}'


# ============================================================== 1. functional checks
W, STATE, RATE = 2048, 1600, 136
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
      0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
      0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
      0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]


def idx(x, y, z):
    return 64 * (x + 5 * y) + z


# A layer is (gathers, terms); a term is (sel list over W, kind, uses) with kind in
# 'lin', 'prod', 'chi'. This mirrors keccak.rs theta_a / theta_b / chi.
def theta_a():
    g = [list(range(W))]
    for y in range(5):
        s = list(range(W))
        for c in range(320):
            s[STATE + c] = idx(c // 64, y, c % 64)
        g.append(s)
    sel_a = [1 if s < STATE else 0 for s in range(W)]
    sel_c = [1 if STATE <= s < STATE + 320 else 0 for s in range(W)]
    return g, [(sel_a, 'lin', [0]), (sel_c, 'prod', [1, 2, 3, 4, 5])]


def theta_b():
    g1, g2 = list(range(W)), list(range(W))
    for x in range(5):
        for y in range(5):
            for z in range(64):
                g1[idx(x, y, z)] = STATE + 64 * ((x + 4) % 5) + z
                g2[idx(x, y, z)] = STATE + 64 * ((x + 1) % 5) + (z + 63) % 64
    sel = [1 if s < STATE else 0 for s in range(W)]
    return [list(range(W)), g1, g2], [(sel, 'prod', [0, 1, 2])]


def chi(rnd):
    src = [[None] * 5 for _ in range(5)]
    for x in range(5):
        for y in range(5):
            src[y][(2 * x + 3 * y) % 5] = (x, y)

    def b(xx, yy, z):
        x, y = src[xx][yy]
        return idx(x, y, (z + 64 - ROT[x][y]) % 64)
    g = [list(range(W)) for _ in range(3)]
    for xx in range(5):
        for yy in range(5):
            for z in range(64):
                for k in range(3):
                    g[k][idx(xx, yy, z)] = b((xx + k) % 5, yy, z)
    sel = [0 if s >= STATE else (-1 if s < 64 and (RC[rnd] >> s) & 1 else 1) for s in range(W)]
    return g, [(sel, 'chi', [0, 1, 2])]


def specs():
    out = []
    for r in range(24):
        out += [theta_a(), theta_b(), chi(r)]
    return out


def kind_degree(kind, uses):
    return {'lin': 1, 'prod': len(uses), 'chi': 3}[kind]


def layer_deg(spec):
    return max(kind_degree(k, u) for _, k, u in spec[1])


def apply_layer(spec, row):
    gathers, terms = spec
    out = [0] * W
    for sel, kind, uses in terms:
        for s in range(W):
            if sel[s] == 0:
                continue
            v = [row[gathers[j][s]] for j in uses]
            if kind == 'lin':
                f = v[0]
            elif kind == 'prod':
                f = 1
                for a in v:
                    f = f * a % p
            else:
                t = (1 + v[1]) * (1 - v[2]) % p
                f = v[0] * (1 - t * HALF) % p
            out[s] = (out[s] + (f if sel[s] == 1 else -f)) % p
    return out


def keccak_f(lanes):
    a = list(lanes)
    M = (1 << 64) - 1
    rot = lambda v, n: ((v << n) | (v >> (64 - n))) & M if n else v
    for r in range(24):
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x + 4) % 5] ^ rot(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        bb = [0] * 25
        for x in range(5):
            for y in range(5):
                bb[y + 5 * ((2 * x + 3 * y) % 5)] = rot(a[x + 5 * y], ROT[x][y])
        a = [bb[i] ^ ((~bb[(i % 5 + 1) % 5 + 5 * (i // 5)]) & bb[(i % 5 + 2) % 5 + 5 * (i // 5)]) for i in range(25)]
        a[0] ^= RC[r]
    return a


def enc(lanes):
    return [(p - 1 if (lanes[s // 64] >> (s % 64)) & 1 else 1) if s < STATE else 0 for s in range(W)]


def dec(row):
    lanes = [0] * 25
    for s in range(W):
        if s < STATE:
            assert row[s] in (1, p - 1), 'state cell not +-1'
            if row[s] == p - 1:
                lanes[s // 64] |= 1 << (s % 64)
        else:
            assert row[s] == 0, 'padding cell not 0'
    return lanes


def src_of(qq, s):
    if qq >= 8 or s >= 8 * RATE:
        return None
    b, beta = s // 8, s % 8
    a = RATE * qq + b
    if a < 64:
        return ('mu', a, beta)
    j = a - 64
    return ('u', beta & 3, 2 * j + (beta >> 2))


def upos_of(plane, coef):
    j = coef // 2
    beta = (coef & 1) * 4 + plane
    a = 64 + j
    return a // RATE, 8 * (a % RATE) + beta


def pad_block(suffix=0x1f):
    blk = [0] * RATE
    blk[0] = suffix
    blk[RATE - 1] |= 0x80
    return blk


def functional_checks(quick):
    rng = random.Random(20261024)
    sp = specs()
    # degrees and gather counts of the 72 layers
    assert [layer_deg(s) for s in sp] == [5, 3, 3] * 24
    assert [len(s[0]) for s in sp] == [6, 3, 3] * 24
    print('[check] 72 layers: degrees (5,3,3) x 24, gathers (6,3,3) x 24')
    # signed chi: the code's A (1 - (1 + B)(1 - C)/2) equals A (1 - B + C + BC)/2 and encodes a ^ (~b & c)
    for a in (0, 1):
        for b_ in (0, 1):
            for c in (0, 1):
                A, Bv, Cv = 1 - 2 * a, 1 - 2 * b_, 1 - 2 * c
                code = A * (2 - (1 + Bv) * (1 - Cv))       # twice the code's value, in integers
                signed = A * (1 - Bv + Cv + Bv * Cv)           # twice the signed form
                assert code == signed == 2 * (1 - 2 * (a ^ ((1 - b_) & c)))
    print('[check] signed chi: A(1 - (1+B)(1-C)/2) = A(1 - B + C + BC)/2 = enc(a ^ (~b & c)) on all 8 inputs (A = 1 - 2a)')
    # zero row is a fixed point of every layer (dummy slots)
    z = [0] * W
    assert all(apply_layer(s, z) == z for s in sp[:3])
    print('[check] the zero row is a fixed point of theta-a, theta-b, chi (the dummy slots)')
    # 72 layers == Keccak-f[1600] on +-1 rows, padding cells come out zero
    trials = 1 if quick else 8
    for _ in range(trials):
        lanes = [rng.getrandbits(64) for _ in range(25)]
        row = enc(lanes)
        for s in sp:
            row = apply_layer(s, row)
        assert dec(row) == keccak_f(lanes)
    print(f'[check] 72 layers on +-1 rows equal Keccak-f[1600] ({trials} random states); padding cells stay 0')
    # padding cells of a layer output never depend on anything but the layer definition
    th_a = sp[0]
    assert all(sel[s] == 0 for sel, _, _ in th_a[1] for s in range(STATE + 320, W))
    assert all(sel[s] == 0 for sel, _, _ in sp[1][1] for s in range(STATE, W))
    assert all(sel[s] == 0 for sel, _, _ in sp[2][1] for s in range(STATE, W))
    # theta-a reads only state cells
    for j, gth in enumerate(th_a[0]):
        for sel, _, uses in th_a[1]:
            if j in uses:
                assert all(gth[s] < STATE for s in range(W) if sel[s])
    print('[check] theta-a reads only cells < 1600; chi and theta-b outputs vanish on cells >= 1600')
    # sponge layout: src_of / upos_of bijection on the 8192 U positions
    seen = set()
    for plane in range(4):
        for coef in range(2048):
            qq, s = upos_of(plane, coef)
            assert src_of(qq, s) == ('u', plane, coef)
            seen.add((qq, s))
    assert len(seen) == 8192
    assert sum(1 for qq in range(8) for s in range(8 * RATE) if src_of(qq, s) and src_of(qq, s)[0] == 'u') == 8192
    print('[check] upos_of is a bijection from (plane, coefficient) onto the 8,192 U positions; src_of inverts it')
    # full sponge: nine permutations of the trace reproduce SHAKE256(mu || w1Encode(u), 64)
    mu = bytes(rng.getrandbits(8) for _ in range(64))
    u = [rng.randrange(16) for _ in range(2048)]
    U = bytes(u[2 * j] | (u[2 * j + 1] << 4) for j in range(1024))
    msg = mu + U
    assert len(msg) == 8 * RATE
    blocks = [list(msg[RATE * k:RATE * (k + 1)]) for k in range(8)] + [pad_block()]
    st = [0] * 25
    states = []
    for k in range(9):
        for l in range(RATE // 8):
            st[l] ^= int.from_bytes(bytes(blocks[k][8 * l:8 * l + 8]), 'little')
        st = keccak_f(st)
        states.append(list(st))
    ct = b''.join(x.to_bytes(8, 'little') for x in states[8][:8])
    assert ct == hashlib.shake_256(msg).digest(64)
    print('[check] nine permutations with the 0x1f || ... || 0x80 padding block give hashlib SHAKE256(mu || U, 64)')
    # bit level: block bit at (q, s) equals the mu bit or the u bit named by src_of
    for k in range(8):
        for s in range(8 * RATE):
            bit = (blocks[k][s // 8] >> (s % 8)) & 1
            src = src_of(k, s)
            ref = (mu[src[1]] >> src[2]) & 1 if src[0] == 'mu' else (u[src[2]] >> src[1]) & 1
            assert bit == ref
    print('[check] every absorbed rate bit is the mu bit or the u bit (plane, coefficient) given by src_of')
    # input-link summand reproduces the Keccak input rows pointwise (one signature)
    T = [enc(states[k]) for k in range(8)]          # T_1..T_8
    Ubits = [[0] * W for _ in range(8)]
    for k in range(8):
        for s in range(8 * RATE):
            src = src_of(k, s)
            if src and src[0] == 'u':
                Ubits[k][s] = (u[src[2]] >> src[1]) & 1
    pad = pad_block()
    pad_bit = lambda s: (pad[s // 8] >> (s % 8)) & 1 if s < 8 * RATE else 0
    for k in range(16):
        prev = [0] * 25 if k == 0 else (states[k - 1] if k <= 8 else None)
        for s in range(W):
            # definition used by link_f / link_public / link_patterns
            a = 1 if s < STATE else 0
            a8 = 0 if s >= STATE else (p - 1 if pad_bit(s) else 1)
            bp = (p - 2) if s < 8 * RATE else 0
            cp = (p - 2) if 512 <= s < 8 * RATE else 0
            if 1 <= k <= 7:
                v = (a * T[k - 1][s] + bp * T[k - 1][s] * Ubits[k][s]) % p
            elif k == 8:
                v = a8 * T[7][s] % p
            elif k == 0:
                pub = ((p - 1) if (mu[s // 8] >> (s % 8)) & 1 else 1) if s < 512 else (1 if s < STATE else 0)
                v = (pub + cp * Ubits[0][s]) % p
            else:
                v = 0
            if k <= 8:
                stt = list(prev)
                for l in range(RATE // 8):
                    stt[l] ^= int.from_bytes(bytes(blocks[k][8 * l:8 * l + 8]), 'little')
                ref = enc(stt)[s]
            else:
                ref = 0
            assert v == ref, (k, s)
    print('[check] the input-link summand (Wa, Wa8, Wb, Wc patterns, e_q slot weights) equals the true Keccak input rows on all 16 x 2048 cells')
    # masked output: q < 8 keep everything, q = 8 keeps s < 512 and that equals 1 - 2 c_tilde
    for s in range(512):
        assert enc(states[8])[s] == ((p - 1) if (ct[s // 8] >> (s % 8)) & 1 else 1)
    print('[check] slot-8 output cells s < 512 equal 1 - 2 c_tilde bit s')
    # d0 / d15 region identities (master_f9) for all u in [0, 15], S in {-1, 0, 1}
    G, A = (q - 1) // 32, (q - 1) // 16
    for uu in range(16):
        bj = [(uu >> j) & 1 for j in range(4)]
        d0 = math.prod(1 - x for x in bj)
        d15 = math.prod(bj)
        cls = 0 if uu == 0 else (1 if uu == 15 else 2)
        cd0, cd15 = (1, 0) if cls == 0 else ((0, 1) if cls == 1 else (0, 0))
        for S in (-1, 0, 1):
            l, r = (S * S - S) // 2, (S * S + S) // 2
            start = -G + 1 - cd0 - G * l + (A + cd0) * r
            width = A - 1 + cd0 - (G + cd0) * l + (-G - cd0 + cd15) * r
            sp_ = (S + S * S) // 2
            kv = d0 * (1 - S * S) + d15 * sp_ - S * S * G
            st1, st2 = (G + A) // 2, (A - G) // 2   # class-2 coefficients (G + A and A - G are even)
            sv = S * st1 + S * S * st2 + d0 * (sp_ - 1)
            assert kv == width - (A - 1) and sv == start - (-G + 1), (uu, S)
    print('[check] K - (a - 1) and start - st0_2 written with d0 = prod(1 - Bj), d15 = prod Bj equal the public-u region polynomials (48 cases)')
    # the false shortcut of round 9 section B.4: s = (0, 1), b = (1, 0), r = 2
    s_, b_, rr = (0, 1), (1, 0), 2
    mle = lambda v: (1 - rr) * v[0] + rr * v[1]
    lhs = mle([x + y - 2 * x * y for x, y in zip(s_, b_)])
    rhs = mle(s_) + mle(b_) - 2 * mle(s_) * mle(b_)
    assert (lhs, rhs) == (1, 5)
    print('[check] XOR of multilinear evaluations is not the multilinear evaluation of the XOR: 1 vs 5')
    # no-wrap bound of the integer lift with the u term (hidden.rs lift_bound9, c = 512)
    half = (q - 1) // 2
    wrap = half * (1792 * 512 * 524167 + 2048 * 512 * 523777 + 2048 * 512 * 15 + 1) + q * 2**39
    assert wrap == 8923771996974608384 and wrap < p
    print(f'[check] hidden-u no-wrap bound {wrap} < p')


# ============================================================== 2. round table
KB = 40
LOGW, LOGQ, LOG_TAB, TRIALS, CHUNK, SLOTS, NCLAIMS, LOG_BW = 11, 4, 19, 14, 512, 2048, 29, 13
MASTER_DEG = 8
THETA_POOL = 376
LAYERS = [(5, 6), (3, 3), (3, 3)] * 24     # (deg_f, gathers), checked against specs() above


def log2i(x):
    assert x & (x - 1) == 0
    return x.bit_length() - 1


def ceil_log2(v):
    return (v - 1).bit_length()


def tree(n):
    log_dc = 11 + log2i(n)
    dc, tab = 1 << log_dc, 1 << LOG_TAB
    if 256 * n == tab:
        d = log_dc + 1
    elif dc >= tab:
        d = ceil_log2(2 * dc + tab)
    else:
        d = ceil_log2(tab + 2 * dc)
    return d, log_dc


def stacked_vars(n):
    return ceil_log2(15 * n * SLOTS + (2 << LOG_TAB))


def nvk(n):
    return LOGW + LOGQ + log2i(n)


def johnson_queries(target, r):
    return math.ceil(-target / (math.log2(21 / 20) - 0.5 * r))


def ud_queries(target, r):
    return math.ceil(-target / (math.log2(1 + 2.0 ** -r) - 1))


def whir_shape(nv, sched, target=272, regime='JB'):
    start, rates, folds = sched
    assert len(folds) == len(rates) + 1
    phases, m, r = [], nv, start
    for i, k in enumerate(folds):
        phases.append((m, r, k))
        m -= k
        if i < len(rates):
            r = rates[i]
    final_vars = m
    qf = johnson_queries if regime.startswith('JB') else ud_queries
    queries = [qf(target, r_) for (_, r_, _) in phases]
    index_bits = [m_ + r_ - k_ for (m_, r_, k_) in phases]
    assert nv + start - folds[0] <= 32, 'Goldilocks two-adicity'
    return dict(phases=phases, final_vars=final_vars, queries=queries, index_bits=index_bits,
                ood=1 if regime.startswith('JB') else 0)


def kpool(nk):
    return 8 * (5 * nk + 32) if nk else 0


def qpool(nq, slack):
    return 3 * (nq + slack) if nq else 0


def build_table(n, ws, qslack=512):
    """Port of hidden::build_table9. Each row: (label, body_elems or 'real', nk, nq, theta, widths, opens)."""
    d, log_dc = tree(n)
    chunks = -(-n // CHUNK)
    logp = LOGQ + log2i(n)
    nvx = LOGW + log2i(n)
    rows = []

    def push(label, body, nk=0, nq=0, theta=False, widths=(), opens=None):
        rows.append(dict(label=label, body=body, nk=nk, nq=nq, theta=theta, widths=list(widths), opens=opens))
    push('initial commitment; projections', 'real', nq=TRIALS * (n + SLOTS))
    push('quotients; theta', 5 * TRIALS * chunks / KB, theta=True)
    push('GKR layer-1 finals; beta_0, lambda_1', 4, nk=2)
    for k in range(1, d):
        for _ in range(k):
            push('GKR round', 2, nk=1)
        push('GKR finals; beta_k (, lambda_k+1)', 4, nk=2 if k + 1 < d else 1)
    push('explicit (P_leaf, Q_leaf); gamma_P, gamma_Q', 2, nk=2)
    push('T; gamma_Z, gamma_B, tau, omega, mu, r0', 1, nk=1 + 4 + log_dc + n + chunks * TRIALS + nvk(n))
    for _ in range(log_dc):
        push('master round', MASTER_DEG, nk=1)
    for _ in range(LOG_TAB):
        push('table round', 2, nk=1)
    for v in range(nvk(n)):
        push('mask round', 10 if v == 0 else 2, nk=1)
    for li, (df, ng) in enumerate(reversed(LAYERS)):
        for k in range(logp):
            push('Keccak p-round', df + (1 if k == 0 else 0), nk=1)
        for _ in range(LOGW):
            push('Keccak s-round', df + 1, nk=1)
        push('Keccak gathered values; wiring betas', ng, nk=ng)
        for _ in range(LOGW):
            push('Keccak wiring round', 2, nk=1)
    for v in range(nvx):
        push('input-link round', 4 if v == 0 else 3, nk=1)
    push('re-indexed bit claims; gamma_q', 8, nk=8)
    for _ in range(LOG_BW):
        push('bit-wiring round', 2, nk=1)
    push('empty; initial OOD point', 0, nk=1)
    push('initial OOD answer, 29 opened values; batching alpha', 1 + NCLAIMS, nk=1)
    ph = ws['phases']
    for _ in range(ph[0][2]):
        push('WHIR sumcheck', 2, nk=1)
    prev_tree = 1
    for i in range(1, len(ph)):
        tree_round = len(rows) + 1
        push('WHIR commitment; OOD point', 'real', nk=1)
        push('OOD answer; query indices, gamma', 1, nk=1, widths=[ws['index_bits'][i - 1]] * ws['queries'][i - 1], opens=prev_tree)
        for _ in range(ph[i][2]):
            push('WHIR sumcheck', 2, nk=1)
        prev_tree = tree_round
    push('final polynomial; final query indices', 2 ** ws['final_vars'], widths=[ws['index_bits'][-1]] * ws['queries'][-1], opens=prev_tree)
    for _ in range(ws['final_vars']):
        push('final sumcheck', 2, nk=1)
    for rw in rows:
        rw['used'] = kpool(rw['nk']) + (THETA_POOL if rw['theta'] else 0) + qpool(rw['nq'], qslack) + 4 * len(rw['widths'])
    return rows


def kec_elems(n):
    logp = LOGQ + log2i(n)
    return sum(logp * df + LOGW * (df + 1) + ng + 2 * LOGW + 1 for df, ng in LAYERS)


# Measured values (RESULTS-r9-hidden-u.md section 1 and 3, transcripts/r9-measure.txt,
# transcripts/r9-h9tests-128*.txt): rounds, coin bytes, singleton hashes, component bytes.
MEASURED = {
    32: dict(rounds=2631),
    128: dict(rounds=2785, coin_bytes=935272, singletons=2781,
              bytes={'Keccak GKR, 72 layers': 341760, 'mask sumcheck + output claim': 1800, 'input-link sumcheck': 2160,
                     're-indexed bit claims + bit wiring': 1360, 'master sumcheck (degree 8)': 5760, 'table sumcheck': 1520,
                     'masked-output T openings': 320, 'LogUp GKR': 18400}),
    2048: dict(rounds=3154, coin_bytes=1204844, singletons=3150,
               bytes={'Keccak GKR, 72 layers': 384000, 'mask sumcheck + output claim': 2120, 'input-link sumcheck': 2640,
                      're-indexed bit claims + bit wiring': 1360, 'master sumcheck (degree 8)': 7040, 'table sumcheck': 1520,
                      'masked-output T openings': 320, 'LogUp GKR': 23920}),
}

# WHIR schedules: registered (hidden::schedule9 / pcs::profile) and the large-N candidates.
SCHEDULES = {
    32: (4, [7, 9], [6, 5, 4]),              # nv 21
    128: (4, [7, 9, 11], [6, 5, 4, 4]),      # nv 23
    2048: (2, [5, 8, 10], [6, 5, 5, 5]),     # nv 26, schedule A (measured)
}
UD_PROFILES = [(128, (4, [7, 9, 11], [6, 5, 4, 4])), (2048, (2, [5, 8, 10], [6, 5, 5, 5])), (2048, (3, [5, 8, 10], [6, 5, 5, 5])),
               (16384, (2, [5, 8, 10, 11], [6, 5, 5, 5, 3])), (65536, (2, [4, 7, 9, 11], [6, 5, 5, 5, 5])), (65536, (1, [2, 5, 8, 11], [6, 5, 5, 5, 5]))]
CANDIDATES = {
    2048: [('B (benchmarked)', (3, [5, 8, 10], [6, 5, 5, 5]))],
    16384: [('C16-a', (2, [5, 8, 10, 11], [6, 5, 5, 5, 3])), ('C16-b', (3, [5, 8, 10, 11], [6, 5, 5, 5, 3]))],
    65536: [('C64 (round-9 candidate)', (1, [2, 5, 8, 11], [6, 5, 5, 5, 5])), ('C64-b', (2, [4, 7, 9, 11], [6, 5, 5, 5, 5]))],
}


def check_table(n, rows):
    m = MEASURED.get(n)
    if not m:
        return
    assert len(rows) == m['rounds'], (n, len(rows), m['rounds'])
    if 'coin_bytes' in m:
        assert sum(r['used'] for r in rows) == m['coin_bytes'], (n, sum(r['used'] for r in rows))
        assert sum(1 for r in rows if r['body'] != 'real') == m['singletons']
        d, log_dc = tree(n)
        el = {
            'Keccak GKR, 72 layers': kec_elems(n),
            'mask sumcheck + output claim': 2 * nvk(n) + 1,
            'input-link sumcheck': 3 * (LOGW + log2i(n)),
            're-indexed bit claims + bit wiring': 8 + 2 * LOG_BW,
            'master sumcheck (degree 8)': MASTER_DEG * log_dc,
            'table sumcheck': 2 * LOG_TAB,
            'masked-output T openings': 8,
            'LogUp GKR': sum(2 * k + 4 for k in range(d)),
        }
        for k_, v in m['bytes'].items():
            assert el[k_] * KB == v, (n, k_, el[k_] * KB, v)
        # the scalar bodies of the table are the same elements, in transcript order
        body = sum(r['body'] for r in rows if r['label'].startswith('Keccak'))
        assert body == kec_elems(n) - 0, (body, kec_elems(n))


# ============================================================== 3. per-round errors
def ltail(nn, pr, k):
    """log2 P[Bin(nn, pr) >= k] (exact sum in log space)."""
    if k > nn:
        return -math.inf
    lp, lq = math.log(pr), math.log1p(-pr)
    terms = [math.lgamma(nn + 1) - math.lgamma(j + 1) - math.lgamma(nn - j + 1) + j * lp + (nn - j) * lq
             for j in range(k, min(nn, k + 6000) + 1)]
    mx = max(terms)
    return (mx + math.log(sum(math.exp(t - mx) for t in terms))) / math.log(2)


RP = (2**64 - p) / 2**64          # rejection probability of an 8-byte F_p candidate
RQ = (2**23 - q) / 2**23          # rejection probability of a 23-bit F_q candidate


def decoder_delta(rw, qslack):
    """Statistical distance of the round's typed coins from uniform (fs7::decode)."""
    e = 0.0
    if rw['nk']:
        e += 2 ** ltail(5 * rw['nk'] + 32, RP, 33)
    if rw['theta']:
        e += 2 ** ltail(47, RP, 33) + 2.0 ** (-4 * 64 * 3)
    if rw['nq']:
        e += 2 ** ltail(rw['nq'] + qslack, RQ, qslack + 1)
    return D(e) if e > 0 else D(0)


def round_errors(n, ws, regime='JB', qslack=512):
    """kappa_i for every registered round, in order; returns rows annotated with 'kappa', 'delta', 'why'."""
    rows = build_table(n, ws, qslack)
    d, log_dc = tree(n)
    logp = LOGQ + log2i(n)
    ph = ws['phases']
    m0, r0, _ = ph[0]
    if regime.startswith('JB'):
        Ls = [D(10 * 2**r_) for (_, r_, _) in ph]
        agree = [D(21) / D(20) / D(2**r_).sqrt() for (_, r_, _) in ph]
    else:
        Ls = [D(1) for _ in ph]
        agree = [(1 + D(2) ** -r_) / 2 for (_, r_, _) in ph]
    L = Ls[0]                            # common candidate list of the first oracle
    occ = 2 * n * (1792 + 2048)

    def C(m_, r_):
        if regime == 'JB-BCGM':  # BCGM 2025/2051 Definition 9.1 / Theorem 9.2, d = 1, m = 10
            return D('10.5')**7 / (D(3) * (D(2)**(-r_)) ** D('1.5')) * D(2)**(2 * (m_ + r_))
        if regime == 'JB':   # DKT26 Theorem 5.12 exceptional count, m = 10 (t = 10.5), as charged by P3
            return D(8) * D(2**(m_ + 2 * r_)) * D('10.5')**3 / (D(3) * (1 - D(2)**(-m_)))
        return D(2**(m_ + r_))  # WHIR Corollary 4.11 with BCIKS20 (unique decoding), l = 2

    layer_iter = iter(list(reversed(LAYERS)))
    cur_df = None
    p_left = 0
    phase = 0
    out = []
    for rw in rows:
        lab = rw['label']
        if lab == 'initial commitment; projections':
            k, why = L * (2 / D(q) - 1 / D(q)**2)**14, 'L (2/q - 1/q^2)^14 (Lemma P)'
        elif lab == 'quotients; theta':
            k, why = L * D(occ + 2**20 - 1) / (QK - D(p)), 'L (2N*3840 + 2^20 - 1)/(|K| - p) (Lemma Q)'
        elif lab.startswith('GKR layer-1') or lab.startswith('GKR finals'):
            k, why = rw['nk'] * L / QK, f"{rw['nk']} L/|K| (interpolation, lambda batch)"
        elif lab == 'GKR round':
            k, why = 2 * L / QK, '2 L/|K| (normalized Gruen, degree 2)'
        elif lab.startswith('explicit (P_leaf'):
            k, why = L / QK, 'L/|K| (leaf batch)'
        elif lab.startswith('T; gamma_Z'):
            k, why = (log_dc + 1 + nvk(n)) * L / QK, f'({log_dc}+1) L/|K| joint zerocheck + {nvk(n)} L/|K| masked-output point (Lemmas Z, M1)'
        elif lab == 'master round':
            k, why = MASTER_DEG * L / QK, '8 L/|K| (degree-8 master)'
        elif lab == 'table round':
            k, why = 2 * L / QK, '2 L/|K|'
        elif lab == 'mask round':
            k, why = 2 * L / QK, '2 L/|K| (mask sumcheck, Lemma M2)'
        elif lab == 'Keccak p-round':
            if p_left == 0:
                cur_df, _ = next(layer_iter)
                p_left = logp
            p_left -= 1
            k, why = cur_df * L / QK, f'{cur_df} L/|K| (Gruen p-round, Lemma K1)'
        elif lab == 'Keccak s-round':
            k, why = (cur_df + 1) * L / QK, f'{cur_df + 1} L/|K| (s-round, Lemma K1)'
        elif lab.startswith('Keccak gathered'):
            k, why = L / QK, 'L/|K| (beta batch, Lemma K2)'
        elif lab == 'Keccak wiring round':
            k, why = 2 * L / QK, '2 L/|K| (wiring, Lemma K2)'
        elif lab == 'input-link round':
            k, why = 3 * L / QK, '3 L/|K| (degree-3 XOR link, Lemma X)'
        elif lab.startswith('re-indexed bit claims'):
            k, why = L / QK, 'L/|K| (gamma_q batch, Lemma W)'
        elif lab == 'bit-wiring round':
            k, why = 2 * L / QK, '2 L/|K| (bit wiring, Lemma W)'
        elif lab == 'empty; initial OOD point':
            k = Ls[0]**2 * D(2**m0) / (2 * B) if regime.startswith('JB') else D(0)
            why = 'L0^2 2^m0 / 2B (WHIR eps_out)'
        elif lab.startswith('initial OOD answer'):
            k, why = NCLAIMS * Ls[0] / B, '29 L0/B (30-functional batch)'
        elif lab == 'WHIR sumcheck':
            m_, r_, _ = ph[phase]
            k, why = 2 * C(m_, r_) / B + 2 * Ls[phase] / B, f'2C({m_},{r_})/B + 2L/B (fold: MCA + sumcheck)'
        elif lab == 'WHIR commitment; OOD point':
            phase += 1
            m_, r_, _ = ph[phase]
            k = Ls[phase]**2 * D(2**m_) / (2 * B) if regime.startswith('JB') else D(0)
            why = f'L^2 2^{m_}/2B (eps_out)'
        elif lab.startswith('OOD answer; query'):
            t = ws['queries'][phase - 1]
            k, why = agree[phase - 1]**t + 2 * D(t + 1) * Ls[phase] / B, f'agree^{t} + 2({t}+1)L/B (eps_shift)'
        elif lab.startswith('final polynomial'):
            t = ws['queries'][-1]
            k, why = agree[-1]**t, f'agree^{t} (eps_fin)'
        elif lab == 'final sumcheck':
            k, why = 2 / B, '2/B'
        else:
            raise ValueError(lab)
        rw['kappa'], rw['why'], rw['delta'] = k, why, decoder_delta(rw, qslack)
        out.append(rw)
    return out


def merkle_params(n, ws, rows):
    k = len(rows)
    real = [i for i, r in enumerate(rows) if r['body'] == 'real']
    singles = k - len(real)
    tq = ws['queries']
    ib = ws['index_bits']
    qV = k + singles + sum(t * (h + 1) for t, h in zip(tq, ib))
    q_pi = singles + sum(tq)
    log_l = max(ib)            # largest tree: 2^(m0 + r0 - f0) leaves
    formal = max(r['used'] for r in rows)
    return dict(k=k, singles=singles, qV=qV, q_pi=q_pi, log_l=log_l, h=log_l + 1, r_min=8 * formal, formal=formal)


def classical(eps, mp, R, E):
    """CF24 Lemma 9.12 + Lemma 7.15 (no simulation, no programming), SR error (t + k) eps."""
    k = mp['k']
    t = D(R) + D(E) * (mp['qV'] + mp['singles'])
    sr = (t + k) * eps
    mt = (D('1.5') * t * t + 3 * k * (mp['log_l'] + 1) * t) / D(2)**512
    return D(E) * (sr + mt), D(E) * sr, D(E) * mt


def quantum(eps, mp, Qq, E):
    """CDHZ Theorem 11.3 with Theorem 6.10 (w = t) and Theorem 8.3, sigma = 512."""
    k, qV = mp['k'], mp['qV']
    t = D(Qq) + D(E) * (qV + mp['singles'])     # same accounting for one output (E = 1) and for E submissions
    T = t + 1 + qV + k
    sr = 4 * (80 * (t + k + 1) * (t + k) * eps + (t + k + 1) * k / D(2)**min(mp['r_min'], 8000))
    off = 8 * (160 * t * (2 * t + 1)**2 + 16 * mp['q_pi'] * mp['h']) / D(2)**512
    onl = 4 * 240 * T * T * T / D(2)**512
    com = 2 * D(qV)**2 * 240 * (T + 1) / D(2)**512
    tot = sr + off + onl + com
    return D(E) * tot, D(E) * sr, D(E) * (off + onl + com)


def profile_report(name, n, sched, target=272, regime='JB', qslack=512, verbose=False, assert_measured=False, strict=True):
    nv = stacked_vars(n)
    ws = whir_shape(nv, sched, target, regime)
    rows = round_errors(n, ws, regime, qslack)
    if assert_measured:
        check_table(n, rows)
    mp = merkle_params(n, ws, rows)
    kap = [r['kappa'] + r['delta'] for r in rows]
    eps_sum, eps_max = sum(kap), max(kap)
    imax = kap.index(eps_max)
    front = sum(kap[:next(i for i, r in enumerate(rows) if r['label'].startswith('empty; initial OOD'))])
    delta_tot = sum(r['delta'] for r in rows)
    iwhir = next(i for i, r in enumerate(rows) if r['label'].startswith('empty; initial OOD'))
    Lf = D(10 * 2**ws['phases'][0][1]) if regime.startswith('JB') else D(1)
    d_alg = sum(r['kappa'] for r in rows[2:iwhir]) * QK / Lf     # all frontend root numerators except projection and lookup
    d_alg = int(d_alg.to_integral_value())
    census = dict(k=mp['k'] <= 2**16, qV=mp['qV'] <= 2**24, qPi=mp['q_pi'] <= 2**20, h=mp['h'] <= 32, r_min=mp['r_min'] >= 512)
    if strict:
        assert d_alg <= 2**20 and delta_tot <= D(2)**-400 and all(census.values()), (d_alg, delta_tot, census)
    res = dict(name=name, n=n, nv=nv, ws=ws, rows=rows, mp=mp, eps_sum=eps_sum, eps_max=eps_max, front=front,
               whir=eps_sum - front, argmax=rows[imax]['label'] + ' / ' + rows[imax]['why'], delta=delta_tot, d_alg=d_alg)
    for E in (1, 2**20):
        res[f'cl_sum_{E}'] = classical(eps_sum, mp, 2**64, E)[0]
        res[f'cl_max_{E}'] = classical(eps_max, mp, 2**64, E)[0]
        res[f'qu_max_{E}'] = quantum(eps_max, mp, 2**64, E)[0]
        res[f'qu_sum_{E}'] = quantum(eps_sum, mp, 2**64, E)[0]
    return res


def print_profile(res, detail=False):
    ws, mp = res['ws'], res['mp']
    print(f"\n### {res['name']}: N = {res['n']}, PCS dimension {res['nv']}, regime {'Johnson' if ws['ood'] else 'unique decoding'}")
    print(f"WHIR phases (m, r, k) {ws['phases']}, final variables {ws['final_vars']}, queries {ws['queries']}, index bits {ws['index_bits']}")
    print(f"rounds k = {mp['k']}, singleton rounds {mp['singles']}, q_V = {mp['qV']}, q_Pi = {mp['q_pi']}, largest tree 2^{mp['log_l']} leaves, "
          f"formal coin block {mp['formal']} B (r_min = {mp['r_min']} bits)")
    if detail:
        groups = {}
        for r in res['rows']:
            g = r['label']
            e = r['kappa'] + r['delta']
            c, s, mx = groups.get(g, (0, D(0), D(0)))
            groups[g] = (c + 1, s + e, max(mx, e))
        print(f"{'round type':58s} {'count':>6s} {'sum -log2':>10s} {'max -log2':>10s}")
        for g, (c, s, mx) in groups.items():
            print(f'{g:58s} {c:6d} {fmt(s):>10s} {fmt(mx):>10s}')
    print(f"frontend (rounds before WHIR): {fmt(res['front'])}; WHIR: {fmt(res['whir'])}; decoders: {fmt(res['delta'])}")
    print(f"D_alg = {res['d_alg']} <= 2^20 (sum of frontend root numerators, projection and lookup excluded); decoder distance {fmt(res['delta'])} >= 400 bits; "
          f"census k <= 2^16, q_V <= 2^24, q_Pi <= 2^20, h <= 32, r_min >= 512: all hold")
    print(f"eps_sum (sum over rounds): {fmt(res['eps_sum'])}   eps_max (largest round): {fmt(res['eps_max'])}  [{res['argmax']}]")
    for E in (1, 2**20):
        print(f"  E = 2^{int(math.log2(E))}: classical (CF24) with eps_max {fmt(res[f'cl_max_{E}'])}, with eps_sum {fmt(res[f'cl_sum_{E}'])};"
              f"  quantum (CDHZ) with eps_max {fmt(res[f'qu_max_{E}'])}, with eps_sum {fmt(res[f'qu_sum_{E}'])}")


def needed_eps_quantum(mp, goal=128, E=2**20):
    lo, hi = D(2)**-400, D(2)**-200
    for _ in range(200):
        mid = (lo * hi).sqrt()
        if bits(quantum(mid, mp, 2**64, E)[0]) >= goal:
            lo = mid
        else:
            hi = mid
    return lo


def main():
    quick = '--quick' in sys.argv
    print('# Hidden-u certificate: round-10 security ledger (ledger10.py)\n')
    print('## 1. Functional checks')
    functional_checks(quick)

    print('\n## 2. Round tables vs measurements')
    for n in (32, 128, 2048):
        nv = stacked_vars(n)
        ws = whir_shape(nv, SCHEDULES[n])
        rows = build_table(n, ws)
        check_table(n, rows)
        mp = merkle_params(n, ws, rows)
        extra = f", coin bytes {sum(r['used'] for r in rows)}, singletons {mp['singles']}" if n != 32 else ''
        print(f'[check] N = {n}: {len(rows)} registered rounds{extra} (equal to the measured transcript)')
    print('[check] N = 128 and 2048: component element counts x 40 B equal the measured bytes (Keccak GKR, mask, link, bit wiring, master, table, T openings, LogUp GKR)')
    # P3's composed figures recomputed by the round-9 script: WHIR(2048, A) = 270.368, WHIR(128) = 270.539
    res = profile_report('registered A', 2048, SCHEDULES[2048], assert_measured=True)
    assert abs(float(bits(res['whir'])) - 270.368) < 0.01, bits(res['whir'])
    r128 = profile_report('registered', 128, SCHEDULES[128], assert_measured=True)
    assert abs(float(bits(r128['whir'])) - 270.539) < 0.01, bits(r128['whir'])
    print('[check] the per-round WHIR terms sum to the round-9 / p3 composed values (270.368 at N = 2048 A, 270.539 at N = 128)')

    print('\n## 3. Per-round ledger and compiled bounds (Johnson regime, planner target 272, REQ-1 and REQ-2 assumed)')
    print_profile(r128)
    print_profile(res, detail=True)
    profiles = [res]
    for n, cands in CANDIDATES.items():
        for name, sch in cands:
            slack = 512 if n <= 2048 else (960 if n == 16384 else 2112)
            rr = profile_report(name, n, sch, qslack=slack)
            print_profile(rr, detail=(n == 65536 and name.startswith('C64 (')))
            profiles.append(rr)
    print('\n### Decoder slack 512 (current code) at large N, for comparison')
    for n, cands in CANDIDATES.items():
        if n <= 2048:
            continue
        rr = profile_report(cands[0][0] + ', slack 512', n, cands[0][1], qslack=512, strict=False)
        print(f"N = {n}: decoder distance {fmt(rr['delta'])}, classical E = 2^20 {fmt(rr['cl_max_1048576'])}, quantum E = 2^20 {fmt(rr['qu_max_1048576'])}")

    print('\n## 4. Quantum goal 2^-128 at Q = 2^64, E = 2^20')
    for rr in profiles:
        need = needed_eps_quantum(rr['mp'])
        nonq = max(r['kappa'] + r['delta'] for r in rr['rows'] if not (r['label'].startswith('OOD answer; query') or r['label'].startswith('final polynomial')))
        print(f"{rr['name']:>24s} N = {rr['n']:6d}: needs every round <= 2^-{bits(need):.2f}; largest non-query round 2^-{bits(nonq):.2f} -> "
              f"{'reachable by raising the query target' if nonq <= need else 'NOT reachable in this regime'}")
    print('\nUnique-decoding regime (WHIR Corollary 4.11 + BCIKS20; list size 1; no OOD needed), query target T:')
    for n, sch in [(2048, (2, [5, 8, 10], [6, 5, 5, 5])), (2048, (3, [5, 8, 10], [6, 5, 5, 5])),
                   (16384, (2, [5, 8, 10, 11], [6, 5, 5, 5, 3])), (65536, (2, [4, 7, 9, 11], [6, 5, 5, 5, 5])),
                   (65536, (1, [2, 5, 8, 11], [6, 5, 5, 5, 5]))]:
        slack = 512 if n <= 2048 else (960 if n == 16384 else 2112)
        for T in (272, 286, 290):
            rr = profile_report(f'UD T={T}', n, sch, target=T, regime='UD', qslack=slack)
            print(f"N = {n:6d} {str(sch):34s} T = {T}: queries {rr['ws']['queries']}, eps_max {fmt(rr['eps_max'])}, "
                  f"quantum E=2^20 {fmt(rr['qu_max_1048576'])}, classical E=2^20 {fmt(rr['cl_max_1048576'])}")
    print('\n## 5. The unique-decoding profile family (T = 286, pow 0, no OOD; REQ-1, REQ-2): full per-round ledgers')
    print('NOTE: the round table is the Johnson one with the OOD error terms set to 0; removing the OOD rounds changes k by at most 1 + (number of WHIR rounds), which moves no figure by more than 0.001 bit.')
    for n, sch in UD_PROFILES:
        slack = 512 if n <= 2048 else (960 if n == 16384 else 2112)
        rr = profile_report(f'UD-286 {sch}', n, sch, target=286, regime='UD', qslack=slack)
        print_profile(rr, detail=(n == 2048 and sch[0] == 2))
    print('\nJohnson regime with a higher query target (shows that queries are not the binding term):')
    for T in (286, 300):
        rr = profile_report(f'JB T={T}', 2048, SCHEDULES[2048], target=T)
        print(f"N = 2048 A, T = {T}: queries {rr['ws']['queries']}, eps_max {fmt(rr['eps_max'])} [{rr['argmax']}], quantum E=2^20 {fmt(rr['qu_max_1048576'])}")

    print('\nJohnson regime with the MCA constant of BCGM 2025/2051 Theorem 9.2 (n^2 dependence) instead of DKT26 Theorem 5.12:')
    for n, sch in [(128, SCHEDULES[128]), (2048, SCHEDULES[2048]), (16384, CANDIDATES[16384][0][1]), (65536, CANDIDATES[65536][0][1])]:
        slack = 512 if n <= 2048 else (960 if n == 16384 else 2112)
        rr = profile_report('BCGM', n, sch, regime='JB-BCGM', qslack=slack)
        print(f"N = {n:6d} {str(sch):34s}: eps_sum {fmt(rr['eps_sum'])}, eps_max {fmt(rr['eps_max'])}; classical E=2^20 {fmt(rr['cl_max_1048576'])} (sum: {fmt(rr['cl_sum_1048576'])}); quantum E=2^20 {fmt(rr['qu_max_1048576'])}")
    print('\nNOTE: conditional on the cited theorems and hypotheses listed in SECURITY-hidden-u.md (H1-H9).')


# ============================================================== 6. registry-driven ledger
import os
import re

REG_DIR = os.environ.get('H10_REGISTRY', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'registry'))
REG_FILES = {(128, 'J'): 'fff91007', (128, 'U'): 'fff91207', (2048, 'J'): 'fff9100b', (2048, 'U'): 'fff9120b',
             (4096, 'J'): 'fff9100c', (4096, 'U'): 'fff9120c', (16384, 'J'): 'fff9100e', (16384, 'U'): 'fff9120e',
             (65536, 'J'): 'fff91010', (65536, 'U'): 'fff91210'}


def parse_registry(n, fam):
    path = os.path.join(REG_DIR, f'r10-registry-{n}-{REG_FILES[(n, fam)]}.txt')
    rows, tail = [], []
    with open(path) as fh:
        for line in fh:
            line = line.rstrip('\n')
            parts = line.split(' | ')
            if parts and parts[0].isdigit() and len(parts) >= 13:
                rows.append(dict(round=int(parts[0]), phase=parts[1], layer=parts[2], index=parts[3], vars=parts[4],
                                 claim=parts[5], deg_before=parts[6], deg=parts[7], sent=parts[8], body=parts[9],
                                 coin=parts[10], terminal=parts[11], merge=' | '.join(parts[12:])))
            elif not (parts and parts[0].isdigit()):
                tail.append(line)
    head = next(l for l in tail if 'registered rounds' in l)
    assert f'N = {n}: {len(rows)} registered rounds' in head, (head, len(rows))
    assert [r['round'] for r in rows] == list(range(1, len(rows) + 1))
    census = next(l for l in tail if l.startswith('k (registered rounds)'))
    info = dict(
        k=int(re.search(r'k \(registered rounds\) = (\d+)', census).group(1)),
        real=int(re.search(r'real trees = (\d+)', census).group(1)),
        r_min=int(re.search(r'minimum raw coin block = \d+ bytes = (\d+) bits', census).group(1)),
        h=int(re.search(r'Merkle depth h \(largest tree\) = (\d+)', census).group(1)),
        qrows=int(re.search(r'query rows opened = (\d+)', census).group(1)),
        claims=int(re.search(r'total: (\d+) scalar claims', '\n'.join(tail)).group(1)),
        ood=int(re.search(r'OOD claims: (\d+)', '\n'.join(tail)).group(1)),
        batch_deg=int(re.search(r'power polynomial of degree (\d+)', '\n'.join(tail)).group(1)),
        slack=int(re.search(r'slack (\d+) words', '\n'.join(tail)).group(1)),
        nq=int(re.search(r'projection block \(atomic, round 1\): (\d+) F_q', '\n'.join(tail)).group(1)),
        reject_short='short pool = reject (no padding)' in '\n'.join(tail),
        per_tree='per-tree hash domains' in '\n'.join(tail) and 'true' in next((l for l in tail if 'per-tree hash domains' in l), ''),
        honest_match=next((l for l in tail if 'every body length and coin prefix equal to the registry: true' in l), None) is not None,
        qv_measured=None,
    )
    m = next((l for l in tail if l.startswith('verifier oracle calls q_V')), None)
    if m:
        info['qv_measured'] = int(m.split('=')[-1])
    assert info['k'] == len(rows)
    return rows, info


def coin_shape(coin):
    """(nk, theta, nq, slack, index_count, index_bits) from a registry coin cell."""
    shape = coin.split(';')[0].strip()
    nk = theta = nq = slack = cnt = bitsw = 0
    for part in shape.split('+'):
        part = part.strip()
        if m := re.fullmatch(r'(\d+) K', part):
            nk = int(m.group(1))
        elif part == 'theta':
            theta = 1
        elif m := re.fullmatch(r'(\d+) F_q \(slack (\d+)\)', part):
            nq, slack = int(m.group(1)), int(m.group(2))
        elif m := re.fullmatch(r'(\d+) indices of (\d+) bits', part):
            cnt, bitsw = int(m.group(1)), int(m.group(2))
        elif part in ('root', '-', ''):
            pass
        else:
            raise ValueError(part)
    raw = int(coin.split(';')[1]) if ';' in coin else 0
    return nk, theta, nq, slack, cnt, bitsw, raw


def registry_ledger(n, fam, target=None):
    rows, info = parse_registry(n, fam)
    regime = 'JB' if fam == 'J' else 'UD'
    # WHIR phases from the registry: (m, f) per phase, index bits and query counts
    wh = [r for r in rows if r['phase'] in ('WHIR', 'WHIR sumcheck')]
    phases = []          # list of dict(m, f, name)
    for r in wh:
        nm = r['layer']
        if nm == 'final':
            continue
        if not phases or phases[-1]['name'] != nm:
            phases.append(dict(name=nm, m=None, f=0))
        if r['phase'] == 'WHIR' and phases[-1]['m'] is None:
            phases[-1]['m'] = int(r['vars'])
        if r['phase'] == 'WHIR sumcheck':
            phases[-1]['f'] += 1
    queries, ibits = [], []
    for r in wh:
        if r['phase'] == 'WHIR':
            nk, th, nq, sl, cnt, bw, raw = coin_shape(r['coin'])
            if cnt:
                queries.append(cnt)
                ibits.append(bw)
    v_fin = sum(1 for r in wh if r['phase'] == 'WHIR sumcheck' and r['layer'] == 'final')
    assert len(queries) == len(phases)
    for i, ph in enumerate(phases):
        ph['r'] = ibits[i] - ph['m'] + ph['f']
        ph['t'] = queries[i]
        ph['ib'] = ibits[i]
    assert phases[-1]['m'] - phases[-1]['f'] == v_fin
    rates = [ph['r'] for ph in phases]
    if regime == 'JB':
        Ls = [D(10 * 2**r_) for r_ in rates]
        agree = [D(21) / D(20) / D(2**r_).sqrt() for r_ in rates]
    else:
        Ls = [D(1)] * len(rates)
        agree = [(1 + D(2) ** -r_) / 2 for r_ in rates]
    L = Ls[0]
    # planner query counts must follow from the registry's own rates
    tgt = target or (272 if regime == 'JB' else 286)
    qf = johnson_queries if regime == 'JB' else ud_queries
    assert queries == [qf(tgt, r_) for r_ in rates], (queries, rates)

    def C(m_, r_):
        if regime == 'JB':
            return D(8) * D(2**(m_ + 2 * r_)) * D('10.5')**3 / (D(3) * (1 - D(2)**(-m_)))
        return D(2**(m_ + r_))

    log_dc = 11 + log2i(n)
    nvk_ = nvk(n)
    occ = 2 * n * (1792 + 2048)
    out = []
    d_alg = 0
    pidx = {ph['name']: i for i, ph in enumerate(phases)}
    for r in rows:
        ph, merge = r['phase'], r['merge']
        nk, th, nq, sl, cnt, bw, raw = coin_shape(r['coin'])
        delta = D(0)
        e = 0.0
        if nk:
            e += 2 ** ltail(5 * nk + 32, RP, 33)
        if th:
            e += 2 ** ltail(47, RP, 33) + 2.0 ** (-768)
        if nq:
            e += 2 ** ltail(nq + sl, RQ, sl + 1)
        delta = D(e)
        num = 0      # frontend root numerator (charged x L / |K|)
        if ph == 'commitment':
            k_ = L * (2 / D(q) - 1 / D(q)**2)**14
        elif ph == 'projections':
            k_ = L * D(occ + 2**20 - 1) / (QK - D(p))
        elif ph == 'master weights':
            num = log_dc + 1 + nvk_
            k_ = num * L / QK
        elif ph in ('LogUp GKR', 'LogUp leaves', 'master sumcheck', 'table sumcheck', 'mask sumcheck', 'Keccak GKR main',
                    'Keccak GKR wiring', 'input link', 'bit wiring'):
            if r['deg'] != '-':
                num = int(r['deg'])
            else:
                num = len(re.findall(r'degree 1', merge))
                assert num >= 1, r
            k_ = num * L / QK
        elif ph == 'WHIR sumcheck':
            if r['layer'] == 'final':
                k_ = 2 / B
            else:
                i = pidx[r['layer']]
                k_ = 2 * C(phases[i]['m'], phases[i]['r']) / B + 2 * Ls[i] / B
        elif ph == 'WHIR':
            if r['layer'] == 'final':
                k_ = agree[-1]**phases[-1]['t']
            elif 'alpha: batching power polynomial' in merge:
                k_ = int(re.search(r'degree (\d+)', merge).group(1)) * Ls[0] / B
            elif 'OOD point' in merge:
                i = pidx[r['layer']]
                k_ = Ls[i]**2 * D(2**phases[i]['m']) / (2 * B)
            elif 'gamma: batches' in merge:
                i = pidx[r['layer']]
                t = phases[i - 1]['t']
                k_ = agree[i - 1]**t + 2 * D(t + 1) * Ls[i] / B
            else:
                raise ValueError(r)
        else:
            raise ValueError(ph)
        d_alg += num
        out.append(dict(r, kappa=k_, delta=delta))
    k = info['k']
    singles = k - info['real']
    qV = k + singles + sum(ph['t'] * (ph['ib'] + 1) for ph in phases)
    q_pi = singles + sum(ph['t'] for ph in phases)
    mp = dict(k=k, singles=singles, qV=qV, q_pi=q_pi, log_l=max(ph['ib'] for ph in phases), h=info['h'] + 1,
              r_min=info['r_min'], formal=None)
    assert info['h'] == max(ph['ib'] for ph in phases)
    kap = [x['kappa'] + x['delta'] for x in out]
    eps_sum, eps_max = sum(kap), max(kap)
    res = dict(n=n, fam=fam, rows=out, info=info, phases=phases, mp=mp, eps_sum=eps_sum, eps_max=eps_max,
               delta=sum(x['delta'] for x in out), d_alg=d_alg,
               argmax=out[kap.index(eps_max)]['phase'] + ' ' + out[kap.index(eps_max)]['layer'])
    for E in (1, 2**20):
        res[f'cl_max_{E}'] = classical(eps_max, mp, 2**64, E)[0]
        res[f'cl_sum_{E}'] = classical(eps_sum, mp, 2**64, E)[0]
        res[f'qu_max_{E}'] = quantum(eps_max, mp, 2**64, E)[0]
        res[f'qu_sum_{E}'] = quantum(eps_sum, mp, 2**64, E)[0]
    # gates
    assert d_alg <= 2**20 and res['delta'] <= D(2)**-400
    assert k <= 2**16 and qV <= 2**24 and q_pi <= 2**20 and mp['h'] <= 32 and mp['r_min'] >= 512
    assert info['slack'] >= 512 + -(-info['nq'] // 400) and info['reject_short']
    assert info['claims'] == 29 and info['ood'] == (1 if fam == 'J' else 0) and info['batch_deg'] == 29 - (0 if fam == 'J' else 1)
    return res


def crosscheck_port(reg, n):
    """The Python port (Johnson) must give the same rows, degrees and error vector as the registry."""
    if reg['fam'] != 'J':
        return None
    sched = (reg['phases'][0]['r'], [ph['r'] for ph in reg['phases'][1:]], [ph['f'] for ph in reg['phases']])
    port = profile_report('port', n, sched, qslack=reg['info']['slack'])
    assert len(port['rows']) == len(reg['rows'])
    diff = abs(float(bits(port['eps_sum'])) - float(bits(reg['eps_sum']))) + abs(float(bits(port['eps_max'])) - float(bits(reg['eps_max'])))
    assert diff < 1e-6, diff
    assert port['d_alg'] == reg['d_alg'], (port['d_alg'], reg['d_alg'])
    assert port['mp']['qV'] == reg['mp']['qV'] and port['mp']['q_pi'] == reg['mp']['q_pi']
    return sched


# Round-10 registry results (eps_sum, eps_max, classical E = 2^20, quantum E = 2^20), frozen before the round-11 proof
# patch; the patch changes the knowledge state, not any per-round charge.
ROUND10 = {(128, 'J'): (270.539, 272.075, 188.075, 115.753), (128, 'U'): (284.41, 286.146, 202.146, 129.824),
           (2048, 'J'): (270.368, 272.116, 188.116, 115.794), (2048, 'U'): (284.242, 286.146, 202.146, 129.824),
           (4096, 'J'): (270.249, 272.075, 188.075, 115.753), (4096, 'U'): (284.071, 286.146, 202.146, 129.824),
           (16384, 'J'): (270.141, 272.116, 188.116, 115.794), (16384, 'U'): (283.205, 286.146, 202.146, 129.824),
           (65536, 'J'): (269.266, 272.116, 188.116, 115.794), (65536, 'U'): (282.696, 286.0, 202.0, 129.678)}


def registry_main():
    print('\n## 6. Registry-driven ledger (round table, degrees, opening shape and census read from the verifier registry export)')
    print(f'registry directory: {REG_DIR} (r10-large-n commit 43383ca; rows asserted equal to the enforced verifier table by the exporter)')
    hdr = f"{'N':>6s} {'fam':>3s} {'k':>5s} {'schedule (r0, rates, folds)':38s} {'queries':26s} {'D_alg':>6s} {'dec':>7s} {'q_V':>6s} {'q_V(M)':>7s} {'h=d+1':>5s} {'r_min':>5s} {'IOP sum':>8s} {'max':>8s} {'cl 2^20':>8s} {'cl sum':>8s} {'qu E=1':>8s} {'qu 2^20':>8s}"
    print(hdr)
    out = {}
    for (n, fam) in sorted(REG_FILES):
        reg = registry_ledger(n, fam)
        # round-11 repair: the handoff entry is (m - 1)|Lambda|/|K| with m = claims + OOD, charged (m - 1) L0 / B,
        # and the final tail has v_fin degree-2 rounds charged 2/B each; the error vector must equal round 10's.
        m_open = reg['info']['claims'] + reg['info']['ood']
        L0 = D(10 * 2**reg['phases'][0]['r']) if fam == 'J' else D(1)
        hand = [r for r in reg['rows'] if 'alpha: batching power polynomial' in r['merge']]
        assert len(hand) == 1 and hand[0]['kappa'] == (m_open - 1) * L0 / B
        tail = [r for r in reg['rows'] if r['phase'] == 'WHIR sumcheck' and r['layer'] == 'final']
        assert len(tail) == reg['phases'][-1]['m'] - reg['phases'][-1]['f'] and all(r['kappa'] == 2 / B for r in tail)
        got = tuple(round(float(bits(reg[k_])), 3) for k_ in ('eps_sum', 'eps_max', 'cl_max_1048576', 'qu_max_1048576'))
        assert got == ROUND10[(n, fam)], ((n, fam), got, ROUND10[(n, fam)])
        sched = crosscheck_port(reg, n) if fam == 'J' else None
        ph = reg['phases']
        sch = f"({ph[0]['r']}, {[x['r'] for x in ph[1:]]}, {[x['f'] for x in ph]})"
        qm = reg['info']['qv_measured']
        print(f"{n:6d} {fam:>3s} {reg['mp']['k']:5d} {sch:38s} {str([x['t'] for x in ph]):26s} {reg['d_alg']:6d} {fmt(reg['delta']):>7s} "
              f"{reg['mp']['qV']:6d} {str(qm or '-'):>7s} {reg['mp']['h']:5d} {reg['mp']['r_min']:5d} {fmt(reg['eps_sum']):>8s} {fmt(reg['eps_max']):>8s} "
              f"{fmt(reg['cl_max_1048576']):>8s} {fmt(reg['cl_sum_1048576']):>8s} {fmt(reg['qu_max_1'] if fam == 'U' else reg['qu_max_1']):>8s} {fmt(reg['qu_max_1048576']):>8s}")
        out[(n, fam)] = reg
    print('[check] round-11 patch: handoff entry = (m - 1) L0 / B with m = 30 (J) / 29 (U); final tail = v_fin rounds of 2/B;')
    print('        every (eps_sum, eps_max, classical, quantum) equals the round-10 value to 0.001 bit: no registered round changed')
    print('[check] every Johnson registry equals the Python port: same row count, same D_alg, q_V, q_Pi, and the same eps_sum and eps_max to 1e-6 bit')
    print('[check] gates on every registry: D_alg <= 2^20, decoder distance <= 2^-400, k <= 2^16, q_V <= 2^24, q_Pi <= 2^20, h <= 32, r_min >= 512,')
    print('        F_q slack >= 512 + ceil(nq/400) with short pools rejected, 29 scalar claims, OOD 1 (J) / 0 (U), batch degree 29 (J) / 28 (U)')
    print('[check] every registry query count equals the planner formula at its own rates (Johnson target 272, unique decoding target 286)')
    print('NOTE: quantum figures are claimed only for the unique-decoding family (U); the Johnson column is shown for comparison.')
    for (n, fam), reg in out.items():
        if n == 2048:
            groups = {}
            for r in reg['rows']:
                g = r['phase'] + (' ' + r['layer'] if r['phase'].startswith('WHIR') and r['layer'] in ('initial', 'final') else '')
                e = r['kappa'] + r['delta']
                c, s_, mx = groups.get(g, (0, D(0), D(0)))
                groups[g] = (c + 1, s_ + e, max(mx, e))
            print(f"\n### registry N = 2048, family {fam}: per-phase errors (count, sum -log2, max -log2); largest round: {reg['argmax']}")
            for g, (c, s_, mx) in groups.items():
                print(f'{g:28s} {c:6d} {fmt(s_):>10s} {fmt(mx):>10s}')
    return out


if __name__ == '__main__':
    main()
    registry_main()
