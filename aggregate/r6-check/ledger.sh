python3 - <<'PY'
from decimal import Decimal as D, getcontext, ROUND_CEILING

getcontext().prec = 90
p = 2**64 - 2**32 + 1
Q, B, q, L = D(p**5), D(2**319), D(8380417), D(160)
phases = [(24,4,6), (18,7,5), (13,9,5), (8,11,4)]
queries = [141,80,62,51]

def ls(r):
    return D(10 * 2**r)

def agree(r):
    return D(21) / D(20) / D(2**r).sqrt()

def bits(e):
    return -e.ln() / D(2).ln()

def C(n, r):
    return (D(8) * D(2**(n+2*r)) * D('10.5')**3
            / (D(3) * (1-D(2)**(-n))))

terms = [5*L/B]
for i, (n,r,k) in enumerate(phases):
    terms.append(ls(r)**2 * D(2**n)/(2*B))
    if i:
        t, old = queries[i-1], phases[i-1][1]
        terms += [agree(old)**t, 2*D(t+1)*ls(r)/B]
    for _ in range(k):
        terms += [2*C(n,r)/B, 2*ls(r)/B]
terms += [agree(11)**51] + [2/B]*4

proj = L*(2/q-1/q**2)**14
lookup = L*D(2**24-1)/(Q-D(p))
other = D(701)*L/Q
front = proj + lookup + other
whir = sum(terms)
eps = front + whir

derived_queries = [
    int((D(272)/(-agree(r).ln()/D(2).ln()))
        .to_integral_value(rounding=ROUND_CEILING))
    for _,r,_ in phases
]
assert queries == derived_queries and len(terms) == 56
assert pow(3, (p-1)//5, p) == 1041288259238279555

wrap = ((8380417-1)//2) * (
    1792*512*524167 + 2048*512*523777 + 1
) + 8380417*2**39
assert wrap == 8923706090701451264 and wrap < p

print('queries:', queries, 'WHIR terms:', len(terms))
for name, e in [
    ('projection', proj), ('lookup', lookup), ('other', other),
    ('frontend', front), ('WHIR', whir), ('IOP', eps)
]:
    print(f'{name}: {bits(e):.9f} bits')

R, E = D(2**64), D(2**20)
canonical = R*eps + 3*(R*R+1)/D(2**512)
print(f'canonical BCS, one epoch: {bits(canonical):.9f} bits')
print(f'canonical BCS, 2^20 epochs: {bits(E*canonical):.9f} bits')
print('PASS: field, no-wrap, and ledger arithmetic')
print('NOTE: compiler compatibility is an unproved hypothesis.')
PY
