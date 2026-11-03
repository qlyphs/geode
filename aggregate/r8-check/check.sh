python3 - <<'PY'
from decimal import Decimal as D, getcontext
from hashlib import shake_256

getcontext().prec = 90
TWO = D(2)
k, qv, qp, h, r = 354, 7559, 684, 23, 1388544
R = 2**64
eps = TWO**(-D('269.973536023')) + TWO**(-D('727.20'))

def bits(x):
    return -x.ln() / TWO.ln()

def qbound(t):
    t = D(t)
    T = t + 1 + qv + k
    return (
        320*(t+k+1)*(t+k)*eps
        + 4*(t+k+1)*k/TWO**r
        + (
            1280*t*(2*t+1)**2
            + 960*T**3
            + 480*qv*qv*(T+1)
            + 128*qp*h
        )/TWO**512
    )

for E in (1, 2**20):
    t = D(R + 7909*E)
    classical = E * (
        (t+k)*eps
        + (D('1.5')*t*t + 24426*t)/TWO**512
    )
    tq = R + 350 if E == 1 else R + 7909*E
    quantum = E*qbound(tq)
    print(
        f'E={E} classical={bits(classical):.9f} '
        f'quantum_candidate={bits(quantum):.9f}'
    )

preimage = (
    b'\x81'
    + (0x00080001).to_bytes(4, 'little')
    + (330).to_bytes(2, 'little')
    + bytes(range(64))
    + bytes(range(64, 128))
)
assert len(preimage) == 135
print('node_preimage_bytes=135')
print('node_330=' + shake_256(preimage).hexdigest(64))
PY
