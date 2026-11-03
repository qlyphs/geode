python3 - <<'PY'
import hashlib
import struct

P = 2**64 - 2**32 + 1
Q = 8380417
DOMAIN = b"Qlyphs/Archive/CF24/v1\0"
PROFILE = 0xffffffff  # Test only; production MUST reject this ID.
COIN_BYTES = 1572     # Production profile 0x00070001 uses 173568.

def u16(x): return struct.pack("<H", x)
def u32(x): return struct.pack("<I", x)
def u64(x): return struct.pack("<Q", x)
def frame(tag, value): return u16(tag) + u64(len(value)) + value

def descriptor(nk=0, theta=False, nq=0, widths=()):
    return (u32(nk) + bytes([int(theta)]) + u32(nq)
            + u32(len(widths)) + bytes(widths))

def used_bytes(nk=0, theta=False, nq=0, widths=()):
    return ((8*(5*nk+32) if nk else 0) + (376 if theta else 0)
            + (3*(nq+512) if nq else 0) + 4*len(widths))

def pool(raw, count, width, modulus, mask):
    accepted = []
    for offset in range(0, len(raw), width):
        x = int.from_bytes(raw[offset:offset+width], "little") & mask
        if x < modulus and len(accepted) < count:
            accepted.append(x)
    return accepted + [0]*(count-len(accepted))

def decode(raw, nk=0, theta=False, nq=0, widths=()):
    assert len(raw) >= used_bytes(nk, theta, nq, widths)
    offset = 0

    def take(n):
        nonlocal offset
        result = raw[offset:offset+n]
        offset += n
        assert len(result) == n
        return result

    ks, th, qs, indices = [], None, [], []

    if nk:
        a = pool(take(8*(5*nk+32)), 5*nk, 8, P, 2**64-1)
        ks = [tuple(a[j:j+5]) for j in range(0, len(a), 5)]

    if theta:
        a = pool(take(376), 15, 8, P, 2**64-1)
        candidates = [tuple(a[j:j+5]) for j in (0, 5, 10)]
        th = next((x for x in candidates if any(x[1:])),
                  (0, 1, 0, 0, 0))

    if nq:
        qs = pool(take(3*(nq+512)), nq, 3, Q, 0x7fffff)

    for bits in widths:
        assert bits in (22, 20, 17, 15)
        indices.append(int.from_bytes(take(4), "little")
                       & ((1 << bits)-1))

    return ks, th, qs, indices

def leaf_root(profile, round_id, kind, payload):
    symbol = (u32(profile) + u32(round_id) + bytes([kind])
              + u32(len(payload)) + payload)
    return hashlib.shake_256(b"\x80" + symbol).digest(64)

def coin(round_id, statement, roots, shape, profile=PROFILE):
    assert len(roots) == round_id
    assert all(len(x) == 64 for x in roots)
    assert used_bytes(*shape) <= COIN_BYTES

    history = b"".join(
        frame(16, u32(j) + root + b"\x00")
        for j, root in enumerate(roots, 1)
    )

    preimage = (
        DOMAIN + u32(profile) + frame(1, statement) + history
        + frame(3, descriptor(*shape))
        + u32(round_id) + u64(COIN_BYTES)
    )
    return hashlib.shake_256(preimage).digest(COIN_BYTES)

statement = b"abc"
shapes = [
    (1, False, 0, ()),
    (0, True, 0, ()),
    (0, False, 8, (22, 20, 15)),
]
bodies = [b"", bytes(range(16)), b"xyz"]

roots, blocks = [], []
for i, (shape, body) in enumerate(zip(shapes, bodies), 1):
    roots.append(leaf_root(PROFILE, i, 1, body))
    raw = coin(i, statement, roots, shape)
    blocks.append(raw)

    print(f"round={i} bytes={len(raw)} used={used_bytes(*shape)} "
          f"head={raw[:16].hex()}")
    print("sha3_512=" + hashlib.sha3_512(raw).hexdigest())

    ks, th, qs, indices = decode(raw, *shape)
    if ks:
        print("K=" + ",".join(str(x) for x in ks[0]))
    if th is not None:
        print("theta=" + ",".join(str(x) for x in th))
    if qs:
        print("q=" + ",".join(str(x) for x in qs))
    if indices:
        print("indices=" + ",".join(str(x) for x in indices))

    # To display every byte of this block as well: print(raw.hex())

assert decode(b"\xff"*296, 1)[0] == [(0, 0, 0, 0, 0)]
assert decode(b"\0"*376, theta=True)[1] == (0, 1, 0, 0, 0)
assert decode(b"\xff"*(3*(8+512)), nq=8)[2] == [0]*8

assert pool(u64(P-1)+u64(P), 2, 8, P, 2**64-1) == [P-1, 0]
assert pool(
    (Q-1).to_bytes(3, "little")+Q.to_bytes(3, "little"),
    2, 3, Q, 0x7fffff
) == [Q-1, 0]

for raw, shape in zip(blocks, shapes):
    assert decode(raw, *shape) == decode(
        raw[:used_bytes(*shape)], *shape
    )

changed = list(roots)
changed[0] = leaf_root(PROFILE, 1, 1, b"changed")
assert all(
    coin(i, statement, changed[:i], shapes[i-1]) != blocks[i-1]
    for i in (1, 2, 3)
)
assert all(
    coin(i, b"abd", roots[:i], shapes[i-1]) != blocks[i-1]
    for i in (1, 2, 3)
)

print("PASS fallback, boundary, prefix, and full-history tests")
PY
