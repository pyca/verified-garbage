"""Checks the identities and bounds of README.md, and counts operations."""
import random, sys
M64 = (1 << 64) - 1
def cl(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def classes(a, k, w):
    m = sum(1 << i for i in range(0, w, k))
    return [(a >> j) & m for j in range(k)], m
def by_classes(a, b, w, k):
    """k*k integer products of classes, XORed per residue, masked once."""
    A = [((a >> j) << j) & sum(1 << i for i in range(j, w, k)) for j in range(k)]
    B = [((b >> j) << j) & sum(1 << i for i in range(j, w, k)) for j in range(k)]
    z = 0
    for r in range(k):
        s = 0
        for i in range(k):
            s ^= A[i] * B[(r - i) % k]
        z ^= s & sum(1 << i for i in range(r, 2 * w, k))
    return z
def kara(A, B):
    """Products of class polynomials, Karatsuba; list of 2n-1 (unmasked) words."""
    n = len(A)
    if n == 1: return [A[0] * B[0]], 1
    h = n // 2
    l, cl_ = kara(A[:h], B[:h]); u, cu = kara(A[h:], B[h:])
    m, cm = kara([x ^ y for x, y in zip(A[:h], A[h:])], [x ^ y for x, y in zip(B[:h], B[h:])])
    out = [0] * (2 * n - 1)
    for i, x in enumerate(l): out[i] ^= x; out[i + h] ^= x
    for i, x in enumerate(u): out[i + n] ^= x; out[i + h] ^= x
    for i, x in enumerate(m): out[i + h] ^= x
    return out, cl_ + cu + cm
def by_kara(a, b, w, k):
    A, m = classes(a, k, w); B, _ = classes(b, k, w)
    out, cnt = kara(A, B)
    mm = sum(1 << i for i in range(0, 2 * w, k))
    z = 0
    for j, x in enumerate(out): z ^= (x & mm) << j
    return z, cnt
def test(f, w, n=20000):
    full = (1 << w) - 1
    bad = 0
    for t in range(n):
        a, b = (full, full) if t == 0 else (random.getrandbits(w), random.getrandbits(w))
        if f(a, b) != cl(a, b): bad += 1
    return bad
for w in (32, 60, 64):
    for k in (2, 3, 4, 5):
        terms = -(-w // k)
        print(f"w={w} k={k} terms={terms} fits={terms < 2**k} failures classes={test(lambda a,b: by_classes(a,b,w,k), w, 2000)}",
              f"kara={test(lambda a,b: by_kara(a,b,w,k)[0], w, 2000) if k in (2,4) else '-'}")
