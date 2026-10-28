#!/usr/bin/env python3
"""Throwaway experiment, never merged: RISC-V assembly variants of
PBKDF2-HMAC-SHA-1's iteration step, to measure candidate optimizations of
the verified `vg_pbkdf2_hmac_sha1_iterate` on real hardware before proving
any of them.

Each variant is `iter_<name>(state, u, n)`: `state` is 15 native u32 words
(the inner midstate, the outer midstate, T), `u` 5 words (U, updated), and
`n` iterations of `U <- HMAC(U); T ^= U`, all with the verified code's
register assignment and round structure (`v0` copies it), then:

* `fold`:    the padding's constant words folded (no registers, no adds of 0)
* `order`:   the K addition moved before f (shorter dependency chain)
* `dbl`:     each new `a` kept doubled (x * (2^32 + 1)), so ROTL5 and ROTL30
             are one `srli` each
"""

import sys

K = [0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xCA62C1D6]
MASK = 0xFFFFFFFF


def s32(v):
    v &= MASK
    return v - (1 << 32) if v & 0x80000000 else v


def li(rd, v):
    v = s32(v)
    if -2048 <= v < 2048:
        return [f"addi {rd}, zero, {v}"]
    hi = ((v + 0x800) >> 12) & 0xFFFFF
    lo = v - s32(hi << 12)
    return [f"lui {rd}, {hi}", f"addiw {rd}, {rd}, {lo}"]


def rotl1(v):
    return ((v << 1) | (v >> 31)) & MASK


def fn(t):
    return "ch" if t < 20 else "parity" if t < 40 else "maj" if t < 60 else "parity"


# Padding of a 20-byte message after a 64-byte block: words 5..15.
CONST = {5: 0x80000000, 15: 672, **{i: 0 for i in range(6, 15)}}


def block(work, wregs, fold, order, dbl):
    """80 rounds over working registers `work` (a..e) and window registers
    `wregs` (slot i holds W[i mod 16])."""
    out = []
    T1, T2, KR, T3 = "a6", "a4", "a5", "a3"
    # Symbolic window: an int (constant) or None (in its register).
    win = [None] * 16
    if fold:
        for i, c in CONST.items():
            win[i] = c
    else:
        for i, c in CONST.items():
            out += li(wregs[i], c)

    def var(t, k):
        return work[(k + 5 - t % 5) % 5]

    if dbl:
        # a and b of round 0 doubled.
        for r in (work[0], work[1]):
            out += [f"slli {T3}, {r}, 32", f"or {r}, {r}, {T3}"]
    for t in range(80):
        if t % 20 == 0:
            out += li(KR, K[t // 20])
        s = t % 16
        if t >= 16:
            terms = [(t - 16) % 16, (t - 14) % 16, (t - 8) % 16, (t - 3) % 16]
            c = 0
            regs = []
            for j in terms:
                if win[j] is None:
                    regs.append(wregs[j])
                else:
                    c ^= win[j]
            dst = wregs[s]
            if not regs:
                win[s] = rotl1(c)
            else:
                if len(regs) == 1:
                    src = regs[0]
                else:
                    out.append(f"xor {dst}, {regs[0]}, {regs[1]}")
                    for r in regs[2:]:
                        out.append(f"xor {dst}, {dst}, {r}")
                    src = dst
                out += [f"slliw {T1}, {src}, 1", f"srliw {dst}, {src}, 31", f"or {dst}, {dst}, {T1}"]
                rc = s32(rotl1(c))
                if c:
                    if -2048 <= rc < 2048:
                        out.append(f"xori {dst}, {dst}, {rc}")
                    else:
                        out += li(T3, rc) + [f"xor {dst}, {dst}, {T3}"]
                win[s] = None
        a, b, c_, d, e = (var(t, k) for k in range(5))
        w = win[s]
        kadd = [f"add {e}, {e}, {KR}"]
        if w is None:
            wadd = [f"add {e}, {e}, {wregs[s]}"]
        elif w == 0:
            wadd = []
        elif -2048 <= s32(w) < 2048:
            wadd = [f"addi {e}, {e}, {s32(w)}"]
        else:
            wadd = li(T3, K[t // 20] + w) + [f"add {e}, {e}, {T3}"]
            kadd = []
        f = fn(t)
        if f == "ch":
            fc = [f"xor {T1}, {c_}, {d}", f"and {T1}, {T1}, {b}", f"xor {T1}, {T1}, {d}"]
        elif f == "parity":
            fc = [f"xor {T1}, {b}, {c_}", f"xor {T1}, {T1}, {d}"]
        else:
            fc = [f"or {T1}, {b}, {c_}", f"and {T1}, {T1}, {d}", f"and {T2}, {b}, {c_}", f"or {T1}, {T1}, {T2}"]
        fadd = [f"add {e}, {e}, {T1}"]
        if dbl:
            rot5 = [f"srli {T1}, {a}, 27", f"add {e}, {e}, {T1}"]
            rot30 = [f"srli {b}, {b}, 2"]
        else:
            rot5 = [f"slliw {T1}, {a}, 5", f"add {e}, {e}, {T1}", f"srliw {T1}, {a}, 27", f"add {e}, {e}, {T1}"]
            rot30 = [f"slliw {T1}, {b}, 30", f"srliw {b}, {b}, 2", f"or {b}, {b}, {T1}"]
        if order:
            out += wadd + kadd + fc + fadd + rot5 + rot30
        else:
            out += wadd + fc + fadd + kadd + rot5 + rot30
        if dbl and t < 79:
            out += [f"slli {e}, {e}, 32", f"srli {T3}, {e}, 32", f"or {e}, {e}, {T3}"]
    return out


def variant(name, fold=False, order=False, dbl=False):
    A = ["s6", "s7", "s8", "s9", "s10"]
    B = ["s1", "s2", "s3", "s4", "s5"]
    rest = ["s11", "s0", "ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a7"]
    saved = ["ra", "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
    o = [f".globl iter_{name}", f".type iter_{name}, @function", f"iter_{name}:",
         "addi sp, sp, -112"]
    o += [f"sd {r}, {8 * i}(sp)" for i, r in enumerate(saved)]
    o += ["sd a1, 104(sp)"]
    o += [f"lwu {B[i]}, {4 * i}(a1)" for i in range(5)]
    o += [f"beqz a2, 9f", "1:"]
    # Inner: work A from the inner midstate, W0..4 = U in B.
    o += [f"lwu {A[i]}, {4 * i}(a0)" for i in range(5)]
    o += block(A, B + rest, fold, order, dbl)
    for i in range(5):
        o += [f"lwu a6, {4 * i}(a0)", f"add {A[i]}, {A[i]}, a6"]
    # Outer: work B from the outer midstate, W0..4 = the inner digest in A.
    o += [f"lwu {B[i]}, {20 + 4 * i}(a0)" for i in range(5)]
    o += block(B, A + rest, fold, order, dbl)
    for i in range(5):
        o += [f"lwu a6, {20 + 4 * i}(a0)", f"add {B[i]}, {B[i]}, a6"]
    for i in range(5):
        o += [f"lwu a6, {40 + 4 * i}(a0)", f"xor a6, a6, {B[i]}", f"sw a6, {40 + 4 * i}(a0)"]
    o += ["addi a2, a2, -1", "bnez a2, 1b", "9:", "ld a1, 104(sp)"]
    o += [f"sw {B[i]}, {4 * i}(a1)" for i in range(5)]
    o += [f"ld {r}, {8 * i}(sp)" for i, r in enumerate(saved)]
    o += ["addi sp, sp, 112", "ret", f".size iter_{name}, .-iter_{name}"]
    return o


VARIANTS = {
    "v0": {},
    "fold": {"fold": True},
    "fold_order": {"fold": True, "order": True},
    "fold_dbl": {"fold": True, "dbl": True},
    "fold_order_dbl": {"fold": True, "order": True, "dbl": True},
}

if __name__ == "__main__":
    lines = [".text", ".option push", ".option arch, +m"]
    for name, kw in VARIANTS.items():
        body = variant(name, **kw)
        n_loop = sum(1 for l in body[body.index("1:"):body.index("9:")] if not l.endswith(":"))
        print(f"{name}: {n_loop} instructions per step", file=sys.stderr)
        lines += body
    lines += [".option pop"]
    open(sys.argv[1], "w").write("\n".join(lines) + "\n")
