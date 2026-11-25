# P-256 doubling, linear combinations and inversion on AArch64: working

Written before the code it decides. Prior exposure (reported to the coordinator): the names of the removed
code's helpers, its three combinations (12a-9b, 4a-b, 3a-8b) and its field-operation order, which were in
Impl/P256/EcdhDouble.lean, a user. None of those is kept. The order of operations there also looked to me like an
external library's, from memory, so the formula is chosen again below from the group law.

## 1. Which doubling

Contract: X3, Y3, Z3 equal `dblJMul`'s as field elements (a = -3): M = 3(X-Z^2)(X+Z^2), S = 4XY^2,
X3 = M^2-2S, Y3 = M(S-X3)-8Y^4, Z3 = 2YZ.

Instruction estimates, operands in registers: mul 75, square 55 (P-256 sparse Montgomery), canonical a-b 12
(4 subs, mask, 3 masked prime, 4 adds), canonical a+b 18 (5 add, 5-6 compare with p, 4 csel + constants).

A fused reduction of T = t4 2^256 + L, 0 <= t4 small: with q = t4+1 and c = 2^256-p < 2^224,
T-qp = L + t4 c - p, in [-p, (t4+1)c), so one masked addition of p makes it canonical.
q p mod 2^256 for 1 <= q < 2^32 has words (-q, (q<<32)-1, 0, q-(q<<32)) and the 4-word subtraction's borrow is
the sign, since T's and q p's top words are equal (t4 = q-1). Cost 1 + 4 + 4 + 1 + 2 + 4 = 16 after T is formed.

(a) 3M+5S, Z3 = (Y+Z)^2-Y^2-Z^2, the 3 of M deferred into X3 and Y3: 3*75+5*55 = 500;
    X-d 12, X+d 18, Y+Z 18, two subs 24, three fused ops ~ 30-45 each = 115: total ~ 687.
(b) 4M+4S, Z3 = 2YZ, M = 3m reduced, X3 = M^2-8b fused, W = 4b-X3 fused, Y3 = MW-8g^2 fused:
    520 + 12+18+27+31+28+31+18 = 685.
(c) 4M+4S with h = 2Y: g = h^2 (= 4Y^2), S = Xg, Z3 = hZ, Y3 = M W - g^2/2, W = S-X3, X3 = M^2-S-S:
    520 + 12 (X-d) + 18 (X+d) + 18 (2Y) + 27 (3m) + 24 (X3) + 12 (W) + half 14 + 12 = 657.
(c) has the fewest, every constant but 3 and 1/2 is gone, and its only operations that are not already verified ones
(`VerifySparse.op`) are *3x* and *x/2*. CHOSEN (c). 8Y^4 = (4Y^2)^2/2 is the only use of the half.

Alternatives for (c) not taken at first (to try after measuring): X+d left below 2^256 rather than below p (saves ~5
of 18, but needs the multiplication's bound for an operand up to 2^256); X3 = M^2-2S in one reduction
(31 against 24 for two subtractions, but one carry chain less in latency).

Latency: longest path per doubling: Z^2, (X+d), m, 3m, M^2, 2 subs, W, MW, sub: 5 products + 6 short ops; Z3 and g, S, g^2
run beside it. (a) has 5 products + 3 heavier ops on the same path. No clear winner on latency; mca decides when built.

## 2. 3x

T = x + 2x, 5 words: 2x by adds/adcs chain (or lsl/extr): d0 = x0<<1, d1 = extr(x1,x0,63), d2, d3, d4 = x3>>63 (5 instr);
adds/adcs x4, adc (5). t4 in {0,1,2}: 3x <= 3(p-1) < 3*2^256. q = t4+1 in 1..3. Then the fused reduction. 10+16 = 26.

## 3. x/2

x < p: if x odd add p (odd), then shift the 5-word sum right by one: mask = -(x0 & 1);
masked p = (mask, mask>>32, 0, (mask<<32)-mask); adds/adcs/adcs/adcs, adc top; extr x3, lsr... The sum x+p < 2p < 2^257, and the result
(x+p)/2 < p. Count: and 1, neg 1, lsr 1, lsl 1, sub 1, 4 adds, 1 adc, 4 extr = 14.

## 4. Scheduling

Raw = the list above, each op loading and storing slots; ci/p256_aarch64_schedule.py forwards, schedules and allocates registers,
and the existing symbolic certificate (CheckedObserved) proves the result equal on the observed slots. Nothing about order or registers
is decided by hand. Needs the script to know `logic and`, `.addImm`, `.subImm` if used; I avoid the immediates.

## 5. Inversion

The repository's published-algorithm machinery (Proof/Divstep, generic Impl/Weierstrass/AArch64/Inv.lean `pwords`: batches of 59
packed divsteps) already proves batch, fg update and ab update for any modulus. The P-256 inversions become:
  loop (batchStart; pwords; update) 10 times, finish, where `update` is the register allocation of the generic
  fgUpdate ++ abUpdate of the configuration, made by the script from the generic code and checked by CheckedObserved.
No divstep code of its own. Field (ECDH, constant time, ten batches: 590 divsteps, the repository's bound for 256 bits) and order (ECDSA
verification, early exit, existing wrapper) use the same scheme. x0, x1 (delta), x19 (counter), x20 (ECDH's output pointer) are not allocated.
Cost expected: 10 * (59*13 + ~60 + update) ; the update is 4 rows of 2*5 products: ~ 90 mul/umulh + ~250 other.
Candidates after a baseline: P-256's m = -1/p mod 2^64 = 1 makes k = t0, and k p by shifts, no products (words: k(2^256-2^224+2^192+2^96-1)).

## 6. After the first version (dated by this commit)

Built as designed. mca (Neoverse N2, dispatch 5, one iteration): doubling raw 1154 instructions, 276 cycles; allocated 999, 260 cycles
(945 at 4 tries, 265 cycles). Updates: 791 raw; allocated 414 (field), 432 (order). Field estimate in section 1 for the doubling (657) did not count loads,
moves of constants or the canonical correction of every product (~18 each): that is why 945.
Candidate improvements, in order of expected gain, decided on the first measurement:
 (i) canonical corrections after each product: 8 x ~14 instructions. A product below 2^256 (not p) costs 5 fewer and is acceptable only as one operand
     of a product; not with the present contract of `VerifySparse.op`.
 (ii) the 3x: 26 -> two adds is 36; keep.
 (iii) the first batch's P-256 reduction in `abUpdate`: m = 1, so `mul x16 = t0 * minv` is t0, and k p is 4 products (mul/umulh pairs 8); by shifts 0. 2 rows
     per batch: 16+ products of ~ 90 in the update; about 60 instructions of 414.
