# P-384 on AArch64: working, before any code

Written before any of the code it decides. `derive.py` checks every identity
here on random and edge values. x = 2^32; p = x^12 - x^4 - x^3 + x - 1;
c = 2^384 - p = x^4 + x^3 - x + 1; R = 2^384 (fixed by the contracts).

## What I saw of the old code, by accident

Comments that name the old source (heads of files, and one grep of
`Impl/Weierstrass/AArch64/Mont.lean` that printed the composition of the two
old functions: load b, product, reductions, add the high half, conditional
subtraction); theorem *names and signatures* of the old `lin` proof (from a
grep for declarations), which name a fold and a correction and masks; and
P-521's doubling steps. None of it is used. Two things I noticed I know from
elsewhere and therefore do not use: the fused `12 b - 9 a^2` for the doubling's
`4 b - X3` (I take 4 b - X3 from X3 itself), and any library's Karatsuba or
Montgomery schedule. Karatsuba itself is textbook, chosen by the counts below.

## Costs on the machines

CI's AArch64 runner is the machine to please. Published guides of the Arm
Neoverse cores: one or two multiplies a cycle (64x64 low and high each a
multiply, 2 to 5 cycles' latency), 3-4 additions a cycle, flags renamed,
madd does not set flags. So count M (mul, umulh) apart from A (everything
else on the integer side). Which binds is to be measured (an unproven
prototype, `bench/` branch) since the guides differ between cores.

## Product of 6x6 words

* Schoolbook, by rows: 72 M; a row is two carry chains, 7 + 6 A; first row 5:
  70 A.
* One level of Karatsuba on 3+3 words: 3 (18 M + 17 A) = 54 M, 51 A, and
  - subtracting: P1 = (a0-a1)(b1-b0), Mid = P0 + P2 + P1. Signs:
    (i) absolute values: 2 (3 sub + 1 mask + 3 eor + 3 sub) = 20, the sign
    applied to a six-word product 1 + 6 + 1;
    (ii) keep a0-a1 mod 2^192 with its borrow mask ma (4 A each, 8), multiply
    the residues A, B, and take off 2^192 (ma&B), 2^192 (mb&A), add back
    2^384 (ma&mb): and 6+1, sub 4+4+1: 8 + 16 = 24 against 28. Shorter to the
    multiplication too (one chain, not two). Take (ii).
  - adding: (a0+a1)(b0+b1) has the same corrections, then must *subtract* P0
    and P2 (6 + 6 more than below can share). Worse.
  - joining, with S = P0h + P2l used twice: S 4, words 3-5 = S + P0l 4,
    words 6-8 = S + P2h 4, the carry of the first at word 6: 4, + P1: 7,
    top 3: 26 A.
  Total 54 M + 51 + 24 + 26 = 101 A, and 12 more memory operations (P1 has to
  be spilt: 22 registers are free to inline code). 155 ALU+M against
  schoolbook's 142, but 18 fewer M. If a core does one M a cycle, 72 cycles
  against 54 (and 292 instructions / 5 = 58); if two, a tie or a small loss.
  => measure both.
* Two levels, or 2+2+2: 3 words do not split evenly; 2x3x(2x2 Karatsuba) saves
  one more M pair per 2x2 for ~12 A. No.

## Square

Cross products 15 pairs (30 M) doubled, 6 squares (12 M): 42 M;
A: rows 5+9+7+5+2 = 28, doubling 11, squares 11 = 50. Karatsuba would be
36 M for about 40 more A: no.

## Montgomery reduction of 6 words

-p^-1 = 1 + x (mod 2^64) and 1 + x + x^2 (mod 2^128) (no multiplications).

* One word a round: m = t0 + (t0<<32) with carry b; then
  (T + m p)/2^64 = T>>64 + (m>>32) + b - m 2^32 - m 2^64 + m 2^320, where the
  carry of computing m is the only thing the low word leaves. 4 A for m and
  g = (m>>32)+b, 5 for D = m(2^64+2^32) - g, 6 for the chain: 15. Six: 90 A.
* Two words a round, M = T0 (1+x+x^2) mod x^4: m0 = t0 + (t0<<32),
  m1 = t1 + (t1:t0)>>32 + t0 + carry: 5 A.  Y = M (1 - x + x^3) = T0 + x^4 YH,
  (T + M p)/x^4 = T>>128 - (YH + M) + M x^8.
  YH = (M>>32) - (m1>>32) + k, k the carry (-1..1) of the low halves:
  the low word of Y gives only a borrow b0 = [m0 < m0<<32], the second word is
  m1 + (m0<<32) [carry ka] - (M>>32)_0 - b0 [borrow kb] = t1, k = ka - kb.
  ka is the carry in of D = M + (M>>32), kb the borrow in of subtracting m1>>32.
  So both need no materialising: 5 + 3 (shifts) + 1 + 3 + 2 + 3 + 6 = 23 A a
  round, three rounds: 69 A. The order matters: subtracting m1>>32 + kb first
  could go below zero (M < 2^32). Take this.
* Three words a round: the inverse mod x^6 is 1+x+x^2-2x^4-4x^5: more shifts
  and adds than the saved chain. Six at once (R = TH + M - H): M still has to be
  found in order. No.
The result T/R mod p is below 2p when T < R p; one conditional subtraction:
p's words 3 equal all-ones; 4 A to make from zero or 6 loads.

## Doubling

The window's contract wants exactly X3 = 9a^2 - 8b, Y3 = 3a(4b - X3) - 8g^2,
Z3 = 2YZ with d = Z^2, g = Y^2, b = Xg, a = (X-d)(X+d) (a = -3 tangent). The
halved form ((3/2)a, three squares fewer linear steps) has other coordinates:
out. (Y+Z)^2 - g - d: a square for a product (-12 M, about -60 A) but two
linear steps more (+50 A): equal; keep 2YZ first, measure later.
Linear steps, each to the canonical range: X-d, X+d, 9a^2-8b, 4b-X3, 3v-8g^2,
2(YZ). With B' = p - B (6 A, no borrow): 8(A+B')+A, 4A+B', 2(4B'+A)+A: shifts
by extr, seven words (7 A each), additions 7 A; no multiplications (a mul/umulh
version of 9A-8B is 24 M). The top word t is small: L + t 2^384 = L + t c,
t c = t 2^128 + (t<<32) 2^64 - ((t<<32) - t): 4 A + 7 A; L + tc < 2p; then the
conditional subtraction as everywhere. A fused doubling keeps words in
registers between operations; the order and registers will be found by a
script of mine and checked by the value-numbering certificate.

## Bounds used

product: a any 384-bit, b < p: T < R p. Mid < 2^385: its top word is 0 or 1.
Word 9 takes k + C2 + carry + top(P1) which is >= 0 as P0h + Mid + 2^192 P2l >= 0.
linear: 9A+8B' < 17p, 3A+8B' < 11 p: t < 2^5, t c < 2^134, L + t c < 2^384 + 2^134 < 2p.

# Measurements of the prototypes (CI aarch64, CPU part 0xd49; runs 45669004711, 45669474920)

`gen.py`, `gen2.py` (candidates), `asm.py`, `asm2.py` (what was timed; no proofs).
Eight dependent / eight independent operations, ns: Karatsuba 257 / 243,
schoolbook 254 / 235, square 211 / 184. Single instructions, 256 of each, ns:
add chain 65 (so a cycle is about 0.25 ns), add/adc/lsl/csel 20.5 (4 a cycle),
adds 31 (about 2.2 a cycle), mul, umulh, extr 38 (about 2 a cycle), madd 76,
mul latency 2, umulh 3, str 72 (about 1 a cycle), ldr 29.

So: multiplies are not the bound (Karatsuba is a tie and is dropped: simpler
code), and neither is the instruction count: 255 instructions in 118 cycles.
Independent copies hardly overlap: the window (some 160 instructions) holds
less than one operation, so what binds is the depth of the product followed
by that of the reduction. Hence: reduce two words as soon as two rows of the
product are in (rows 0-1, reduce, rows 2-3, reduce, rows 4-5, reduce), so that
the reduction runs beside the next rows; only 8-9 accumulator words live.
To be checked with a small model of the pipeline (`sim.py`) before the code.
