# X25519 on AArch64: working notes

Each entry is committed before the code or run it decides.

## 0. What has no recorded working

The first design (`Impl/X25519/AArch64/Ladder.lean`, `FixedBase.lean`) was
made before this file. Its order of operations is RFC 7748's, its field code
the repository's generic `Word.lean` rows; the rest came from the author's own
understanding, with no recorded working. Of the old code the author saw only
file names, line counts (`git --numstat`), the names its users use, and the
base commit's benchmark times.

## 1. Counts of the first design (from its generated loop body)

918 instructions a step, 330 of them `mul`/`umulh`:
5 products x 41, 4 squares x 29, 9 in `a24`. 281 `adcs`.
Measured (run 45660788674): x25519 31.16 us, base 26.93 us.
`llvm-mca` (Neoverse N2 model): 222 cycles a step; the measurement is near
400 if the clock is 3.4 GHz. One of these is wrong. Candidates:

* H1: 64-bit multiplies have a throughput of one a cycle (330 cycles).
* H2: the carry chains, all through one flag register, are the limit.
* H3: latency: each field operation waits for the one before, and the window
  does not reach past it.

Experiment 1 (`lab/gen.py`): time single instructions (throughput, latency)
against a chain of dependent `add`s, which gives the clock; then the step and
its pieces, alone.

## 2. Experiment 1's result (run 45675997093) and what it decides

Clock 3.4 GHz (100 dependent `add`s: 29.4 ns). Throughput a cycle: `mul`,
`umulh` 2 (latency 2, 3); `add`, `csel`, `lsr` 4; flag setting about 3; a
carry chain 1; `extr`, shifted `add` 2; `ldp` 1.5; `stp` 2; NEON `umull` 1;
`madd` 1. The step: 396 cycles. A product alone, repeated with nothing
depending on the last: 38.4 cycles (41 multiplies: a floor of 20.5, 5-wide
dispatch about 20). A square: 30.6, dependent 43.2. 5 products + 4 squares at
those costs are 314, the front 23.5: the step is the sum of its parts.

H1 is false (multiplies would allow 165). Since even independent operations do
not overlap, the likely limit is the issue queues: `adcs` that wait on a chain
fill them and dispatch stops, long before the reorder buffer is full. Two carry
chains cannot alternate instruction by instruction (one flag register), but
they can row by row.

Dependencies of a step: front; then {AA, BB, DA, CB}; then {x3 = (DA+CB)^2,
t = (DA-CB)^2, x2 = AA BB, z2 = E(AA + a24 E)}; then z3 = x1 t. So 9 operations
in 3 levels; they pair as DA|CB, AA|BB, x3|t, x2|z2 and z3 alone.
Latency floor about 24 + 3 x 45 = 160.

Experiment 2: two products, rows alternating. Registers: fixed x0 x10 x19 (and
x1); a row has a, b0-b3, four low products: 9, the high products overwrite b;
each product has 4 live words between rows (5 in one), as word i is final after
row i and is stored. 9 + 8 + 1 = 18 of the 20. b is loaded again for each row
(24 loads a pair, against 1.5 `ldp` a cycle). Folds one after the other.
Compare 2 x 38.4 = 77; floor about 45.

## 3. Experiment 2's result (run 45677393309)

Two products one after the other (this row code, words stored): 74.0 cycles,
the same when each depends on the one before. Rows alternating: 69.9 (dependent
76.4). So H3 is false too: what limits is a resource. 41 multiplies + about 45
flag-setting operations take 37 cycles, though 2 and 3 of them a cycle are
possible alone. Hypothesis H4: flag-setting operations share the two multiply
pipes, with at most one other: (41 + 45)/3 = 29, or worse. Experiment 3:
mixtures of `mul` with `adds`, `adcs` chains, `add`, at two ratios, and
additions that take their operand from a multiply.

## 4. Experiment 3's result (run 45677858987)

Cycles for a body: 50 `mul` + 50 `adds` 25.5 (4 a cycle: no shared limit, H4
false); 100 `mul` + 25 chains of 4: 53.3 (floor 50); 100 `add` + the same
chains 52.6; 50 `mul` + the same chains 47.7 (floor 37.5); the chains alone 34.4;
the chains each on the one before's words 51 (latency alone would be 28);
12 chains of 8: 45.3 (2.1 a cycle). `adc`, which reads the flags but does not
write them: 4 a cycle.

H5: every flag-setting instruction takes a renamed flag register until a later
one retires, and there are only some 40 of them. A product sets flags 45 times,
so the window is about one product whatever the reorder buffer: which explains
why neither independence nor alternating rows helped.

What follows if so: (a) write the flags as rarely as possible: end a chain with
`adc`, not `adcs x, zero, zero`: a product could have 24 + 9 rather than 45;
(b) let the flag setters of an operation be short-lived: have the multiplies
before them, and arrange the chains as a tree rather than one after the other.

Tree: the four rows' products on their own (3 setters each: `adds, adcs, adcs,
adc`), P0 + 2^64 P1 and P2 + 2^64 P3 (4 each), and their sum (5): 25 setters,
depth about 4 + 5 + 6 against 8 chains after each other.

Experiment 4: (i) two independent chains of 12 `umulh` (36 cycles) with N
`adds` (or `add`) after each: 36 cycles while the window holds both, 72 when not:
find N. (ii) `mulA`: rows as now with `adc` ends; `mulT`: the tree.

## 5. Experiment 4's result (run 45678496885)

Two independent 36-cycle `umulh` chains with N operations after each, cycles a
body: `add` N = 10..60: 36 36 36 37 42 49. `adds`: 36 36 51 59 95 100. So H5 holds:
some 40 flag writes may be in flight, and past that the machine is serial. `mulT`
(34 setters): 34.6 cycles, dependent 52.8, against 38.4 for the product in use
(45 setters) and 30.6 for the square (37). (`mulA`'s line fell outside the log read.)

So the cost is nearly the number of flag setters: about 0.85 cycle each, and the
step has 405. An instruction that sets flags nobody reads wastes a slot: `adcs`
at the end of a chain becomes `adc`, or `adds` `add`. Predicted: about 100 fewer
setters, 300 cycles.

Experiment 5: the step with every dead flag write removed (by liveness,
`lab/gen.py: minflags`), alone, and with it the tree product's order. This
touches no arithmetic.

## 6. Experiment 5's result (run 45678967840)

Cycles: step 396, `step_min` 375, `step_tree` 375; product 35.2 (`mulA` 35.4,
`mulT` 34.6), square 28.0. Parts: 5 x 35 + 4 x 28 + 23 = 310, so 65 cycles
are lost where an operation follows the one it needs (a dependent product costs
53). The order AA BB E DA CB x3 t z3 x2 z2 has CB -> x3 and t -> z3 adjacent.

Every step's swap needs all four results, so the loop has a bubble at its end:
the last operation's latency beyond its share. The critical path is front, DA,
(sum), t, z3: 20 + 53 + 8 + 44 + 53 = 178.

Candidates, operations that depend on each other apart:
 o1: DA CB AA BB t x3 z3 x2 z2
 o2: DA CB AA BB t x3 x2 z3 z2
 o3: AA BB DA CB x2 z2 t x3 z3
Doubling a square's cross products with `extr` (no flags; 7 setters less).

## 7. Experiment 6's result (run 45679510352)

Cycles: o0 393, o1 367 (without `extr` 369), o2 364, o3 360; square with `extr`
27.9 (no gain alone). So order is worth about 15 cycles and the scalar parts'
sum (310) is near the end of what scalar code gives: the base is about 325 (26.93 us,
less an inversion of about 2 us). To go below it, work that writes no flags must
run beside the scalar code: NEON `umull` (1 a cycle, 2 products each) next to it
(`vmix100`: 100 `umlal` and 100 `mul` together in 100 cycles).

## 8. Radix 2^51, from the flag limit

(Recognised: five 51-bit limbs is a well-known representation of this field,
and so is each of its steps. It is considered here because experiment 4's limit
asks for it; counts and bounds below are this derivation's own.)

With five limbs of 51 bits the carries of sums need no flags (there are 13 free
bits), and a product's columns are sums of 128-bit products: `adds` and `adc`
per term, one setter each, not chained to another column's. Setters: product 20
(25 terms, 5 first of their column), square 10, sums and differences 0, against
32, 20, 6-7. A step: 5 x 20 + 4 x 10 = 140, against 295.

Bounds. Results below 2^51 + 2^13. Sums below 2^52 + 2^14; differences with 2p
added (limbs 2^52 - 38, 2^52 - 2) below 2^52 + 2^51 + 2^13. A column is at most
a0 b_c + 19 (the rest): 1 + 4 x 19 = 77 < 2^6.3 terms for column 0, so with
factors < 2^52.6 and 2^52.1 a column is < 2^111, its carry (>> 51) < 2^60, and
column 4 (no 19) has carry < 2^56, times 19 < 2^61. One parallel round: r_i =
(l_i mod 2^51) + c_(i-1) < 2^51 + 2^61, r_0 with 19 c_4; a second parallel round:
limb < 2^51 + 19 x 2^10 . So limbs < 2^51 + 2^15: fine.

Instructions: product: 6 loads, 4 (19 b), 50, 40, round 1: 5 extr 5 and 5 add
2 (19 c4), round 2: 4 add-with-lsr 5 and 3 (or lsr and add apart), 3 stores:
about 128. Square about 92. Front about 75. The a24 product with no setters.
In all about 1150: at 4 integer operations a cycle 250-260 cycles, multiplies
390 / 2 = 195, setters 140. Latency of a product about 3 + 6 + 8 = 20-25,
against 53, so dependences matter little: the order can be the plain one.
Predicted 260-290, against 360 (o3) and the base's about 325.

Registers of a product: row by row over a: b 5, 19 b 4, columns 10, product 2,
a_i 1: 22 = x1-x17, x20-x24 but x1 (the output's address, kept in memory).

Experiment 7: `m51`, `s51` (alone and dependent) and the step `st51`.

## 9. Experiment 7's result (run 45680363598): radix 2^51 rejected

Product 43.1 (dependent 48.8), square 31.6 (dependent 39.6), step 396: no
better than the first step, though it sets flags a third as often. Its 1308
instructions run at 3.3 a cycle, and its products at 3.3. The prediction (4 a
cycle) was wrong. What runs best here runs at about 3.1-3.3: `mul50_chain4x25`
3.1, `m51` 3.3, `pair` 3.1; while the step in the order o3 runs at 2.5. So:
fewest instructions (four words, 910), scheduled so that they run at about 3.1:
910 / 3.1 = 293. Two ways to fill what is lost to dependent neighbours:
schedule across operations (interleave at the granularity of carry chains), or
run one pair of operations on NEON.

## 10. NEON beside scalar code, both in five limbs of 51 bits

(Recognised: running NEON beside scalar code for this function is known from
libraries; here it follows from sections 4-9 - what is short is flag registers
and integer issue, and vector code uses neither - and from this repository's
own X448 code, `Impl/Curve448/AArch64/Neon.lean`, `AArch64Weave.lean`, which
does it for another field. No library's arrangement is used: the format, the
split of the step and the products below are worked out here.)

Format shared by both: five limbs, so no conversion but a split of each limb
into 26 low bits and the rest (<= 27 bits for limbs < 2^53). Weights: lo_k at
2^(51 k), hi_k at 2^(51 k + 26). lo lo at 51(i+j); the two cross terms at
51(i+j) + 26; hi hi at 51(i+j) + 52 = 2 x 2^(51 (i+j+1)). Wrapping: x 19.

A vector holds [lo of element 1, lo of 2, hi of 1, hi of 2] of one limb:
`umull`/`umlal` multiply the lows, `umull2` the highs, and with one operand's
halves exchanged (`ext`) the cross terms. 4 a pair of limbs: 100 for a pair of
products; 55 for a pair of squares. Bounds: hi < 2^27, 19 hi < 2^32; a column
< 2^63 (5 x 19 x 2 x 2^54 = 2^61.6 for hi hi doubled, + lo lo).
Columns E_m (lo lo and 2 hi hi), X_m (cross). Reduction: one parallel round on
the 10 columns (26 and 25 bits), limbs E + 2^26 X < 2^64, one parallel round on
51 bits. Carries times 19 as shifts.

Cost (vector operations, 2 a cycle, multiplies 1 a cycle): products 100 + about
70 + 50 = 220; squares 55 + 70 + 35 = 160. Which operations:
 - one square pair and one product pair on NEON (190 cycles of it), the scalar
   side 3 products and 2 squares (about 190) and the front: balanced.
 - AA|BB and x2|z2 (the second needs the first; about 200 of latency) beside
   DA, CB, x3, t, z3 (160): two independent branches of the step, joined only at
   its ends. So the whole of the two branches can be woven.
Dispatch: about 380 + 780 = 1160 operations, 232 cycles at 5. Predicted 235-250
(the prediction for 51-bit scalar code alone was 10-40% optimistic).

Slots 48 bytes apart for `ldr q`. Constants (masks, 19) in memory, loaded.
Experiment 8: `sq2`, `mu2` alone, and the step with the two branches woven
(`st_neon`), and unwoven (`st_neon_seq`).

## 11. Experiment 8's result (run 45681381157), and the base's step

Cycles: `sq2` 116, `mu2` 173, woven step 341, unwoven 520, o3 360. The vector
side is the longer (its multiplier idles while a pair is split and reduced, as
the window does not reach the next pair), so more weaving alone will not help;
Karatsuba in the pair of halves (75 and 45 multiplies for 100 and 55) and
storing by `stp` for `ldr q` to forward would, to an estimated 310.

The base: 26.93 us = 91.6k cycles; this code's 31.16 us = 105.9k of which the
ladder is 255 x 396 = 101.0k, so the rest is 4.9k, and the base's step about
340. The target is therefore below 340.

Scalar first, as its proof is much smaller: experiment 9, `lab/sched.py`: the
step in SSA form, list scheduled over whole operations with each carry chain
kept together, registers allocated again (x1-x17, x20-x28), several settings
measured at once. Constants 19 and 38 kept in registers; DA + CB and DA - CB
formed from one load. If it pays, equality with the plain code can be proven by
a checked value numbering of both.

## 12. Experiment 9's result (run 45682346223): scheduling rejected

The step with its constants in registers (o3) 355; 28 schedules 350 to 365 (best
`sc_o3_19_50`). Scheduling and register allocation are worth 5 cycles: the
limit is the flag window, not order. Scalar code ends near 350; the base is 340.

Experiment 10, NEON:
 (a) `stp` for what a `ldr q` reads next (front: limbs 0-1, 2-3 stored in
     pairs, 4 with zero; E and F likewise): a vector load does not forward from
     two separate 8-byte stores.
 (b) Karatsuba in the halves: LL_m, HH_m (same limbs i + j = m, 19 when they
     wrap), K_m = (lo + hi)(lo' + hi'): X_m = K_m - LL_m - HH_m, E_m = LL_m +
     2 HH_(m-1), E_0 = LL_0 + 38 HH_4: 75 multiplies for 100, 45 for 55. With
     hi < 2^27: 19 (lo + hi) < 2^32; K_m < 5 x 2^27.6 x 2^31.9 < 2^62.
     In two passes: LL and HH from a, b, 19 b (14 registers, 10 sums), then
     a, b, 19 b become lo + hi in place, and K (5 sums).
 (c) the other split: NEON AA|BB then x3|t; scalar DA CB then E, F, x2, z2, and z3.

## 13. Experiment 10's result (run 45683118899)

Cycles: sn1 341 (as before), sn2 (a) 333, sn3 (a, b) 318, sn4 (a, b, c) 313; pair
of squares 122.8 with Karatsuba (116 without), of products 160 (173).
Projected: 313 x 255 + 4.9k = 84.7k cycles, 24.9 us, against 26.93.

Split (c) is kept: it also needs no pair of products on NEON, so one vector
kernel to prove (the pair of squares) and one scalar one (the product).

Experiment 11: in split (c), sn5: the plain pair of squares; sn6: and 2^51 - 1,
19 and 2p's limb kept in x25-x27 (six instructions less an operation); sn7: and a
sequential carry (26 instructions for 32, 5 more setters).

## 14. Experiment 11's result (run 45683741432)

sn4 323 (313 before E, F took the slots of B, A; alignment or forwarding),
sn5 317, sn6 317, sn6k 319, sn7 320: the instruction count no longer shows; the
all-51-bit design ends near 315.

Design weighed again. Instructions: four-word product 96 (51-bit 137), square
72 (94); NEON pair of squares 196. So four-word scalar code with NEON pairs
costs fewer instructions than 51-bit scalar code with the same pairs, if the
conversion is cheap: the split of four words into the ten limbs is 31 vector
operations (22 from 51-bit limbs; the same positions 51 k, 51 k + 26), and the
result's five limbs are packed by 16 scalar operations an element, 3 setters.
Also the scalar proofs that exist stay.

Experiment 12: `h1`: AA|BB on NEON beside DA, CB (and t, `h2`; and t, x3, `h3`),
everything else four-word code in the order pack, E, x2, z2, (t, x3,) z3.
`h4`: also x3|t on NEON (limbs of DA, CB added and subtracted as vectors, plus 4p
in limbs) beside E, x2, z2.

## 15. Experiment 12's result (run 45684660340)

Cycles: h1 369, h1b 356, **h2 334**, h3 336, h4 340; src 356, sn5 319. One NEON
pair beside DA, CB, t beats the base's 340 with the scalar code (and its
proofs) kept; sn5 is 15 faster but needs every scalar proof again. h2's family
is taken. Experiment 13 tunes it: constants 19 and 38 in registers (c), the
order of the rest, the weave's ratio (the vector block ended earlier), and the
Karatsuba pair.

## 16. Experiment 13's result (run 45685276137), and what is landed first

Cycles: h2 334; ta 331.5, tan 331 (squares doubled with `adcs`, as now: `extr` is
not worth it), tg 331, te 333, tj 333, th 333, tb, tc, tf, ti 335-336, td 350;
vector block ended earlier: 4/3 347, 3/2 356, 2 371; Karatsuba pair 335.
Projected for 331: 89.3k cycles, 26.3 us, against 26.93.

Order of landing: (A) dead flag writes out of the shared rows (`Word.lean`:
`adcs` that nothing reads becomes `adc`), for every user of them; (B) the order
of the ladder's operations; (C) the NEON pair, woven. Then measured again.

## 17. Landed on claude/cleanroom-aarch64-x25519: (A) and (B)

Dead flag writes out of `Word.lean`'s rows, and the ladder in the order o3, both
proven. Predicted: step about 358 (o3 360 here, with `adcs` doubling), x25519
about 28.3 us, and 5-8% less for base points and Ed25519 signing.

## 18. A and B measured (run 45688134188)

x25519 27.66 us (base 26.95), public key 7.71 (7.69), keygen 7.93 (8.05), sign/64
8.33 (8.44), verify/64 42.61 (45.42). The real step is 351 cycles, better than the
lab's 360 for the same order: `Word.lean`'s reduction, which alternates each `mul`
with the `adcs` that takes it, does better than the lab's. So orders are searched
on the real blocks. Experiment 14: the emitted step cut into its operations, in
orders that respect dependences (a random sample of 24), and the sums of DA
and CB from one load (`one`).

## 19. Experiment 14's result (run 45688803078)

The landed order 350.1 cycles; 24 others 347.7 (r2: BB DA CB AA E t x3 z3 z2 x2)
to 383. Order is worth 2.4 more cycles; the base is about 340. What is left is the
NEON pair (h2 / ta: 334-331 with the lab's reduction, which is slower than
`Word.lean`'s, so about 322-325 is expected with the real one): (C).

## 20. Experiment 15: the NEON pair beside the real scalar blocks

The h2 family again, with the emitted blocks (`step2.s`) for the scalar side:
front, weave(DA CB t, AA|BB on NEON), then the pack and the rest. The pack leaves
AA and BB in the registers E reads them from, so E loads nothing. Also: the
weave starting already at C and D (A and B, which the squares need, are stored
first), and other orders of the rest. Expected 322-325.

## 21. Experiment 15's result (run 45697622448), and experiment 16

Cycles: ue 322.5 (DA CB t x3 woven; then the pack, E, x2, z2, z3), ui 323, vc 323,
uc 324, ua 324.5, ve 324, others 327-330, two scalar products only (uj, vj) 349;
the landed code 349.6, r2 347. ue is taken: 322.5 x 255 + 4.9k = 87.1k = 25.6 us.

A saving seen while writing the kernel out: every product of X_m has an even
coefficient (cross terms of a square), so the exchanged vectors are taken of 2a
once (`ext` of D) and the 15 `add`s into a temporary go; 181 operations for 196.
Experiment 16: ue, uc, ui with that (`xe`, `xc`, `xi`), `xE`: t after x3.
