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
