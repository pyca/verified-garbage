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
