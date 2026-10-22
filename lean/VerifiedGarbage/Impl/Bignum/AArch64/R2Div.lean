module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-!
# `R² mod m` by word steps of long division (AArch64)

For a modulus `m` of `w ≥ 2` words whose top bit is set
(`2^(64 w - 1) ≤ m`), `R² mod m` (`R = 2^(64 w)`) from `R mod m = R - m` by
`w` steps `x := x 2^64 mod m`, which give `2^(64 w) R mod m`, with no
Montgomery multiplication: where `double` adds one bit at a time, each step
adds a word, as a step of long division (Knuth, TAOCP vol. 2, §4.3.1,
Algorithm D), as x86-64's `R2Words` and `R2Adx` do:

* the quotient `q = ⌊x 2^64 / m⌋` is estimated as
  `q̂ = min(⌊(u₂ 2^64 + u₁) / d⌋, 2^64 - 1)` from the top words `u₂`, `u₁` of
  `x` and `d` of `m`, which for `d ≥ 2^63` gives `q ≤ q̂ ≤ q + 2`, by
  division by the reciprocal `v = ⌊(2^128 - 1) / d⌋ - 2^64` (Möller and
  Granlund, "Improved division by invariant integers", IEEE Trans. Computers
  60(2), 2011, Algorithm 4), its two corrections by `csel` (`quot`); `v` is
  computed once, by restoring division, a bit at a time (`recip`), or, for a
  public `m`, by Newton steps (`recipN`);
* `q̂ m` into the accumulator (`w + 2` words) by `zeroAcc` and `mulAddRow`,
  Montgomery multiplication's row;
* `t = x 2^64 - q̂ m` over the accumulator's `w + 1` words, in two's
  complement (`subPass`);
* `m` added to `t` while it is negative, twice, masked by its sign
  (`addBack`);
* `t` back into `x`.

Every loop count, branch and address depends only on `w` (and `fastTest` on
`m`'s top bit); the arithmetic on `m`'s words is branch-free. Other moduli
take the doublings and squarings of `old`; `choice` takes this one when it
can.

The registers of a step: `x8` the accumulator, `x9` `m`, `x11` `x`
(`aR2`), `x6` the temporary (whose first word is `v`), `x12` `w`, `x7` zero,
`x1` `q̂`; the rest temporaries. No callee-saved register is written.
-/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.R2Div

open VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64

/-! ## A step -/

/-- The bases of the accumulator, `m`, `x` and the temporary, `w`, and zero. -/
def bases : List Instr :=
  [ldh .x8 (sArr aAcc), ldh .x9 (sArr aN), ldh .x11 (sArr aR2), ldh .x6 (sArr aTmp), ldh .x12 sW,
    movi .x7 0]

/-- `d = m[w - 1]` into `x5`, `u₂ = x[w - 1]` into `x2`, `u₁ = x[w - 2]` into
`x3`, and `x4 = d - u₂`, zero iff `u₂ = d` (as `x < m` has `u₂ ≤ d`). -/
def quotHead : List Instr :=
  [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 8, .add .x .x14 .x9 .x13, ld .x5 .x14,
    .add .x .x16 .x11 .x13, ld .x2 .x16, .subImm .x .x16 .x16 8, ld .x3 .x16, .sub .x .x4 .x5 .x2]

/-- `⌊(u₂ 2^64 + u₁) / d⌋` into `x14`, for `u₂ < d` in `x2`, `u₁` in `x3`,
`d ≥ 2^63` in `x5` and `v` at `x6`: `(q₁, q₀) = v u₂ + (u₂, u₁)`, the
candidate `q₁ + 1` and its remainder `r = u₁ - (q₁ + 1) d mod 2^64`; one less
and `r + d` if `r > q₀`, and one more if then `r ≥ d`. -/
def quotMG : List Instr :=
  [ld .x17 .x6, .mul .x .x13 .x17 .x2, .umulh .x14 .x17 .x2, .adds .x .x13 .x13 .x3,
    .adc .x .x14 .x14 .x2, .addImm .x .x14 .x14 1, .mul .x .x15 .x14 .x5, .sub .x .x15 .x3 .x15,
    .subImm .x .x16 .x14 1, .add .x .x17 .x15 .x5, .subs .x .x3 .x13 .x15,
    .cselc .x .x14 .x16 .x14 .lo, .cselc .x .x15 .x17 .x15 .lo,
    .subs .x .x3 .x15 .x5, .adc .x .x14 .x14 .x7]

/-- `q̂` into `x1`: the quotient, all ones if `u₂ = d`. -/
def quot : List Instr :=
  quotHead ++ quotMG ++ ([movi .x16 0, .subImm .x .x16 .x16 1, .tst .x .x4 .x4, .cselc .x .x1 .x16 .x14 .eq] : List Instr)

/-- `t := x 2^64 - q̂ m` over the accumulator's `w + 1` words, which hold
`q̂ m`: word 0 is `0 - p₀`, word `i ≥ 1` is `x[i - 1] - pᵢ` less the borrow. -/
def subPass : Prog isa :=
  .seq (.block [mov .x16 .x8, mov .x17 .x11, mov .x14 .x12, ld .x3 .x16, .subs .x .x3 .x7 .x3, st .x3 .x16,
      next .x16])
    (countLoop .x14 [ld .x4 .x17, ld .x3 .x16, .sbcs .x .x3 .x4 .x3, st .x3 .x16, next .x16, next .x17])

/-- `t := t + m` if `t` is negative (the top bit of its word `w`), over its
`w + 1` words: `m` masked by the sign, added by a chain of `adcs` from the
carry clear, then the carry into word `w`. -/
def addBack : Prog isa :=
  .seq (.block [.lsl .x .x13 .x12 3, .add .x .x13 .x8 .x13, ld .x3 .x13, .lsr .x .x3 .x3 63,
      .sub .x .x15 .x7 .x3, mov .x16 .x8, mov .x17 .x9, mov .x14 .x12, .adds .x .x3 .x7 .x7])
    (.seq (countLoop .x14 [ld .x4 .x17, .logic .and .x .x4 .x4 .x15, ld .x3 .x16, .adcs .x .x3 .x3 .x4,
        st .x3 .x16, next .x16, next .x17])
      (.block [ld .x3 .x16, .adc .x .x3 .x3 .x7, st .x3 .x16]))

/-- `w` words of the accumulator into `x`. -/
def copyBack : Prog isa :=
  .seq (.block [mov .x16 .x8, mov .x17 .x11]) copyWords

/-- `x := x 2^64 mod m`. -/
def step : Prog isa :=
  seqs [.block (bases ++ quot), zeroAcc, mulAddRow, subPass, addBack, addBack, copyBack]

/-- `step` `x13` times (a public count, at least 1), counted in `sCnt`. -/
def steps : Prog isa :=
  .seq (.block [sth .x13 sCnt])
    (.loop (.seq step (.block [ldh .x13 sCnt, .subImm .x .x13 .x13 1, sth .x13 sCnt])) (.nonzero .x .x13))

/-! ## The reciprocal -/

/-- A bit of restoring division by `d` (`x5`) of the remainder `r < d` (`x2`)
and a one bit: `r := 2 r + 1`, its carry into `x3`; subtract `d` if the carry
is set or `r ≥ d` (`x16`, 0 or 1), by `csel`; the quotient
`x10 := 2 x10 + x16`. `x4` is 1. -/
def divBit : List Instr :=
  [.lsr .x .x3 .x2 63, .lsl .x .x2 .x2 1, .logic .orr .x .x2 .x2 .x4, .subs .x .x15 .x2 .x5,
    .adc .x .x16 .x7 .x7, .logic .orr .x .x16 .x16 .x3, .tst .x .x16 .x16, .cselc .x .x2 .x15 .x2 .ne,
    .add .x .x10 .x10 .x10, .add .x .x10 .x10 .x16]

/-- `v = ⌊(2^128 - 1) / d⌋ - 2^64 = ⌊((2^64 - 1 - d) 2^64 + 2^64 - 1) / d⌋`
for `d = m[w - 1]` (`m` at `x9`, `w` in `x12`), by 64 bits of restoring
division, into the first word of the temporary (at `x6`). -/
def recip : Prog isa :=
  .seq (.block [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 8, .add .x .x13 .x9 .x13, ld .x5 .x13,
      .sub .x .x2 .x7 .x5, .subImm .x .x2 .x2 1, movi .x10 0, movi .x4 1, movi .x13 64])
    (.seq (countLoop .x13 divBit) (.block [st .x10 .x6]))

/-! ## `R² mod m` -/

/-- `x := R - m`: `0 - m` over `w` words, a chain of `sbcs` from the carry
set (no borrow). -/
def neg : Prog isa :=
  .seq (.block [mov .x16 .x11, mov .x17 .x9, mov .x14 .x12, .subs .x .x3 .x7 .x7])
    (countLoop .x14 [ld .x4 .x17, .sbcs .x .x3 .x7 .x4, st .x3 .x16, next .x16, next .x17])

/-- `x := R - m`, `v`, and `w` steps. -/
def fast : Prog isa := seqs [
  .block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0],
  neg,
  recip,
  .block [ldh .x13 sW],
  steps]

/-! ## For a public `m`

`m` and every value computed from it are public in `vg_rsa_public_precompute`,
whose contract allows its timing to depend on `n`: there, `addBack` runs only
when `t` is negative (rarely), by a branch on its sign, and `v` is found by
six Newton steps from a guess, then corrected one at a time down and up until
it is exact (`recipN`), rather than by `recip`'s 64 steps of division. -/

/-- A Newton step towards `v = ⌊(2^128 - 1) / d⌋ - 2^64` for `d` (`x5`) from
`v` (`x10`), as `x = 2^64 + v` approximates `2^128 / d` from below: the high
word `e = 2^64 - 1 - (d + ⌊v d / 2^64⌋)` of the error `2^128 - x d` (`x4` all
ones), and `v := v + e + ⌊v e / 2^64⌋`, which is `x + ⌊x e / 2^64⌋`. Only the
speed of `recipN` depends on how close it comes. -/
def recipStep : List Instr :=
  [.umulh .x2 .x10 .x5, .add .x .x2 .x2 .x5, .logic .eor .x .x2 .x2 .x4, .umulh .x3 .x2 .x10, .add .x .x2 .x2 .x3,
    .add .x .x10 .x10 .x2]

/-- `d = m[w - 1]` into `x5` (`m` at `x9`, `w` in `x12`), the first guess
`v = 2^64 - 1 - d` into `x10` (`x = 2^65 - 1 - d`, within a quarter of
`2^128 / d`), and six Newton steps. -/
def recipGuess : List Instr :=
  [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 8, .add .x .x13 .x9 .x13, ld .x5 .x13, .subImm .x .x4 .x7 1,
    .logic .eor .x .x10 .x5 .x4] ++ (List.replicate 6 recipStep).flatten

/-- `v := v - 1` if `(2^64 + v) d ≥ 2^128` (the carry of `d + ⌊v d / 2^64⌋`),
which is `x16`. -/
def recipDown : List Instr := [.umulh .x2 .x10 .x5, .adds .x .x2 .x2 .x5, .adc .x .x16 .x7 .x7, .sub .x .x10 .x10 .x16]

/-- `v := v + 1` if `v + 1 < 2^64` and `(2^64 + v + 1) d < 2^128`, which is
`x16` (`x15` is 1). -/
def recipUp : List Instr :=
  [.adds .x .x3 .x10 .x15, .adc .x .x13 .x7 .x7, .umulh .x2 .x3 .x5, .adds .x .x2 .x2 .x5, .adc .x .x16 .x7 .x7,
    .logic .orr .x .x16 .x16 .x13, .sub .x .x16 .x15 .x16, .add .x .x10 .x10 .x16]

/-- `v = ⌊(2^128 - 1) / d⌋ - 2^64` for `d = m[w - 1] ≥ 2^63` into the first
word of the temporary (at `x6`), as `recip` but by `recipGuess`, then
`recipDown` and `recipUp` while they change it: whatever `recipGuess` gives,
`v` is then the largest with `(2^64 + v) d < 2^128`. The loops branch on
values of the modulus: for a public `m`. -/
def recipN : Prog isa := seqs [.block recipGuess, .loop (.block recipDown) (.nonzero .x .x16), .block [movi .x15 1],
  .loop (.block recipUp) (.nonzero .x .x16), .block [st .x10 .x6]]

/-- `x3 :=` the sign of `t`, the top bit of the accumulator's word `w`. -/
def signTest : List Instr := [.lsl .x .x13 .x12 3, .add .x .x13 .x8 .x13, ld .x3 .x13, .lsr .x .x3 .x3 63]

/-- `addBack` if `t` is negative, by a branch on its sign: for a public `m`. -/
def addBackPub : Prog isa := .seq (.block signTest) (.ite (.zero .x .x3) (.block []) addBack)

/-- `step` with `addBackPub`: for a public `m`. -/
def stepPub : Prog isa :=
  seqs [.block (bases ++ quot), zeroAcc, mulAddRow, subPass, addBackPub, addBackPub, copyBack]

/-- `steps` of `stepPub`. -/
def stepsPub : Prog isa :=
  .seq (.block [sth .x13 sCnt])
    (.loop (.seq stepPub (.block [ldh .x13 sCnt, .subImm .x .x13 .x13 1, sth .x13 sCnt])) (.nonzero .x .x13))

/-- `fast` by `recipN` and `stepsPub`: for a public `m`. -/
def fastPub : Prog isa := seqs [
  .block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0],
  neg,
  recipN,
  .block [ldh .x13 sW],
  stepsPub]

/-- `x3` zero iff the top bit of `m`'s top word is clear. -/
def fastTest : List Instr :=
  [ldh .x12 sW, ldh .x9 (sArr aN), .lsl .x .x13 .x12 3, .subImm .x .x13 .x13 8, .add .x .x13 .x9 .x13,
    ld .x3 .x13, .lsr .x .x3 .x3 63]

/-- `R² mod m` by `fast` when the top bit of `m` is set, by `old` (the
doublings and squarings) otherwise. -/
def choice (old : Prog isa) : Prog isa := .seq (.block fastTest) (.ite (.zero .x .x3) old fast)

/-- `choice` by `fastPub`: for a public `m`. -/
def choicePub (old : Prog isa) : Prog isa := .seq (.block fastTest) (.ite (.zero .x .x3) old fastPub)

end VG.Impl.Bignum.AArch64.R2Div
