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
  `q̂₀ = min(⌊(u₂ 2^64 + u₁) / d⌋, 2^64 - 1)` from the top words `u₂`, `u₁` of
  `x` and `d` of `m`, which for `d ≥ 2^63` gives `q ≤ q̂₀ ≤ q + 2`, by
  division by the reciprocal `v = ⌊(2^128 - 1) / d⌋ - 2^64` (Möller and
  Granlund, "Improved division by invariant integers", IEEE Trans. Computers
  60(2), 2011, Algorithm 4), its two corrections by `csel` (`quot`); `v` is
  computed once, by restoring division, a bit at a time (`recip`);
* corrected with the next words of `x` and `m` (Knuth's step D3, a 3-by-2
  estimate) to `q̂ = min(⌊U / D⌋, 2^64 - 1)` for the top three words `U` of
  `x 2^64` and the top two `D` of `m`, which gives `q ≤ q̂ ≤ q + 1` (`quot3`);
* `t = x 2^64 - q̂ m` in place of `x`, over its `w + 1` words, in one pass
  (`mulSub`);
* `m` added to `t` if it is negative, masked by its sign (`addBack`).

Every loop count, branch and address depends only on `w` (and `fastTest` on
`m`'s top bit); the arithmetic on `m`'s words is branch-free. Other moduli
take the doublings and squarings of `old`; `choice` takes this one when it
can.

The registers of a step: `x9` `m`, `x11` `x` (`aR2`), `x6` the temporary
(whose first word is `v`), `x12` `w`, `x7` zero, `x1` `q̂`; the rest
temporaries. No callee-saved register is written.
-/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.R2Div

open VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64

/-! ## A step -/

/-- The bases of `m`, `x` and the temporary, `w`, and zero. -/
def bases : List Instr :=
  [ldh .x9 (sArr aN), ldh .x11 (sArr aR2), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0]

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

/-- `q̂₀ D` over three words (`x13`, `x14`, `x17`, least significant first),
for `q̂₀` in `x1` and `D = (d, dₗ)` in `x5`, `x15`. -/
def quot3Mul : List Instr :=
  [.mul .x .x13 .x1 .x15, .umulh .x14 .x1 .x15, .mul .x .x16 .x1 .x5, .umulh .x17 .x1 .x5,
    .adds .x .x14 .x14 .x16, .adc .x .x17 .x17 .x7]

/-- `t = U - q̂₀ D` over three words (`x4`, `x3`, `x2`), for `U = (u₂, u₁, u₀)`
in `x2`, `x3`, `x4`. -/
def quot3Sub : List Instr := [.subs .x .x4 .x4 .x13, .sbcs .x .x3 .x3 .x14, .sbc .x .x2 .x2 .x17]

/-- If `t` is negative (its top word's sign): `q̂ := q̂ - 1` and `t := t + D`,
by `csel` (only `t`'s top word is kept, in `x2`). -/
def quot3Fix : List Instr :=
  [.adds .x .x4 .x4 .x15, .adcs .x .x3 .x3 .x5, .adc .x .x16 .x2 .x7, .subImm .x .x17 .x1 1, .tst .x .x2 .x2,
    .cselc .x .x1 .x17 .x1 .mi, .cselc .x .x2 .x16 .x2 .mi]

/-- `q̂ := min(⌊U / D⌋, 2^64 - 1)` from `quot`'s `q̂₀` (`x1`), at most 2 more
(Knuth, TAOCP vol. 2, §4.3.1, Theorem B), for the top three words
`U = (u₂, u₁, u₀)` (`x2`, `x3`, `x4`) of `x 2^64` and the top two
`D = (d, dₗ)` (`x5`, `x15`) of `m` (of `x P` and `m P` in `stepN`):
`t = U - q̂₀ D` over three words,
then `q̂` one less and `t := t + D` if `t` is negative, and `q̂` one less
again if `t` still is. -/
def quot3Core : List Instr := quot3Mul ++ quot3Sub ++ quot3Fix ++ [.lsr .x .x2 .x2 63, .sub .x .x1 .x1 .x2]

/-- `u₁ = x[w - 2]` into `x3`, `u₀ = x[w - 3]` into `x4` (0 for `w = 2`, by
`csel` on `w`) and `dₗ = m[w - 2]` into `x15`, after `quot`. -/
def quot3Load : List Instr :=
  [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 24, .add .x .x16 .x11 .x13, ld .x3 .x16 8, ld .x4 .x16,
    .add .x .x17 .x9 .x13, ld .x15 .x17 8, .subImm .x .x14 .x12 2, .tst .x .x14 .x14,
    .cselc .x .x4 .x14 .x4 .eq]

/-- `quot3Core` from `x` and `m`. -/
def quot3 : List Instr := quot3Load ++ quot3Core

/-- The pointers into `x` (`x16`) and `m` (`x17`), `w` (`x14`), the
product's carry `x2 := 0`, all ones in `x15` and `x13` (the complement of
`x`'s word below the first, 0), and the carry flag clear. -/
def mulSubHead : List Instr :=
  [mov .x16 .x11, mov .x17 .x9, mov .x14 .x12, mov .x2 .x7, movi .x15 0, .subImm .x .x15 .x15 1,
    mov .x13 .x15, .adds .x .x3 .x7 .x7]

/-- A word of `mulSub`, which computes the complement `x'` of `t` as a sum:
`x'ᵢ = q̂ mᵢ + c + ~xᵢ₋₁` (`~xᵢ₋₁` in `x13`), the product's carry in `x2`
and the sum's in the carry flag, as `mac`'s; `tᵢ = ~x'ᵢ` over `xᵢ`, whose
complement is the next `x13`. -/
def mulSubWord : List Instr :=
  [ld .x3 .x17, .mul .x .x4 .x1 .x3, .umulh .x3 .x1 .x3, .adcs .x .x4 .x4 .x2, .adc .x .x2 .x3 .x7,
    ld .x3 .x16, .adds .x .x4 .x4 .x13, .logic .eor .x .x13 .x3 .x15, .logic .eor .x .x4 .x4 .x15,
    st .x4 .x16, next .x16, next .x17]

/-- The top word: `t_w = ~(~x_{w-1} + c)`. -/
def mulSubTop : List Instr := [.adc .x .x4 .x13 .x2, .logic .eor .x .x4 .x4 .x15, st .x4 .x16]

/-- `t := x 2^64 - q̂ m` modulo `2^(64 (w + 1))` in place of `x` (`x11`), its
`w + 1` words, for `q̂` in `x1`: `~t = ~(x 2^64) + q̂ m`, in one pass. -/
def mulSub : Prog isa :=
  .seq (.block mulSubHead) (.seq (countLoop .x14 mulSubWord) (.block mulSubTop))

/-- `t := t + m` if `t` is negative (the top bit of its word `w`), over its
`w + 1` words at `x11`: `m` masked by the sign, added by a chain of `adcs`
from the carry clear, then the carry into word `w`. -/
def addBack : Prog isa :=
  .seq (.block [.lsl .x .x13 .x12 3, .add .x .x13 .x11 .x13, ld .x3 .x13, .lsr .x .x3 .x3 63,
      .sub .x .x15 .x7 .x3, mov .x16 .x11, mov .x17 .x9, mov .x14 .x12, .adds .x .x3 .x7 .x7])
    (.seq (countLoop .x14 [ld .x4 .x17, .logic .and .x .x4 .x4 .x15, ld .x3 .x16, .adcs .x .x3 .x3 .x4,
        st .x3 .x16, next .x16, next .x17])
      (.block [ld .x3 .x16, .adc .x .x3 .x3 .x7, st .x3 .x16]))

/-- `x := x 2^64 mod m`: `q̂` within one of the quotient, `t = x 2^64 - q̂ m`
in place of `x`, and `m` added back once if `t` is negative. -/
def step : Prog isa := seqs [.block (bases ++ quot), .block quot3, mulSub, addBack]

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
when `t` is negative (rarely), by a branch on its sign. -/

/-- `x3 :=` the sign of `t`, the top bit of its word `w` (at `x11`). -/
def signTest : List Instr := [.lsl .x .x13 .x12 3, .add .x .x13 .x11 .x13, ld .x3 .x13, .lsr .x .x3 .x3 63]

/-- `addBack` if `t` is negative, by a branch on its sign: for a public `m`. -/
def addBackPub : Prog isa := .seq (.block signTest) (.ite (.zero .x .x3) (.block []) addBack)

/-- `step` with `addBackPub`: for a public `m`. -/
def stepPub : Prog isa := seqs [.block (bases ++ quot), .block quot3, mulSub, addBackPub]

/-- `steps` of `stepPub`. -/
def stepsPub : Prog isa :=
  .seq (.block [sth .x13 sCnt])
    (.loop (.seq stepPub (.block [ldh .x13 sCnt, .subImm .x .x13 .x13 1, sth .x13 sCnt])) (.nonzero .x .x13))

/-- `fast` by `stepsPub`: for a public `m`. -/
def fastPub : Prog isa := seqs [
  .block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0],
  neg,
  recip,
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

/-! ## Any top word, for a public `m`

For `m` whose top bit is clear (`fastTest`), `q̂` is estimated from the top
words of `x P` and `m P` for `P = 2^z` such that
`d' = ⌊m P / 2^(64 (w - 1))⌋ ≥ 2^63` (Knuth's normalization), while
`t = x 2^64 - q̂ m` is computed from `x` and `m` themselves: `normN` puts `P`,
`d'` and the next word `d'ₗ` of `m P` into the temporary's words 1, 2 and 3,
`recipN` `v` for `d'` into its word 0, and `quotN` and `quot3N` the top words
of `x P`. As `m < 2^(64 w - 1)` here,
`x` starts at `2^(64 (w - 1))`, below `m` (whose top word is not zero), and
takes `w + 1` steps. -/

/-- `x15` (`m`'s top word times `P`) and `P` (`x10`) doubled while the
former's top bit is clear, by `csel`. -/
def normStep : List Instr :=
  [.add .x .x16 .x15 .x15, .add .x .x17 .x10 .x10, .tst .x .x15 .x15, .cselc .x .x15 .x16 .x15 .pl,
    .cselc .x .x10 .x17 .x10 .pl]

/-- `P = 2^z`, `d' = T P + ⌊m[w - 2] P / 2^64⌋` (`T = m[w - 1] ≠ 0`) and
`d'ₗ = m[w - 2] P + ⌊m[w - 3] P / 2^64⌋ mod 2^64`, the top two words of
`m P`, into the temporary's words 1, 2 and 3: 63 of `normStep` from `T`. -/
def normN : Prog isa :=
  .seq (.block [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 24, .add .x .x13 .x9 .x13, ld .x15 .x13 16,
      ld .x3 .x13 8, ld .x4 .x13, movi .x10 1, movi .x13 63])
    (.seq (countLoop .x13 normStep) (.block [.mul .x .x16 .x3 .x10, .umulh .x4 .x4 .x10, .add .x .x16 .x16 .x4,
      .umulh .x3 .x3 .x10, .add .x .x15 .x15 .x3, st .x10 .x6 8, st .x15 .x6 16, st .x16 .x6 24]))

/-- `recip` for `d'` (the temporary's word 2). -/
def recipN : Prog isa :=
  .seq (.block [ld .x5 .x6 16, .sub .x .x2 .x7 .x5, .subImm .x .x2 .x2 1, movi .x10 0, movi .x4 1, movi .x13 64])
    (.seq (countLoop .x13 divBit) (.block [st .x10 .x6]))

/-- `d'` into `x5`, the top two words `u₂`, `u₁` of `x P` into `x2`, `x3` from
`x`'s top three words, and `x4 = d' - u₂`, zero iff `u₂ = d'`. -/
def quotHeadN : List Instr :=
  [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 24, .add .x .x16 .x11 .x13, ld .x2 .x16 16, ld .x3 .x16 8, ld .x4 .x16,
    ld .x17 .x6 8, ld .x5 .x6 16, .mul .x .x2 .x2 .x17, .umulh .x15 .x3 .x17, .add .x .x2 .x2 .x15,
    .mul .x .x3 .x3 .x17, .umulh .x15 .x4 .x17, .add .x .x3 .x3 .x15, .sub .x .x4 .x5 .x2]

/-- `q̂` into `x1`, as `quot`, from `x P` and `d'`. -/
def quotN : List Instr :=
  quotHeadN ++ quotMG ++ ([movi .x16 0, .subImm .x .x16 .x16 1, .tst .x .x4 .x4, .cselc .x .x1 .x16 .x14 .eq] : List Instr)

/-- `u₁ = x₂ P + ⌊x₁ P / 2^64⌋` into `x3` and `u₀ = x₁ P + ⌊x₀ P / 2^64⌋`
into `x4` (mod `2^64`), the next words of `x P`, from `x`'s words
`x₂ = x[w - 2]`, `x₁ = x[w - 3]` and `x₀ = x[w - 4]` (0 for `w = 3`), and
`d'ₗ` into `x15`, after `quotN`. -/
def quot3LoadN : List Instr :=
  [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 32, .add .x .x16 .x11 .x13, ld .x3 .x16 16, ld .x4 .x16 8,
    ld .x14 .x16, .subImm .x .x15 .x12 3, .tst .x .x15 .x15, .cselc .x .x14 .x15 .x14 .eq, ld .x17 .x6 8,
    .mul .x .x3 .x3 .x17, .umulh .x15 .x4 .x17, .add .x .x3 .x3 .x15, .mul .x .x4 .x4 .x17,
    .umulh .x15 .x14 .x17, .add .x .x4 .x4 .x15, ld .x15 .x6 24]

/-- `quot3Core` from `x P` and `m P`. -/
def quot3N : List Instr := quot3LoadN ++ quot3Core

/-- `stepPub` with `quotN` and `quot3N`. -/
def stepN : Prog isa := seqs [.block (bases ++ quotN), .block quot3N, mulSub, addBackPub]

/-- `steps` of `stepN`. -/
def stepsN : Prog isa :=
  .seq (.block [sth .x13 sCnt])
    (.loop (.seq stepN (.block [ldh .x13 sCnt, .subImm .x .x13 .x13 1, sth .x13 sCnt])) (.nonzero .x .x13))

/-- `x := 2^(64 (w - 1))`, from its base in `x11`: `setWord` for one in word
`w - 1`, but with no load from the header. -/
def setTop : Prog isa :=
  .seq (.block [mov .x8 .x11, movi .x9 1, .subImm .x .x13 .x12 1])
    (.seq zeroAcc (.block [.lsl .x .x16 .x13 3, .add .x .x16 .x8 .x16, st .x9 .x16]))

/-- `R² mod m` for a public `m` whose top word is not zero: `P`, `d'`, `v`,
`x := 2^(64 (w - 1))` (`setTop`) and `w + 1` steps. -/
def fastN : Prog isa := seqs [
  .block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0],
  normN,
  recipN,
  setTop,
  .block [.addImm .x .x13 .x12 1],
  stepsN]

/-- `old` for `w = 2`, whose `x` has no third word for `quotN`, and `f`
otherwise (`w ≥ 2`, public). -/
def choiceW (old f : Prog isa) : Prog isa :=
  .seq (.block [ldh .x12 sW, .subImm .x .x13 .x12 2]) (.ite (.zero .x .x13) old f)

end VG.Impl.Bignum.AArch64.R2Div
