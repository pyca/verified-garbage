module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-!
# The precomputed values of an RSA modulus on RISC-V

`vg_rsa_public_precompute(pre = a0, pre_len = a1, n = a2, n_len = a3,
scratch = a4, scratch_len = a5)`: with the modulus `n` (`k = n_len` bytes,
most significant first) of `w = ⌈k / 8⌉` words, writes `n` and `R² mod n`
for `R = 2^(64 w)` to `pre` and returns 1, or writes zeros and returns 0 if
`n` is not a valid modulus (odd, its first byte not zero, and at least
`2^511`, which for `k = 64` is its top bit).

The working space (`scratch`) is laid out as `Impl/Bignum/Layout.lean`'s,
with `n` in array 0, `x` in array 1, the accumulator in array 2 and the
temporary in array 3; the callee-saved registers it uses are saved in its
header's words 16–24. `R² mod n = 2^(128 w) mod n` is computed (`lz`, then
`r2Words`) by long division of `2^(128 w)` by `n`, 63 bits a step, for any
top word of `n`, with `z`, the leading zeros of `n`'s top word (`lz`), to
normalize the estimates of the quotients. `r2`, which other functions use, starts from
`2^(64 (w - 1))`, makes `64 + w` modular doublings to `2^w R mod n` (the
double into the accumulator, then `MontMul.lean`'s `subMod64` and
`selectAcc64` into `x`) and six Montgomery squares (`MontMul.tail`), with
`-n⁻¹ mod 2⁶⁴` from `n`'s low word by Newton's iteration.

`n` is public: timing may depend on it, and the code branches on its
validity; every count of `r2Words` depends only on `w`.

Registers: `s5` `pre`, `s6` the working space, `s7` `n`'s bytes, `s8` `k`;
`a7` `n`'s base (array 0), `a2` `x`'s, `a5` the accumulator's, `a6` the
temporary's, `t0` `w`; in `r2`, `t1` `-n⁻¹ mod 2⁶⁴` and `a1` the doublings
left; in `r2Words`, `a1` the leading zeros, then the steps left.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.Precompute

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64

/-- The callee-saved registers used, in the order they are saved: `s6`
keeps the working space's address, and is restored last. -/
def saved (i : Nat) : Reg :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s7, .s8, .s6].getD i .s0

/-- The header words where they are saved. -/
def saveOff (i : Nat) : Nat := 8 * sFn i

/-- Save them in the working space at `a4`, and keep its address in `s6`. -/
def save : List Instr :=
  (List.range 9).flatMap (fun i => [.store .d (saved i) .a4 (saveOff i)]) ++ [.addi .s6 .a4 0]

/-- Restore them, through `s6`, which is restored last. -/
def restore : List Instr :=
  (List.range 8).flatMap (fun i => [.load .d (saved i) .s6 (saveOff i)]) ++
    [.load .d .s6 .s6 (saveOff 8)]

/-- `pre` into `s5`, `n`'s bytes into `s7`, `k` into `s8`, `w = ⌈k / 8⌉`
into `t0` and the header's `w`, and the arrays' bases (each `w + 2` words:
`8 w + 16` bytes, in `a1`). -/
def setup : List Instr :=
  [.addi .s5 .a0 0, .addi .s7 .a2 0, .addi .s8 .a3 0, .addi .t0 .a3 7, .shift .srl .d .t0 .t0 3,
    .store .d .t0 .s6 (8 * sW), .shift .sll .d .a1 .t0 3, .addi .a1 .a1 16, .addi .a7 .s6 hdrBytes,
    .add .a2 .a7 .a1, .add .a5 .a2 .a1, .add .a6 .a5 .a1]

/-- The `w` words at `t3` := 0, through `t5`. -/
def zeroWords : Prog isa :=
  .seq (.block [.addi .t5 .t0 0, .li .s0 0]) (countLoop .t5 [.store .d .s0 .t3 0, .addi .t3 .t3 8])

/-- `n`'s `k` bytes (at `s7`), most significant first, into array 0: byte
`i` is byte `k - 1 - i` of the number, which is little-endian in memory. -/
def loadN : Prog isa :=
  .seq (.block [.addi .t3 .a7 0]) (.seq zeroWords
    (.seq (.block [.add .t4 .a7 .s8, .addi .t4 .t4 (-1), .addi .a0 .s7 0, .addi .t5 .s8 0])
      (countLoop .t5 [.load .b .s0 .a0 0, .store .b .s0 .t4 0, .addi .a0 .a0 1, .addi .t4 .t4 (-1)])))

/-- `n`'s last byte's low bit, inverted, into `s0`, and its first byte into
`t4`. -/
def check1 : List Instr :=
  [.add .t4 .s7 .s8, .addi .t4 .t4 (-1), .load .b .s0 .t4 0, .logicImm .and .s0 .s0 1,
    .logicImm .xor .s0 .s0 1, .load .b .t4 .s7 0]

/-- The rest of `check`, from the bytes `check1` loaded. -/
def check2 : Prog isa :=
  .seq (.ite (.zero .t4) (.block [.li .s0 1]) (.block []))
    (.seq (.block [.addi .t5 .s8 (-64)])
      (.ite (.zero .t5) (.block [.shift .srl .d .t4 .t4 7, .logicImm .xor .t4 .t4 1,
        .logic .or .s0 .s0 .t4]) (.block [])))

/-- Whether `n` is a valid modulus, in `s0`: 0 if it is. Its last byte is
odd, its first is not zero, and if `k = 64`, its first byte's top bit is
set: `s0 := (1 - last & 1) | (first = 0) | (k = 64 ∧ first < 128)`. -/
def check : Prog isa := .seq (.block check1) check2

/-- `acc := 2 x`, `w + 1` words, for `x` in array 1 (`a2`), the bit shifted
out of each word in `s4`. -/
def double64 : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t4 .a2 0, .addi .t5 .t0 0, .li .s4 0])
    (.seq (countLoop .t5 [.load .d .s2 .t4 0, .shift .sll .d .s3 .s2 1, .add .s3 .s3 .s4,
        .shift .srl .d .s4 .s2 63, .store .d .s3 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8])
      (.block [.store .d .s4 .t3 0]))

/-- `x := 2 x mod n`: `double64`, then `MontMul.lean`'s `subMod64` and
`selectAcc64`, whose output is `x` (`a2`). -/
def doubleMod64 : Prog isa := .seq double64 (.seq subMod64 selectAcc64)

/-- `x := 2^(64 (w - 1))`: array 1 (`a2`) zeroed, then its word `w - 1` := 1. -/
def r2Top : Prog isa :=
  .seq (.block [.addi .t3 .a2 0]) (.seq zeroWords
    (.block [.shift .sll .d .t3 .t0 3, .add .t3 .t3 .a2, .addi .t3 .t3 (-8), .li .s0 1,
      .store .d .s0 .t3 0]))

/-- `64 + w` doublings of `x = 2^(64 (w - 1))` (`r2Top`), counted by `a1`:
`2^w R mod n`, for `n` above `2^(64 (w - 1))`. -/
def r2HiDbl : Prog isa :=
  .seq r2Top (.seq (.block [.addi .a1 .t0 64])
    (.loop (.seq doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)))

/-- One step of Newton's iteration for the inverse `y` (`s0`) of `n₀` (`s3`)
modulo a power of 2: `y := y (2 - n₀ y)`, which doubles the bits of `y`
that are right. -/
def newton : List Instr :=
  [.mul .s1 .s3 .s0, .li .s2 2, .sub .s1 .s2 .s1, .mul .s0 .s0 .s1]

/-- `t1 := -n⁻¹ mod 2⁶⁴`, from `n`'s low word `n₀`: `n₀` is its own inverse
modulo `2³` (an odd square is 1 modulo 8), and five steps of Newton's
iteration make it right modulo `2⁹⁶`. -/
def minv : List Instr :=
  [.load .d .s3 .a7 0, .addi .s0 .s3 0] ++ newton ++ newton ++ newton ++ newton ++ newton ++
    [.li .s1 0, .sub .t1 .s1 .s0]

/-- `x := x² R⁻¹ mod n` in array 1: `MontMul.tail`, with `o`, `a` and `b`
all `x`. -/
def r2Sq : Prog isa := .seq (.block [.addi .a3 .a2 0, .addi .a4 .a2 0]) tail

/-- Six Montgomery squares of `x` in array 1 (`r2Sq`), each doubling the
power of 2 of `x = 2^e R mod n` (`(2^e R)² R⁻¹ = 2^(2 e) R`): from `2^w R mod n`
to `2^(64 w) R mod n = R² mod n`. -/
def r2Squares : Prog isa := .seq r2Sq (.seq r2Sq (.seq r2Sq (.seq r2Sq (.seq r2Sq r2Sq))))

/-- `x := R² mod n = 2^(128 w) mod n` in array 1, for `n` of `w` words with
its top word not zero: `r2HiDbl`, `minv`, then `r2Squares`. -/
def r2 : Prog isa := .seq r2HiDbl (.seq (.block minv) r2Squares)

/-- One step of `lz`: if `s0`'s top bit is clear, `s0 := 2 s0` and `a1 += 1`. -/
def lzStep : List Instr :=
  [.shift .srl .d .s1 .s0 63, .logicImm .xor .s1 .s1 1, .shiftReg .sll .d .s0 .s0 .s1, .add .a1 .a1 .s1]

/-- `a1 := z`, the leading zeros of `n`'s top word (word `w - 1` of array 0),
for a top word not zero: 63 steps of `lzStep`, counted by `t5`. -/
def lz : Prog isa :=
  .seq (.block [.shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .s0 .t3 0, .li .a1 0,
      .li .t5 63])
    (countLoop .t5 lzStep)

/-! ## `R² mod n` by steps of long division

For `vg_rsa_public_precompute`: `R² mod n = 2^(128 w) mod n` by steps of
long division (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D) of `X = 2^(128 w)`
by `n`, 63 bits at a time, as for any dividend (`WordDiv.divW`): its digits
are the 63-bit chunks of `X`, most significant first, and each step makes the
next number `V = r 2^63 + c` from the remainder `r` and the next chunk `c`.
The remainder is kept lazily, in `[0, 2 n)` rather than reduced (so that
`V < n 2^64`, as the estimate needs), and reduced once, at the end
(`finish`). A step estimates the quotient `q = ⌊V / n⌋` from the top words of
`V P` and `n P` for `P = 2^z`, `z` the leading zeros of `n`'s top word
(`lz`), so that the divisor's top word `d' = ⌊n P / 2^(64 (w - 1))⌋` has its
top bit set, for any `n` (`normTail`):
`q̂ = min(⌊(u₂ 2^64 + u₁) / d'⌋, 2^64 - 1)`, by division by the reciprocal
`v = ⌊(2^128 - 1) / d'⌋ - 2^64` (Möller and Granlund, "Improved division by
invariant integers", IEEE Trans. Computers 60(2), 2011, Algorithm 4), as
AArch64's (`Impl/Bignum/AArch64/R2Div.lean`), `v` computed once by
restoring division (`recip`), corrected by a third word to `q ≤ q̂ ≤ q + 1`
(`quot3`) and lowered by one (`dec`), so that `q - 1 ≤ q̂ ≤ q` and the
remainder `t = V - q̂ n` is in `[0, 2 n)` without adding `n` back. `t` is
written in place of `V`, shifted up by 63 bits, with the next chunk below
it, as the next `V` (`mulSub`). The arithmetic is branch-free, by masks, and
every count depends only on `w`.

The number `V` is `w + 1` words in array 1 (`a2`). From the top bits of
`X`, `V = 2^(65 w - 63 c)`, `S = w + 1 + c` steps (`stepCount`, for
`c = ⌈(w + 1) / 63⌉`) with zero chunks make `V = r 2^63`, `r ≡ X` modulo `n`
and `r < 2 n`, and `finish` makes `x = r mod n`.

Registers: `a7` `n`, `a2` `V`, `a6` the temporary (`P`, `d'` and `v` in its
words 0–2), `t0` `w`, `a4` zero, `a1` the steps left. -/

/-- After `lz` (`a1 = z`): `P = 2^z`, `d' = T P + ⌊L P / 2^64⌋` and
`d'ₗ = L P + ⌊L' P / 2^64⌋ mod 2^64`, the top two words of `n P`, for `n`'s top
three words `T`, `L` and `L'`, into the temporary's words 0, 1 and 3, `d'`
also in `s2`. -/
def normTail : List Instr :=
  [.li .s0 1, .shiftReg .sll .d .s0 .s0 .a1, .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-24),
    .load .d .s2 .t3 16, .load .d .s3 .t3 8, .shiftReg .sll .d .s2 .s2 .a1, .mulhu .s4 .s3 .s0,
    .add .s2 .s2 .s4, .mul .s3 .s3 .s0, .load .d .s1 .t3 0, .mulhu .s1 .s1 .s0, .add .s3 .s3 .s1,
    .store .d .s0 .a6 0, .store .d .s2 .a6 8, .store .d .s3 .a6 24]

/-- `a4 := 0`, the remainder `r := 2^64 - 1 - d'` (`s3`, for `d'` in `s2`),
the quotient `q := 0` (`s4`) and 64 (`t5`). -/
def recipHead : List Instr := [.li .a4 0, .li .s3 (-1), .sub .s3 .s3 .s2, .li .s4 0, .li .t5 64]

/-- A bit of restoring division by `d'` (`s2`) of the remainder `r < d'`
(`s3`) and a one bit: `r := 2 r + 1`, its carry into `s1`; `d'` subtracted
if the carry is set or `r ≥ d'` (`s0`, 0 or 1), by a mask; `q := 2 q + s0`. -/
def divBit : List Instr :=
  [.shift .srl .d .s1 .s3 63, .shift .sll .d .s3 .s3 1, .logicImm .or .s3 .s3 1, .sltu .s0 .s3 .s2,
    .logicImm .xor .s0 .s0 1, .logic .or .s0 .s0 .s1, .sub .s1 .a4 .s0, .logic .and .s1 .s1 .s2,
    .sub .s3 .s3 .s1, .shift .sll .d .s4 .s4 1, .logic .or .s4 .s4 .s0]

/-- `v = ⌊(2^128 - 1) / d'⌋ - 2^64 = ⌊((2^64 - 1 - d') 2^64 + 2^64 - 1) / d'⌋`
by 64 bits of restoring division, into the temporary's word 2. -/
def recip : Prog isa :=
  .seq (.block recipHead) (.seq (countLoop .t5 divBit) (.block [.store .d .s4 .a6 16]))

/-- `u₂ = x₂ P + ⌊x₁ P / 2^64⌋` (`t4`) and `u₁ = x₁ P + ⌊x₀ P / 2^64⌋` (`t5`),
the top two words of `x P`, from the top three words `x₂`, `x₁`, `x₀` of
`x = ⌊V / 2^64⌋` (`V`'s words 1 to `w`, at `a2 + 8`); `d'` (`s2`), `v`
(`s3`), and `e = d' - u₂` (`a3`). -/
def quotHead : List Instr :=
  [.shift .sll .d .t3 .t0 3, .add .t3 .t3 .a2, .addi .t3 .t3 (-16), .load .d .t4 .t3 16, .load .d .t5 .t3 8,
    .load .d .t6 .t3 0, .load .d .s0 .a6 0, .load .d .s2 .a6 8, .load .d .s3 .a6 16, .mul .t4 .t4 .s0,
    .mulhu .s1 .t5 .s0, .add .t4 .t4 .s1, .mul .t5 .t5 .s0, .mulhu .s1 .t6 .s0, .add .t5 .t5 .s1,
    .sub .a3 .s2 .t4]

/-- `⌊(u₂ 2^64 + u₁) / d'⌋` into `s1`, for `u₂ < d'`: `(q₁, q₀) = v u₂ +
(u₂, u₁)`, the candidate `q₁ + 1` and its remainder `r = u₁ - (q₁ + 1) d'
mod 2^64` (`t6`); one less and `r + d'` if `r > q₀`, and one more if then
`r ≥ d'`, by masks. -/
def quotMG : List Instr :=
  [.mul .s0 .s3 .t4, .mulhu .s1 .s3 .t4, .add .s0 .s0 .t5, .sltu .t6 .s0 .t5, .add .s1 .s1 .t4,
    .add .s1 .s1 .t6, .addi .s1 .s1 1, .mul .t6 .s1 .s2, .sub .t6 .t5 .t6, .sltu .s4 .s0 .t6,
    .sub .s1 .s1 .s4, .sub .s4 .a4 .s4, .logic .and .s4 .s4 .s2, .add .t6 .t6 .s4, .sltu .s4 .t6 .s2,
    .logicImm .xor .s4 .s4 1, .add .s1 .s1 .s4]

/-- `q̂ := q`, or all ones if `u₂ = d'` (`e = 0`). -/
def quotFix : List Instr := [.sltu .s4 .a4 .a3, .addi .s4 .s4 (-1), .logic .or .s1 .s1 .s4]

/-- `q̂` into `s1`. -/
def quot : List Instr := quotHead ++ quotMG ++ quotFix

/-- `u₀ = x₀ P + ⌊x₋₁ P / 2^64⌋ mod 2^64` (`t6`), the third word of `x P`,
from `x`'s words `x₀` and `x₋₁` below its top two (at `t3`), and `t = U - q̂ D`
over three words (`t4`, `t5`, `t6`), for `U = (u₂, u₁, u₀)`, `D = (d', d'ₗ)`
(`s2`, `a0`) and `q̂` (`s1`): `q̂ D` (`s4`, `s3`, `s0`), then subtracted
with its borrows. -/
def quot3Head : List Instr :=
  [.load .d .s0 .a6 0, .load .d .t6 .t3 0, .addi .a0 .t3 (-8), .load .d .a0 .a0 0, .mul .t6 .t6 .s0,
    .mulhu .a0 .a0 .s0, .add .t6 .t6 .a0, .load .d .a0 .a6 24, .mul .s0 .s1 .a0, .mulhu .a3 .s1 .a0,
    .mul .s3 .s1 .s2, .mulhu .s4 .s1 .s2, .add .s3 .s3 .a3, .sltu .a3 .s3 .a3, .add .s4 .s4 .a3,
    .sltu .a3 .t6 .s0, .sub .t6 .t6 .s0, .sltu .s0 .t5 .s3, .sub .t5 .t5 .s3, .sltu .s3 .t5 .a3,
    .sub .t5 .t5 .a3, .logic .or .a3 .s0 .s3, .sub .t4 .t4 .s4, .sub .t4 .t4 .a3]

/-- `q̂ := q̂ - 1` and `t := t + D` if `t` is negative (its top word's sign),
by a mask. -/
def quot3Fix : List Instr :=
  [.shift .srl .d .a3 .t4 63, .sub .s1 .s1 .a3, .sub .a3 .a4 .a3, .logic .and .s0 .a0 .a3,
    .logic .and .s3 .s2 .a3, .add .t6 .t6 .s0, .sltu .s0 .t6 .s0, .add .t5 .t5 .s3, .sltu .s3 .t5 .s3,
    .add .t5 .t5 .s0, .sltu .s0 .t5 .s0, .logic .or .s3 .s3 .s0, .add .t4 .t4 .s3]

/-- `q̂ := min(⌊U / D⌋, 2^64 - 1)` from `quot`'s `min(⌊(u₂ 2^64 + u₁) / d'⌋,
2^64 - 1)`, at most 2 more (Knuth, TAOCP vol. 2, §4.3.1, Theorem B): `t = U -
q̂ D`, and `q̂` one less while `t` is negative, twice (the second time only
`q̂`). -/
def quot3 : List Instr := quot3Head ++ quot3Fix ++ [.shift .srl .d .a3 .t4 63, .sub .s1 .s1 .a3]

/-- `q̂ := q̂ - 1` unless it is 0: `q̂ - 1 ≤ ⌊V / n⌋ ≤ q̂` from `quot3`'s
`⌊V / n⌋ ≤ q̂ ≤ ⌊V / n⌋ + 1`. -/
def dec : List Instr := [.sltu .s4 .a4 .s1, .sub .s1 .s1 .s4]

/-- The pointers into `V` (`t3`) and `n` (`t4`), `w` (`t5`), and the carry
`c` (`s0`) and the borrow `b` (`s4`) := 0; `t6`, the next chunk shifted up
a bit, is set before. -/
def mulSubHead : List Instr := [.addi .t3 .a2 0, .addi .t4 .a7 0, .addi .t5 .t0 0, .li .s0 0, .li .s4 0]

/-- A word of `mulSub`: `p = n_i q̂ + c` (the low word `s3`, the high word the
next `c`), `t_i = V_i - p - b` (`s3`), and `V_i := ⌊t_{i-1} / 2⌋ + 2^63 t_i
mod 2^64` from the previous `t_{i-1}` (`t6`), which `t_i` becomes. -/
def mulSubWord : List Instr :=
  [.load .d .s2 .t4 0, .mul .s3 .s2 .s1, .mulhu .s2 .s2 .s1, .add .s3 .s3 .s0, .sltu .s0 .s3 .s0,
    .add .s0 .s2 .s0, .load .d .a0 .t3 0, .sltu .s2 .a0 .s3, .sub .s3 .a0 .s3, .sltu .a3 .s3 .s4,
    .sub .s3 .s3 .s4, .logic .or .s4 .s2 .a3, .shift .srl .d .a0 .t6 1, .shift .sll .d .a3 .s3 63,
    .logic .or .a0 .a0 .a3, .store .d .a0 .t3 0, .addi .t6 .s3 0, .addi .t3 .t3 8, .addi .t4 .t4 8]

/-- The top word: `t_w = V_w - c - b`, and `V_w := ⌊t_{w-1} / 2⌋ + 2^63 t_w
mod 2^64`. -/
def mulSubTop : List Instr :=
  [.load .d .a0 .t3 0, .sub .s3 .a0 .s0, .sub .s3 .s3 .s4, .shift .srl .d .a0 .t6 1,
    .shift .sll .d .a3 .s3 63, .logic .or .a0 .a0 .a3, .store .d .a0 .t3 0]

/-- `V := t 2^63 + ⌊t₆ / 2⌋` modulo `2^(64 (w + 1))` for `t = V - q̂ n`
modulo `2^(64 (w + 1))`, after `mulSubHead`, `q̂` in `s1`. -/
def mulSub : Prog isa := .seq (countLoop .t5 mulSubWord) (.block mulSubTop)

/-- A step of the division: `q̂` (`quot`, `quot3`, `dec`), `mid`, which sets
`t6` to the next chunk shifted up a bit, and `V := (V - q̂ n) 2^63 + ⌊t₆ / 2⌋`
(`mulSub`). -/
def step (mid : List Instr) : Prog isa :=
  .seq (.block (quot ++ quot3 ++ dec ++ mid ++ mulSubHead)) mulSub

/-- `c = ⌈(w + 1) / 63⌉ = 1 + [w > 62] + [w > 125]` into `s0` (for
`w < 189`), and the steps `S = w + 1 + c` into `a1`. -/
def stepCount : List Instr :=
  [.li .s0 62, .sltu .s0 .s0 .t0, .li .s1 125, .sltu .s1 .s1 .t0, .add .s0 .s0 .s1, .addi .s0 .s0 1,
    .add .a1 .t0 .s0, .addi .a1 .a1 1]

/-- A word of `finish`'s first pass: `R`'s word `i`, `⌊V_i / 2^63⌋ + 2
(V_{i+1} mod 2^63)`, from `V`'s word `i` (`s2`) and the next (which `s2`
becomes), in place of `V_i`, and the borrow (`s4`) of `R - n` over it. -/
def finWord1 : List Instr :=
  [.load .d .s3 .t3 8, .shift .srl .d .s2 .s2 63, .shift .sll .d .a0 .s3 1,
    .logic .or .s2 .s2 .a0, .store .d .s2 .t3 0, .load .d .a0 .t4 0, .sltu .s0 .s2 .a0, .sub .s2 .s2 .a0,
    .sltu .a3 .s2 .s4, .logic .or .s4 .s0 .a3, .addi .s2 .s3 0, .addi .t3 .t3 8, .addi .t4 .t4 8]

/-- A word of `finish`'s second pass: `x_i := R_i - (n_i & mask) - b`. -/
def finWord2 : List Instr :=
  [.load .d .s2 .t3 0, .load .d .s3 .t4 0, .logic .and .s3 .s3 .s1,
    .sltu .s0 .s2 .s3, .sub .s2 .s2 .s3, .sltu .a3 .s2 .s4, .sub .s2 .s2 .s4, .logic .or .s4 .s0 .a3,
    .store .d .s2 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8]

/-- `R`'s top word `⌊V_w / 2^63⌋` in place of `V_w`, the mask (`s1`) of
`R ≥ n` (no borrow out of `R - n`), and the second pass's pointers. -/
def finMid : List Instr :=
  [.shift .srl .d .s2 .s2 63, .store .d .s2 .t3 0, .sltu .s4 .s2 .s4, .logicImm .xor .s4 .s4 1,
    .sub .s1 .a4 .s4, .addi .t3 .a2 0, .addi .t4 .a7 0, .addi .t5 .t0 0, .li .s4 0]

/-- `x := R mod n`, for `R = ⌊V / 2^63⌋ < 2 n`: `R` (`w + 1` words) in place
of `V`, with the borrow of `R - n` (`finWord1`), then `n` subtracted from `R`
if there was none, by a mask (`finWord2`). -/
def finish : Prog isa :=
  .seq (.block [.addi .t3 .a2 0, .addi .t4 .a7 0, .addi .t5 .t0 0, .li .s4 0, .load .d .s2 .a2 0])
    (.seq (countLoop .t5 finWord1) (.seq (.block finMid) (.seq (countLoop .t5 finWord2)
      (.block [.load .d .s2 .t3 0, .sub .s2 .s2 .s4, .store .d .s2 .t3 0]))))

/-- `V := 2^(65 w - 63 c) = ⌊2^(128 w) / 2^(63 (S - 1))⌋` in `w + 1` words
(`w` zeroed, word `w` from `a4 = 0`, then the bit `e = 65 w - 63 c` set in
word `⌊e / 64⌋`), and `S` (`stepCount`). -/
def r2Init : Prog isa :=
  .seq (.block [.addi .t3 .a2 0]) (.seq zeroWords
    (.block ([.store .d .a4 .t3 0] ++ stepCount ++ [.shift .sll .d .s1 .t0 6, .add .s1 .s1 .t0,
      .shift .sll .d .s2 .s0 6, .sub .s2 .s2 .s0, .sub .s1 .s1 .s2, .shift .srl .d .s2 .s1 6,
      .shift .sll .d .s2 .s2 3, .add .s2 .s2 .a2, .logicImm .and .s1 .s1 63, .li .s3 1,
      .shiftReg .sll .d .s3 .s3 .s1, .store .d .s3 .s2 0])))

/-- The `S` steps, with zero chunks, counted by `a1`. -/
def r2Steps : Prog isa := .loop (.seq (step [.li .t6 0]) (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)

/-- After `lz`: `x := R² mod n` in array 1, for `n` of `w ≥ 4` words with its
top word not zero: `normTail`, `recip`, then the division of `2^(128 w)`
(`r2Init`, `r2Steps`, `finish`). -/
def r2Words : Prog isa := .seq (.block normTail) (.seq recip (.seq r2Init (.seq r2Steps finish)))

/-- `w` words from `t4` to `t3`, both advanced past them. -/
def copyWords : Prog isa :=
  .seq (.block [.addi .t5 .t0 0])
    (countLoop .t5 [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8])

/-- `n` and `x` into `pre`. -/
def write : Prog isa :=
  .seq (.block [.addi .t3 .s5 0, .addi .t4 .a7 0]) (.seq copyWords
    (.seq (.block [.addi .t4 .a2 0]) copyWords))

/-- `pre`'s `2 w` words := 0. -/
def zeroPre : Prog isa :=
  .seq (.block [.addi .t3 .s5 0]) (.seq zeroWords zeroWords)

/-- Load and check `n`, then write `n` and `R² mod n` to `pre` and return 1,
or zero `pre` and return 0. -/
def core : Prog isa :=
  .seq loadN (.seq check (.ite (.zero .s0) (.seq lz (.seq r2Words (.seq write (.block [.li .a0 1]))))
    (.seq zeroPre (.block [.li .a0 0]))))

/-- `vg_rsa_public_precompute(pre, pre_len, n, n_len, scratch, scratch_len)`. -/
def precompute : Prog isa :=
  .seq (.block (save ++ setup)) (.seq core (.block restore))

end VG.Impl.Bignum.RISCV64.Precompute
