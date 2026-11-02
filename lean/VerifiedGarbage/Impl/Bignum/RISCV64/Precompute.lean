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
header's words 16–24. `R² mod n = 2^(128 w) mod n` is computed from `x =
2^(64 (w - 1))`, which is below a valid `n`, by `64 + w` modular doublings to
`2^w R mod n` (the double into the accumulator, then `MontMul.lean`'s
`subMod64` and `selectAcc64` into `x`), then six Montgomery squares
(`MontMul.tail`), with `-n⁻¹ mod 2⁶⁴` from `n`'s low word by Newton's
iteration.

`n` is public: timing may depend on it, and the code branches on its
validity.

Registers: `s5` `pre`, `s6` the working space, `s7` `n`'s bytes, `s8` `k`;
`a7` `n`'s base (array 0), `a2` `x`'s, `a5` the accumulator's, `a6` the
temporary's, `t0` `w`, `t1` `-n⁻¹ mod 2⁶⁴`, `a1` the doublings left.
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
  .seq loadN (.seq check (.ite (.zero .s0) (.seq r2 (.seq write (.block [.li .a0 1])))
    (.seq zeroPre (.block [.li .a0 0]))))

/-- `vg_rsa_public_precompute(pre, pre_len, n, n_len, scratch, scratch_len)`. -/
def precompute : Prog isa :=
  .seq (.block (save ++ setup)) (.seq core (.block restore))

end VG.Impl.Bignum.RISCV64.Precompute
