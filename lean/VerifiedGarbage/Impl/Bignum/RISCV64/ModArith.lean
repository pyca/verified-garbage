module

public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked

/-!
# Modular arithmetic on RISC-V: reduction, and masked addition

On the arrays of the public-key operation's working space
(`Impl/Bignum/RISCV64/PublicChecked.lean`): `a7` array 0's base, `s5` an
array's size and `t0` the words `w` of the modulus `m` in array 0.

* `reduce64`: `x mod m` for a number `x` of a public number of bytes, read
  most significant first from memory (`s9`, `s10` bytes), into array 1. Each
  bit of `x`, from the top, takes the accumulator to `2 a + b mod m`
  (`doubleBitMod64`: `dbl64In`, the double with the bit as its carry in, then
  `MontMul.lean`'s `subMod64` and `selectAcc64`), so nothing branches on
  `x`. As PPC64LE's `ModArith.reduce64`.
* `addMask64`: `[t3] += [t4] & s4` over `w` words, the carry out dropped.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.ModArith

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.PublicChecked

/-- `acc := 2 x + b`, `w + 1` words, for `x` in array 1 (`a2`) and the bit
`b` in `s4`: `Precompute.double64` with its carry in given. -/
def dbl64In : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t4 .a2 0, .addi .t5 .t0 0])
    (.seq (countLoop .t5 [.load .d .s2 .t4 0, .shift .sll .d .s3 .s2 1, .add .s3 .s3 .s4,
        .shift .srl .d .s4 .s2 63, .store .d .s3 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8])
      (.block [.store .d .s4 .t3 0]))

/-- `x := 2 x + b mod m`, `b` the top bit of `s7`, which is shifted left. -/
def doubleBitMod64 : Prog isa :=
  .seq (.block [.shift .srl .d .s4 .s7 63, .shift .sll .d .s7 .s7 1]) (.seq dbl64In (.seq subMod64 selectAcc64))

/-- The eight bits of the byte at `s9`, from the top, `s9` advanced, counted
by `s8`. -/
def reduceByte : Prog isa :=
  .seq (.block [.load .b .s7 .s9 0, .shift .sll .d .s7 .s7 56, .addi .s9 .s9 1, .li .s8 8])
    (.loop (.seq doubleBitMod64 (.block [.addi .s8 .s8 (-1)])) (.nonzero .s8))

/-- The `s10` bytes from `s9`, each scanned. -/
def reduceScan : Prog isa :=
  .loop (.seq reduceByte (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10)

/-- `x mod m` into array 1, for `x`'s `s10 ≥ 1` bytes at `s9`. -/
def reduce64 : Prog isa :=
  .seq (.block (base .t3 1)) (.seq Precompute.zeroWords
    (.seq (.block (base .a2 1 ++ base .a5 2 ++ base .a6 3)) reduceScan))

/-- `[t3] += [t4] & s4` over `w` (`t0`) words, the carry (`s1`) out of the top
dropped: each word's two carries are never both set (`x + y` wraps only if
its sum is at most `2⁶⁴ - 2`, to which the carry in adds at most 1). -/
def addMask64 : Prog isa :=
  .seq (.block [.addi .t5 .t0 0, .li .s1 0])
    (countLoop .t5 [.load .d .s2 .t3 0, .load .d .s3 .t4 0, .logic .and .s3 .s3 .s4, .add .s2 .s2 .s3,
      .sltu .s0 .s2 .s3, .add .s2 .s2 .s1, .sltu .s1 .s2 .s1, .logic .or .s1 .s1 .s0, .store .d .s2 .t3 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8])

end VG.Impl.Bignum.RISCV64.ModArith
