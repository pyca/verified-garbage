module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# Modular arithmetic on PPC64LE: reduction

`reduce`: `x mod m` for a number `x` of a public number of bytes, read most
significant first from memory (`r30`, `r31` bytes), into array 1 of the
public-key operation's working space (`PublicChecked`), with `m` in array 0,
`r10` array 0's base, `r29` an array's size and `r11` `2 w`. Each bit of `x`,
from the top, takes the accumulator to `2 a + b mod m` (`doubleBitMod`:
`Precompute.double` with the bit as its carry in, then `subMod` and
`selectAcc`), so nothing branches on `x`.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.ModArith

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

/-- The accumulator (`r8`, `n + 1` digits) := `2 x + b` for `x` at `r5` (`n =
r11` digits) and `b` the top bit of `r24`, which is shifted left. -/
def doubleBit : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .addi .r17 .r11 0, .lsr .d .r20 .r24 63,
      .lsl .r24 .r24 1])
    (.seq (Precompute.countLoop .r17 [.load .w .r0 .r15 0, .add .r0 .r0 .r0, .add .r0 .r0 .r20,
        .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4, .addi .r15 .r15 4])
      (.block [.store .w .r20 .r14 0]))

/-- `x := 2 x + b mod m`, in arrays 1 (`x`), 2 and 3 with `m` in array 0. -/
def doubleBitMod : Prog isa := .seq doubleBit (.seq subMod selectAcc)

/-- The eight bits of the byte at `r30`, from the top, `r30` advanced. -/
def reduceByte : Prog isa :=
  .seq (.block [.lbz .r24 .r30 0, .lsl .r24 .r24 56, .addi .r30 .r30 1, .li .r25 8])
    (.loop (.seq doubleBitMod (.block [.subi .r25 .r25 1])) (.nonzero .d .r25))

/-- The `r31` bytes from `r30`, each scanned. -/
def reduceScan : Prog isa :=
  .loop (.seq reduceByte (.block [.subi .r31 .r31 1])) (.nonzero .d .r31)

/-- `x mod m` into array 1. -/
def reduce : Prog isa :=
  .seq (.block (base .r14 1)) (.seq Precompute.zeroWords
    (.seq (.block (base .r5 1 ++ base .r8 2 ++ base .r9 3)) reduceScan))

end VG.Impl.Bignum.PPC64LE.ModArith
