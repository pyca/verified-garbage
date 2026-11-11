module

public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # `R² mod n` for a public modulus, from its top bit

For `n` of `w` words whose top word `T` (word `w - 1`) has its top bit at
position `j`, `x = 2^(64 (w - 1) + j) ≤ n` (and `x < n`, `n` being odd), and
`w + 1 + (63 - j)` doublings take `x` to `2^(64 w + w)`, which six
Montgomery squarings take to `R² mod n` as in `r2`. The top word's halves
are in array 0; its high half `h` if not zero, else its low half `l`, is
searched for its top bit `b` from `2^31` down. A top word of zero (not a
valid modulus) takes `r2`'s `65 w` doublings from 1. Every branch and count
depends only on `n`, which is public.
-/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Array 0's pointer into r6, `w` into r1. -/
def topPointers : List Instr := [.ldr .r6 .r0 64, .ldr .r1 .r0 48]

/-- r4 `:= 8 w - 8`, r6 at the top word, its low half `l` into r3, its high
half `h` into r5, and Z set iff both are zero. -/
def topWord : List Instr :=
  [.mov .r4 (.shifted .r1 .lsl 3), .dp .sub .r4 .r4 (.imm 8), .dp .add .r6 .r6 (.reg .r4),
   .ldr .r3 .r6 0, .ldr .r5 .r6 4, .dp .orr .r2 .r3 (.reg .r5), .cmp .r2 (.imm 0)]

/-- r4 at `h`'s offset, and Z set iff `h = 0`. -/
def topHalf : List Instr := [.dp .add .r4 .r4 (.imm 4), .cmp .r5 (.imm 0)]

/-- `h = 0`: search `l` instead, 32 more doublings. -/
def lowHalf : List Instr := [.dp .sub .r4 .r4 (.imm 4), .mov .r5 (.reg .r3), .dp .add .r1 .r1 (.imm 32)]

/-- `b := 2^31` in r2, and Z set iff the half's bit `b` is clear. -/
def bitTest : List Instr := [.mov .r2 (.imm 0x80000000), .dp .and .r3 .r5 (.reg .r2), .cmp .r3 (.imm 0)]

/-- `b := b / 2`, one more doubling, and Z set iff the half's bit `b` is clear. -/
def bitStep : List Instr :=
  [.mov .r2 (.shifted .r2 .lsr 1), .dp .add .r1 .r1 (.imm 1), .dp .and .r3 .r5 (.reg .r2), .cmp .r3 (.imm 0)]

/-- `b` the half's top bit, and one doubling more for each bit below `2^31`. -/
def bitFind : Prog isa := .seq (.block bitTest) (.ite .eq (.loop (.block bitStep) .eq) (.block []))

/-- `b` into the zeroed array 4 at the half's offset, and the doublings
`r1 + 1` into header 208. -/
def topStore : List Instr :=
  [.ldr .r6 .r0 96, .dp .add .r6 .r6 (.reg .r4), .str .r2 .r6 0, .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 208]

/-- From a top word not zero: `x` and the count from its top bit. -/
def topInit : Prog isa :=
  .seq (.block topHalf) (.seq (.ite .eq (.block lowHalf) (.block [])) (.seq bitFind (.block topStore)))

/-- Array 4 zeroed, array 7 `:= 2`, then `x` and the count from the top
word, or `r2Init`'s if it is zero. -/
def r2PublicInit : Prog isa :=
  .seq (smallConst 4 0) (.seq (smallConst 7 2) (.seq (.block topPointers)
    (.seq (.block topWord) (.ite .eq r2Init topInit))))

def r2Public : Prog isa := .seq r2PublicInit (.seq doubleLoop r2Squares)

end VG.Impl.Bignum.Arm
