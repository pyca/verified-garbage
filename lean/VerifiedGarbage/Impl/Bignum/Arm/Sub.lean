module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Packed-word subtraction using the ARMv7 carry flag -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Subtract two words and materialize the borrow as zero or one.
The destination and borrow registers must be distinct. -/
def subWord (d borrow a b : Reg) : List Instr :=
  [.subs d a (.reg b), .mov borrow (.imm 0),
   .adc borrow borrow (.imm 0), .dp .eor borrow borrow (.imm 1)]

/-- Subtract `r2` and incoming borrow `r11` from `r1`, leaving the
difference in `r3` and the outgoing borrow in `r11`. -/
def subBorrow : List Instr :=
  subWord .r3 .r4 .r1 .r2 ++ subWord .r3 .r5 .r3 .r11 ++
    [.dp .add .r11 .r4 (.reg .r5)]

end VG.Impl.Bignum.Arm
