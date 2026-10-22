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
difference in `r3` and the outgoing borrow in `r11`. The two subtraction
carry bits cannot both be zero for a one-bit incoming borrow, so their sum
is one or two. Adding one and XORing with three gives the outgoing borrow. -/
def subBorrow : List Instr :=
  [.subs .r3 .r1 (.reg .r2), .mov .r4 (.imm 1), .adc .r4 .r4 (.imm 0),
   .subs .r3 .r3 (.reg .r11), .adc .r4 .r4 (.imm 0), .dp .eor .r11 .r4 (.imm 3)]

end VG.Impl.Bignum.Arm
