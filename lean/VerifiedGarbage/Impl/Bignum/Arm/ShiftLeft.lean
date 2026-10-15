module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # In-place one-bit left shift with a materialized carry

The carry lives in `r11`, so decrementing the public loop counter cannot
clobber it. This is the shift used by fixed-iteration RSA key division.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def shiftLeftStep : List Instr :=
  [.ldr .r3 .r0 0, .mov .r4 (.shifted .r3 .lsr 31),
   .dp .add .r3 .r3 (.reg .r3), .dp .add .r3 .r3 (.reg .r11),
   .mov .r11 (.reg .r4), .str .r3 .r0 0,
   .dp .add .r0 .r0 (.imm 4), .subs .lr .lr (.imm 1)]

/-- Shift `lr` native words at `r0` left by one bit, inserting `r11` (0 or
1) at the bottom and returning the top bit in `r11`. The count is public
and nonzero; the words and carry may be secret. -/
def shiftLeft : Prog isa := .loop (.block shiftLeftStep) .ne

end VG.Impl.Bignum.Arm
