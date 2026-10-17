module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Shift a packed-word accumulator down by one word -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def shiftStep : List Instr :=
  [.ldr .r3 .r0 4, .str .r3 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .lr .lr (.imm 1)]

/-- Copy `lr` words from `r0 + 4` down to `r0`, in place. The count is
nonzero and public. The word above the destination range is untouched. -/
def shift : Prog isa := .loop (.block shiftStep) .ne

end VG.Impl.Bignum.Arm
