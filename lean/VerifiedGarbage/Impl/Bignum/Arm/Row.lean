module

public import VerifiedGarbage.Impl.Bignum.Arm.RowStep

/-! # Runtime-length packed-word rows for ARMv7 RSA -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Advance the two pointers and decrement the public word count in `lr`.
The final subtraction supplies the loop condition. -/
def rowAdvance : List Instr :=
  [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 4), .subs .lr .lr (.imm 1)]

def rowBody : Prog isa := .seq rowStep (.block rowAdvance)

/-- Add `r1` times `lr` input words at `r12`, plus carry `r11`, into the
same number of accumulator words at `r0`. `lr` must initially be nonzero.
The carry out remains in `r11`; both pointers finish past their arrays. -/
def row : Prog isa := .loop rowBody .ne

end VG.Impl.Bignum.Arm
