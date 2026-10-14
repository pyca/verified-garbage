module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Initialize a runtime-length packed-word accumulator -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def zeroStep : List Instr :=
  [.str .r3 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .lr .lr (.imm 1)]

/-- Clear `lr` words at `r0`. The nonzero count and pointer are public;
`r3` holds zero and is preserved. -/
def zero : Prog isa := .loop (.block zeroStep) .ne

end VG.Impl.Bignum.Arm
