module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Initialize the public exponent pointer and byte count in the workspace -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def expControls : List Instr := [.str .r1 .r0 128, .str .r2 .r0 132]

end VG.Impl.Bignum.Arm
