module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Save the active CRT workspace for arithmetic helpers -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def activateWorkspace : List Instr := [.addSp .r12 0, .str .r0 .r12 0]

end VG.Impl.Bignum.Arm
