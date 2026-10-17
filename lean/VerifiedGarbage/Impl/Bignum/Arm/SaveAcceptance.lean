module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Save the secret input-comparison bit in the caller-clobbered frame slot -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def saveAcceptance : List Instr := [.addSp .r12 48, .str .r11 .r12 0]

end VG.Impl.Bignum.Arm
