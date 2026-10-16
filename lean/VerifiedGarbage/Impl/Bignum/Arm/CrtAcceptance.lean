module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Pass the accumulated secret validity bit into a factor workspace -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def installAcceptance : List Instr := [.addSp .r12 48, .ldr .r11 .r12 0, .str .r11 .r0 212]

end VG.Impl.Bignum.Arm.Crt
