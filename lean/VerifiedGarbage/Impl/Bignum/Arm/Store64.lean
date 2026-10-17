module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Store a 64-bit register pair through two native ARMv7 stores -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def store64 (lo hi ptr : Reg) (d : Nat) : List Instr := [.str lo ptr d, .str hi ptr (d + 4)]

end VG.Impl.Bignum.Arm
