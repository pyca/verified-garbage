module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Fixed-offset workspace loop controls -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def headerIncrement (d k : Nat) : List Instr :=
  [.ldr .r1 .r0 d, .dp .add .r1 .r1 (.imm k), .str .r1 .r0 d]
def headerDecrement (d : Nat) : List Instr :=
  [.ldr .r1 .r0 d, .subs .r1 .r1 (.imm 1), .str .r1 .r0 d]

end VG.Impl.Bignum.Arm
