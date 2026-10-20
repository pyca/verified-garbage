module

public import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # Clear an extended arithmetic operand buffer

The buffer pointer is in the chosen header slot. The shared limb count
at offset 48 determines the operand's 2*w+2 native words.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def clearOperandBufferArgs (slot : Nat) : List Instr :=
  [.ldr .lr .r0 48, .mov .lr (.shifted .lr .lsl 1), .dp .add .lr .lr (.imm 2),
   .mov .r3 (.imm 0), .ldr .r0 .r0 slot]
def clearOperandBuffer (slot : Nat) : Prog isa :=
  .seq (.block (clearOperandBufferArgs slot)) (.seq zero (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
