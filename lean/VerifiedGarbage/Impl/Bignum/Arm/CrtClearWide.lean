module

public import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # Clear an extended CRT product or comparison buffer

The buffer pointer is in the chosen header slot. The shared limb count
at offset 48 determines the full product's 4*w+2 native words.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def clearWideArgs (slot : Nat) : List Instr :=
  [.ldr .lr .r0 48, .mov .lr (.shifted .lr .lsl 2), .dp .add .lr .lr (.imm 2),
   .mov .r3 (.imm 0), .ldr .r0 .r0 slot]
def clearWide (slot : Nat) : Prog isa :=
  .seq (.block (clearWideArgs slot)) (.seq zero (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm.Crt
