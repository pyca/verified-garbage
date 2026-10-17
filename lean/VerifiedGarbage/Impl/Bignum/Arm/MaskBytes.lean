module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Branchless byte masking for rejected RSA inputs

The pointer and nonzero length are public. The mask in r2 may be secret.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def maskByteStep : List Instr :=
  [.ldrb .r1 .r0 0, .dp .and .r1 .r1 (.reg .r2), .strb .r1 .r0 0,
   .dp .add .r0 .r0 (.imm 1), .subs .lr .lr (.imm 1)]

def maskBytes : Prog isa := .loop (.block maskByteStep) .ne

end VG.Impl.Bignum.Arm
