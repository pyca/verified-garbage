module

public import VerifiedGarbage.Impl.Bignum.Arm.SubRow

/-! # Compare arbitrary RSA operands using a disjoint temporary array -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def arrayCompareArgs (a b : Nat) : List Instr :=
  [.ldr .r10 .r0 (64 + 8 * a), .ldr .r12 .r0 (64 + 8 * b), .ldr .lr .r0 48,
   .dp .add .lr .lr (.reg .lr), .ldr .r0 .r0 88, .mov .r11 (.imm 0)]
def arrayCompare (a b : Nat) : Prog isa :=
  .seq (.block (arrayCompareArgs a b)) (.seq subRow (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
