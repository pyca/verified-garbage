module

public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
public import VerifiedGarbage.Impl.Bignum.Arm.SubModBuffers

/-! # Branchless modular subtraction of workspace operands -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def subModArrayArgs (o a b : Nat) : Prog isa :=
  .seq (.block [.ldr .r9 .r0 64]) (.block (selectArrayArgs o a b))
def subModArray (o a b : Nat) : Prog isa :=
  .seq (clearOperandBuffer (64 + 8 * o))
    (.seq (subModArrayArgs o a b) (.seq subModBuffers (.block [.ldrSp .r0 0])))

end VG.Impl.Bignum.Arm
