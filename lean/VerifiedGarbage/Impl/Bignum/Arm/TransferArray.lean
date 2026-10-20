module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray

/-! # Copy an array between disjoint RSA workspaces

The destination workspace is in r0 and the source workspace in r1.
The destination workspace remains the saved base on the stack.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def transferArrayArgs (o a : Nat) : List Instr :=
  [.ldr .r4 .r0 (64 + 8 * o), .mov .r0 (.reg .r1), .mov .r2 (.imm (BitVec.ofNat 32 a))]
def transferArray (o a : Nat) : Prog isa :=
  .seq (.block (transferArrayArgs o a)) (.seq exportArray (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
