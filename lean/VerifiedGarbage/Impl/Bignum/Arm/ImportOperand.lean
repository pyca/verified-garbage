module

public import VerifiedGarbage.Impl.Bignum.Arm.LoadBEFn

/-! # Import an RSA operand into a fixed workspace array -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def importOperand (o : Nat) : Prog isa :=
  .seq (.block [.mov .r2 (.imm (BitVec.ofNat 32 o))]) loadBEFn

end VG.Impl.Bignum.Arm
