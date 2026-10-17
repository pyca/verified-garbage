module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn

/-! # Fixed-index Montgomery operations inside an RSA stack frame -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def montOpArgs (o a b : Nat) : List Instr :=
  [.mov .r2 (.imm o), .mov .r3 (.imm a), .mov .r12 (.imm b)]

def montOp (o a b : Nat) : Prog isa :=
  .seq (.block (montOpArgs o a b)) (.seq MontFn.body (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
