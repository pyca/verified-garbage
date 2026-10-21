module

public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp

/-! Fixed-index operations reuse the shared scanning-round implementation. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontPipeline
open VG VG.Arm

def op (round : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block (montOpArgs o a b)) (.seq (fnBody round) (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm.MontPipeline
