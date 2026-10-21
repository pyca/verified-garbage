module

public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
public import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.Square

/-! Compile-time selection of the shared Montgomery kernel for primality testing. -/

@[expose] public section
namespace VG.Impl.MillerRabin.Arm.Arithmetic
open VG VG.Arm VG.Impl.Bignum.Arm

def product (fios : Bool) (o a b : Nat) : Prog isa :=
  if fios then
    .seq (.block (montOpArgs o a b))
      (.seq (MontPipeline.fnBody FiosFast.round) (.block [.ldrSp .r0 0]))
  else montOp o a b

def square (fios : Bool) (o a : Nat) : Prog isa :=
  if fios then product true o a a else squareOp o a

end VG.Impl.MillerRabin.Arm.Arithmetic
