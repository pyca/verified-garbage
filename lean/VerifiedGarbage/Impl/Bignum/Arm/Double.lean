module

public import VerifiedGarbage.Impl.Bignum.Arm.MontInit
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Impl.Bignum.Arm.MontFinish

/-! # Modular doubling for RSA precomputation

The scalar array begins with 2. One scalar multiply into a zero accumulator,
followed by conditional subtraction, computes twice the operand modulo m.
The same metadata layout is used as by Montgomery multiplication.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def doubleProduct : Prog isa := .seq productStage (.block [.dp .add .r0 .r0 (.imm 16)])
def doubleCore : Prog isa := .seq doubleProduct montFinish
def doubleBody : Prog isa := .seq montInit doubleCore

end VG.Impl.Bignum.Arm
