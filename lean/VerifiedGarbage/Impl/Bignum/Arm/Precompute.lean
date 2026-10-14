module

public import VerifiedGarbage.Impl.Bignum.Arm.LoadBEFn
public import VerifiedGarbage.Impl.Bignum.Arm.InitInverse
public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # RSA modulus precomputation in an initialized workspace

r0 is the workspace, r4 the modulus byte pointer, and r6 its byte count.
The outer frame saves the workspace base at stack offset zero.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def importModulus : Prog isa := .seq (.block [.mov .r2 (.imm 0)]) loadBEFn
def inverseArgs : List Instr := [.mov .r12 (.reg .r0), .ldr .r0 .r0 64]
def precomputeInverse : Prog isa := .seq (.block inverseArgs) initInverse
def precompute : Prog isa := .seq importModulus (.seq precomputeInverse r2)

end VG.Impl.Bignum.Arm
