module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Impl.Bignum.Arm.LoadBE

/-! # Import a big-endian integer into a shared RSA workspace array

r0 is the workspace, r2 the array index, r4 the input pointer, and r6 the
input byte count. The outer frame saves the workspace base at stack offset zero.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def loadBEFnTail : List Instr :=
  [.ldr .lr .r0 48, .dp .add .lr .lr (.reg .lr), .mov .r3 (.imm 0), .mov .r0 (.reg .r5)]
def loadBEFnArgs : List Instr := MontFn.loadArray .r5 .r2 ++ loadBEFnTail
def loadBEFnBody : Prog isa := .seq (.block loadBEFnArgs) loadBE
def loadBEFn : Prog isa := .seq loadBEFnBody (.block [.ldrSp .r0 0])

end VG.Impl.Bignum.Arm
