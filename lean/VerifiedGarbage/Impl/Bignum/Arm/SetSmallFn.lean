module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Impl.Bignum.Arm.SetSmall

/-! # Initialize a shared RSA workspace array to a native-word value

r0 is the workspace, r2 the array index, and r5 the value. The outer RSA
frame saves the workspace pointer at stack offset zero.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def setSmallTail : List Instr :=
  [.ldr .lr .r0 48, .dp .add .lr .lr (.reg .lr), .mov .r3 (.imm 0), .mov .r0 (.reg .r4)]
def setSmallArgs : List Instr := MontFn.loadArray .r4 .r2 ++ setSmallTail
def setSmallFnBody : Prog isa := .seq (.block setSmallArgs) setSmall
def setSmallFn : Prog isa := .seq setSmallFnBody (.block [.ldrSp .r0 0])

end VG.Impl.Bignum.Arm
