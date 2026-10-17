module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes

/-! # Export a shared RSA array as packed little-endian words

r0 holds the workspace, r2 the array index, and r4 the output pointer.
The workspace pointer is restored after the copy; r4 is preserved.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def exportArrayTail : List Instr :=
  [.mov .r5 (.reg .r0), .ldr .lr .r0 48, .mov .lr (.shifted .lr .lsl 3), .mov .r0 (.reg .r4)]
def exportArrayArgs : List Instr := MontFn.loadArray .r1 .r2 ++ exportArrayTail
def exportArray : Prog isa := .seq (.block exportArrayArgs)
  (.seq copyBytes (.block [.mov .r0 (.reg .r5)]))

end VG.Impl.Bignum.Arm
