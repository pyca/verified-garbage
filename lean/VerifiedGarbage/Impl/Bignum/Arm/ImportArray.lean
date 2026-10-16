module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray

/-! # Import packed little-endian RSA words into an initialized array

r0 is the workspace, r2 the array index, and r4 the source pointer.
The byte count comes from the public workspace width. The array's two
extension words are unchanged; arithmetic helpers initialize them when needed.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def importArraySwap : List Instr :=
  [.mov .r2 (.reg .r0), .mov .r0 (.reg .r1), .mov .r1 (.reg .r2)]
def importArray : Prog isa := .seq (.block exportArrayArgs)
  (.seq (.block importArraySwap) (.seq copyBytes (.block [.mov .r0 (.reg .r5)])))

end VG.Impl.Bignum.Arm
