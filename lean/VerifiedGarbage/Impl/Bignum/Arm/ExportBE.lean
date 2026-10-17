module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Impl.Bignum.Arm.ReverseBytes

/-! # Export a shared RSA array as a fixed-width big-endian integer -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- r0 workspace, r2 array index, r4 destination, r6 byte count. -/
def exportBETail : List Instr :=
  [.mov .r5 (.reg .r0), .mov .lr (.reg .r6), .dp .add .r1 .r1 (.reg .r6),
   .dp .sub .r1 .r1 (.imm 1), .mov .r0 (.reg .r4)]
def exportBEArgs : List Instr := MontFn.loadArray .r1 .r2 ++ exportBETail
def exportBE : Prog isa :=
  .seq (.block exportBEArgs) (.seq reverseBytes (.block [.mov .r0 (.reg .r5)]))

end VG.Impl.Bignum.Arm
