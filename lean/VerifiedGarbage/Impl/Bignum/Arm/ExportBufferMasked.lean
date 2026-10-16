module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportBE
public import VerifiedGarbage.Impl.Bignum.Arm.MaskOutput

/-! # Serialize a wide result buffer and mask secret rejection

r1 points to the little-endian result, r4 to the output, and r6 holds
its public byte count. Acceptance is saved at stack offset 48.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def exportBuffer : Prog isa := .seq (.block exportBETail) reverseBytes
def exportBufferMasked : Prog isa := .seq exportBuffer maskOutput

end VG.Impl.Bignum.Arm
