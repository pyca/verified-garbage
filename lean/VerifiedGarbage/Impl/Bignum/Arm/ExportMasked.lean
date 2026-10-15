module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportBE
public import VerifiedGarbage.Impl.Bignum.Arm.MaskOutput

/-! # Serialize the RSA result and mask rejection without secret-dependent control flow -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def exportMasked : Prog isa := .seq exportBE maskOutput

end VG.Impl.Bignum.Arm
