module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PackedNaf
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64

/-! # ECDSA verification over P-521 on AArch64: nine-word field elements and scalars.

The variable-base multiplication uses public width-five NAF with its table
and cached Z powers packed within the existing scratch space. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := Cfg.packedNafVerify Impl.Ecdsa.AArch64.p521

end VG.Impl.Ecdsa.Verify.AArch64
