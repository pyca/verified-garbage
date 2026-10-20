module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian

/-! # ECDSA verification over P-256 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa := Cfg.nafVerify Impl.Ecdsa.AArch64.p256

end VG.Impl.Ecdsa.Verify.AArch64
