module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64

/-! # ECDSA verification over P-384 on AArch64: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := Cfg.verify Impl.Ecdsa.AArch64.p384

end VG.Impl.Ecdsa.Verify.AArch64
