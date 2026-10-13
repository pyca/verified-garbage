module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64

/-! # ECDSA verification over P-224 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verify Impl.Ecdsa.AArch64.p224

end VG.Impl.Ecdsa.Verify.AArch64
