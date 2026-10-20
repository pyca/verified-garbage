module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PubNaf
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64

/-! # ECDSA verification over P-384 on AArch64: six-word field elements and scalars

`[u]G` by the comb and `[v]Q` by the public width-five NAF (`Cfg.pubNafVerify`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := Cfg.pubNafVerify Impl.Ecdsa.AArch64.p384

end VG.Impl.Ecdsa.Verify.AArch64
