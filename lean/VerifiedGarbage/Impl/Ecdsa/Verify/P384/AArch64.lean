module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PubNaf
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.P384.EcdhAllocatedCode

/-! # ECDSA verification over P-384 on AArch64: six-word field elements and scalars

`[u]G` by the comb and `[v]Q` by the public width-five NAF (`Cfg.pubNafVerify`),
its doublings the register-allocated ones of ECDH's window
(`Impl/P384/EcdhDouble.lean`), which has the same slots. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa :=
  Cfg.pubNafVerify Impl.Ecdsa.AArch64.p384 (some (.block Impl.P384.EcdhAllocatedCode.doubleRD))

end VG.Impl.Ecdsa.Verify.AArch64
