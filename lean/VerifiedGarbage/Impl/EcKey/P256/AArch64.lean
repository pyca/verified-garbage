module

public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64

/-! # P-256 public keys on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.AArch64

open VG.AArch64

/-- `vg_ec_p256_public_key`. -/
def publicKeyP256 : Prog isa := Cfg.publicKey Impl.Ecdsa.AArch64.p256

end VG.Impl.EcKey.AArch64
