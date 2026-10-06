import VerifiedGarbage.Impl.EcKey.AArch64
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64

/-! # P-224 public keys on AArch64: four-word field elements and scalars -/

namespace VG.Impl.EcKey.AArch64

open VG.AArch64

/-- `vg_ec_p224_public_key`. -/
def publicKeyP224 : Prog isa := Cfg.publicKey Impl.Ecdsa.AArch64.p224

end VG.Impl.EcKey.AArch64
