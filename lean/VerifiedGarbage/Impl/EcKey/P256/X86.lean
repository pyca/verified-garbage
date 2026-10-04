import VerifiedGarbage.Impl.EcKey.X86
import VerifiedGarbage.Impl.Ecdsa.P256.X86

/-! # P-256 public keys on x86 (32-bit): four-word field elements and scalars -/

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p256_public_key`. -/
def publicKeyP256 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.p256

end VG.Impl.EcKey.X86
