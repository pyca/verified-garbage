import VerifiedGarbage.Impl.EcKey.X86
import VerifiedGarbage.Impl.Ecdsa.P384.X86

/-! # P-384 public keys on x86 (32-bit): six-word field elements and scalars -/

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p384_public_key`. -/
def publicKeyP384 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.p384

end VG.Impl.EcKey.X86
