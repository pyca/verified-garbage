import VerifiedGarbage.Impl.EcKey.X86
import VerifiedGarbage.Impl.Ecdsa.P192.X86

/-! # P-192 public keys on x86 (32-bit): three-word field elements and scalars -/

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p192_public_key`. -/
def publicKeyP192 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.p192

end VG.Impl.EcKey.X86
