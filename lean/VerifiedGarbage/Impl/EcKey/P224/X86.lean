import VerifiedGarbage.Impl.EcKey.X86
import VerifiedGarbage.Impl.Ecdsa.P224.X86

/-! # P-224 public keys on x86 (32-bit): four-word field elements and scalars -/

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p224_public_key`. -/
def publicKeyP224 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.p224

end VG.Impl.EcKey.X86
