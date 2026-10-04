import VerifiedGarbage.Impl.EcKey.X86_64
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64

/-! # P-384 public keys on x86-64: six-word field elements and scalars -/

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

/-- `vg_ec_p384_public_key`. -/
def publicKeyP384 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p384

end VG.Impl.EcKey.X86_64
