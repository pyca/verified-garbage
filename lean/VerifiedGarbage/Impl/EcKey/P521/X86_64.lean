import VerifiedGarbage.Impl.EcKey.X86_64
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64

/-! # P-521 public keys on x86-64: nine-word field elements and scalars -/

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

/-- `vg_ec_p521_public_key`. -/
def publicKeyP521 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p521

end VG.Impl.EcKey.X86_64
