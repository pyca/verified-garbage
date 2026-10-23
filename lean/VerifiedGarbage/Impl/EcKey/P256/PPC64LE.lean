module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE

/-! # P-256 public keys on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p256_public_key`. -/
def publicKeyP256 : Prog isa := Cfg.publicKey Impl.Ecdsa.PPC64LE.p256

end VG.Impl.EcKey.PPC64LE
