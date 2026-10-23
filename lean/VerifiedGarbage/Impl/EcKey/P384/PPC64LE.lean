module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE

/-! # P-384 public keys on PPC64LE: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p384_public_key`. -/
def publicKeyP384 : Prog isa := Cfg.publicKey Impl.Ecdsa.PPC64LE.p384

end VG.Impl.EcKey.PPC64LE
