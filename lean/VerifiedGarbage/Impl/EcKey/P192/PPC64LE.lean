module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE

/-! # P-192 public keys on PPC64LE: three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p192_public_key`. -/
def publicKeyP192 : Prog isa := Cfg.publicKey Impl.Ecdsa.PPC64LE.p192

end VG.Impl.EcKey.PPC64LE
