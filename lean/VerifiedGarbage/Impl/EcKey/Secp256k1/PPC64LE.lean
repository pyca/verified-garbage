module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE

/-! # secp256k1 public keys on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE

/-- `vg_ec_secp256k1_public_key`. -/
def publicKeySecp256k1 : Prog isa := Cfg.publicKey Impl.Ecdsa.PPC64LE.secp256k1

end VG.Impl.EcKey.PPC64LE
