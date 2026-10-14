module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86

/-! # secp256k1 public keys on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_secp256k1_public_key`. -/
def publicKeySecp256k1 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.secp256k1

end VG.Impl.EcKey.X86
