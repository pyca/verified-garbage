module

public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64

@[expose] public section

namespace VG.Impl.EcKey.AArch64

/-- secp256k1 public-key derivation by the complete ladder. -/
def publicKeySecp256k1 : Prog VG.AArch64.isa :=
  Cfg.publicKeyWith Ecdsa.AArch64.secp256k1 Ecdsa.AArch64.Secp256k1.gMul

end VG.Impl.EcKey.AArch64
