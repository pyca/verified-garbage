module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LE

/-! # brainpoolP256r1 public keys on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE

/-- `vg_ec_brainpoolp256r1_public_key`. -/
def publicKeyBrainpoolP256r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.PPC64LE.brainpoolp256r1

end VG.Impl.EcKey.PPC64LE
