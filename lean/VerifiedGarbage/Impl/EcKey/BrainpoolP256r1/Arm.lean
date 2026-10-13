module

public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.Arm

/-! # brainpoolP256r1 public keys on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_brainpoolp256r1_public_key`. -/
def publicKeyBrainpoolP256r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.brainpoolp256r1

end VG.Impl.EcKey.Arm
