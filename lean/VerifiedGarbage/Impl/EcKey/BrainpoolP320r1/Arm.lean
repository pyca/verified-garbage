module

public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.Arm

/-! # brainpoolP320r1 public keys on 32-bit ARM: five-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_brainpoolp320r1_public_key`. -/
def publicKeyBrainpoolP320r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.brainpoolp320r1

end VG.Impl.EcKey.Arm
