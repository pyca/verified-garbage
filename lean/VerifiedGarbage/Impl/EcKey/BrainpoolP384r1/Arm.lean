module

public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.Arm

/-! # brainpoolP384r1 public keys on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_brainpoolp384r1_public_key`. -/
def publicKeyBrainpoolP384r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.brainpoolp384r1

end VG.Impl.EcKey.Arm
