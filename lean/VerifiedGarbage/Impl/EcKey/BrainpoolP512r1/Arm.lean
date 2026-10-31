module

public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm

/-! # brainpoolP512r1 public keys on 32-bit ARM: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_brainpoolp512r1_public_key`, or with `u` `vg_ec_brainpoolp512r1_public_key_umaal`. -/
def publicKeyBrainpoolP512r1With (u : Bool) : Prog isa := Cfg.publicKey (Impl.Ecdsa.Arm.brainpoolp512r1With u)

/-- `vg_ec_brainpoolp512r1_public_key`. -/
def publicKeyBrainpoolP512r1 : Prog isa := publicKeyBrainpoolP512r1With false

/-- `vg_ec_brainpoolp512r1_public_key_umaal`. -/
def publicKeyBrainpoolP512r1U : Prog isa := publicKeyBrainpoolP512r1With true

end VG.Impl.EcKey.Arm
