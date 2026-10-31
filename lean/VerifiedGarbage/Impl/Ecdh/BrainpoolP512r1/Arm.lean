module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm

/-! # ECDH over brainpoolP512r1 on 32-bit ARM: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_brainpoolp512r1`, or with `u` `vg_ecdh_brainpoolp512r1_umaal`. -/
def exchangeBrainpoolP512r1With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.brainpoolp512r1With u)

/-- `vg_ecdh_brainpoolp512r1`. -/
def exchangeBrainpoolP512r1 : Prog isa := exchangeBrainpoolP512r1With false

/-- `vg_ecdh_brainpoolp512r1_umaal`. -/
def exchangeBrainpoolP512r1U : Prog isa := exchangeBrainpoolP512r1With true

end VG.Impl.Ecdh.Arm
