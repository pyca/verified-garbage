module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.Arm

/-! # ECDH over brainpoolP320r1 on 32-bit ARM: five-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_brainpoolp320r1`, or with `u` `vg_ecdh_brainpoolp320r1_umaal`. -/
def exchangeBrainpoolP320r1With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.brainpoolp320r1With u)

/-- `vg_ecdh_brainpoolp320r1`. -/
def exchangeBrainpoolP320r1 : Prog isa := exchangeBrainpoolP320r1With false

/-- `vg_ecdh_brainpoolp320r1_umaal`. -/
def exchangeBrainpoolP320r1U : Prog isa := exchangeBrainpoolP320r1With true

end VG.Impl.Ecdh.Arm
