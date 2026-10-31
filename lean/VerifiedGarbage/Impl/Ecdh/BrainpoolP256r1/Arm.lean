module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.Arm

/-! # ECDH over brainpoolP256r1 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_brainpoolp256r1`, or with `u` `vg_ecdh_brainpoolp256r1_umaal`. -/
def exchangeBrainpoolP256r1With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.brainpoolp256r1With u)

/-- `vg_ecdh_brainpoolp256r1`. -/
def exchangeBrainpoolP256r1 : Prog isa := exchangeBrainpoolP256r1With false

/-- `vg_ecdh_brainpoolp256r1_umaal`. -/
def exchangeBrainpoolP256r1U : Prog isa := exchangeBrainpoolP256r1With true

end VG.Impl.Ecdh.Arm
