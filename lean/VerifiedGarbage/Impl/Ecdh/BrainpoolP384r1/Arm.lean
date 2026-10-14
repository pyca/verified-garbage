module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.Arm

/-! # ECDH over brainpoolP384r1 on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_brainpoolp384r1`. -/
def exchangeBrainpoolP384r1 : Prog isa := Cfg.exchange Impl.Ecdsa.Arm.brainpoolp384r1

end VG.Impl.Ecdh.Arm
