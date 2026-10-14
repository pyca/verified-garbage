module

public import VerifiedGarbage.Impl.Sm4.Arm.Cbc
public import VerifiedGarbage.Impl.Modes.Arm.Ctr

/-! # SM4-CTR on baseline ARMv7 -/

@[expose] public section

namespace VG.Impl.Sm4.Arm

/-- CTR calling the verified SM4 ECB primitive on each counter block. -/
def ctr : Prog VG.Arm.isa := (ecbCore .encrypt).seq Modes.Arm.ctr

end VG.Impl.Sm4.Arm
