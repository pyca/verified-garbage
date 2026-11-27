module

public import VerifiedGarbage.Impl.Camellia.Arm.Cbc
public import VerifiedGarbage.Impl.Modes.Arm.Wide

@[expose] public section

namespace VG.Impl.Camellia.Arm

/-- Camellia-CTR using the verified encryption core: the counter blocks of a
group of 8, 4 or 2 blocks at a time, then of the blocks left one at a time
(`Impl/Modes/Arm/Wide.lean`). -/
def ctr : Prog Arm.isa := (ecbCore .encrypt).seq8 Modes.Arm.ctr Modes.Arm.ctrW

end VG.Impl.Camellia.Arm
