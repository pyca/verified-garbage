module

public import VerifiedGarbage.Impl.Camellia.Arm.Cbc
public import VerifiedGarbage.Impl.Modes.Arm.Ctr

@[expose] public section

namespace VG.Impl.Camellia.Arm

/-- Camellia-CTR using the verified encryption core, one counter block at a time. -/
def ctr : Prog Arm.isa := (ecbCore .encrypt).seq Modes.Arm.ctr

end VG.Impl.Camellia.Arm
