module

public import VerifiedGarbage.Impl.Camellia.X86.Modes
public import VerifiedGarbage.Impl.Modes.Ctr

@[expose] public section

namespace VG.Impl.Camellia.X86

/-- Camellia-CTR using the verified encryption core, one counter block at a time. -/
def ctr : Prog X86.isa := (dirCore .encrypt).seq Modes.Mode.ctr

end VG.Impl.Camellia.X86
