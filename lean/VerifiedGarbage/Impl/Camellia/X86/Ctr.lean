module

public import VerifiedGarbage.Impl.Camellia.X86.Modes

@[expose] public section

namespace VG.Impl.Camellia.X86

/-- Camellia-CTR using the verified encryption core, the counter blocks in
groups of `levels`, then one at a time (`Impl/Modes/X86/Wide.lean`). -/
def ctr : Prog X86.isa := (dirCore .encrypt).seqLevels Modes.Mode.ctrWide levels Modes.Mode.ctrEarly

end VG.Impl.Camellia.X86
