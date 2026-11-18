module

public import VerifiedGarbage.Impl.Sm4.X86.Modes

/-! # SM4-CTR on baseline x86 -/

@[expose] public section

namespace VG.Impl.Sm4.X86

/-- CTR with full 128-bit big-endian counter increments, the counter blocks
in groups of `levels`, then one at a time (`Impl/Modes/X86/Wide.lean`). -/
def ctr : Prog VG.X86.isa := (dirCore .encrypt).seqLevels Modes.Mode.ctrWide levels Modes.Mode.ctrEarly

end VG.Impl.Sm4.X86
