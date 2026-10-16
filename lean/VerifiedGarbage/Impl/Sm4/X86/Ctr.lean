module

public import VerifiedGarbage.Impl.Sm4.X86.Modes
public import VerifiedGarbage.Impl.Modes.Ctr

/-! # SM4-CTR on baseline x86 -/

@[expose] public section

namespace VG.Impl.Sm4.X86

/-- CTR with full 128-bit big-endian counter increments. -/
def ctr : Prog VG.X86.isa := (dirCore .encrypt).seq Modes.Mode.ctr

end VG.Impl.Sm4.X86
