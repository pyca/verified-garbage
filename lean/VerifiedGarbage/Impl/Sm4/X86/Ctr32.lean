module

public import VerifiedGarbage.Impl.Sm4.X86.Modes
public import VerifiedGarbage.Impl.Modes.Ctr32

/-! # SM4's counter mode with GCM's `inc₃₂` on baseline x86 -/

@[expose] public section

namespace VG.Impl.Sm4.X86

/-- `vg_sm4_ctr32`: CTR (`Ctr.lean`) with GCM's `inc₃₂` on the counter
block's last 32 bits. -/
def ctr32 : Prog VG.X86.isa := (dirCore .encrypt).seq Modes.Mode.ctr32

end VG.Impl.Sm4.X86
