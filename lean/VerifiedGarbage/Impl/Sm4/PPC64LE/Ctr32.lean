module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.Ctr32

/-!
# SM4's counter mode with GCM's `inc₃₂` on PPC64LE

`ctr32` (schedule = r3, counter = r4, data = r5, n = r6, scratch = r7): the
generic `Mode.ctr32` of `Impl/Modes/PPC64LE/Seq.lean` over SM4's core in the
encryption direction (`Modes.lean`), one block at a time.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE

/-- `vg_sm4_ctr32`, with its scratch buffer as the fifth argument. -/
def ctr32 : Prog isa := (dirCore .encrypt).seq Modes.Mode.ctr32

end VG.Impl.Sm4.PPC64LE
