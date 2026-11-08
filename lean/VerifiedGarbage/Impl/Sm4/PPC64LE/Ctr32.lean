module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.Wide

/-!
# SM4's counter mode with GCM's `inc₃₂` on PPC64LE

`ctr32` (schedule = r3, counter = r4, data = r5, n = r6, scratch = r7): the
generic counter mode with GCM's `inc₃₂` of `Impl/Modes/PPC64LE/Wide.lean`,
the counter block stepped before the block cipher, over SM4's core in the
encryption direction (`Modes.lean`): sixteen blocks a step while sixteen are
left, then one.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE

/-- `vg_sm4_ctr32`, with its scratch buffer as the fifth argument. -/
def ctr32 : Prog isa := (dirCore .encrypt).seq2 (Modes.Mode.ctr32Wide 16) Modes.Mode.ctr32Early 4

end VG.Impl.Sm4.PPC64LE
