module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.Ctr

/-!
# SM4-CTR on PPC64LE

`ctr` (schedule = r3, ctr = r4, data = r5, n = r6, scratch = r7): the generic
counter mode of `Impl/Modes/PPC64LE/Seq.lean` over SM4's core in the
encryption direction (`Modes.lean`), one block at a time.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE

/-- `vg_sm4_ctr`, with its scratch buffer as the fifth argument. -/
def ctr : Prog isa := (dirCore .encrypt).seq Modes.Mode.ctr

end VG.Impl.Sm4.PPC64LE
