module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr32

/-!
# SM4's counter mode with GCM's `inc₃₂`, bitsliced, on AArch64

`ctr32(schedule = x0, counter = x1, data = x2, n = x3, scratch = x4)`:
`vg_sm4_ctr32`, the modes' counter mode with `inc₃₂`
(`Impl/Modes/AArch64/Ctr32.lean`) over SM4's core, `modeCore`, as
`vg_sm4_ctr` (`Ctr.lean`) is their CTR over it.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64

/-- `vg_sm4_ctr32`. -/
def ctr32 : Prog isa := modeCore.ctr32 ⟨.x1, .x2, .x3, .x4⟩

end VG.Impl.Sm4.AArch64
