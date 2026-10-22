module

public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr32

/-!
# SM4's counter mode with GCM's `inc₃₂`, bitsliced, on x86-64

`ctr32(schedule = rdi, counter = rsi, data = rdx, n = rcx, scratch = r8)`:
`vg_sm4_ctr32`, the modes' counter mode with `inc₃₂`
(`Impl/Modes/X86_64/Ctr32.lean`) over SM4's core, `modeCore`, as
`vg_sm4_ctr` (`Ctr.lean`) is their CTR over it.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64

open VG.X86_64

/-- `vg_sm4_ctr32`. -/
def ctr32 : Prog isa := modeCore.ctr32 ⟨.rsi, .rdx, .rcx, .r8⟩

end VG.Impl.Sm4.X86_64
