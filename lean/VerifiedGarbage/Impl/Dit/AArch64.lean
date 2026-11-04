module

public import VerifiedGarbage.TCB.AArch64.Isa

/-! Entering and leaving data independent timing (PSTATE.DIT) on AArch64. -/

@[expose] public section

namespace VG.Impl.Dit.AArch64
open VG.AArch64

/-- `vg_dit_enter`: PSTATE.DIT into bit 24 of `x0`, down to bit 0, then on. -/
def enter : Prog isa := .block [.mrsDit .x0, .lsr .x .x0 .x0 24, .msrDitImm true]

/-- `vg_dit_clear`: PSTATE.DIT off. -/
def clear : Prog isa := .block [.msrDitImm false]

end VG.Impl.Dit.AArch64
