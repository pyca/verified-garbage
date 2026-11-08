module

public import VerifiedGarbage.TCB.AArch64.Isa

/-! Entering and leaving data independent timing (PSTATE.DIT) on AArch64. -/

@[expose] public section

namespace VG.Impl.Dit.AArch64
open VG.AArch64

/-- PSTATE.DIT into bit 24 of `x0`, down to bit 0; then, only if it was off,
on, followed by the barriers `bars` (a write of PSTATE.DIT costs tens of
nanoseconds on Apple's cores, a read little). -/
def enterWith (bars : List Barrier) : Prog isa :=
  .seq (.block [.mrsDit .x0, .lsr .x .x0 .x0 24])
    (.ite (.zero .x .x0) (.block (.msrDitImm true :: bars.map .barrier)) (.block []))

/-- `vg_dit_enter`: `enterWith` no barrier, as Arm specifies a write of a
PSTATE field to take effect for the instructions after it. -/
def enter : Prog isa := enterWith []

/-- `vg_dit_enter_dsb`: with DSB SY and ISB after turning the mode on, the
speculation barrier Apple asks for on its cores, where FEAT_SB is missing
(as Apple's corecrypto, `cc_timing_safe.c`). -/
def enterDsb : Prog isa := enterWith [.dsbSy, .isb]

/-- `vg_dit_enter_sb`: with SB (FEAT_SB) after turning the mode on, the
speculation barrier Apple's documentation asks for. -/
def enterSb : Prog isa := enterWith [.sb]

/-- `vg_dit_clear`: PSTATE.DIT off. -/
def clear : Prog isa := .block [.msrDitImm false]

end VG.Impl.Dit.AArch64
