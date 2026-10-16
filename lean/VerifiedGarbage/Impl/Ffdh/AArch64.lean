module

public import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section

namespace VG.Impl.Ffdh.AArch64
open VG.AArch64

/-- Select a word using the low bit, without memory accesses or branches. -/
def choose : Prog isa := .block [
  .movz .x .x3 1 0,
  .tst .x .x2 .x3,
  .cselc .x .x0 .x0 .x1 .eq]

end VG.Impl.Ffdh.AArch64
