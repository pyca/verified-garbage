module

public import VerifiedGarbage.Impl.Ct.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Ct on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Ct/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Ct.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

/-- `eq`, then `x4`, `x6` and `x7` cleared. -/
def eq : Prog isa := withClears [.x4, .x6, .x7] [] none Impl.Ct.AArch64.eq

end VG.Impl.Ct.AArch64.Fn
