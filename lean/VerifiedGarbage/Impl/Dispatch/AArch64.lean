module

public import VerifiedGarbage.Impl.Dispatch
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Choosing code by a public selector on AArch64

`chain t r cases` is `Dispatch.chain` with the selector in the register `r`:
each test is `sub t, r, #k` (an immediate: for keys below 4096) into the
scratch register `t`, and a case runs if `t` is zero (`cbz`). Only `t`
changes: the code of a case starts with every other register, the flags and
the memory as before.
-/

@[expose] public section

namespace VG.Impl.Dispatch.AArch64

open VG.AArch64

/-- `sub t, r, #k`. -/
def test (t r : Reg) (k : Nat) : List Instr := [.subImm .x t r k]

/-- The case of `cases` whose key is in `r`, with `t` the scratch register. -/
def chain (t r : Reg) (cases : List (Nat × Prog isa)) : Prog isa :=
  Dispatch.chain (test t r) (.zero .x t) cases

end VG.Impl.Dispatch.AArch64
