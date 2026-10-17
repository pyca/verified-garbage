module

public import VerifiedGarbage.Impl.Dispatch
public import VerifiedGarbage.TCB.X86.Isa

/-!
# Choosing code by a public selector on x86 (32-bit)

`chain r cases` is `Dispatch.chain` with the selector in the register `r`:
each test is `cmp r, k` (an immediate: for keys below `2^31`), and a case
runs if `ZF` is set. Only the flags change: the code of a case starts with
`r` the selector, and every other register and the memory as before. The
register is the caller's choice, since on x86 every other one may hold an
argument of the case's call (e.g. `ebx`, which no call takes).
-/

@[expose] public section

namespace VG.Impl.Dispatch.X86

open VG.X86

/-- `cmp r, k`. -/
def test (r : Reg) (k : Nat) : List Instr := [.alu .cmp r (.imm (BitVec.ofNat 32 k))]

/-- The case of `cases` whose key is in `r`. -/
def chain (r : Reg) (cases : List (Nat × Prog isa)) : Prog isa := Dispatch.chain (test r) .e cases

end VG.Impl.Dispatch.X86
