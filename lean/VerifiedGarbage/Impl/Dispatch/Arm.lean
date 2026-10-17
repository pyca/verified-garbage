module

public import VerifiedGarbage.Impl.Dispatch
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# Choosing code by a public selector on 32-bit ARM

`chain r cases` is `Dispatch.chain` with the selector in the register `r`:
each test is `cmp r, #k` (an immediate: for keys below 256, which every
rotation encodes), and a case runs if `Z` is set (`beq`). Only the flags
change: the code of a case starts with every register and the memory as
before. A call may change `r12` and the flags (`VG.Arm.call`, a linker
veneer), so `r` is a register the code's calls preserve.
-/

@[expose] public section

namespace VG.Impl.Dispatch.Arm

open VG.Arm

/-- `cmp r, #k`. -/
def test (r : Reg) (k : Nat) : List Instr := [.cmp r (.imm (BitVec.ofNat 32 k))]

/-- The case of `cases` whose key is in `r`. -/
def chain (r : Reg) (cases : List (Nat × Prog isa)) : Prog isa := Dispatch.chain (test r) .eq cases

end VG.Impl.Dispatch.Arm
