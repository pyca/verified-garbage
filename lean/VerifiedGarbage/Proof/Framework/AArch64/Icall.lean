module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Indirect calls (AArch64): the instructions that stand for them

The model has no indirect calls on this target (`ISA.fnAt` holds no
function), so no run calls a function indirectly, and no instructions stand
for one (`instrs`). -/

@[expose] public section

namespace VG.AArch64

instance : IcallInstrs Instr := ⟨[]⟩

@[simp] theorem icallInstrs_eq : (icallInstrs : List Instr) = [] := rfl

end VG.AArch64
