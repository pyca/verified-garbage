module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Indirect calls (X86): the instructions that stand for them

The model has no indirect calls on this target (`ISA.fnAt` holds no
function), so no run calls a function indirectly, and no instructions stand
for one (`instrs`). -/

@[expose] public section

namespace VG.X86

instance : IcallInstrs Instr := ⟨[]⟩

@[simp] theorem icallInstrs_eq : (icallInstrs : List Instr) = [] := rfl

end VG.X86
