module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext

/-! # Trial resources depend only on memory, permissions, and the stack pointer -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86

theorem TrialInputs.keep {s t : State} {base : Addr} {input table : BitVec 32} {len entries : Nat} {regs : List Reg}
    (R : TrialInputs s base input table len entries) (mem : t.mem = s.mem) (K : Keeps regs s t) (sp : .esp ∉ regs) :
    TrialInputs t base input table len entries := by
  exact ⟨R.frame.keeps K sp, R.lenPos, R.lenEven, R.lenBound, R.entriesPos, R.entriesBound,
    R.inputFit, R.tableFit, by intro i hi; rw [K.2.1, K.2.2]; exact R.inputRead i hi,
    by intro d hd; rw [K.2.1, K.2.2]; exact R.tableRead d hd,
    R.inputApart, R.tableApart, by rw [mem]; exact R.values⟩
theorem keeps_allocated {s t : State} {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) (n : Nat) :
    Keeps regs (allocated n s) (allocated n t) := by
  refine ⟨?_, K.2.1, ?_⟩
  · intro r hr
    by_cases eq : r = .esp
    · subst r; rw [allocated_esp, allocated_esp, K.1 _ sp]
    · rw [allocated_gpr _ _ eq, allocated_gpr _ _ eq, K.1 _ hr]
  · rw [allocated_wr, allocated_wr, K.1 _ sp, K.2.2]
end VG.Proof.Dsa.X86.Generation
