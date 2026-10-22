module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! The scan's loop condition depends only on candidate pointers. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem trial_advance {s : State} {endSlot : Nat} {last : BitVec 32}
    (read : readSrc s (.mem (at_ .esp endSlot)) = some last) :
    WP isa (.block (trialAdvance endSlot)) s fun t =>
      t.gpr .ebp = s.gpr .ebp + 4 ∧
      t.zf = some (s.gpr .ebp + 4 - last == 0) ∧
      t.mem = s.mem ∧ Keeps [.ebp, .edx] s t := by
  unfold trialAdvance
  refine wp_addS rfl fun u U _ => ?_
  have read' : readSrc u (.mem (at_ .esp endSlot)) = some last := by
    have eq : readSrc u (.mem (at_ .esp endSlot)) = readSrc s (.mem (at_ .esp endSlot)) := by
      show u.load32 (u.ea (at_ .esp endSlot)) = s.load32 (s.ea (at_ .esp endSlot))
      simp only [State.load32, State.ea, at_, U.other .esp (by decide), U.mem, U.rd, U.wr]
      rfl
    exact eq.trans read
  refine wp_movS read' fun v V _ => wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, ?_, T.mem.trans (V.mem.trans U.mem),
    ((U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))).trans (T.keeps _)⟩
  · rw [congrFun T.gpr .ebp, V.other .ebp (by decide), U.gpr]
  · rw [Z, V.other .ebp (by decide), U.gpr, V.gpr]

end VG.Proof.Dsa.X86.Generation
