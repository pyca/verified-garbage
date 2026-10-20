module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameStatus

/-! # Mutable frame slots preserve all persistent parameter-search resources -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem searchSlot_frame {P : SearchContextPlan} {s t : State} {i : Nat}
    (hi : i < 37) (O : Outside P.geometry.frameBase (4 * i) 4 s.mem t.mem) :
    Frame [⟨P.geometry.frameBase, frameBytes⟩] s.mem t.mem := by
  have F : Frame [⟨off P.geometry.frameBase (4 * i), 4⟩] s.mem t.mem := sampleOutside_frame O (by omega)
  exact F.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; omega)⟩)

theorem SearchContext.slot {P : SearchContextPlan} {W : Nat → BitVec 32} {s t : State}
    {i : Nat} {v : BitVec 32} {regs : List Reg} (R : SearchContext P W s)
    (hi : i < 37) (mutable : i ∈ parameterMutableSlots)
    (rep : FrameWords t.mem P.geometry.frameBase (frameUpdate W i v))
    (O : Outside P.geometry.frameBase (4 * i) 4 s.mem t.mem) (K : Keeps regs s t) (sp : .esp ∉ regs) :
    SearchContext P (frameUpdate W i v) t := by
  apply R.frame rep ?_ ((searchSlot_frame hi O).mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [parameterWrites])) K sp
  intro j _ hx
  exact ite_eq_right (by intro h; subst j; exact hx mutable)

theorem searchCandidatePointer_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchContext P W s) (offset : Nat) :
    WP isa (.block (candidatePointer offset)) s fun t =>
      SearchContext P (frameUpdate W 22 (P.geometry.pointer offset)) t ∧
      Frame [⟨P.geometry.frameBase, frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  have parent : W 5 = P.geometry.parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  refine WP.mono (candidatePointer_ok R.arena.frame R.representation offset) fun t ⟨_, rep, O, K⟩ => ?_
  rw [parent] at rep
  exact ⟨R.slot (by decide) (by decide) rep O K (by decide), searchSlot_frame (by decide : 22 < 37) O, K⟩

theorem searchStatus_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchContext P W s) (status : Nat) :
    WP isa (.block (frameStatus status)) s fun t =>
      SearchContext P (frameUpdate W 19 (BitVec.ofNat 32 status)) t ∧
      Frame [⟨P.geometry.frameBase, frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (frameStatus_ok R.arena.frame R.representation status) fun t ⟨_, rep, O, K⟩ => ?_
  exact ⟨R.slot (by decide) (by decide) rep O K (by decide), searchSlot_frame (by decide : 19 < 37) O, K⟩
end VG.Proof.Dsa.X86.Generation
