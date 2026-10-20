module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! A nested key-generation attempt changes its outputs, workspace and its
own stack, preserving the retry policy and saved controller frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

namespace KeyInput
variable {p : KeyPublic} {s : State}

theorem call_control (h : KeyInput p s) : ∀ r ∈ callChanges p, (rControl p).Disjoint r := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  have sep := h.output_regions_disjoint
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact sep.2.2.2.1
  · exact sep.2.2.2.2.1
  · exact sep.2.2.2.2.2
  · apply Region.Disjoint.symm
    apply (h.stack_separate (r := rControl p) (by rw [h.write_regions]; simp)).sub_left
    exact arguments_sub h.bounds.stackFits
  · apply Region.Disjoint.symm
    apply (h.stack_separate (r := rControl p) (by rw [h.write_regions]; simp)).sub_left
    exact callStack_sub h.bounds.stackFits

theorem call_read (h : KeyInput p s) {r : Region} (read : r ∈ s.rd) :
    ∀ w ∈ callChanges p, r.Disjoint w := by
  intro w hw
  have sep (q : Region) (hq : q ∈ s.wr) : r.Disjoint q := by
    apply Region.Disjoint.symm
    apply h.layout.separate q (by rw [← h.layout.wr]; exact hq) r
    rw [← h.layout.rd]; exact read
  have saved := h.stack_separate (List.mem_append_right s.wr read)
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact (saved.sub_left (arguments_sub h.bounds.stackFits)).symm
  · exact (saved.sub_left (callStack_sub h.bounds.stackFits)).symm

theorem call_saved (h : KeyInput p s) : ∀ r ∈ callChanges p, (rSaved p).Disjoint r := by
  intro r hr
  have below : (rSaved p).Sub (FrameStack.belowA p.sp stackUse) :=
    FrameStack.belowA_sub (by decide : 24 ≤ stackUse) h.bounds.stackFits
  have sep (q : Region) (hq : q ∈ s.wr) : (rSaved p).Disjoint q :=
    (h.stack_separate (List.mem_append_left _ hq)).sub_left below
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact saved_arguments_separate h.bounds.stackFits
  · exact saved_callStack_separate h.bounds.stackFits

theorem call_domain_frame (h : KeyInput p s) {m m' : Mem} (frame : Frame (callChanges p) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.dp) p.dlen = Spec.Rsa.bytesAt m (State.addr p.dp) p.dlen :=
  bytesAt_frame (r := rDomain p) frame (h.call_read (by rw [h.read_regions]; simp))
    (by change p.dlen ≤ 2 ^ 64; have := h.bounds.domainFit; omega)

theorem call_random_frame (h : KeyInput p s) {m m' : Mem} (frame : Frame (callChanges p) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.rp) p.randLen = Spec.Rsa.bytesAt m (State.addr p.rp) p.randLen :=
  bytesAt_frame (r := rRandom p) frame (h.call_read (by rw [h.read_regions]; simp))
    (by change p.randLen ≤ 2 ^ 64; have := h.bounds.randomFits; omega)

end KeyInput

theorem KeyLive.restore {p : KeyPublic} {original s t : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (kept : ∀ r ∈ keptRegisters, t.gpr r = s.gpr r)
    (frame : Frame (callChanges p) s.mem t.mem) : KeyLive p original used keys scalars t := by
  refine ⟨h.input, h.used_le, h.keys_le, h.scalars_le, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    (kept .r4 (by decide)).trans h.pointer,
    fun r hr => (kept r (List.mem_cons_of_mem _ hr)).trans (h.kept r hr),
    ?_, (h.input.call_random_frame frame).trans h.random,
    (h.input.call_domain_frame frame).trans h.domain, ?_, ?_⟩
  · apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.input.call_saved
  · intro e he
    have index : e.1 < 16 := by
      simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only; decide
    exact (frame.readW (r := rControl p) (Offset.contains_base _ (by omega) (by omega))
      h.input.call_control (by decide)).trans (h.headers e he)
  · intro j hj
    exact (frame.readW (r := rControl p) (Offset.contains_base _ (by omega) (by omega))
      h.input.call_control (by decide)).trans (h.high j hj)

end VG.Proof.Ffdh.Arm.KeySearch
