module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.InitialWords
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.PushedArguments
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions

/-! The native entry code establishes the complete key-search loop invariant. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem KeyInput.pushed_read {p : KeyPublic sampling} {s : State} {r : Region}
    (h : KeyInput p s) (read : r ∈ s.rd) :
    Spec.Rsa.bytesAt (searchPushed s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len := by
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have fit : 232 ≤ s.sp.toNat := by rw [← rootSp]; exact h.bounds.stackFits
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; omega)
  have sep : r.Disjoint (FrameStack.belowA s.sp 24) := by
    apply Region.Disjoint.symm
    apply (h.stack_separate (List.mem_append_right _ read)).sub_left
    rw [rootSp]
    exact FrameStack.belowA_sub (by decide : 24 ≤ stackUse) fit
  apply bytesAt_frame frame (by simpa using sep)
  have nowrap := h.layout.nowrap r (by rw [← h.layout.wr, ← h.layout.rd]; exact List.mem_append_right _ read)
  omega

theorem start_ok {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.entry) (searchPushed s) fun t =>
      KeyLive p s 0 p.keys p.scalars t := by
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have fit : 24 ≤ s.sp.toNat := by rw [← rootSp]; have := h.bounds.stackFits; change 232 ≤ p.sp.toNat at this; omega
  have space : Workspace (searchPushed s) p.control 128 :=
    h.control_space (fun _ hr => List.mem_cons_of_mem _ hr)
  have x : (searchPushed s).gpr .r0 = p.xp := by rw [← h.2.1]; rfl
  have y : (searchPushed s).gpr .r2 = p.yp := by rw [← h.2.1]; rfl
  refine WP.mono_syms (entry_ok (searchPushed s) h.pushed_arguments space x y) ?_
  rintro t ⟨⟨context, mem⟩, rest⟩ syms
  have frame : Frame [rControl p] (searchPushed s).mem t.mem := by
    rw [mem]; exact writeLow_frame _ _ _ (entryValues_bound p)
  have saved : Spill.Saved (searchPushed s).mem (State.addr (p.sp - 24#32)) s.gpr savedSlots := by
    rw [rootSp]; exact push_saved s fit
  refine ⟨h, Nat.zero_le _, h.bounds.keys, h.bounds.scalars, rest.rd, ?_, ?_, context.controller.ptr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr]
    change (⟨State.addr (s.sp - 24#32), 24⟩ :: s.wr) = _
    rw [rootSp]
  · rw [rest.sp]
    change s.sp - 24#32 = p.sp - 24#32
    rw [rootSp]
  · intro r hr
    exact rest.gpr r (by revert r hr; decide)
  · apply saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.saved_control
  · exact (bytesAt_frame (r := rRandom p) frame (by simpa using h.random_control)
      (by change p.randLen ≤ 2 ^ 64; have := h.bounds.randomFits; omega)).trans
        (h.pushed_read (r := rRandom p) (by rw [h.read_regions]; simp))
  · have original : Spec.Rsa.bytesAt s.mem (State.addr p.dp) p.dlen = p.dom := by rw [← h.2.1]; rfl
    exact (bytesAt_frame (r := rDomain p) frame (by simpa using h.domain_control)
      (by change p.dlen ≤ 2 ^ 64; have := h.bounds.domainFit; omega)).trans
        ((h.pushed_read (r := rDomain p) (by rw [h.read_regions]; simp)).trans original)
  · rw [mem]
    exact entry_fields p _ h.pushed_policy.1 h.pushed_policy.2.1 h.pushed_policy.2.2.1
  · intro j hj
    rw [mem, highWord_writeLow _ _ _ (entryValues_bound p) j (by omega)]
    exact h.pushed_policy.2.2.2 j hj

  · have ptrS : KeyConstants.tablePtr sampling s = p.tablePtr := by rw [← h.2.1]; rfl
    cases sampling <;> simpa only [KeyConstants.tablePtr, syms, searchPushed, pushed] using ptrS
  · have ptrS : KeyConstants.tablePtr sampling s = p.tablePtr := by rw [← h.2.1]; rfl
    have heldS := KeyConstants.held_of_consts h.2.2
    rw [ptrS] at heldS
    have pushedFrame : Frame [FrameStack.belowA p.sp 24] s.mem (searchPushed s).mem := by
      rw [rootSp]
      exact FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) fit
    have heldP := KeyConstants.held_after_frame heldS pushedFrame (by
      intro table ht r hr
      have er := List.mem_singleton.mp hr
      subst r
      exact (h.constants_stack table ht).sub_right (FrameStack.belowA_sub (by decide : 24 ≤ stackUse) h.bounds.stackFits))
    exact KeyConstants.held_after_frame heldP frame (by
      intro table ht r hr
      have er := List.mem_singleton.mp hr
      subst r
      exact h.constants_control table ht)

end VG.Proof.Ffdh.Arm.KeySearch
