module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbHead
import VerifiedGarbage.Proof.Framework.Offset

/-! # CBC encryption's input and output copies -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcFill

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

theorem count_wp (s : State) : WP isa SerialCbc.count s fun s' =>
    s'.gpr .r11 = (1 : BitVec 32) ∧
      (∀ r, r ≠ .r11 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.seq (WP.mono (SerialCfbHead.count_wp s) fun s' h => ?_)
  exact WP.of_runBlock ⟨s', CfbFill.pad_run s', h⟩

structure Post (s : State) (B D : BitVec 32) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B 0, 16⟩] s.mem s'.mem
  block : bytesAt s'.mem (bufferAddr B 0) 16 =
    Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (bytesAt s.mem (counterAddr B) 16)

theorem fill_wp {s : State} {B D : BitVec 32} (h : CfbFill.Pre B D 1 s) :
    WP isa SerialCbc.fill s (Post s B D) := by
  refine WP.seq (WP.mono (CfbFill.first_wp h) fun s₁ f => ?_)
  have hb : s₁.gpr sb = B := (f.regs _ (by decide) (by decide)).trans h.base
  have hd : s₁.gpr .r6 = D := (f.regs _ (by decide) (by decide)).trans h.data
  have xp : NPre 4 s₁ sb .r6 (4 * tailSlot) 0 (bufferAddr B 0) (State.addr D) := by
    refine ⟨by rw [hb]; rfl, by rw [hd]; simp, ?_, ?_, by decide, by decide,
      by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
    · rw [hb]; have := h.fitB; change B.toNat + 256 + 16 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega
    · rw [hd]; simpa using h.fitD
    · rw [f.wr]; exact workspace_part h.hw 256 16 (by decide)
    · rw [f.rd, f.wr]; exact Covers.right h.wd
    · exact h.sep.symm.sub_left (Offset.sub_base _ (by decide))
  refine WP.mono (xorN_wp xp) fun s₂ x => ?_
  have fx : Frame [⟨bufferAddr B 0, 16⟩] s₁.mem s₂.mem := by
    rw [x.mem]; exact Proof.Modes.over_frame _ _ _ _
  refine ⟨fun r h9 h10 => (x.regs r h9 h10).trans (f.regs r h9 h10),
    x.rd.trans f.rd, x.wr.trans f.wr, x.sp.trans f.sp, f.frame.trans fx, ?_⟩
  rw [x.mem, bytesAt_over_self _ _ _ (by decide), xor_bytes, f.block]
  have d : bytesAt s₁.mem (State.addr D) 16 = bytesAt s.mem (State.addr D) 16 := by
    apply bytes_frame f.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact h.sep.sub_right (Offset.sub_base _ (by decide))
  rw [d, xor_comm]

theorem copy_wp {s : State} {B D : BitVec 32} (h : CfbFill.Pre B D 1 s) :
    WP isa (.block SerialCbc.copyOutput) s (CopyPost s (State.addr D) (bufferAddr B 0)) := by
  apply copyBlock_wp
  refine ⟨by rw [h.data]; simp, by rw [h.base]; rfl, ?_, ?_, by decide, by decide,
    by decide, by decide, by decide, by decide, h.wd,
    Covers.right (workspace_part h.hw 256 16 (by decide)), ?_⟩
  · rw [h.data]; simpa using h.fitD
  · rw [h.base]; have := h.fitB; change B.toNat + 256 + 16 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega
  · exact h.sep.sub_right (Offset.sub_base _ (by decide))

end VG.Proof.Sm4.Arm.SerialCbcFill
