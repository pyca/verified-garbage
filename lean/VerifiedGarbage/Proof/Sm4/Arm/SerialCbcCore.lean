module

import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcFill
import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # Encrypting the CBC input under the prepared round keys -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcCore

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchGroup
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

structure Post (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r6, .r7, .r8, .r11], s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨State.addr B, 4 * slots⟩] s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  block : bytesAt s'.mem (bufferAddr B 0) 16 =
    Spec.Sm4.cipher K (Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (bytesAt s.mem (counterAddr B) 16))

theorem core_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule}
    (h : CfbFill.Pre B D 1 s) (ht : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa SerialCbc.core s (Post s B D K) := by
  refine WP.seq (WP.mono (SerialCbcFill.fill_wp h) fun s₁ f => ?_)
  have hb : s₁.gpr sb = B := (f.regs _ (by decide) (by decide)).trans h.base
  have ht₁ := table_frame ht f.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  have hw₁ : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f.wr]
    simpa only [BitVec.add_zero] using workspace_part h.hw 0 (4 * slots) (by decide)
  refine WP.mono (BatchCalls.crypt_wp hb (by
    have := h.fitB; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega)
    hw₁ ht₁) fun s₂ ⟨c, ht₂, ecb⟩ => ?_
  have ff : Frame [⟨State.addr B, 4 * slots⟩] s.mem s₁.mem := f.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  refine ⟨fun r hr => ?_, c.rd.trans f.rd, c.wr.trans f.wr, c.sp.trans f.sp,
    ff.trans c.frame, ht₂, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide)]
  · rw [encrypted_lane ecb (by decide), f.block]

end VG.Proof.Sm4.Arm.SerialCbcCore
