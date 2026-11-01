module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCfb
import VerifiedGarbage.Proof.Sm4.Arm.CfbGroup
import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
import VerifiedGarbage.Proof.Sm4.Arm.Keys
import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # One prepared-key CFB encryption block -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCfbGroup

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions table_frame difference_zero)
open VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Modes.Arm
open VG.Impl.Modes.Arm (copyWord)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

structure GroupPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + 16
  left : s'.gpr .r7 = BitVec.ofNat 32 (n - 1)
  z : s'.z = decide (n = 1)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D 1) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 =
    Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (Spec.Sm4.cipher K (bytesAt s.mem (counterAddr B) 16))
  block : bytesAt s'.mem (State.addr D) 16 = bytesAt s'.mem (counterAddr B) 16

theorem save_wp {s : State} {B D : BitVec 32}
    (hB : s.gpr sb = B) (hD : s.gpr .r6 = D + 16)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩) :
    WP isa (.block SerialCfb.saveCipher) s fun s' =>
      (∀ r, r ≠ .r0 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨counterAddr B, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (State.addr D) 16 := by
  let a := s.setReg .r0 (s.gpr .r6 - 16)
  have ha : runBlock isa [.dp .sub .r0 .r6 (.imm 16)] s = some a := by rfl
  have h0 : a.gpr .r0 = D := by
    change s.gpr .r6 - 16 = D
    rw [hD, BitVec.add_sub_cancel]
  apply (WP.block_append_iff (M := isa) (l₁ := [.dp .sub .r0 .r6 (.imm 16)])
    (l₂ := (List.range 4).flatMap (copyWord sb .r0 (4 * BatchCtr.counterSlot) 0))).mpr
  refine WP.of_runBlock ⟨a, ha, ?_⟩
  have h8 : a.gpr sb = B := by simpa [a, State.setReg, sb] using hB
  have cp : NPre 4 a sb .r0 (4 * BatchCtr.counterSlot) 0 (counterAddr B) (State.addr D) := by
    refine ⟨?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      workspace_part hw 1492 16 (by decide), Covers.right wd, ?_⟩
    · rw [h8]
    · rw [h0]; simp
    · rw [h8]; change B.toNat + 1492 + 16 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at fitB; omega
    · rw [h0]; exact fitD
    · exact (sep.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
  refine WP.mono (copyBlock_wp cp) fun s' h => ?_
  exact ⟨fun r h0' h9 h10 => (h.regs r h9 h10).trans (by simp [a, State.setReg, h0']),
    h.rd, h.wr, h.sp, h.frame, h.block⟩

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa SerialCfb.group s (GroupPost s B D K n) := by
  obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := movImm_ok s .r11 1 (by decide)
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.of_runBlock ⟨s₁, CfbFill.pad_run s₁, ?_⟩⟩))
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide)).trans hB
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide)).trans hD
  have wd₁ : Covers [⟨State.addr D, 16⟩] s₁.wr := by
    rw [wr₁]
    exact (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by simp,
        by change 0 + 16 ≤ 16 * n; omega⟩).trans wd
  have sep₁ := sep.sub_left (Region.sub_prefix (show 16 ≤ 16 * n by omega))
  refine WP.seq (WP.mono (CfbGroup.batch_wp (g := 1) (by decide) (by decide) b₁ d₁ g₁ fitB
    (by omega) (by rw [wr₁]; exact hw) wd₁ sep₁ (by rw [m₁]; exact hH)) fun s₂ b => ?_)
  have b₂ : s₂.gpr sb = B := (b.regs _ (by simp [sb])).trans b₁
  refine WP.seq (WP.mono (save_wp b₂ b.data fitB (by omega)
    (by rw [b.wr, wr₁]; exact hw) (by rw [b.wr]; exact wd₁) sep₁)
    fun s₃ ⟨o₃, rd₃, wr₃, sp₃, f₃, c₃⟩ => ?_)
  have n₃ : s₃.gpr .r7 = BitVec.ofNat 32 n :=
    (o₃ _ (by decide) (by decide) (by decide)).trans
      ((b.regs _ (by simp)).trans ((o₁ _ (by decide)).trans hN))
  have g₃ : s₃.gpr .r11 = 1 :=
    (o₃ _ (by decide) (by decide) (by decide)).trans ((b.regs _ (by simp)).trans g₁)
  have out₂ : bytesAt s₂.mem (State.addr D) 16 =
      Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (Spec.Sm4.cipher K (bytesAt s.mem (counterAddr B) 16)) := by
    simpa [dataAddr, CfbGroup.inputBlock, m₁] using b.blocks 0 (by decide)
  have data₃ : bytesAt s₃.mem (State.addr D) 16 = bytesAt s₂.mem (State.addr D) 16 := by
    apply bytes_frame f₃
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.sub_right (Offset.sub_base _ (by decide))
  have frame₃ : Frame (batchRegions B D 1) s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
  have table₃ := table_frame b.table f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  obtain ⟨s₄, e₄, r₄, z₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := subsR_ok s₃ .r7 .r7 .r11
  refine WP.of_runBlock ⟨s₄, e₄, fun r hr => ?_, ?_, ?_, ?_,
    rd₄.trans (rd₃.trans (b.rd.trans rd₁)), wr₄.trans (wr₃.trans (b.wr.trans wr₁)),
    sp₄.trans (sp₃.trans (b.sp.trans sp₁)), ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [o₄ _ (by decide), o₃ _ (by decide) (by decide) (by decide), b.regs _ (by simp), o₁ _ (by decide)]
  · rw [o₄ _ (by decide), o₃ _ (by decide) (by decide) (by decide)]; exact b.data
  · rw [r₄, n₃, g₃]; exact Offset.ofNat_sub_ofNat hn
  · rw [z₄, n₃, g₃]; exact difference_zero hn32 hn
  · rw [m₄, ← m₁]; exact b.frame.trans frame₃
  · rw [m₄]; exact table₃
  · rw [m₄, c₃, out₂]
  · rw [m₄, data₃, c₃]

end VG.Proof.Sm4.Arm.SerialCfbGroup
