module

import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcCore
import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbHead
import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbGroup
import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcFill

/-! # One prepared-key CBC encryption block -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcGroup

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions table_frame difference_zero)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Sm4.Prepared (Holds)

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
    Spec.Sm4.cipher K (Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (bytesAt s.mem (counterAddr B) 16))
  block : bytesAt s'.mem (State.addr D) 16 = bytesAt s'.mem (counterAddr B) 16

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (ht : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa SerialCbc.group s (GroupPost s B D K n) := by
  refine WP.seq (WP.mono (SerialCbcFill.count_wp s) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans hB
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans hD
  have wd₁ : Covers [⟨State.addr D, 16⟩] s₁.wr := by
    rw [wr₁]
    exact (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by simp,
        by change 0 + 16 ≤ 16 * n; omega⟩).trans wd
  have sep₁ := sep.sub_left (Region.sub_prefix (show 16 ≤ 16 * n by omega))
  have p₁ : CfbFill.Pre B D 1 s₁ := ⟨b₁, d₁, g₁, fitB, by omega,
    by rw [wr₁]; exact hw, wd₁, sep₁⟩
  refine WP.seq (WP.mono (SerialCbcCore.core_wp p₁ (by rw [m₁]; exact ht)) fun s₂ c => ?_)
  have p₂ : CfbFill.Pre B D 1 s₂ := ⟨(c.regs _ (by simp [sb])).trans b₁,
    (c.regs _ (by simp)).trans d₁, (c.regs _ (by simp)).trans g₁, fitB, by omega,
    by rw [c.wr, wr₁]; exact hw, by rw [c.wr]; exact wd₁, sep₁⟩
  refine WP.seq (WP.mono (SerialCbcFill.copy_wp p₂) fun s₃ cp => ?_)
  have b₃ : s₃.gpr sb = B := (cp.regs _ (by decide) (by decide)).trans p₂.base
  refine WP.seq (WP.mono (SerialOfbGroup.save_wp b₃ fitB (by rw [cp.wr, c.wr, wr₁]; exact hw))
    fun s₄ sv => ?_)
  have buf₃ : bytesAt s₃.mem (bufferAddr B 0) 16 = bytesAt s₂.mem (bufferAddr B 0) 16 := by
    apply bytes_frame cp.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.symm.sub_left (Offset.sub_base _ (by decide))
  have data₄ : bytesAt s₄.mem (State.addr D) 16 = bytesAt s₃.mem (State.addr D) 16 := by
    apply bytes_frame sv.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.sub_right (Offset.sub_base _ (by decide))
  have f₂ : Frame (batchRegions B D 1) s₁.mem s₂.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]
  have f₃ : Frame (batchRegions B D 1) s₂.mem s₃.mem := cp.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]
  have f₄ : Frame (batchRegions B D 1) s₃.mem s₄.mem := sv.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]
  have table₃ := table_frame c.table cp.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.symm.sub_left (Offset.sub_base _ (by decide)))
  have table₄ := table_frame table₃ sv.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  have n₄ : s₄.gpr .r7 = BitVec.ofNat 32 n := by
    rw [sv.regs _ (by decide) (by decide), cp.regs _ (by decide) (by decide),
      c.regs _ (by simp), o₁ _ (by decide) (by decide), hN]
  have g₄ : s₄.gpr .r11 = 1 := by
    rw [sv.regs _ (by decide) (by decide), cp.regs _ (by decide) (by decide), c.regs _ (by simp), g₁]
  have d₄ : s₄.gpr .r6 = D := by
    rw [sv.regs _ (by decide) (by decide), cp.regs _ (by decide) (by decide)]; exact p₂.data
  obtain ⟨s₅, e₅, d₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := addImm_ok s₄ .r6 .r6 16 (by decide)
  apply (WP.block_append_iff (M := isa) (l₁ := [.dp .add .r6 .r6 (.imm 16)])
    (l₂ := [.subs .r7 .r7 (.reg .r11)])).mpr
  refine WP.of_runBlock ⟨s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, n₆, z₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := subsR_ok s₅ .r7 .r7 .r11
  refine WP.of_runBlock ⟨s₆, e₆, fun r hr => ?_, ?_, ?_, ?_,
    rd₆.trans (rd₅.trans (sv.rd.trans (cp.rd.trans (c.rd.trans rd₁)))),
    wr₆.trans (wr₅.trans (sv.wr.trans (cp.wr.trans (c.wr.trans wr₁)))),
    sp₆.trans (sp₅.trans (sv.sp.trans (cp.sp.trans (c.sp.trans sp₁)))), ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [o₆ _ (by decide), o₅ _ (by decide), sv.regs _ (by decide) (by decide),
        cp.regs _ (by decide) (by decide), c.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [o₆ _ (by decide), d₅, d₄]
  · rw [n₆, o₅ _ (by decide), o₅ _ (by decide), n₄, g₄]; exact Offset.ofNat_sub_ofNat hn
  · rw [z₆, o₅ _ (by decide), o₅ _ (by decide), n₄, g₄]; exact difference_zero hn32 hn
  · rw [m₆, m₅, ← m₁]; exact (f₂.trans f₃).trans f₄
  · rw [m₆, m₅]; exact table₄
  · rw [m₆, m₅, sv.block, buf₃, c.block, m₁]
  · rw [m₆, m₅, data₄, cp.block, sv.block, buf₃]

end VG.Proof.Sm4.Arm.SerialCbcGroup
