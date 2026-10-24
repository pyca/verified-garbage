module

public import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbHead
public import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbLoop
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Public registers across prepared-key OFB encryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialOfbHead

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor

abbrev groupHead := SerialCfbHead.groupHead
abbrev proHead := SerialCfbHead.proHead
abbrev HeadPre := SerialCfbHead.HeadPre
abbrev HeadPost := SerialCfbHead.HeadPost
abbrev head_wp := @SerialCfbHead.head_wp

def groupTail : Prog isa := .seq BatchCtr.xorGroup
  (.seq (.block SerialOfb.saveFeedback) (.block [.subs .r7 .r7 (.reg .r11)]))

theorem loop_pre {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (_hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : SerialOfbLoop.LoopInv s₀ B D K t n i s) : HeadPre B (D + BitVec.ofNat 32 (16 * i)) (n - i) s := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  have diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega)
  have diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega)
  have subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega)
  have wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr, by change 16 * i + 16 * (n - i) ≤ 16 * n; omega⟩
  exact ⟨(h.regs _ (by simp [sb])).trans hB, h.left, fitB, by rw [h.wr]; exact hw,
    ⟨K, h.table⟩, h.data, by change Di.toNat + 16 * (n - i) ≤ 2 ^ 32; rw [diNat]; omega, wdi, sep.sub_left subD⟩

end VG.Proof.Sm4.Arm.SerialOfbHead
