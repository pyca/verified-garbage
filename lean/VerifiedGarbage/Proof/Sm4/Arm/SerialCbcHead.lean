module

public import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcLoop
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbHead
import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcCore
import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcFill
import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbHead

/-! # Public registers across prepared-key CBC encryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcHead

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor

def groupHead : Prog isa := .seq SerialCbc.count SerialCbc.core
abbrev proHead := SerialCfbHead.proHead
abbrev HeadPre := SerialCfbHead.HeadPre
abbrev HeadPost := SerialCfbHead.HeadPost
theorem head_wp {s : State} {B D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (_hn32 : n < 2 ^ 32)
    (h : HeadPre B D n s) : WP isa groupHead s (HeadPost s n) := by
  obtain ⟨K, ht⟩ := h.table
  refine WP.seq (WP.mono (SerialCbcFill.count_wp s) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have wd₁ : Covers [⟨State.addr D, 16⟩] s₁.wr := by
    rw [wr₁]
    exact (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by simp,
        by change 0 + 16 ≤ 16 * n; omega⟩).trans h.wdata
  have p : CfbFill.Pre B D 1 s₁ := ⟨(o₁ _ (by decide) (by decide)).trans h.base,
    (o₁ _ (by decide) (by decide)).trans h.data, g₁, h.fit, by have := h.fitD; omega,
    by rw [wr₁]; exact h.writable, wd₁, h.sep.sub_left (Region.sub_prefix (by omega))⟩
  refine WP.mono (SerialCbcCore.core_wp p (by rw [m₁]; exact ht)) fun s₂ c => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [c.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by simp), g₁]; rfl

def groupTail : Prog isa := SerialCbc.tail

theorem loop_pre {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (_hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : SerialCbcLoop.LoopInv s₀ B D K t n i s) : HeadPre B (D + BitVec.ofNat 32 (16 * i)) (n - i) s := by
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

end VG.Proof.Sm4.Arm.SerialCbcHead
