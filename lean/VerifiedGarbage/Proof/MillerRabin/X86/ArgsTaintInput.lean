module

public import VerifiedGarbage.Proof.MillerRabin.X86.TaintStage
import VerifiedGarbage.Proof.Framework.Offset

/-! # Public argument construction inside the borrowed Montgomery call frame -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

namespace PieceInput

theorem args_wf {base : Addr} {bytes w : Nat} {sp len : BitVec 32} {s : State}
    (h : PieceInput base bytes w sp len s) : VG.X86.Taint.Wf argsTaint (allocFrame 36 s) := by
  have low : 40 ≤ sp.toNat := by rw [← h.stack]; exact h.room.low
  have esp : (allocFrame 36 s).gpr .esp = sp - BitVec.ofNat 32 36 := by rw [allocFrame_esp, h.stack]
  have wr : (allocFrame 36 s).wr = [below sp 36, ⟨byteAddr sp, 1132⟩, ⟨base, bytes⟩] := by
    rw [allocFrame_wr, h.wr, h.stack]
  have frameApart : (below sp 36).Disjoint ⟨base, bytes⟩ := by
    have room := h.room.apart
    rw [h.stack] at room
    exact room.sub_left (below_sub (by decide) low)
  have stackApart : (below sp 36).Disjoint ⟨byteAddr sp, 1132⟩ := by
    change (⟨(sp - BitVec.ofNat 32 36).setWidth 64, 36⟩ : Region).Disjoint _
    rw [Taint.sub_setWidth (by omega)]
    exact (Offset.base_disjoint_below _ (by decide)).symm
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [wr]
    refine ⟨.cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons h.capacity .nil)), ?_, ?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨stackApart, frameApart⟩, by simpa only [h.stack, VG.Impl.MillerRabin.X86.frameBytes] using h.context.apart.symm, by simp⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change (byteAddr (sp - BitVec.ofNat 32 36)).toNat + 36 ≤ 2 ^ 32
        rw [byteAddr_toNat, sub_toNat (by omega)]
        have := sp.isLt
        omega
      · rw [byteAddr_toNat, ← h.stack]
        exact h.context.stackFit
      · exact h.context.ws.nowrap
  · intro p hp
    simp only [argsTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simp only [VG.X86.Taint.region, wr, esp, addr]
      rw [BitVec.add_zero]
      rfl
    · simp only [VG.X86.Taint.region, wr, esp, addr]
      rw [BitVec.sub_add_cancel]
      rfl
    · simp only [VG.X86.Taint.region, wr, addr, allocFrame_gpr (q := .edi) _ _ (by decide)]
      rw [BitVec.add_zero]
      exact h.context.ws.edi
  · intro p hp
    cases hp
  · intro hp
    exact (Nat.lt_irrefl 0 hp).elim
  · intro p hp
    cases hp

theorem agree_args {base : Addr} {bytes w : Nat} {sp len : BitVec 32} {s t : State}
    (h : PieceInput base bytes w sp len s) (g : PieceInput base bytes w sp len t) :
    VG.X86.Taint.Agree argsTaint (allocFrame 36 s) (allocFrame 36 t) := by
  have rf := h.agree g
  have wrS : (allocFrame 36 s).wr = [below sp 36, ⟨byteAddr sp, 1132⟩, ⟨base, bytes⟩] := by
    rw [allocFrame_wr, h.wr, h.stack]
  have wrT : (allocFrame 36 t).wr = [below sp 36, ⟨byteAddr sp, 1132⟩, ⟨base, bytes⟩] := by
    rw [allocFrame_wr, g.wr, g.stack]
  refine ⟨⟨?_, fun h => nomatch h⟩, fun _ => wrS.trans wrT.symm, h.args_wf, g.args_wf, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [argsTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide)]
      exact rf.rf.1 .edi (by simp [pieceTaint, RegSet.mem_ofList])
    · rw [allocFrame_esp, allocFrame_esp, h.stack, g.stack]
  · intro i k hk
    simp only [argsTaint, Slots.has_add, Slots.has_empty, Bool.false_or, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at hk
    rcases hk with ⟨⟨rfl, lo⟩, hi⟩ | ⟨⟨rfl, lo⟩, hi⟩
    · change k < 1600
      omega
    · change k < 1132
      change 52 ≤ k at lo
      change k < 56 at hi
      omega
  · intro i k hk
    simp only [argsTaint, Slots.has_add, Slots.has_empty, Bool.false_or, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at hk
    rcases hk with ⟨⟨rfl, lo⟩, hi⟩ | ⟨⟨rfl, lo⟩, hi⟩
    · dsimp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region]
      rw [wrS, wrT, allocFrame_mem, allocFrame_mem]
      exact public_word_bytes (h.width.trans g.width.symm) lo hi
    · dsimp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region]
      rw [wrS, wrT, allocFrame_mem, allocFrame_mem]
      exact public_word_bytes (h.length.trans g.length.symm) lo hi
  · intro hp
    exact (Nat.lt_irrefl 0 hp).elim
  · intro _ _ hp
    exact (Nat.not_lt_zero _ hp).elim

end PieceInput
end VG.Proof.MillerRabin.X86
