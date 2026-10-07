import VerifiedGarbage.Proof.Weierstrass.X86.InvSet
import VerifiedGarbage.Proof.Weierstrass.X86.InvWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvState

/-! # Initializing the word matrix for a divstep batch -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem batchStart_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) :
    WP isa (.block P.batchStart) s fun u =>
      wordState u.mem base P.sW =
        ⟨s.mem.readW (off base P.sW) 32, s.mem.readW (off base P.sF) 32,
          s.mem.readW (off base P.sG) 32, 1, 0, 0, 1⟩ ∧
      Keeps [.eax] s u ∧ Outside base (P.sW + 4) 24 s.mem u.mem := by
  have hn := hs.nowrap
  have eW : P.sW = P.tbl + 288 := rfl
  have eF : P.sF = P.tbl := rfl
  have eG : P.sG = P.tbl + 36 := rfl
  unfold InvCfg.batchStart
  refine WP.block_append (WP.block_append (WP.mono
    (copy_ok 1 hs (o := P.sW + 4) (a := P.sF) (by omega) (by omega) (by omega))
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_))
  simp only [val32, Nat.mul_zero, Nat.add_zero] at F₁
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copy_ok 1 hs₁ (o := P.sW + 8) (a := P.sG) (by omega) (by omega) (by omega))
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  simp only [val32, Nat.mul_zero, Nat.add_zero] at G₂
  rw [O₁.w32 (by omega) (by omega)] at G₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (setMatrix_ok hs₂ (dst := P.sW + 12) (by omega))
    fun u ⟨U, V, Q, R, K₃, O₃⟩ => ⟨?_, (K₁.trans K₂).trans K₃, ?_⟩
  · have D : w32 u.mem base P.sW = w32 s.mem base P.sW := by
      rw [O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega), O₁.w32 (by omega) (by omega)]
    have F : w32 u.mem base (P.sW + 4) = w32 s.mem base P.sF := by
      rw [O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega), F₁]
    have G : w32 u.mem base (P.sW + 8) = w32 s.mem base P.sG := by
      rw [O₃.w32 (by omega) (by omega), G₂]
    simp only [wordState, atWord, Divstep.W32.WSt.mk.injEq, Nat.reduceMul, Nat.add_zero]
    refine ⟨BitVec.eq_of_toNat_eq D, BitVec.eq_of_toNat_eq F, BitVec.eq_of_toNat_eq G,
      BitVec.eq_of_toNat_eq U, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 16) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using V
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 20) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Q
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 24) = 1
      simpa only [Nat.add_assoc, Nat.reduceAdd] using R
  · intro x hx
    rw [O₃ x (by omega), O₂ x (by omega), O₁ x (by omega)]

end VG.Proof.Weierstrass.X86.Inv
