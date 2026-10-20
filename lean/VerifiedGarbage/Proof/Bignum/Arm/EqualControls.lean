module

public import VerifiedGarbage.Impl.Bignum.Arm.EqualBuffers
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Branchless setup and result combination for exact buffer equality -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem equalHead_ok (s : State) : WP isa (.block equalHead) s fun t =>
    t.gpr .r8 = s.gpr .lr ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r8, .r11] s t := by
  unfold equalHead
  refine wp_mov (op2_reg _ _) fun u h => ?_
  refine wp_mov (op2_imm (by decide)) fun t j => WP.block_nil ?_
  exact ⟨(j.other .r8 (by decide)).trans h.gpr, j.gpr, j.mem.trans h.mem,
    (h.rest (by simp)).trans (j.rest (by simp))⟩

theorem equalFinish_ok (s : State) {A B : Nat}
    (left : s.gpr .r6 = (if A < B then 1 else 0))
    (right : s.gpr .r11 = (if B < A then 1 else 0)) :
    WP isa (.block equalFinish) s fun t =>
      t.gpr .r11 = (if A = B then 1 else 0) ∧ t.mem = s.mem ∧ Rest [.r11] s t := by
  unfold equalFinish
  refine wp_dp (op2_reg _ _) fun u h => ?_
  refine wp_dp (op2_imm (by decide)) fun t j => WP.block_nil ?_
  refine ⟨?_, j.mem.trans h.mem, (h.rest (by simp)).trans (j.rest (by simp))⟩
  rw [j.gpr, dpVal, h.gpr, dpVal, left, right]
  rcases Nat.lt_trichotomy A B with lt | eq | gt
  · rw [ite_eq_left lt, ite_eq_right (by omega : ¬B < A), ite_eq_right (by omega : A ≠ B)]; decide
  · rw [ite_eq_right (by omega : ¬A < B), ite_eq_right (by omega : ¬B < A), ite_eq_left eq]; decide
  · rw [ite_eq_right (by omega : ¬A < B), ite_eq_left gt, ite_eq_right (by omega : A ≠ B)]; decide

end VG.Proof.Bignum.Arm
