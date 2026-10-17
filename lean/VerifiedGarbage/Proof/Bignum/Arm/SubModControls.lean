module

public import VerifiedGarbage.Impl.Bignum.Arm.SubModBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Preserve public buffer addresses and carry the secret borrow into addition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem subModHead_ok (s : State) : WP isa (.block subModHead) s fun t =>
    t.gpr .r7 = s.gpr .r0 ∧ t.gpr .r8 = s.gpr .lr ∧ t.gpr .r11 = 0 ∧
    Preserves [.r7, .r8, .r11] s t := by
  apply WP.of_runBlock
  simp only [subModHead, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    ↓reduceIte, gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

theorem subModAddArgs_ok (s : State) : WP isa (.block subModAddArgs) s fun t =>
    t.gpr .r1 = s.gpr .r11 ∧ t.gpr .r0 = s.gpr .r7 ∧ t.gpr .r12 = s.gpr .r9 ∧ t.gpr .lr = s.gpr .r8 ∧ t.gpr .r11 = 0 ∧
    Preserves [.r1, .r0, .r12, .lr, .r11] s t := by
  apply WP.of_runBlock
  simp only [subModAddArgs, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    ↓reduceIte, gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

end VG.Proof.Bignum.Arm
