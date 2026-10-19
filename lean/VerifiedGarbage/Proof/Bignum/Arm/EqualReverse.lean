module

public import VerifiedGarbage.Impl.Bignum.Arm.EqualBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Swap and rewind the comparison inputs while retaining the first borrow -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem equalReverse_ok (s : State) : WP isa (.block equalReverse) s fun t =>
    t.gpr .r6 = s.gpr .r11 ∧ t.gpr .r0 = s.gpr .r0 - (s.gpr .r8 <<< 2) ∧
    t.gpr .r10 = s.gpr .r12 - (s.gpr .r8 <<< 2) ∧
    t.gpr .r12 = s.gpr .r10 - (s.gpr .r8 <<< 2) ∧ t.gpr .lr = s.gpr .r8 ∧ t.gpr .r11 = 0 ∧
    Preserves [.r0, .r6, .r7, .r10, .r11, .r12, .lr] s t := by
  apply WP.of_runBlock
  simp only [equalReverse, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    ↓reduceIte, gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

end VG.Proof.Bignum.Arm
