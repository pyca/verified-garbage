module

import VerifiedGarbage.Proof.Ffdh.VettedBounds
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration

/-! Exact public caps select the reviewed byte widths and masks. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem vetted_caps {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    bits = 225 ∨ bits = 275 ∨ bits = 325 ∨ bits = 375 ∨ bits = 400 := by
  unfold Spec.Ffdh.vettedExponentBits at recognized
  repeat' split at recognized
  all_goals cases recognized
  all_goals simp

theorem vetted_cap_result {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) (old : BitVec 32 × BitVec 32) :
    VG.Impl.Ffdh.Arm.VettedCap.result VG.Impl.Ffdh.Arm.VettedCap.choices (BitVec.ofNat 32 bits) old =
      (BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width bits),
       (VG.Proof.Ffdh.ScalarWidth.mask bits).setWidth 32) := by
  rcases vetted_caps recognized with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem vetted_cap_unrecognized (old : BitVec 32 × BitVec 32) :
    VG.Impl.Ffdh.Arm.VettedCap.result VG.Impl.Ffdh.Arm.VettedCap.choices (0#32) old = old := rfl

theorem vetted_layout_width {p : Inputs} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) = some bits) :
    (ScalarLayout.vetted p).width = VG.Proof.Ffdh.ScalarWidth.width bits := by
  have uncapped := VG.Proof.Ffdh.VettedPolicy.bits_of_recognized_uncapped recognized
  have fit := VG.Proof.Ffdh.ScalarWidth.width_le (by have := p.minLength; omega)
    (Nat.le_trans (VG.Proof.Ffdh.VettedPolicy.recognized_le_bound recognized) p.scalarBound_bits_fit)
  simp only [ScalarLayout.width, ScalarLayout.vetted, uncapped]
  omega

theorem vetted_layout_mask {p : Inputs} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) = some bits) :
    (ScalarLayout.vetted p).mask = (VG.Proof.Ffdh.ScalarWidth.mask bits).setWidth 32 := by
  simp only [ScalarLayout.vetted, VG.Proof.Ffdh.VettedPolicy.bits_of_recognized_uncapped recognized]

theorem vetted_cap_layout {p : Inputs} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) = some bits)
    (old : BitVec 32 × BitVec 32) :
    VG.Impl.Ffdh.Arm.VettedCap.result VG.Impl.Ffdh.Arm.VettedCap.choices (BitVec.ofNat 32 bits) old =
      (BitVec.ofNat 32 (ScalarLayout.vetted p).width, (ScalarLayout.vetted p).mask) := by
  rw [vetted_cap_result recognized, vetted_layout_width recognized, vetted_layout_mask recognized]

end VG.Proof.Ffdh.Arm
