module

public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.Rsa.SuccessBits32

/-! # The shared fault-check logic applies to 32-bit return registers -/

@[expose] public section
namespace VG.Proof.Rsa
open VG

theorem successBits_widen (r2 r1 r3 : BitVec 32) :
    (successBits r2 r1 r3).setWidth 64 = Rsa.gOf (r2.setWidth 64) (r1.setWidth 64) (r3.setWidth 64) := by
  unfold successBits Rsa.gOf
  rw [BitVec.setWidth_and, BitVec.setWidth_and, BitVec.setWidth_and, BitVec.and_comm (r1.setWidth 64) (r2.setWidth 64)]
  rfl

theorem successBits_one (r2 r1 r3 : BitVec 32) :
    successBits r2 r1 r3 = 1 ↔ Rsa.gOf (r2.setWidth 64) (r1.setWidth 64) (r3.setWidth 64) = 1 := by
  rw [← successBits_widen]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    have eq := congrArg (BitVec.setWidth 32) h
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] at eq
    exact eq

theorem check_logic32 {r1 r2 r3 : BitVec 32} {nb eb xb mb ob : List Byte}
    (h3 : match Spec.Rsa.publicPrecompute nb with | some _ => r3 = 1 | none => r3 = 0)
    (h2 : (Spec.Rsa.publicPrecompute nb).isSome = true →
      match Spec.Rsa.publicOpChecked nb eb mb with
      | some y => r2 = 1 ∧ ob = y | none => r2 = 0) :
    (if decide (successBits r2 r1 r3 = 1) then if decide (ob = xb) then 1 else 2 else 0 : BitVec 32) =
      (Rsa.checkResult (r1.setWidth 64) nb eb xb mb).setWidth 32 ∧
    ((successBits r2 r1 r3 = 1 ∧ ob = xb) ↔ Rsa.released (r1.setWidth 64) nb eb xb mb) := by
  have narrow (r : BitVec 32) : (r.setWidth 64).setWidth 32 = r := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have logic := Rsa.check_logic (r₁ := r1.setWidth 64) (r₂ := r2.setWidth 64) (r₃ := r3.setWidth 64)
    (nB := nb) (eB := eb) (xB := xb) (mB := mb) (outB := ob)
    (by cases hp : Spec.Rsa.publicPrecompute nb <;> simp only [hp] at h3 ⊢ <;> simpa only [narrow] using h3)
    (by intro hs
        have h2 := h2 hs
        cases hp : Spec.Rsa.publicOpChecked nb eb mb <;> simp only [hp] at h2 ⊢ <;> simpa only [narrow] using h2)
  refine ⟨?_, by simpa only [successBits_one] using logic.2⟩
  rw [← logic.1]
  simp only [Rsa.result, decide_eq_true_eq, apply_ite,
    successBits_one]
  split
  · split <;> rfl
  · rfl
end VG.Proof.Rsa
