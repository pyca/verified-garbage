module

public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Dsa.X86.Width
public import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Combining supported public-width masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Proof.Ecdsa.X86

theorem mask_or (p q : Prop) [Decidable p] [Decidable q] : mask32 p ||| mask32 q = mask32 (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [mask32, hp, hq, ite_true, ite_false, or_self, or_false, false_or] <;> decide

theorem supported_masks (p q : Nat) (odd : Prop) [Decidable odd] :
    ((mask32 (p = 1024) &&& mask32 (q = 160)) |||
      ((mask32 (q = 224) ||| mask32 (q = 160) ||| mask32 (q = 256)) &&& mask32 (p = 2048)) |||
      (mask32 (p = 3072) &&& mask32 (q = 256))) &&& mask32 odd =
      mask32 (Spec.Dsa.supportedSizes p q ∧ odd) := by
  simp only [mask32_and, mask_or]
  simp only [Spec.Dsa.supportedSizes, and_comm, or_assoc, or_comm]

end VG.Proof.Dsa.X86
