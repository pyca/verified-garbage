module

public import VerifiedGarbage.Proof.Rsa.MontContract

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Omega

/-! # The compact multiplication fits the existing prepared RSA workspace -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.Proof.Rsa.Mont
open VG.Impl.Mont.X86.Compact

/-- Either operand is wholly outside the scratch arrays. -/
theorem operand_apart {w j : Nat} (operand : Operand j) :
    arrAt w j + 8 * w ≤ arrAt w 2 ∨ arrAt w 4 ≤ arrAt w j := by
  obtain ⟨bound, notAcc, notTmp⟩ := operand
  change j ≠ 2 at notAcc
  change j ≠ 3 at notTmp
  unfold arrAt hdrBytes
  by_cases before : j < 2
  · exact Or.inl (by
      have : j ≤ 1 := by omega
      have := Nat.mul_le_mul_right (8 * (w + 2)) this
      omega)
  · exact Or.inr (by
      have : 4 ≤ j := by omega
      have := Nat.mul_le_mul_right (8 * (w + 2)) this
      omega)

end VG.Proof.Mont.X86.Compact
