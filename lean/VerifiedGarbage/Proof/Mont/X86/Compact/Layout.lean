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

/-- The row multiplier precedes every product word. -/
theorem multiplier_before_product (w : Nat) :
    arrAt w 2 + VG.Impl.Mont.X86.Rt.multOff + 4 ≤ arrAt w 2 + accOff := by
  unfold VG.Impl.Mont.X86.Rt.multOff accOff
  omega

/-- Arrays 2 and 3 hold the multiplier and the full 4w+1 native-word product,
including its carry. No operand is copied into those arrays. -/
theorem product_fits (w : Nat) :
    arrAt w 2 + accOff + 4 * (4 * w + 1) ≤ arrAt w 4 := by
  unfold arrAt hdrBytes accOff
  omega

/-- A native word of the product lies inside the function's two arrays. -/
theorem product_word {w i : Nat} (index : i < 4 * w + 1) :
    arrAt w 2 ≤ arrAt w 2 + accOff + 4 * i ∧
      arrAt w 2 + accOff + 4 * i + 4 ≤ arrAt w 4 := by
  have := product_fits w
  constructor <;> omega

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
