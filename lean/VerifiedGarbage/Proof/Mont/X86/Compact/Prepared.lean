module

import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import Init.Prelude
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Mont.X86.Compact.Layout`, which this module and modules that import it used -/

section

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
      have : j ≤ 1 := by omega_using [before]
      have := Nat.mul_le_mul_right (8 * (w + 2)) this
      omega_using [this])
  · exact Or.inr (by
      have : 4 ≤ j := by omega_using [notAcc, notTmp, before]
      have := Nat.mul_le_mul_right (8 * (w + 2)) this
      omega_using [this])

end VG.Proof.Mont.X86.Compact

end

end

/-! # The reviewed prepared workspace supplies native-word metadata -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont
open VG.Proof.Rsa.Mont

theorem header_low (m : Mem) (W : Addr) (i : Nat) :
    w32 m W (8 * i) = (wordAt m W i).toNat % 2 ^ 32 := by
  unfold w32 wordAt off
  rw [← VG.Proof.Rc2.Word32.readW64_lo, BitVec.extractLsb'_toNat]
  simp only [Nat.shiftRight_zero]

theorem array_mono (w : Nat) {i j : Nat} (bound : i < j) :
    arrAt w i + 8 * (w + 2) ≤ arrAt w j := by
  have h := Nat.mul_le_mul_right (8 * (w + 2)) bound
  unfold arrAt hdrBytes
  rw [Nat.succ_mul] at h
  omega_using [h]

theorem array_fit {w L j : Nat} (fit : arrAt w 8 ≤ L) (index : j < 8) :
    arrAt w j + 8 * w ≤ L := by
  have := array_mono w index
  omega_using [fit, this]

end VG.Proof.Mont.X86.Compact
