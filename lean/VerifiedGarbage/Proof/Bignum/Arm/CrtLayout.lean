module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The complete CRT layout fits the existing cross-architecture scratch contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

theorem crt_workspace_end (w : Nat) : arrAt w 8 ≤ stride w := by
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, stride, workspaceWords]
  omega

theorem crt_buffer_sizes (w : Nat) :
    productWords w = 2 * w + 2 * w + 2 ∧
    productOffset w + productBytes w = compareOffset w ∧
    compareOffset w + productBytes w = modulusOffset w ∧
    modulusOffset w + productBytes w = narrowOffset w := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [productWords]
  omega

/-- The zero-extended modulus buffer ends before the narrow workspace. -/
theorem crt_modulus_end_le (w : Nat) : modulusOffset w + 4 * (4 * w + 2) ≤ totalBytes w := by
  simp only [totalBytes, narrowOffset, productBytes, productWords]
  omega

theorem crt_layout_fits {k : Nat} (hk : Spec.Rsa.lenValid k) :
    totalBytes (Spec.Rsa.modulusWords k) ≤ 8 * Spec.Rsa.scratchWords k := by
  simp only [Spec.Rsa.lenValid] at hk
  simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes,
    productWords, stride, workspaceWords, Spec.Rsa.modulusWords, Spec.Rsa.scratchWords]
  omega

theorem crt_width_valid {k : Nat} (hk : Spec.Rsa.lenValid k) :
    2 ≤ Spec.Rsa.modulusWords k ∧ Spec.Rsa.modulusWords k ≤ 128 ∧
      k ≤ 8 * Spec.Rsa.modulusWords k := by
  simp only [Spec.Rsa.lenValid] at hk
  simp only [Spec.Rsa.modulusWords]
  omega

end VG.Proof.Bignum.Arm
