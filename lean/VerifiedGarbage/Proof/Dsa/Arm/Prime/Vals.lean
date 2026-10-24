module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # DSA's probable-prime test on ARMv7: the candidate's bounds

The candidate `cv` (`Base.lean`) is odd and has exactly `bits` bits, which
fit the arithmetic's `8 L` bytes (`cv_shape`); octets of `rand` from an
offset (`seg_bytesAt`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm

theorem seg_bytesAt (m : Mem) (p : Addr) {a n k : Nat} (h : a + n ≤ k) :
    VG.Proof.RsaKeyGen.seg (Spec.Rsa.bytesAt m p k) a n = Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) n :=
  VG.Proof.RsaKeyGen.seg_bytesAt m p h

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n :=
  VG.Proof.RsaKeyGen.rand_bytes_length m p n

section
variable {P : CP} {σ : State}

/-- The sizes of the five widths: `bits` fits the arithmetic, and is at least 160. -/
theorem In.sizes (pre : In P σ) : 160 ≤ P.bits ∧ P.bits ≤ 8 * P.L ∧ P.bits = 8 * P.len ∧
    P.len ≤ P.L ∧ P.len ≤ P.D ∧ P.D ≤ P.L ∧ 4 ≤ P.len ∧ P.len % 4 = 0 ∧ 24 ≤ P.D := by
  have hL := pre.L
  simp only [CP.len, CP.D, Impl.Dsa.Arm.ProbablePrime.len, Impl.Dsa.Arm.ProbablePrime.draw,
    Impl.Dsa.Arm.ProbablePrime.words] at *
  rcases pre.bits with h | h | h | h | h <;> rw [h] at hL ⊢ <;> simp at hL <;> omega

/-- The candidate is odd, has `bits` bits, and fits `8 L` bits. -/
theorem cv_shape (pre : In P σ) : cv P σ % 2 = 1 ∧ 2 ^ (P.bits - 1) ≤ cv P σ ∧ cv P σ < 2 ^ (8 * P.L) := by
  have sz := pre.sizes
  obtain ⟨lo, hi⟩ := (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mp pre.bl
  exact ⟨pre.odd, lo, Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) sz.2.1)⟩

end

end VG.Proof.Dsa.Arm.Prime
