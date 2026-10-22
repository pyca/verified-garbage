module

public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Witness sampling as an interval mask and a fixed fallback, for a candidate of `32 k` bits -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG

theorem witness_sample {c x w : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    (bound : x < 2 ^ (64 * w)) :
    Spec.RsaKeyGen.witness (c - 1) x =
      (if decide (2 ≤ x ∧ x < c - 1) then x else (x ||| 2) % 2 ^ (64 * w - 1), decide (2 ≤ x ∧ x < c - 1)) := by
  unfold Spec.RsaKeyGen.witness
  simp only [shape, Nat.mod_eq_of_lt bound]
  by_cases h : 2 ≤ x ∧ x < c - 1 <;> simp [h]

theorem witness_sampleAt {c x k : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k)
    (bound : x < 2 ^ (32 * k)) :
    Spec.RsaKeyGen.witness (c - 1) x =
      (if decide (2 ≤ x ∧ x < c - 1) then x else (x ||| 2) % 2 ^ (32 * k - 1), decide (2 ≤ x ∧ x < c - 1)) := by
  unfold Spec.RsaKeyGen.witness
  simp only [shape, Nat.mod_eq_of_lt bound]
  by_cases h : 2 ≤ x ∧ x < c - 1 <;> simp [h]

/-- The witness depends only on the draw's low `32 k` bits. -/
theorem witness_mod {c x k : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) :
    Spec.RsaKeyGen.witness (c - 1) (x % 2 ^ (32 * k)) = Spec.RsaKeyGen.witness (c - 1) x := by
  unfold Spec.RsaKeyGen.witness
  simp only [shape, Nat.mod_mod]

end VG.Proof.RsaKeyGen
