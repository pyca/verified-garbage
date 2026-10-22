module

public import VerifiedGarbage.Proof.Dsa.Generation.Contributions
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The shared native shaper and divider implement DSA's p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

/-- Numeric value of one hash contribution, before truncation. -/
def pDigest (n : Nat) (seed : List Byte) (offset j : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Dsa.seedHash n (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + offset + j)))

theorem digest_value_lt {n : Nat} (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash n bs).length = n)
    (seed : List Byte) (offset j : Nat) : pDigest n seed offset j < 2 ^ n := by
  have h := decodeBE_lt (Spec.Dsa.seedHash n (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + offset + j)))
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, hlen] at h
  exact h

/-- The p search can concatenate whole digests, shape the low L bits with
the existing routine, and divide by 2*q. This is exactly the reviewed DSA
formula, including the final partial digest and low-bit adjustment. -/
theorem pCandidate_shaped {l n : Nat} (hl : 2 ≤ l)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash n bs).length = n)
    (q : Nat) (seed : List Byte) (offset : Nat) :
    Spec.Dsa.pCandidate l n q seed offset =
      let x := Spec.Ffdh.candidateOf l (contributions n (pDigest n seed offset) ((l - 1) / n + 1))
      x + 1 - x % (2 * q) := by
  have hpow : 2 ^ (((l - 1) / n) * n) * 2 ^ ((l - 1) % n) = 2 ^ (l - 1) := by
    rw [← Nat.pow_add, Nat.mul_comm ((l - 1) / n) n, Nat.div_add_mod]
  have hv : ∀ j < (l - 1) / n, pDigest n seed offset j < 2 ^ n :=
    fun j _ => digest_value_lt hlen seed offset j
  have hcut := contributions_cut n ((l - 1) % n) ((l - 1) / n) (pDigest n seed offset) hv
  rw [hpow] at hcut
  dsimp only [Spec.Dsa.pCandidate]
  dsimp only [pDigest] at hcut
  rw [hcut, VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega), pReduction_orOne]

/-- Shaping and the even-modulus reduction leave an odd, positive candidate
strictly below the requested output width. The lower-width guard is separate. -/
theorem pCandidate_shape {l n : Nat} (hl : 2 ≤ l)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash n bs).length = n)
    (q : Nat) (seed : List Byte) (offset : Nat) :
    (Spec.Dsa.pCandidate l n q seed offset) % 2 = 1 ∧
      0 < Spec.Dsa.pCandidate l n q seed offset ∧ Spec.Dsa.pCandidate l n q seed offset < 2 ^ l := by
  rw [pCandidate_shaped hl hlen q seed offset]
  have shape := VG.Proof.Ffdh.ParameterCandidate.candidate_shape hl
    (contributions n (pDigest n seed offset) ((l - 1) / n + 1))
  exact ⟨pReduction_odd _ _, (pReduction_le shape.1).1,
    Nat.lt_of_le_of_lt (pReduction_le shape.1).2 shape.2.2⟩

/-- Taking only the bytes needed for the candidate before shaping is
identical to shaping the full radix assembly. -/
theorem candidateOf_mod_width {l width : Nat} (hl : 1 ≤ l) (hw : l ≤ width) (x : Nat) :
    Spec.Ffdh.candidateOf l (x % 2 ^ width) = Spec.Ffdh.candidateOf l x := by
  rw [VG.Proof.Ffdh.ParameterCandidate.candidate_low_high hl,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high hl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

end VG.Proof.Dsa.Generation
