module

public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # DSA's seed-hash candidate uses the existing verified byte shaping

Setting the digest's most and least significant bits implements FIPS 186-4
A.1.1.2 steps 5–6 exactly. The same byte operations already shape FFDH
candidates; only their input, the seed hash, differs.
-/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG
open VG.Proof.Ffdh.ParameterCandidate

theorem or_one_value (x : Nat) : x ||| 1 = x + 1 - x % 2 := by
  have hd : (x ||| 1) / 2 = x / 2 := by rw [Nat.or_div_two]; simp
  have hm : (x ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
  omega

/-- DSA's arithmetic definition and the shared byte shaper agree. -/
theorem qCandidate_eq_shaped {n : Nat} (hn : 2 ≤ n) (seed : List Byte) :
    Spec.Dsa.qCandidate n seed = Spec.Ffdh.candidateOf n (Spec.Dsa.decodeBE (Spec.Dsa.seedHash n seed)) := by
  rw [candidate_low_high (by omega), or_one_value]
  have he : 2 ^ (n - 1) % 2 = 0 := by
    rw [show n - 1 = n - 2 + 1 by omega, Nat.pow_succ, Nat.mul_mod]
    simp
  unfold Spec.Dsa.qCandidate
  simp only [Nat.add_mod, he, Nat.add_zero, Nat.mod_mod]
  omega

theorem qCandidate_shape {n : Nat} (hn : 2 ≤ n) (seed : List Byte) :
    (Spec.Dsa.qCandidate n seed) % 2 = 1 ∧
      2 ^ (n - 1) ≤ Spec.Dsa.qCandidate n seed ∧ Spec.Dsa.qCandidate n seed < 2 ^ n := by
  rw [qCandidate_eq_shaped hn]
  exact candidate_shape hn _

theorem qCandidate_bitLength {n : Nat} (hn : 2 ≤ n) (seed : List Byte) :
    Spec.Dsa.bitLength (Spec.Dsa.qCandidate n seed) = n :=
  (bitLength_iff_bounds (by omega)).mpr (qCandidate_shape hn seed).2

/-- The concrete digest bytes after the two endpoint writes. -/
theorem qCandidate_octets {n : Nat} (hn : 2 ≤ n) (seed : List Byte)
    (hlen : 8 * (Spec.Dsa.seedHash n seed).length = n) :
    Spec.Dsa.decodeBE (shapedOctets (Spec.Dsa.seedHash n seed) 7) = Spec.Dsa.qCandidate n seed := by
  have hne : Spec.Dsa.seedHash n seed ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil, Nat.mul_zero] at hlen
    omega
  rw [decodeBE_os2ip, shapedOctets_value hne (by decide) (show n = _ by
    have := List.length_pos_iff.mpr hne
    omega), qCandidate_eq_shaped hn, decodeBE_os2ip]

end VG.Proof.Dsa.Generation
