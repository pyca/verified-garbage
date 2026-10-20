module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
public import VerifiedGarbage.Spec.Ffdh

import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import Mathlib.Data.List.Induction
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter candidates: the shaped big-endian encoding -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Proof.Bignum

/-- Keep the first byte's low j bits and set bit j. -/
def topByte (j : Nat) (b : Byte) : Byte :=
  (b &&& BitVec.ofNat 8 (2 ^ j - 1)) ||| BitVec.ofNat 8 (2 ^ j)

def topCut (bs : List Byte) (j : Nat) : List Byte := topByte j (bs.getD 0 0) :: bs.drop 1

theorem topCut_getD (bs : List Byte) (j i : Nat) :
    (topCut bs j).getD i 0 = if i = 0 then topByte j (bs.getD 0 0) else bs.getD i 0 := by
  cases i with
  | zero => rfl
  | succ i => simp [topCut, List.getD_eq_getElem?_getD]

theorem topByte_value {j : Nat} (hj : j < 8) (b : Byte) :
    (topByte j b).toNat = b.toNat % 2 ^ j + 2 ^ j := by
  have hpow : 2 ^ j < 256 := Nat.pow_lt_pow_right (by decide) hj
  simp only [topByte, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ j - 1 < 2 ^ 8 by omega), Nat.mod_eq_of_lt hpow,
    Nat.and_two_pow_sub_one_eq_mod, Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))]

theorem topCut_length {bs : List Byte} (hne : bs ≠ []) (j : Nat) : (topCut bs j).length = bs.length := by
  simp only [topCut, List.length_cons, List.length_drop]
  have := List.length_pos_iff.mpr hne
  omega

/-- The first-byte operation is reduction modulo the lower bits, plus the high bit. -/
theorem topCut_value {bs : List Byte} (hne : bs ≠ []) {j : Nat} (hj : j < 8) :
    Spec.Rsa.os2ip (topCut bs j) =
      Spec.Rsa.os2ip bs % 2 ^ (8 * (bs.length - 1) + j) + 2 ^ (8 * (bs.length - 1) + j) := by
  have hl : 1 ≤ bs.length := List.length_pos_iff.mpr hne
  have hm : (BitVec.ofNat 8 (2 ^ j - 1)).toNat = 2 ^ j - 1 := by
    have hp : 2 ^ j < 256 := Nat.pow_lt_pow_right (by decide) hj
    exact Nat.mod_eq_of_lt (by omega)
  have hc := KeyScalar.cut_value (r := bs) (n := 0) (e := bs.length) (j := j) (by omega) hl (by omega) hm
  simp only [KeyScalar.cut, List.replicate_zero, List.nil_append, os2ip_cons,
    BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, List.length_drop, Nat.zero_add] at hc
  have hp : 2 ^ j * 256 ^ (bs.length - 1) = 2 ^ (8 * (bs.length - 1) + j) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← Nat.pow_add, Nat.add_comm]
  rw [topCut, os2ip_cons, topByte_value hj, List.length_drop, Nat.add_mul, hp]
  omega

/-- The equivalent arithmetic form used by byte-based shaping. -/
theorem candidate_low_high {bits : Nat} (hb : 1 ≤ bits) (x : Nat) :
    VG.Spec.Ffdh.candidateOf bits x = (x % 2 ^ (bits - 1) + 2 ^ (bits - 1)) ||| 1 := by
  unfold VG.Spec.Ffdh.candidateOf
  congr 1
  rw [← Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases he : i = bits - 1
  · simp [he]
  · have hi : (i < bits) = (i < bits - 1) := propext (by omega)
    simp only [hi]

/-- Set the candidate's least significant bit in its last byte. -/
def lastOne (bs : List Byte) : List Byte :=
  bs.take (bs.length - 1) ++ [bs.getD (bs.length - 1) 0 ||| 1]

theorem lastOne_append (bs : List Byte) (b : Byte) : lastOne (bs ++ [b]) = bs ++ [b ||| 1] := by
  simp [lastOne]

theorem lastOne_length {bs : List Byte} (hne : bs ≠ []) : (lastOne bs).length = bs.length := by
  simp only [lastOne, List.length_append, List.length_take, List.length_singleton]
  have := List.length_pos_iff.mpr hne
  omega

theorem lastOne_getD {bs : List Byte} {i : Nat} (hi : i < bs.length) :
    (lastOne bs).getD i 0 = if i + 1 = bs.length then bs.getD i 0 ||| 1 else bs.getD i 0 := by
  by_cases he : i + 1 = bs.length
  · have hi' : i = bs.length - 1 := by omega
    subst hi'
    simp [lastOne, List.getD_eq_getElem?_getD, List.getElem?_append,
      Nat.min_eq_left (Nat.sub_le bs.length 1), he]
  · have hi' : i < bs.length - 1 := by omega
    simp [lastOne, List.getD_eq_getElem?_getD, List.getElem?_append,
      Nat.min_eq_left (Nat.sub_le bs.length 1), hi', hi, he]

private theorem or_low_sum {b : Nat} (hb : b < 256) (a : Nat) :
    (256 * a + b) ||| 1 = 256 * a + (b ||| 1) := by
  have hbo : b ||| 1 < 2 ^ 8 := Nat.or_lt_two_pow hb (by decide)
  rw [show (256 : Nat) = 2 ^ 8 from rfl,
    Nat.two_pow_add_eq_or_of_lt hb, Nat.two_pow_add_eq_or_of_lt hbo, Nat.or_assoc]

theorem lastOne_value {bs : List Byte} (hne : bs ≠ []) :
    Spec.Rsa.os2ip (lastOne bs) = Spec.Rsa.os2ip bs ||| 1 := by
  induction bs using List.reverseRecOn with
  | nil => contradiction
  | append_singleton bs b _ =>
    have hbyte : ∀ b : Byte, Spec.Rsa.os2ip [b] = b.toNat := fun b => by simp [Spec.Rsa.os2ip]
    rw [lastOne_append, KeyScalar.os2ip_append, KeyScalar.os2ip_append]
    simp only [List.length_singleton, Nat.pow_one, hbyte, BitVec.toNat_or,
      show (1 : Byte).toNat = 1 from rfl]
    simpa only [Nat.mul_comm] using (or_low_sum b.isLt (Spec.Rsa.os2ip bs)).symm

/-- The exact encoded candidate emitted by the native byte operations. -/
def shapedOctets (bs : List Byte) (j : Nat) : List Byte := lastOne (topCut bs j)

theorem shapedOctets_value {bs : List Byte} (hne : bs ≠ []) {j bits : Nat} (hj : j < 8)
    (hbits : bits = 8 * (bs.length - 1) + j + 1) :
    Spec.Rsa.os2ip (shapedOctets bs j) = VG.Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip bs) := by
  have hb : 1 ≤ bits := by omega
  rw [shapedOctets, lastOne_value (by simp [topCut]), topCut_value hne hj, candidate_low_high hb]
  rw [hbits, Nat.add_sub_cancel]

/-- The in-place halving pass produces the exact Sophie Germain candidate. -/
theorem shapedOctets_half_value {bs : List Byte} (hne : bs ≠ []) {j bits : Nat} (hj : j < 8)
    (hb : 2 ≤ bits) (hbits : bits = 8 * (bs.length - 1) + j + 1) :
    Spec.Rsa.os2ip (halfOctets 0 (shapedOctets bs j)) =
      (VG.Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip bs) - 1) / 2 := by
  rw [halfOctets_zero, shapedOctets_value hne hj hbits]
  have ho := (candidate_shape hb (Spec.Rsa.os2ip bs)).1
  omega

end VG.Proof.Ffdh.ParameterCandidate
