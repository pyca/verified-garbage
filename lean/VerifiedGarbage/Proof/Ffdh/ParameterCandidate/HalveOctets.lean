module
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Balancing
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter candidates: halving a big-endian encoding -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Proof.Bignum

/-- One shifted byte, with its predecessor's low bit as carry. -/
def halfByte (carry : Nat) (b : Byte) : Byte := BitVec.ofNat 8 (b.toNat / 2 + 128 * carry)

/-- The byte recurrence used to form the Sophie Germain candidate. -/
def halfOctets (carry : Nat) : List Byte → List Byte
  | [] => []
  | b :: bs => halfByte carry b :: halfOctets (b.toNat % 2) bs

theorem halfOctets_length (carry : Nat) (bs : List Byte) : (halfOctets carry bs).length = bs.length := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [halfOctets, List.length_cons, ih]

theorem halfByte_val {carry : Nat} (hc : carry ≤ 1) (b : Byte) :
    (halfByte carry b).toNat = b.toNat / 2 + 128 * carry := by
  have hb := b.isLt
  simp only [halfByte, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- A carry of zero divides the encoded integer by two. A carry of one
prepends one significant bit before the same shift. -/
theorem halfOctets_value (bs : List Byte) {carry : Nat} (hc : carry ≤ 1) :
    Spec.Rsa.os2ip (halfOctets carry bs) = (carry * 256 ^ bs.length + Spec.Rsa.os2ip bs) / 2 := by
  induction bs generalizing carry with
  | nil =>
    simp only [halfOctets, Spec.Rsa.os2ip, List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
    omega
  | cons b bs ih =>
    rw [halfOctets, os2ip_cons, halfOctets_length, halfByte_val hc, ih (by omega), os2ip_cons]
    simp only [List.length_cons]
    have he : carry * 256 ^ (bs.length + 1) + (b.toNat * 256 ^ bs.length + Spec.Rsa.os2ip bs) =
        (b.toNat % 2 * 256 ^ bs.length + Spec.Rsa.os2ip bs) +
          2 * ((b.toNat / 2 + 128 * carry) * 256 ^ bs.length) := by
      rw [Nat.pow_succ]
      calc
        _ = (carry * 256 + b.toNat) * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
          simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = (2 * (b.toNat / 2 + 128 * carry) + b.toNat % 2) * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
          congr 2
          omega
        _ = _ := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [he, Nat.add_mul_div_left _ _ (by decide)]
    exact Nat.add_comm _ _

theorem halfOctets_zero (bs : List Byte) :
    Spec.Rsa.os2ip (halfOctets 0 bs) = Spec.Rsa.os2ip bs / 2 := by
  simpa only [Nat.zero_mul, Nat.zero_add] using halfOctets_value bs (by decide : 0 ≤ 1)

/-- The incoming bit at a byte position; position zero takes the supplied carry. -/
def carryAt (carry : Nat) (bs : List Byte) (j : Nat) : Nat :=
  if j = 0 then carry else (bs[j - 1]?.getD 0).toNat % 2

theorem carryAt_le {carry : Nat} (hc : carry ≤ 1) (bs : List Byte) (j : Nat) : carryAt carry bs j ≤ 1 := by
  unfold carryAt
  split
  · exact hc
  · omega

theorem carryAt_next (carry : Nat) {bs : List Byte} {j : Nat} (hj : j < bs.length) :
    carryAt carry bs (j + 1) = bs[j].toNat % 2 := by
  simp only [carryAt, Nat.add_one_ne_zero, ite_eq_right_iff, Nat.add_sub_cancel,
    List.getElem?_eq_getElem hj, Option.getD_some]
  simp

theorem halfOctets_get (carry : Nat) {bs : List Byte} {j : Nat} (hj : j < bs.length) :
    (halfOctets carry bs)[j]'(by rw [halfOctets_length]; exact hj) = halfByte (carryAt carry bs j) bs[j] := by
  induction bs generalizing carry j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [halfOctets, List.getElem_cons_succ]
      rw [ih (b.toNat % 2) (by simp only [List.length_cons] at hj; omega)]
      cases j with
      | zero => rfl
      | succ j => simp [carryAt]

end VG.Proof.Ffdh.ParameterCandidate
