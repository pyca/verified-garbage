module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps

/-! # The two public integer fields of an implicit-rejection PRF message -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc
open VG

def prfMessage (i : Nat) (label : List Byte) (length : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ label ++ Spec.Rsa.i2osp (8 * length) 2

theorem prfMessage_length (i : Nat) (label : List Byte) (length : Nat) :
    (prfMessage i label length).length = label.length + 4 := by
  simp only [prfMessage, List.length_append, i2osp_length]
  omega

theorem i2osp_two_lt {i : Nat} (hi : i < 256) : Spec.Rsa.i2osp i 2 = [0, BitVec.ofNat 8 i] := by
  rw [i2osp_two, Nat.div_eq_of_lt hi]
  rfl

theorem shr8 {k : Nat} (bound : k ≤ 1024) :
    BitVec.ofNat 32 (8 * k) >>> 8 = BitVec.ofNat 32 (8 * k / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem prfMessage_high (i : Nat) (label : List Byte) (length : Nat) :
    (prfMessage i label length).getD (label.length + 2) 0 = BitVec.ofNat 8 (8 * length / 256) := by
  simp only [prfMessage, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp only [List.length_append, i2osp_length]; omega)]
  rw [List.length_append, i2osp_length, show label.length + 2 - (2 + label.length) = 0 by omega, i2osp_two]
  rfl

theorem prfMessage_low (i : Nat) (label : List Byte) (length : Nat) :
    (prfMessage i label length).getD (label.length + 3) 0 = BitVec.ofNat 8 (8 * length) := by
  simp only [prfMessage, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp only [List.length_append, i2osp_length]; omega)]
  rw [List.length_append, i2osp_length, show label.length + 3 - (2 + label.length) = 1 by omega, i2osp_two]
  rfl

end VG.Proof.RsaPkcs1Enc
