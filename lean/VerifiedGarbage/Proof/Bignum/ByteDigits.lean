module
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Bytes as radix-256 digits

What reading and writing big-endian numbers a word at a time needs on any
target: byte `i` of a string is a digit of its OS2IP (`os2ip_byte`), byte `j`
of a word is a digit of its value (`extract_nat`), and words with the same
bytes are equal (`eq_of_bytes`).
-/

@[expose] public section

namespace VG.Proof.Bignum.ByteDigits

open VG

/-- An input byte is the corresponding radix-256 digit of OS2IP. -/
theorem os2ip_byte (bs : List Byte) {i : Nat} (hi : i < bs.length) :
    bs[i] = BitVec.ofNat 8 (Spec.Rsa.os2ip bs / 256 ^ (bs.length - 1 - i)) := by
  have h := congrArg (fun xs : List Byte => xs[i]?) (VG.Proof.Rsa.i2osp_os2ip bs)
  simpa [Spec.Rsa.i2osp, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show i < (List.range bs.length).length by simpa using hi)] using h.symm

/-- Extracting a byte of a word is division by its radix-256 position. -/
theorem extract_nat (x : Nat) {j : Nat} (hj : j < 8) :
    (BitVec.ofNat 64 x).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (x / 256 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ (8 * j) * 2 ^ (64 - 8 * j) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [show (256 : Nat) ^ j = 2 ^ (8 * j) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]]

/-- Equality of all eight bytes is equality of words. -/
theorem eq_of_bytes {x y : BitVec 64}
    (h : ∀ j < 8, x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8) : x = y := by
  ext i hi
  have e := congrArg (fun v : Byte => v.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and] at e
  rw [show 8 * (i / 8) + i % 8 = i by omega] at e
  simpa only [BitVec.getLsbD_eq_getElem hi] using e

end VG.Proof.Bignum.ByteDigits
