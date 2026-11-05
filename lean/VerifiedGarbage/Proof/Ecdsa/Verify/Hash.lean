module

public import VerifiedGarbage.Spec.Ecdsa
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.Words
import Mathlib.Tactic.Ring

/-!
# ECDSA verification of the hash function's output: the hash's `len` bytes

Untrusted: everything here is checked by Lean. `vg_ecdsa_<curve>_verify`
takes the hash as the hash function's output (`Instance.verifyHashContract`);
on each target it writes `fixedDigest` of it, `len` bytes, to a buffer, and
runs the verification that takes those `len` bytes (`Instance.verifyContract`)
on them. `fixedDigest` is the hash's leftmost `len` bytes, or, for a shorter
hash, the hash after zero bytes, shifted left by a further 7 bits (`shr1` of
the hash after a zero byte) for a curve whose `n` has 7 bits fewer than `8 len`
(`wide`, P-521). Either way its integer `e` is the hash's
(`hashToInt_fixedDigest`), so the two verifications agree.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify

open VG VG.Proof.Weierstrass VG.Proof.Ecdsa.Rfc6979

/-- The byte of the bits 1–8 of the pair `a b`: `a`'s low bit, then `b`'s
seven high bits. -/
def sh (a b : Byte) : Byte := BitVec.ofNat 8 (a.toNat % 2 * 128 + b.toNat / 2)

/-- The bytes shifted right by one bit, without their last byte: byte `i`
is `sh` of bytes `i` and `i + 1`. -/
def shr1 : List Byte → List Byte
  | a :: b :: r => sh a b :: shr1 (b :: r)
  | _ => []

/-- The `len` bytes whose integer `e` is the hash `H`'s, on a curve whose
`n` has `8 len` bits, or, if `wide`, `8 len - 7`. -/
def fixedDigest (len : Nat) (wide : Bool) (H : List Byte) : List Byte :=
  if len ≤ H.length then H.take len
  else if wide then shr1 (List.replicate (len - H.length) 0 ++ H ++ [0])
  else List.replicate (len - H.length) 0 ++ H

theorem sh_toNat (a b : Byte) : (sh a b).toNat = a.toNat % 2 * 128 + b.toNat / 2 := by
  have hb := b.isLt
  rw [sh, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem length_shr1 : ∀ (a : Byte) (r : List Byte), (shr1 (a :: r)).length = r.length
  | _, [] => rfl
  | a, b :: r => by rw [shr1, List.length_cons, length_shr1 b r, List.length_cons]

theorem ofBytes_cons (b : Byte) (r : List Byte) :
    Spec.Weierstrass.ofBytes (b :: r) = b.toNat * 2 ^ (8 * r.length) + Spec.Weierstrass.ofBytes r := by
  rw [show b :: r = [b] ++ r from rfl, ofBytes_append, ofBytes_single, pow256]

/-- Halving `a P + X` (`X < 2 P`, `P` the place value of `a`'s next byte),
modulo `2 P`... in the form `ofBytes_shr1` needs. -/
theorem half_step (a b P Y Z : Nat) (_ha : a < 256) (hb : b < 256) (hY : Y < P)
    (hZ : Z = (b % 2 * P + Y) / 2) :
    (a % 2 * 128 + b / 2) * P + (b * P + Y) / 2 % P = (a * (256 * P) + (b * P + Y)) / 2 % (256 * P) := by
  have hbP : b % 2 * P ≤ P := by
    have : b % 2 ≤ 1 := by omega
    calc b % 2 * P ≤ 1 * P := Nat.mul_le_mul_right _ this
      _ = P := Nat.one_mul P
  have hZP : Z < P := by omega
  have e1 : b * P + Y = (b % 2 * P + Y) + (b / 2 * P) * 2 := by
    conv => lhs; rw [← Nat.div_add_mod b 2]
    ring
  have e2 : (b * P + Y) / 2 = Z + b / 2 * P := by
    rw [e1, Nat.add_mul_div_right _ _ (by decide), hZ]
  have e3 : (b * P + Y) / 2 % P = Z := by
    rw [e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hZP]
  have e4 : a * (256 * P) + (b * P + Y) =
      (b % 2 * P + Y + ((a % 2 * 128 + b / 2) * P + a / 2 * (256 * P)) * 2) := by
    rw [e1]
    conv => lhs; rw [← Nat.div_add_mod a 2]
    ring
  rw [e3, e4, Nat.add_mul_div_right _ _ (by decide), ← hZ, ← Nat.add_assoc, Nat.add_comm Z,
    Nat.add_mul_mod_self_right]
  refine (Nat.mod_eq_of_lt ?_).symm
  have hs : a % 2 * 128 + b / 2 + 1 ≤ 256 := by omega
  calc (a % 2 * 128 + b / 2) * P + Z < (a % 2 * 128 + b / 2) * P + P := by omega
    _ = (a % 2 * 128 + b / 2 + 1) * P := by rw [Nat.succ_mul]
    _ ≤ 256 * P := Nat.mul_le_mul_right _ hs

/-- `shr1` halves the number, but for its leading byte's bits. -/
theorem ofBytes_shr1 : ∀ (a : Byte) (r : List Byte),
    Spec.Weierstrass.ofBytes (shr1 (a :: r)) = Spec.Weierstrass.ofBytes (a :: r) / 2 % 2 ^ (8 * r.length)
  | _, [] => by simp [shr1, Spec.Weierstrass.ofBytes, Nat.mod_one]
  | a, b :: r => by
    rw [shr1, ofBytes_cons, length_shr1, ofBytes_shr1 b r, sh_toNat, ofBytes_cons a,
      ofBytes_cons b, List.length_cons]
    have hY := ofBytes_lt r
    have hP' : 2 ^ (8 * (r.length + 1)) = 256 * 2 ^ (8 * r.length) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
    rw [hP']
    exact half_step _ _ _ _ _ a.isLt b.isLt hY rfl

theorem ofBytes_replicate_zero (k : Nat) (l : List Byte) :
    Spec.Weierstrass.ofBytes (List.replicate k 0 ++ l) = Spec.Weierstrass.ofBytes l := ofBytes_zeros k l

/-- The integer `e` of `fixedDigest` is the hash's, on a curve whose `n` has
`8 len` bits, or `8 len - 7` if `wide`. -/
theorem hashToInt_fixedDigest {C : Spec.Weierstrass.Curve} {len : Nat} {wide : Bool}
    (hL : 8 * len = Spec.Ecdsa.nBits C + if wide then 7 else 0) (H : List Byte) :
    Spec.Ecdsa.hashToInt C (fixedDigest len wide H) = Spec.Ecdsa.hashToInt C H := by
  have h₁ : Spec.Ecdsa.nBits C ≤ 8 * len := by split at hL <;> omega
  unfold fixedDigest
  by_cases hl : len ≤ H.length
  · simp only [hl, ite_true]
    rw [hashToInt_takeR h₁ (by rw [List.length_take]; omega), List.take_take, Nat.min_self,
      hashToInt_takeR h₁ hl]
  · simp only [hl, ite_false]
    have hs : Spec.Ecdsa.hashToInt C H = Spec.Weierstrass.ofBytes H := by
      rw [Spec.Ecdsa.hashToInt]
      simp only [show 8 * H.length ≤ Spec.Ecdsa.nBits C by split at hL <;> omega, ite_true]
    rw [hs]
    have hH := ofBytes_lt H
    cases wide with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hL ⊢
      rw [Spec.Ecdsa.hashToInt]
      simp only [List.length_append, List.length_replicate,
        show 8 * (len - H.length + H.length) ≤ Spec.Ecdsa.nBits C by omega, ite_true]
      exact ofBytes_replicate_zero _ _
    | true =>
      simp only [ite_true] at hL ⊢
      have hT : List.replicate (len - H.length) (0 : Byte) ++ H ++ [0] =
          (0 : Byte) :: (List.replicate (len - H.length - 1) 0 ++ H ++ [0]) := by
        rw [show len - H.length = (len - H.length - 1) + 1 by omega, List.replicate_succ]
        simp
      have hlen : (List.replicate (len - H.length - 1) (0 : Byte) ++ H ++ [0]).length = len := by
        simp only [List.length_append, List.length_replicate, List.length_singleton]; omega
      have hB : (shr1 ((0 : Byte) :: (List.replicate (len - H.length - 1) 0 ++ H ++ [0]))).length = len := by
        rw [length_shr1, hlen]
      have hv : Spec.Weierstrass.ofBytes (shr1 ((0 : Byte) :: (List.replicate (len - H.length - 1) 0 ++ H ++ [0]))) =
          Spec.Weierstrass.ofBytes H * 128 := by
        rw [ofBytes_shr1, hlen, ofBytes_cons, hlen, List.append_assoc, ofBytes_replicate_zero,
          ofBytes_append, List.length_singleton, ofBytes_single]
        rw [show (0 : Byte).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.pow_one,
          show Spec.Weierstrass.ofBytes H * 256 = Spec.Weierstrass.ofBytes H * 128 * 2 by omega,
          Nat.mul_div_cancel _ (by decide : 0 < 2)]
        refine Nat.mod_eq_of_lt ?_
        have : 2 ^ (8 * H.length) * 128 ≤ 2 ^ (8 * len) := by
          rw [show 8 * len = 8 * H.length + 7 + (8 * (len - H.length) - 7) by omega, Nat.pow_add,
            Nat.pow_add]
          exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
        calc Spec.Weierstrass.ofBytes H * 128 < 2 ^ (8 * H.length) * 128 := Nat.mul_lt_mul_of_pos_right hH (by decide)
          _ ≤ _ := this
      rw [hT, Spec.Ecdsa.hashToInt, hB, hv]
      simp only [show ¬ 8 * len ≤ Spec.Ecdsa.nBits C by omega, ite_false]
      rw [show 8 * len - Spec.Ecdsa.nBits C = 7 by omega, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (by decide)]

end VG.Proof.Ecdsa.Verify
