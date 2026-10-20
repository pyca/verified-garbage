module

public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Dsa.Arithmetic
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Connect the existing byte scan to the sampler's mathematical draw width. -/
@[expose] public section
namespace VG.Proof.Dsa
open VG

theorem random_drawBytes_scan (bs : List Byte) :
    Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE bs) = (significant bs).1 := by
  unfold Spec.Dsa.Random.drawBytes
  rw [significant_bits]
  by_cases hz : (significant bs).1 = 0
  · simp only [hz, ite_true]
  · rw [ite_eq_right hz]
    have hb : (significant bs).2.toNat ≠ 0 := by
      intro he
      exact hz ((significant_nonzero bs).mpr (BitVec.eq_of_toNat_eq he))
    have hlo : (significant bs).2.toNat.log2 < 8 :=
      (Nat.log2_lt hb).mpr (significant bs).2.isLt
    omega

/-- Masking low bits in a byte is reduction modulo the corresponding power
of two; importantly it is not reduction modulo the subgroup order. -/
theorem random_mask_byte (b : Byte) (bits : Nat) (hbits : bits ≤ 8) :
    (b &&& BitVec.ofNat 8 (2 ^ bits - 1)).toNat = b.toNat % 2 ^ bits := by
  have hp : 2 ^ bits ≤ 256 := Nat.pow_le_pow_right (by decide) hbits
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

private theorem mod_scaled_add (a d m c : Nat) (hd : 0 < d) (hc : c < m) :
    (a * m + c) % (d * m) = (a % d) * m + c := by
  have hr := Nat.mod_lt a hd
  have hb := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hb
  have he : a * m + c = ((a % d) * m + c) + (d * m) * (a / d) := by
    calc
      a * m + c = (a % d + d * (a / d)) * m + c :=
        congrArg (fun x => x * m + c) (Nat.mod_add_div a d).symm
      _ = _ := by rw [Nat.add_mul]; ac_rfl
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Masking the leading byte implements truncation of a big-endian draw. -/
theorem random_mask_decode (b : Byte) (bs : List Byte) (bits : Nat) (hbits : bits ≤ 8) :
    Spec.Dsa.decodeBE ((b &&& BitVec.ofNat 8 (2 ^ bits - 1)) :: bs) =
      Spec.Dsa.decodeBE (b :: bs) % (2 ^ bits * 256 ^ bs.length) := by
  rw [decodeBE_os2ip, decodeBE_os2ip, VG.Proof.RsaPss.os2ip_cons',
    VG.Proof.RsaPss.os2ip_cons', random_mask_byte b bits hbits]
  exact (mod_scaled_add b.toNat (2 ^ bits) (256 ^ bs.length) (Spec.Rsa.os2ip bs)
    (Nat.pow_pos (by decide)) (VG.Proof.Rsa.lt_of_os2ip bs)).symm

/-- A full-width random draw is reduced by masking only its leading byte. -/
theorem random_candidate_mask (qBytes : List Byte) (b : Byte) (bs : List Byte)
    (hw : bs.length + 1 = (significant qBytes).1) :
    Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes) (b :: bs) =
      Spec.Dsa.decodeBE ((b &&& BitVec.ofNat 8
        (2 ^ ((significant qBytes).2.toNat.log2 + 1) - 1)) :: bs) := by
  have hn : (significant qBytes).1 ≠ 0 := by omega
  have hb : (significant qBytes).2.toNat ≠ 0 := by
    intro he
    exact hn ((significant_nonzero qBytes).mpr (BitVec.eq_of_toNat_eq he))
  have hbits : (significant qBytes).2.toNat.log2 + 1 ≤ 8 := by
    have h := (Nat.log2_lt hb).mpr (significant qBytes).2.isLt
    omega
  rw [random_mask_decode b bs _ hbits, Spec.Dsa.Random.candidate,
    significant_bits, ite_eq_right hn]
  have he : 8 * ((significant qBytes).1 - 1) + (significant qBytes).2.toNat.log2 + 1 =
      8 * bs.length + ((significant qBytes).2.toNat.log2 + 1) := by omega
  rw [he, Nat.pow_add, Nat.pow_mul]
  rw [show 2 ^ (8 : Nat) = 256 from rfl, Nat.mul_comm]

private theorem bitLength_gt_one (n : Nat) : 1 < n ↔ 1 < Spec.Dsa.bitLength n := by
  by_cases hz : n = 0
  · simp [hz, Spec.Dsa.bitLength]
  · rw [Spec.Dsa.bitLength, ite_eq_right hz]
    have hlog : 1 ≤ n.log2 ↔ 2 ≤ n := Nat.le_log2 hz
    omega

/-- The two public checks in `prepare` reject exactly q=0 and q=1. -/
theorem random_valid_scan (bs : List Byte) :
    1 < Spec.Dsa.decodeBE bs ↔
      (significant bs).1 ≠ 0 ∧ ((significant bs).1 ≠ 1 ∨ (significant bs).2.toNat ≠ 1) := by
  rw [bitLength_gt_one, significant_bits]
  by_cases hw : (significant bs).1 = 0
  · simp [hw]
  · rw [ite_eq_right hw]
    have hb : (significant bs).2.toNat ≠ 0 := by
      intro he
      exact hw ((significant_nonzero bs).mpr (BitVec.eq_of_toNat_eq he))
    have hlog : 1 ≤ (significant bs).2.toNat.log2 ↔ 2 ≤ (significant bs).2.toNat := Nat.le_log2 hb
    omega

theorem random_valid_scan_ge (bs : List Byte) :
    1 < Spec.Dsa.decodeBE bs ↔ 2 ≤ (significant bs).1 ∨ 2 ≤ (significant bs).2.toNat := by
  rw [random_valid_scan]
  by_cases hw : (significant bs).1 = 0
  · have hb := (significant_nonzero bs).mp hw
    simp [hw, hb]
  · have hb : (significant bs).2.toNat ≠ 0 := by
      intro he
      exact hw ((significant_nonzero bs).mpr (BitVec.eq_of_toNat_eq he))
    omega

/-- The range check skips only leading zero bytes of the public modulus. -/
theorem random_significant_drop (bs : List Byte) :
    Spec.Dsa.decodeBE (bs.drop (bs.length - (significant bs).1)) = Spec.Dsa.decodeBE bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases hb : b = 0
    · subst b
      rw [significant, ite_eq_left rfl, List.length_cons]
      have he : bs.length + 1 - (significant bs).1 = (bs.length - (significant bs).1) + 1 := by
        have := significant_fits bs
        omega
      rw [he, List.drop_succ_cons, decodeBE_zero_cons]
      exact ih
    · rw [significant, ite_eq_right hb]
      simp only [List.length_cons, Nat.sub_self, List.drop_zero]

theorem random_significant_drop_length (bs : List Byte) :
    (bs.drop (bs.length - (significant bs).1)).length = (significant bs).1 := by
  rw [List.length_drop]
  have := significant_fits bs
  omega

end VG.Proof.Dsa
