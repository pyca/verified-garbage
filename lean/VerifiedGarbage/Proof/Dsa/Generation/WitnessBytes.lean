module

import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.CutOctets
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.ListSnoc

/-! # RSA's blinded witness transformation on big-endian bytes

DSA uses the exact RSA sampler: in-range draws remain uniform; other draws
clear their top bit and set bit 1. Clearing the top byte and updating the
last byte implements this even for the padded 160-bit subgroup modulus.
-/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Ffdh.ParameterCandidate

def lastOr (bs : List Byte) (mask : Byte) : List Byte :=
  bs.take (bs.length - 1) ++ [bs.getD (bs.length - 1) 0 ||| mask]

theorem lastOr_append (bs : List Byte) (b mask : Byte) :
    lastOr (bs ++ [b]) mask = bs ++ [b ||| mask] := by
  simp [lastOr]

theorem lastOr_length {bs : List Byte} (hne : bs ≠ []) (mask : Byte) :
    (lastOr bs mask).length = bs.length := by
  have hp := List.length_pos_iff.mpr hne
  simp only [lastOr, List.length_append, List.length_take, List.length_singleton,
    Nat.min_eq_left (Nat.sub_le bs.length 1)]
  omega

theorem lastOr_value {bs : List Byte} (hne : bs ≠ []) (mask : Byte) :
    Spec.Rsa.os2ip (lastOr bs mask) = Spec.Rsa.os2ip bs ||| mask.toNat := by
  induction bs using VG.List.reverseRecOn with
  | nil => contradiction
  | append_singleton bs b _ =>
    have hlo : b.toNat ||| mask.toNat < 2 ^ 8 := Nat.or_lt_two_pow b.isLt mask.isLt
    rw [lastOr_append, VG.Proof.Rsa.os2ip_snoc, VG.Proof.Rsa.os2ip_snoc, BitVec.toNat_or]
    rw [show (256 : Nat) = 2 ^ 8 by decide,
      Nat.two_pow_add_eq_or_of_lt hlo, Nat.two_pow_add_eq_or_of_lt b.isLt, Nat.or_assoc]

def forcedWitnessBytes (bs : List Byte) : List Byte := lastOr (cutOctets bs 6) 2

theorem forcedWitnessBytes_length {bs : List Byte} (hlen : 2 ≤ bs.length) :
    (forcedWitnessBytes bs).length = bs.length := by
  have hn : bs ≠ [] := by intro h; simp [h] at hlen
  rw [forcedWitnessBytes, lastOr_length (by simp [cutOctets]), cutOctets_length hn]

theorem forcedWitnessBytes_getD {bs : List Byte} {i : Nat}
    (hlen : 2 ≤ bs.length) (hi : i < bs.length) :
    (forcedWitnessBytes bs).getD i 0 =
      if i = bs.length - 1 then bs.getD i 0 ||| 2
      else if i = 0 then bs.getD 0 0 &&& 127 else bs.getD i 0 := by
  have hn : bs ≠ [] := by intro h; simp [h] at hlen
  have hc := cutOctets_length hn 6
  unfold forcedWitnessBytes lastOr
  rw [hc]
  by_cases he : i = bs.length - 1
  · subst i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_take, hc,
      Nat.min_eq_left (Nat.sub_le bs.length 1), Nat.sub_self, List.getElem?_cons_zero,
      ite_true, Nat.lt_irrefl]
    simp [cutOctets, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show bs.length - 2 + 1 < bs.length by omega), show bs.length - 1 = (bs.length - 2) + 1 by omega]
  · have hit : i < bs.length - 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_take, hc,
      Nat.min_eq_left (Nat.sub_le bs.length 1), hit, ite_true, List.getElem?_take, he, ite_false]
    cases i with
    | zero => simp [cutOctets, List.getD_eq_getElem?_getD]
    | succ i => simp [cutOctets, List.getD_eq_getElem?_getD]

theorem forcedWitnessBytes_value {bs : List Byte} (hlen : 2 ≤ bs.length) :
    Spec.Rsa.os2ip (forcedWitnessBytes bs) = (Spec.Rsa.os2ip bs ||| 2) % 2 ^ (8 * bs.length - 1) := by
  have hne : bs ≠ [] := by intro h; simp [h] at hlen
  have hcut : cutOctets bs 6 ≠ [] := by simp [cutOctets]
  have htwo : 2 < 2 ^ (8 * bs.length - 1) := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ 8 * bs.length - 1 by omega)
    omega
  rw [forcedWitnessBytes, lastOr_value hcut, cutOctets_value hne (by decide)
    (show 8 * bs.length - 1 = 8 * (bs.length - 1) + 6 + 1 by omega), Nat.or_mod_two_pow,
    Nat.mod_eq_of_lt htwo]
  rfl

/-- The high padding bytes of a whole-limb draw do not participate in
RSA's witness transformation. In particular, a 24-byte draw for q160
uses its final 20 bytes while still consuming all 24 from the tape. -/
theorem witness_drop_padding (padding bs : List Byte) {w : Nat}
    (hbits : Spec.RsaKeyGen.bitLength (w - 1) = 8 * bs.length) :
    Spec.RsaKeyGen.witness (w - 1) (Spec.Rsa.os2ip (padding ++ bs)) =
      Spec.RsaKeyGen.witness (w - 1) (Spec.Rsa.os2ip bs) := by
  have hmod : Spec.Rsa.os2ip (padding ++ bs) % 2 ^ (8 * bs.length) = Spec.Rsa.os2ip bs := by
    change Spec.Dsa.decodeBE (padding ++ bs) % 2 ^ (8 * bs.length) = Spec.Dsa.decodeBE bs
    rw [← VG.Proof.Bignum.pow256_eq, decodeBE_append, Nat.mul_comm _ (256 ^ bs.length),
      Nat.mul_add_mod, Nat.mod_eq_of_lt (decodeBE_lt bs)]
  have hfit : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
    rw [← VG.Proof.Bignum.pow256_eq]
    exact VG.Proof.Rsa.lt_of_os2ip bs
  simp only [Spec.RsaKeyGen.witness, hbits, hmod, Nat.mod_eq_of_lt hfit]

/-- The byte transform is exactly the forced branch of RSA's sampler. -/
theorem forcedWitnessBytes_spec {bs : List Byte} {w : Nat} (hlen : 2 ≤ bs.length)
    (hbits : Spec.RsaKeyGen.bitLength (w - 1) = 8 * bs.length)
    (hbad : ¬ (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < w - 1)) :
    Spec.RsaKeyGen.witness (w - 1) (Spec.Rsa.os2ip bs) =
      (Spec.Rsa.os2ip (forcedWitnessBytes bs), false) := by
  have hfit : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
    rw [← VG.Proof.Bignum.pow256_eq]
    exact VG.Proof.Rsa.lt_of_os2ip bs
  rw [Spec.RsaKeyGen.witness, hbits, Nat.mod_eq_of_lt hfit, ite_eq_right hbad, forcedWitnessBytes_value hlen]

end VG.Proof.Dsa.Generation
