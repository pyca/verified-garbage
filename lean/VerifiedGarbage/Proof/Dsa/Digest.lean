module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # DSA digest truncation for byte-aligned subgroup sizes -/

@[expose] public section

namespace VG.Proof.Dsa

/-- Concatenating big-endian byte strings appends base-256 digits. -/
theorem decodeBE_append (a b : List VG.Byte) :
    Spec.Dsa.decodeBE (a ++ b) =
      Spec.Dsa.decodeBE a * 256 ^ b.length + Spec.Dsa.decodeBE b := by
  unfold Spec.Dsa.decodeBE
  rw [List.foldl_append, VG.Proof.Bignum.os2ip_foldl]
  rfl

/-- Right-shifting by the discarded byte count is exactly prefix decoding,
including short and empty digests. -/
theorem decodeBE_prefix (bytes : List VG.Byte) (n : Nat) :
    Spec.Dsa.decodeBE bytes / 256 ^ (bytes.length - n) = Spec.Dsa.decodeBE (bytes.take n) := by
  have split := congrArg Spec.Dsa.decodeBE (List.take_append_drop n bytes)
  rw [decodeBE_append, List.length_drop] at split
  rw [← split, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt, Nat.zero_add]
  rw [decodeBE_os2ip, ← List.length_drop]
  exact VG.Proof.Bignum.os2ip_lt _

/-- The implementation may read min(digest_len, subgroup_bytes) bytes.
Every supported DSA subgroup has a byte-aligned bit length. -/
theorem digestScalar_prefix (q n : Nat) (digest : List VG.Byte)
    (hq : Spec.Dsa.bitLength q = 8 * n) :
    Spec.Dsa.digestScalar q digest = Spec.Dsa.decodeBE (digest.take n) := by
  unfold Spec.Dsa.digestScalar
  rw [hq, Nat.shiftRight_eq_div_pow, ← Nat.mul_sub, ← VG.Proof.Bignum.pow256_eq]
  exact decodeBE_prefix digest n

/-- DSA and RSA emit the same fixed-width big-endian bytes. -/
theorem encodeBE_i2osp (n x : Nat) : Spec.Dsa.encodeBE n x = Spec.Rsa.i2osp x n := by
  unfold Spec.Dsa.encodeBE Spec.Rsa.i2osp
  apply congrArg (List.map · (List.range n))
  funext i
  rw [Nat.shiftRight_eq_div_pow, ← VG.Proof.Bignum.pow256_eq]

end VG.Proof.Dsa
