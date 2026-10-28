module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.ByteWords

/-! # `vg_rsa_keygen_inverse`'s numbers are the workspace's little-endian words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.Mont

theorem os2ip_snoc (l : List Byte) (b : Byte) : Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bytesAt_succ (m : Mem) (a : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m a (n + 1) = m a :: Spec.Rsa.bytesAt m (a + 1) n := by
  unfold Spec.Rsa.bytesAt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega

/-- The octets at `a`, least significant first, are the value of the little-endian read. -/
theorem os2ip_reverse_bytesAt (m : Mem) : ∀ (n : Nat) (a : Addr),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a n).reverse = (m.read a n).toNat
  | 0, _ => rfl
  | n + 1, a => by
    rw [bytesAt_succ, List.reverse_cons, os2ip_snoc, os2ip_reverse_bytesAt m n (a + 1), read_toNat_succ]
    omega

theorem inverseNum_eq (m : Mem) (ws : Addr) (len j : Nat) :
    Spec.RsaKeyGen.inverseNum m ws len j =
      val32 m ws (160 + j * (Spec.RsaKeyGen.inverseBytes len + 8)) (2 * ((len + 7) / 8)) := by
  unfold Spec.RsaKeyGen.inverseNum
  rw [os2ip_reverse_bytesAt, show Spec.RsaKeyGen.inverseBytes len = 4 * (2 * ((len + 7) / 8)) by
    unfold Spec.RsaKeyGen.inverseBytes; omega]
  exact VG.Proof.Bignum.read_eq_val32 m ws _ _

end VG.Proof.RsaKeyGen
