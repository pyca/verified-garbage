module

public import VerifiedGarbage.Proof.Dsa.Generation.Contributions
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The radix value of stored modulus hash contributions is independent of the target ISA. -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum

theorem stored_hash_prefix_value (m : Mem) (output : Addr) (len count : Nat) (digest : Nat → List Byte)
    (hashes : ∀ j < count + 1, Spec.Rsa.bytesAt m (off output ((count - j) * len)) len = digest j)
    (k : Nat) (bound : k ≤ count + 1) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off output ((count + 1 - k) * len)) (k * len)) =
      contributions (8 * len) (fun j => Spec.Dsa.decodeBE (digest j)) k := by
  induction k with
  | zero => simp [Spec.Rsa.bytesAt, Spec.Dsa.decodeBE, contributions]
  | succ k ih =>
    have next : off (off output ((count - k) * len)) len = off output ((count + 1 - k) * len) := by
      rw [off_off]
      congr 1
      rw [show count + 1 - k = count - k + 1 by omega, Nat.add_mul, Nat.one_mul]
    have power : 256 ^ (k * len) = 2 ^ (k * (8 * len)) := by
      rw [pow256_eq, Nat.mul_left_comm 8 k len]
    rw [show (count + 1 - (k + 1)) * len = (count - k) * len by congr 1; omega,
      show (k + 1) * len = len + k * len by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm], bytesAt_append]
    rw [hashes k (by omega), VG.Proof.Dsa.decodeBE_append, bytesAt_length, next, ih (by omega), power,
      contributions_succ, Nat.add_comm]

theorem stored_hash_value (m : Mem) (output : Addr) (len count : Nat) (digest : Nat → List Byte)
    (hashes : ∀ j < count + 1, Spec.Rsa.bytesAt m (off output ((count - j) * len)) len = digest j) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m output ((count + 1) * len)) =
      contributions (8 * len) (fun j => Spec.Dsa.decodeBE (digest j)) (count + 1) := by
  simpa [off] using
    stored_hash_prefix_value m output len count digest hashes (count + 1) (Nat.le_refl _)

end VG.Proof.Dsa.Generation
