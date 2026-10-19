module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan
public import VerifiedGarbage.Proof.Dsa.Generation.Contributions
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega

/-! # Decode the stored p hashes as their radix contribution sum -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.Generation

theorem hash_prefix_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : AArch64.State}
    (hs : HashState p H (p.count + 1) s) (k : Nat) (hk : k ≤ p.count + 1) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off p.output ((p.count + 1 - k) * p.len)) (k * p.len)) =
      contributions (8 * p.len) (fun j => Spec.Dsa.decodeBE (p.digest H j)) k := by
  induction k with
  | zero => simp [Spec.Rsa.bytesAt, Spec.Dsa.decodeBE, contributions]
  | succ k ih =>
    have hkcount : k ≤ p.count := by omega
    have hoff : off (p.dest k) p.len = off p.output ((p.count + 1 - k) * p.len) := by
      rw [HashPlan.dest, off_off]
      congr 1
      rw [show p.count + 1 - k = p.count - k + 1 by omega, Nat.add_mul, Nat.one_mul]
    have hp : 256 ^ (k * p.len) = 2 ^ (k * (8 * p.len)) := by
      rw [pow256_eq, Nat.mul_left_comm 8 k p.len]
    rw [show (p.count + 1 - (k + 1)) * p.len = (p.count - k) * p.len by congr 1; omega,
      show (k + 1) * p.len = p.len + k * p.len by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm], bytesAt_append]
    change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.dest k) p.len ++
      Spec.Rsa.bytesAt s.mem (off (p.dest k) p.len) (k * p.len)) = _
    rw [hs.hashes k (by omega), VG.Proof.Dsa.decodeBE_append, bytesAt_length, hoff, ih (by omega), hp,
      contributions_succ, Nat.add_comm]

end VG.Proof.Dsa.AArch64.Generation
