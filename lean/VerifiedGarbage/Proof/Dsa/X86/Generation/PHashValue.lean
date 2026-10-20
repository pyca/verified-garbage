module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashPrefix
public import VerifiedGarbage.Proof.Dsa.Generation.Contributions
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Native digest ordering equals the specification's radix contribution sum -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Proof.Dsa.Generation VG.Proof.Bignum

theorem contribution_output {G : ContributionPlan} {j : Nat} (hj : j ≤ G.count)
    (fit : G.hashes.toNat + (G.count + 1) * G.seed.length ≤ 2 ^ 32) :
    (G.output j).setWidth 64 = off (G.hashes.setWidth 64) ((G.count - j) * G.seed.length) := by
  apply addr_eq
  have bounds := Nat.mul_le_mul_right G.seed.length (show G.count - j + 1 ≤ G.count + 1 by omega)
  by_cases h : G.seed.length = 0
  · simp only [h, Nat.mul_zero, Nat.add_zero]; exact G.hashes.isLt
  · rw [Nat.add_mul, Nat.one_mul] at bounds
    omega

theorem hash_prefix_value {H : Hash} {K : HashOK H} {G : ContributionPlan} {s : State}
    (fit : G.hashes.toNat + (G.count + 1) * G.seed.length ≤ 2 ^ 32)
    (hashes : ∀ j ≤ G.count, Spec.Rsa.bytesAt s.mem ((G.output j).setWidth 64) G.seed.length = G.digest K j)
    (k : Nat) (hk : k ≤ G.count + 1) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (off (G.hashes.setWidth 64) ((G.count + 1 - k) * G.seed.length)) (k * G.seed.length)) =
      contributions (8 * G.seed.length) (fun j => Spec.Dsa.decodeBE (G.digest K j)) k := by
  induction k with
  | zero => simp [Spec.Rsa.bytesAt, Spec.Dsa.decodeBE, contributions]
  | succ k ih =>
    have dest := contribution_output (G := G) (j := k) (by omega) fit
    have hoff : off ((G.output k).setWidth 64) G.seed.length =
        off (G.hashes.setWidth 64) ((G.count + 1 - k) * G.seed.length) := by
      rw [dest, off_off]
      congr 1
      rw [show G.count + 1 - k = G.count - k + 1 by omega, Nat.add_mul, Nat.one_mul]
    have hp : 256 ^ (k * G.seed.length) = 2 ^ (k * (8 * G.seed.length)) := by
      rw [VG.Proof.Bignum.pow256_eq, Nat.mul_left_comm 8 k G.seed.length]
    rw [show (G.count + 1 - (k + 1)) * G.seed.length = (G.count - k) * G.seed.length by congr 1; omega,
      show (k + 1) * G.seed.length = G.seed.length + k * G.seed.length by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm],
      bytesAt_append, ← dest, hashes k (by omega), VG.Proof.Dsa.decodeBE_append,
      VG.Proof.Bignum.bytesAt_length, hoff, ih (by omega), hp, contributions_succ, Nat.add_comm]

theorem hash_complete_value {H : Hash} {K : HashOK H} {G : ContributionPlan} {s : State}
    (fit : G.hashes.toNat + (G.count + 1) * G.seed.length ≤ 2 ^ 32)
    (hashes : ∀ j ≤ G.count, Spec.Rsa.bytesAt s.mem ((G.output j).setWidth 64) G.seed.length = G.digest K j) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (G.hashes.setWidth 64) ((G.count + 1) * G.seed.length)) =
      contributions (8 * G.seed.length) (fun j => Spec.Dsa.decodeBE (G.digest K j)) (G.count + 1) := by
  simpa [off] using hash_prefix_value fit hashes (G.count + 1) (Nat.le_refl _)
end VG.Proof.Dsa.X86.Generation
