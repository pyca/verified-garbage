module

public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan

import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.Generation.Contributions
import VerifiedGarbage.Proof.Dsa.Digest
/-! # The stored hash suffix determines exactly the specified p candidate -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/HashValue.lean`, which only this module imported.
section

/-! # Decode the stored p hashes as their radix contribution sum -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.Generation

theorem hash_prefix_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : X86_64.State}
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

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.Generation

theorem hash_complete_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : X86_64.State}
    (hs : HashState p H (p.count + 1) s) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.output ((p.count + 1) * p.len)) =
      contributions (8 * p.len) (fun j => Spec.Dsa.decodeBE (p.digest H j)) (p.count + 1) := by
  simpa [off] using
    hash_prefix_value hs (p.count + 1) (Nat.le_refl _)

theorem hash_shaped_candidate {p : HashPlan} {H : Spec.Mgf1.Hash} {s : X86_64.State}
    (hs : HashState p H (p.count + 1) s) {l plen : Nat}
    (hl : 2 ≤ l) (hlp : l = 8 * plen) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (l - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len) (q : Nat) :
    let x := Spec.Ffdh.candidateOf l (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (off p.output ((p.count + 1) * p.len - plen)) plen))
    x + 1 - x % (2 * q) = Spec.Dsa.pCandidate l (8 * p.len) q p.seed p.offset := by
  have hsuf := bytesAt_suffix_value s.mem p.output ((p.count + 1) * p.len - plen) plen
  rw [Nat.sub_add_cancel hroom, hash_complete_value hs, pow256_eq, ← hlp] at hsuf
  have hdig : (fun j => Spec.Dsa.decodeBE (p.digest H j)) = pDigest (8 * p.len) p.seed p.offset := by
    funext j
    simp only [HashPlan.digest, pDigest, p.seed_len, hhash, Nat.add_assoc]
  dsimp only
  rw [← hsuf, candidateOf_mod_width (by omega) (Nat.le_refl _), hdig,
    pCandidate_shaped hl hsize, hcount]

end VG.Proof.Dsa.X86_64.Generation
