module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashValue
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The stored hash suffix determines exactly the specified p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.Generation

theorem hash_complete_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : AArch64.State}
    (hs : HashState p H (p.count + 1) s) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.output ((p.count + 1) * p.len)) =
      contributions (8 * p.len) (fun j => Spec.Dsa.decodeBE (p.digest H j)) (p.count + 1) := by
  simpa [off] using
    hash_prefix_value hs (p.count + 1) (Nat.le_refl _)

theorem hash_shaped_candidate {p : HashPlan} {H : Spec.Mgf1.Hash} {s : AArch64.State}
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

end VG.Proof.Dsa.AArch64.Generation
