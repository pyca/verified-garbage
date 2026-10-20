module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashPrefix
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashValue

/-! # The native hash suffix determines exactly the specified DSA p candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Bignum VG.Proof.Dsa.Generation
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def ContributionPlan.shapedValue {H : Hash} (G : ContributionPlan) (K : HashOK H) (plen : Nat) : Nat :=
  Spec.Ffdh.candidateOf (8 * plen)
    (contributions (8 * G.seed.length) (fun j => Spec.Dsa.decodeBE (G.digest K j)) (G.count + 1))

theorem hash_shaped_value {H : Hash} {K : HashOK H} {G : ContributionPlan} {s : State}
    (fit : G.hashes.toNat + (G.count + 1) * G.seed.length ≤ 2 ^ 32)
    (hashes : ∀ j ≤ G.count, Spec.Rsa.bytesAt s.mem ((G.output j).setWidth 64) G.seed.length = G.digest K j)
    {plen : Nat} (positive : 0 < plen) (room : plen ≤ (G.count + 1) * G.seed.length) :
    Spec.Ffdh.candidateOf (8 * plen) (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (off (G.hashes.setWidth 64) ((G.count + 1) * G.seed.length - plen)) plen)) = G.shapedValue K plen := by
  have suffix := bytesAt_suffix_value s.mem (G.hashes.setWidth 64) ((G.count + 1) * G.seed.length - plen) plen
  rw [Nat.sub_add_cancel room, hash_complete_value fit hashes, pow256_eq] at suffix
  rw [← suffix, candidateOf_mod_width (by omega) (Nat.le_refl _)]
  rfl

theorem shapedValue_candidate {H : Hash} {K : HashOK H} {G : ContributionPlan} {plen : Nat}
    (positive : 0 < plen) (count : G.count = (8 * plen - 1) / (8 * G.seed.length))
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * G.seed.length) bs)
    (size : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.seed.length) bs).length = 8 * G.seed.length)
    (q : Nat) :
    G.shapedValue K plen + 1 - G.shapedValue K plen % (2 * q) =
      Spec.Dsa.pCandidate (8 * plen) (8 * G.seed.length) q G.seed G.offset := by
  have digest : (fun j => Spec.Dsa.decodeBE (G.digest K j)) = pDigest (8 * G.seed.length) G.seed G.offset := by
    funext j
    simp only [ContributionPlan.digest, pDigest, hash]
  rw [pCandidate_shaped (by omega) size, ContributionPlan.shapedValue, digest, count]
end VG.Proof.Dsa.X86.Generation
