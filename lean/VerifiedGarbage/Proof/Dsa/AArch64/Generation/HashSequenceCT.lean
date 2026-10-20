module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCT

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCopyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Constant time of the complete p-candidate hash sequence -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem hashStep_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count) :
    RelCT isa (Two (ContributionBefore H k len count))
      (Impl.Dsa.AArch64.Generation.pHashOne G len count k)
      (Two (ContributionBefore H (k + 1) len count)) := by
  refine two_post (pHashOne_ct hG H hmatch hsize k len count k hlen hc hk) ?_
  intro p s h
  obtain ⟨⟨W, hw, hs⟩, he⟩ := h
  have hd' : G.D = p.plan.len := hd.trans he.1.symm
  have hk' : k ≤ p.plan.count := by rw [he.2]; exact hk
  have step := hashStep_ok (p := p.plan.withWords W hw) hG hmatch hsize hd' hk' hs
  rw [show (p.plan.withWords W _).len = len from he.1,
    show (p.plan.withWords W _).count = count from he.2] at step
  exact WP.mono step fun t ⟨ht, _, _⟩ => ⟨⟨W, hw, ht⟩, he⟩

theorem hashPrefix_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count + 1) :
    RelCT isa (Two (ContributionBefore H 0 len count))
      (Impl.Dsa.AArch64.Generation.pHashPrefix G len count k)
      (Two (ContributionBefore H k len count)) := by
  induction k with
  | zero => exact RelCT.block_nil (fun _ _ h => h)
  | succ k ih =>
    exact RelCT.seq (ih (by omega)) (hashStep_ct hG H hmatch hsize len count k hlen hd hc (by omega))

theorem pHashes_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len) (hc : count ≤ 11) :
    RelCT isa (Two (ContributionBefore H 0 len count))
      (Impl.Dsa.AArch64.Generation.pHashes G len count)
      (Two (ContributionBefore H (count + 1) len count)) :=
  hashPrefix_ct hG H hmatch hsize len count (count + 1) hlen hd hc (Nat.le_refl _)

end VG.Proof.Dsa.AArch64.Generation
