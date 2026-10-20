module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCT

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCopyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Constant time of the complete p-candidate hash sequence -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem hashStep_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (Impl.Dsa.X86_64.Generation.pHashOne G len count k)
      (Two (ContributionBefore n H (k + 1) len count)) := by
  refine two_post (pHashOne_ct hG n hn H hmatch hsize k len count k hlen hc hk) ?_
  intro p s h
  obtain ⟨⟨W, hw, hs, hf⟩, he⟩ := h
  have hd' : G.D = p.plan.len := hd.trans he.1.symm
  have hk' : k ≤ p.plan.count := by rw [he.2]; exact hk
  have step := hashStep_ok (p := p.plan.withWords W hw) hG hmatch hsize hd' hk' hs
  rw [show (p.plan.withWords W _).len = len from he.1,
    show (p.plan.withWords W _).count = count from he.2] at step
  exact WP.mono step fun t ⟨ht, _, wr, _, _⟩ =>
    ⟨⟨W, hw, ht, hf.congr (ht.layout.rsp.trans hs.layout.rsp.symm) wr⟩, he⟩

theorem hashPrefix_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count + 1) :
    RelCT isa (Two (ContributionBefore n H 0 len count))
      (Impl.Dsa.X86_64.Generation.pHashPrefix G len count k)
      (Two (ContributionBefore n H k len count)) := by
  induction k with
  | zero => exact RelCT.block_nil (fun _ _ h => h)
  | succ k ih =>
    exact RelCT.seq (ih (by omega)) (hashStep_ct hG n hn H hmatch hsize len count k hlen hd hc (by omega))

theorem pHashes_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len) (hc : count ≤ 11) :
    RelCT isa (Two (ContributionBefore n H 0 len count))
      (Impl.Dsa.X86_64.Generation.pHashes G len count)
      (Two (ContributionBefore n H (count + 1) len count)) :=
  hashPrefix_ct hG n hn H hmatch hsize len count (count + 1) hlen hd hc (Nat.le_refl _)

end VG.Proof.Dsa.X86_64.Generation
