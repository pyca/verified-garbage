module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCopyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

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
  have hd' : G.D = p.plan.len := hd.trans h.2.1.symm
  have hk' : k ≤ p.plan.count := by rw [h.2.2]; exact hk
  have hw := hashStep_ok hG hmatch hsize hd' hk' h.1.1
  rw [h.2.1, h.2.2] at hw
  exact WP.mono hw fun t ⟨ht, _, wr, _, _⟩ =>
    ⟨⟨ht, h.1.2.congr (ht.layout.rsp.trans h.1.1.layout.rsp.symm) wr⟩, h.2⟩

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
