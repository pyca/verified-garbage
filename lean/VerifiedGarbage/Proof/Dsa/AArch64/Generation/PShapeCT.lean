module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCopyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
/-! Public addressing for shaping the full-width p candidate. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/HashSequenceCT.lean`, which only this module imported.
section

/-! # Constant time of the complete p-candidate hash sequence -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

def PShapeReady (len count plen : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .x2 = p.plan.W 0 ∧
  s.gpr .x12 = VG.Proof.Bignum.off p.plan.output ((count + 1) * len - plen) ∧
  s.gpr .x9 = BitVec.ofNat 64 plen

theorem pShapeArgs_ct (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 4096) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore H k len count))
      (.block (Impl.Dsa.AArch64.Generation.pShapeArgs len count plen))
      (Two (PShapeReady len count plen)) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (hc := .block []) (by rfl)) ?_
  intro p s h
  obtain ⟨⟨W, hw, hs⟩, _⟩ := h
  obtain ⟨V, R⟩ := hs.rep
  exact WP.mono (pShapeArgs_ok hs.layout R (hw 0 (by decide))
    ((hw 4 (by decide)).trans p.plan.output_slot) hn hl)
    fun _ ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩

theorem pShape_ct (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 4096) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore H k len count))
      (Impl.Dsa.AArch64.Generation.pShape len count plen) (fun _ _ => True) := by
  refine RelCT.seq (pShapeArgs_ct H k len count plen hn hl) (qShape_ct ?_)
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.1.trans ht.1.symm
  · exact hs.2.2.trans ht.2.2.symm

theorem pBuild_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count plen : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore H 0 len count))
      (.seq (Impl.Dsa.AArch64.Generation.pHashes G len count)
        (Impl.Dsa.AArch64.Generation.pShape len count plen)) (fun _ _ => True) := by
  refine RelCT.seq (pHashes_ct hG H hmatch hsize len count hlen hd hc)
    (pShape_ct H (count + 1) len count plen ?_ hl)
  rcases hlen with rfl | rfl <;> omega

end VG.Proof.Dsa.AArch64.Generation
