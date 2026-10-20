module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequenceCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT

/-! Public addressing for shaping the full-width p candidate. -/
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
