module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedHash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Copy each p hash contribution with a public address trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

def PHashCopyBefore (len count : Nat) (p : PHashPublic) (s : State) : Prop :=
  Lay s p.plan.F p.plan.S ∧ (∃ V W, Rep s.mem p.plan.F p.plan.S V W ∧ W 4 = p.plan.output) ∧
    p.plan.len = len ∧ p.plan.count = count

def PHashCopyReady (len count j : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .x12 = VG.Proof.Bignum.off p.plan.S oDig ∧ s.gpr .x2 = VG.Proof.Bignum.off p.plan.output ((count - j) * len) ∧
    s.gpr .x9 = BitVec.ofNat 64 len

theorem pSeedHash_copyReady {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {H : Spec.Mgf1.Hash} (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = G.D)
    {k len count j : Nat} {p : PHashPublic} {s : State} (hj : j ≤ count)
    (h : ContributionBefore H k len count p s) :
    WP isa (Impl.Dsa.AArch64.Generation.pSeedHash G len j) s (PHashCopyBefore len count p) := by
  obtain ⟨⟨W, hw, hs⟩, hlenEq, hcountEq⟩ := h
  let q := p.plan.withWords W hw
  have hlen := p.plan.size.2.1
  have hjp : j ≤ p.plan.count := by rw [hcountEq]; exact hj
  have hj' : j < 4096 := by omega_using [p.plan.count_le, hjp]
  obtain ⟨V, R⟩ := hs.rep
  have hs := pSeedHash_ok hG hmatch hsize (show p.plan.len < 4096 by omega) hj'
    (show p.plan.offset + j < 2 ^ 32 by omega_using [p.plan.carry, hjp])
    hs.layout R hs.hashArgs q.seed_slot q.wrapped_slot q.offset_slot
    hs.seedRead hs.wrappedWrite (by
      intro i hi l hl he
      have a : Region.Contains ⟨p.plan.seedPtr, p.plan.len⟩ (VG.Proof.Bignum.off p.plan.seedPtr i) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      have b : Region.Contains ⟨p.plan.wrapped, p.plan.len⟩ (VG.Proof.Bignum.off p.plan.wrapped l) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      change VG.Proof.Bignum.off p.plan.seedPtr i = VG.Proof.Bignum.off p.plan.wrapped l at he
      exact p.plan.seed_wrap _ (he ▸ a) b) p.plan.wrapped_sep
  rw [hlenEq] at hs
  exact WP.mono hs fun _ ⟨L, _, _, ⟨V, R'⟩, _⟩ =>
    ⟨L, ⟨V, W, R', q.output_slot⟩, hlenEq, hcountEq⟩

theorem hashCopyArgs_ct (len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) :
    RelCT isa (Two (PHashCopyBefore len count))
      (.block (Impl.Dsa.AArch64.Generation.hashCopyArgs len count j))
      (Two (PHashCopyReady len count j)) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (hc := .block []) (by rfl)) ?_
  intro p s h
  obtain ⟨V, W, R, hout⟩ := h.2.1
  exact WP.mono (hashCopyArgs_ok (j := j) hlen hc h.1 R hout)
    fun _ ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩

theorem pHashOne_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (k len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) (hj : j ≤ count) :
    RelCT isa (Two (ContributionBefore H k len count))
      (Impl.Dsa.AArch64.Generation.pHashOne G len count j) (fun _ _ => True) := by
  refine RelCT.seq (two_post (pSeedHash_ct hG H k len count j hlen hj (by omega))
    (fun _ _ h => pSeedHash_copyReady hG hmatch hsize hj h))
    (RelCT.seq (hashCopyArgs_ct len count j hlen hc) ?_)
  exact two_taint [.x12, .x2, .x9] (by
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
