module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Copy each p hash contribution with a public address trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

def PHashCopyBefore (len count : Nat) (p : PHashPublic) (s : State) : Prop :=
  Lay s p.plan.F p.plan.S ∧ (∃ V W, Rep s.mem p.plan.F p.plan.S V W ∧ W 4 = p.plan.output) ∧
    p.plan.len = len ∧ p.plan.count = count

def PHashCopyReady (len count j : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .rsi = off p.plan.S oDig ∧ s.gpr .rdi = off p.plan.output ((count - j) * len) ∧
    s.gpr .rcx = BitVec.ofNat 64 len ∧ s.gpr .rdx = BitVec.ofNat 64 (8 * len)

theorem pSeedHash_copyReady {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {H : Spec.Mgf1.Hash} (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = G.D)
    {n k len count j : Nat} {p : PHashPublic} {s : State} (hj : j ≤ count)
    (h : ContributionBefore n H k len count p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pSeedHash G len j) s (PHashCopyBefore len count p) := by
  obtain ⟨⟨W, hw, hs, _⟩, hlenEq, hcountEq⟩ := h
  let q := p.plan.withWords W hw
  have hlen := p.plan.size.2.1
  have hjp : j ≤ p.plan.count := by rw [hcountEq]; exact hj
  have hj' : j < 2 ^ 31 := by omega_using [p.plan.count_le, hjp]
  obtain ⟨V, R⟩ := hs.rep
  have hs := pSeedHash_ok hG hmatch hsize (show p.plan.len < 2 ^ 31 by omega) hj'
    (show p.plan.offset + j < 2 ^ 32 by omega_using [p.plan.carry, hjp])
    hs.layout R hs.hashArgs q.seed_slot q.wrapped_slot q.offset_slot
    hs.seedRead hs.wrappedWrite (by
      intro i hi l hl he
      have a : Region.Contains ⟨p.plan.seedPtr, p.plan.len⟩ (off p.plan.seedPtr i) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      have b : Region.Contains ⟨p.plan.wrapped, p.plan.len⟩ (off p.plan.wrapped l) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      exact p.plan.seed_wrap _ (he ▸ a) b) p.plan.wrapped_sep
  rw [hlenEq] at hs
  exact WP.mono hs fun _ ⟨L, _, _, _, _, ⟨V, R'⟩, _⟩ =>
    ⟨L, ⟨V, W, R', q.output_slot⟩, hlenEq, hcountEq⟩

theorem hashCopyArgs_ct (len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) :
    RelCT isa (Two (PHashCopyBefore len count))
      (.block (Impl.Dsa.X86_64.Generation.hashCopyArgs len count j))
      (Two (PHashCopyReady len count j)) := by
  refine two_post (two_taint [.rsp] ?_ (hc := .block []) (by rfl)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.1.rsp.trans ht.1.rsp.symm
  · intro p s h
    obtain ⟨V, W, R, hout⟩ := h.2.1
    exact WP.mono (hashCopyArgs_ok (j := j) hlen hc h.1 R hout)
      fun _ ⟨a, b, c, d, _, _⟩ => ⟨a, b, c, d⟩

theorem pHashOne_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (k len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) (hj : j ≤ count) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (Impl.Dsa.X86_64.Generation.pHashOne G len count j) (fun _ _ => True) := by
  refine RelCT.seq (two_post (pSeedHash_ct hG n hn H k len count j hlen hj (by omega))
    (fun _ _ h => pSeedHash_copyReady hG hmatch hsize hj h))
    (RelCT.seq (hashCopyArgs_ct len count j hlen hc) ?_)
  apply VG.Proof.Ffdh.X86_64.ParameterCandidate.witnessCut_ct
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.1.trans ht.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

end VG.Proof.Dsa.X86_64.Generation
