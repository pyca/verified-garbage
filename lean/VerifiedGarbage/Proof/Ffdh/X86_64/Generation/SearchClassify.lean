module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchAcceptDone
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRejectStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # The native controller classifies candidate outcomes without host decisions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchClassified (p : SearchPublic) (original : State) (used remaining : Nat) (t : State) : Prop :=
  match searchCandidate p used with
  | none => SearchDone p original (shortResult p used remaining) t
  | some (some prime, rest) => SearchDone p original
      (.accepted prime (used + (p.c.rand.length - used - rest.length))) t
  | some (none, rest) => SearchLive p original (used + (p.c.rand.length - used - rest.length))
      (remaining - 1) t ∧ word t.mem p.control 112 = 4

theorem normalized_status {s t : State} {status : Nat}
    (hs : ((s.gpr .rax).setWidth 32).toNat = status)
    (ht : t.gpr .rax = ((s.gpr .rax).setWidth 32).setWidth 64) :
    t.gpr .rax = BitVec.ofNat 64 status := by
  apply BitVec.eq_of_toNat_eq
  rw [ht, BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]

theorem search_classify {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hr : 0 < remaining)
    (hp : SearchCandidatePost p used s) :
    WP isa classify s (SearchClassified p original used remaining) := by
  unfold classify
  refine WP.seq (WP.mono (candidate_status_guard s) fun u ⟨⟨he, ha, hm⟩, k⟩ => ?_)
  have hu := h.keep k hm (by decide)
  have hs := hp.1
  have hup := hp.used_word
  have hout := hp.2.1
  cases hc : searchCandidate p used with
  | none =>
    rw [hc, Proof.Ffdh.candidateStatus] at hs
    rw [hs] at he
    have hax := normalized_status hs ha
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun v ⟨⟨he2, hm2⟩, k2⟩ => ?_)
    have hv := hu.keep k2 hm2 (by decide)
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    change WP isa short v (fun t => SearchClassified p original used remaining t)
    simp only [SearchClassified, hc]
    apply search_short hv
    rw [hm2, hm]
    simpa only [hc] using hout
  | some pair =>
    obtain ⟨value, rest⟩ := pair
    cases value with
    | some prime =>
      rw [hc, Proof.Ffdh.candidateStatus] at hs
      rw [hs] at he
      refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
      change WP isa (.block accept) u (fun t => SearchClassified p original used remaining t)
      simp only [SearchClassified, hc]
      apply search_accept_done hu
      · rw [hm]
        simpa only [candidateUsed, hc] using hup
      · rw [hm]
        simpa only [hc] using hout
    | none =>
      rw [hc, Proof.Ffdh.candidateStatus] at hs
      rw [hs] at he
      have hax := normalized_status hs ha
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun v ⟨⟨he2, hm2⟩, k2⟩ => ?_)
      have hv := hu.keep k2 hm2 (by decide)
      refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
      change WP isa (.block reject) v (fun t => SearchClassified p original used remaining t)
      simp only [SearchClassified, hc]
      apply search_reject_step hv (Nat.sub_le _ _) hr
      rw [hm2, hm]
      simpa only [candidateUsed, hc] using hup

end VG.Proof.Ffdh.X86_64.Generation
