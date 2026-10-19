module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailCT

/-! # Controller-tail framing and the exact public continuation decision -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem searchTail_ready {limit stride : Nat} (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {p : SearchControlPublic} {s : State} (h : SearchAdvanceBefore limit stride p s) :
    WP isa (.seq (.block pSearchStatusCmp)
      (.seq (.ite .e (pSearchAdvance limit stride) (.block [])) (.block pSearchStatusCmp))) s fun t =>
      SearchControlCompared (p.next limit) t ∧ Outside p.B 0 24 s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  refine WP.seq (WP.mono (searchStatusCmp_ok h.1.1 p.statusBound h.1.2)
    fun u ⟨uz, um, uk⟩ => ?_)
  have ctrl := h.1.1.congr um uk
  have before : SearchTailCompared limit stride p u := ⟨⟨⟨ctrl, um ▸ h.1.2⟩, h.2⟩, uz⟩
  by_cases retry : p.status = 3
  · refine WP.seq (WP.ite true (by simp [eval, uz, retry]) (fun _ => ?_) (fun he => Bool.noConfusion he))
    have ctrl' : SearchControl p.B p.counter stride u := by rw [← h.2.2]; exact ctrl
    refine WP.mono (searchAdvance_ok ctrl' h.2.1 hl hs) fun v ⟨vc, vs, vf, vk⟩ => ?_
    have next : SearchControlBefore (p.next limit) v := by
      simpa only [SearchControlBefore, SearchControlPublic.next, retry, ite_true, h.2.2] using And.intro vc vs
    refine WP.mono (searchStatusCmp_ok next.1 (p.next limit).statusBound next.2)
      fun t ⟨tz, tm, tk⟩ => ?_
    refine ⟨⟨⟨next.1.congr tm tk, tm ▸ next.2⟩, tz⟩, ?_, ?_⟩
    · simpa only [tm, um] using vf
    · exact ((uk.trans vk).trans tk).mono (by decide)
  · refine WP.seq (WP.ite false (by simp [eval, uz, retry]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_))
    have next := searchTail_stop before (by simp [eval, uz, retry])
    refine WP.mono (searchStatusCmp_ok next.1 (p.next limit).statusBound next.2)
      fun t ⟨tz, tm, tk⟩ => ?_
    refine ⟨⟨⟨next.1.congr tm tk, tm ▸ next.2⟩, tz⟩, ?_, (uk.trans tk).mono (by decide)⟩
    rw [tm, um]; exact Outside.refl _ _ _ _

end VG.Proof.Dsa.X86_64.Generation
