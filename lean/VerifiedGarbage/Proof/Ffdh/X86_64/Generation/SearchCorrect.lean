module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchStart
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoop
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchFinish
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSemantics
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.GenerationBounds

/-! # Complete native parameter-generation correctness -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.Ffdh.Generation
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem initial_search_result {p : SearchPublic} {s : State} (h : SearchInput p s) :
    searchResult s = searchTail p 0 p.remaining := by
  cases h.2
  simp only [searchResult, searchTail, searchOfState, SearchPublic.c, candidateOfState,
    List.drop_zero, consume_zero]

theorem returned_post {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hr : SearchReturned p (searchResult s) t) : searchPost s t := by
  cases h.2
  simp only [SearchReturned, SearchOutput, searchPost, searchOfState, SearchPublic.c,
    candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr ⊢
  cases he : searchResult s <;> simpa only [he] using hr

theorem search_correct_ok (v : RoundImpl) {s : State} (h : searchPre s) :
    WP isa (code (candidateCode v)) s fun t => searchPost s t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  unfold code
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (search_start hp) fun u hu => ?_)
  have hinv : SearchInvariant p s (searchResult s) (p.remaining + 1) u :=
    ⟨0, p.remaining, rfl, hu, initial_search_result hp⟩
  refine WP.seq (WP.mono (search_loop v hinv) fun t ht => ?_)
  refine WP.mono (search_finish ht) fun q ⟨hr, hg, hrd, hwr⟩ => ?_
  exact ⟨returned_post hp hr, hg, hrd, hwr⟩

end VG.Proof.Ffdh.X86_64.Generation
