module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSafety
public import VerifiedGarbage.Spec.Ffdh.GenerationContract

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchImplies
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchStart
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSemantics
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchContract
/-! # Verified complete native FFDH parameter generation for every arithmetic backend -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchFinish.lean`, which only this module imported.
section

/-! # Returning a complete native search preserves its output and System V registers -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchReturned (p : SearchPublic) (result : Spec.Ffdh.ParameterSearchResult) (t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = result.status ∧ SearchOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.c.up 1 = [BitVec.ofNat 64 result.used] ∧
    Spec.Rsa.wordsAt t.mem p.control 4 =
      [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.k,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 result.requested]

theorem search_finish {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block finish) s fun t => SearchReturned p result t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = original.gpr reg) ∧ t.rd = original.rd ∧ t.wr = original.wr := by
  refine WP.mono (search_finish_values h) fun t ⟨ha, hr12, hm, k⟩ => ?_
  have hf : Frame [⟨p.c.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have ho : Spec.Rsa.bytesAt t.mem p.c.op p.c.k = Spec.Rsa.bytesAt s.mem p.c.op p.c.k := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.output_used_disjoint)
      (Nat.le_of_lt h.input.length_lt) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.control_used_disjoint) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.2.1.trans h.rd, k.2.2.trans h.wr⟩
  · rw [ha]
    cases result <;> rfl
  · change Spec.Rsa.bytesAt t.mem p.c.op p.c.k = _
    rw [ho]
    exact h.output
  · change [word t.mem p.c.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.c.up (BitVec.ofNat 64 result.used)
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control 0, word t.mem p.control 8, word t.mem p.control 16, word t.mem p.control 24] = _
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
      rfl
    exact he.trans h.policy
  · intro reg hreg
    by_cases he : reg = .r12
    · subst he; exact hr12
    · exact (k.gpr (by cases reg <;> simp_all [calleeSaved])).trans (h.saved reg hreg he)

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchCorrect.lean`, which only this module imported.
section

/-! # Complete native parameter-generation correctness -/

section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchAbi.lean`, which only this module imported.
section

/-! # Complete native parameter generation preserves the System V ABI -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

private theorem search_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : searchPre s) (he : Exec isa (searchCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hrc : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inputControl s) :=
    (h.2.2.2.2.2.1 _ (by simp)).symm
  have hwr := h.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hro, hru, _, hrs, _⟩ := h.1
  have hd := searchCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (searchCode_sp v)) he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    simp only [inputBuffers, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hro, hru, hrs, hrc]
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem search_correct (v : RoundImpl) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (searchCode v) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, hg, _, _⟩ := search_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_exec (searchCode_mx v) he
    ⟨hg, search_return_address v h he⟩, hp⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem search_verified (v : RoundImpl) : Verified target (searchCode v)
    (Spec.Ffdh.parameterSearchContract abi 160) := by
  exact Verified.of_correct (search_correct v) (search_constantTime v) search_implies

end VG.Proof.Ffdh.X86_64.Generation
