module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntry

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntryTail
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout

/-! # Establish the complete parameter-search invariant -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem searchEntryValues_bound (s : State) : ∀ e ∈ searchEntryValues s, e.1 < 16 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact searchHeadValues_bound s e he
  · exact searchTailValues_bound s e he

theorem search_entry_headers {p : SearchPublic} {s : State} (h : SearchInput p s) :
    Slots (writeController s.mem p.control (searchEntryValues s)) p.control (p.headers 0 p.remaining) := by
  cases h.2
  have hlen : (pcRand s).length = (stackArg s 0).toNat := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hwidth : BitVec.ofNat 64 ((s.gpr .r8).setWidth 32).toNat =
      ((s.gpr .r8).setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  intro e he
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (searchEntryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [searchOfState, candidateOfState, SearchPublic.c, controllerValue,
      searchEntryValues, searchHeadValues, searchTailValues, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, off, BitVec.add_zero, BitVec.ofNat_toNat,
      hwidth, hlen, BitVec.setWidth_eq]
  · simp only [Bignum.word, off, BitVec.add_zero]
  · exact h.1.2.2.2.2.2.2.2.2.2.2.1
  · exact h.1.2.2.2.2.2.2.2.2.2.2.2.1
  · rfl
  · rw [Nat.mul_div_cancel _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_start {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) s fun t => SearchLive p s 0 p.remaining t := by
  refine WP.mono (search_entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hf := writeController_frame s.mem p.control (searchEntryValues s) (searchEntryValues_bound s)
  refine ⟨h, by omega, by omega, k.2.1, k.2.2, ?_, hr, ?_, ?_, ?_, ?_⟩
  · cases h.2
    exact k.gpr (by decide)
  · intro r hcal hne
    exact k.gpr (by cases r <;> simp_all [calleeSaved])
  · rw [hm]
    change word (writeController s.mem p.control (searchEntryValues s)) p.control (8 * 4) = _
    rw [writeController_word _ _ _ (searchEntryValues_bound s) 4 (by decide)]
    rfl
  · have hf' : Frame (s.wr ++ [below (s.gpr .rsp) 160]) s.mem t.mem := by
      rw [hm]
      exact hf.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨inputControl s, List.mem_append_left _ (by rw [h.1.2.2.2.1]; simp), by
          cases h.2; exact fun _ hi => hi⟩
    rw [h.random_frame hf']
    cases h.2
    dsimp only [searchOfState, SearchPublic.c, candidateOfState]
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · rw [hm]
    exact search_entry_headers h

end VG.Proof.Ffdh.X86_64.Generation
