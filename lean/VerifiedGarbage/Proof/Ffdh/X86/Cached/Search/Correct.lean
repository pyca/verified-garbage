module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Finish
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Entry
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Loop
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Classify

/-! # The key search against its contract (x86)

The entry, the loop from its first state and the finish run the search from
the tape's start (`operation_ok`), which is `vettedKeySearch`; so the code meets
`vg_ffdh_generate_key_search`'s contract (`correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Spec.Ffdh
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The search the contract specifies. -/
abbrev searchOf (o : State) : KeySearchResult :=
  vettedKeySearch (ofState o).a (ofState o).len ⟨(ofState o).keys, (ofState o).scalars⟩ (randOf o)

theorem tail_zero (o : State) :
    Same ((ofState o).tail (randOf o) 0 (ofState o).keys (ofState o).scalars) (searchOf o) := by
  simp only [Same, KPub.tail, keyTail, after, List.drop_zero, Nat.zero_add]
  exact ⟨rfl, rfl⟩

theorem operation_ok {o : State} (A : KeySearchABI o) :
    WP isa Impl.Ffdh.X86.Cached.Search.code o (Fin o (searchOf o)) := by
  unfold Impl.Ffdh.X86.Cached.Search.code
  refine WP.seq (WP.mono (entry_ok A) fun s hs => ?_)
  refine WP.seq (WP.mono (loop_ok hs) fun t ht => ?_)
  exact finish_ok (ht.congr (tail_zero o))

theorem correct (s : State) (h : (Spec.Ffdh.cachedKeySearchContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Cached.Search.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.cachedKeySearchContract abi stack).post s t := by
  obtain ⟨trace, t, E, F⟩ := operation_ok (keySearchABI_of h)
  refine ⟨trace, t, E, ⟨F.saved, F.ret⟩, ?_⟩
  have out := F.output
  unfold Output at out
  sig_post [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, abi, argSlots, argVal, argBytes]
  refine ⟨?_, out, F.policy, F.used⟩
  rw [BitVec.setWidth_append_eq_right, F.eax, toNat_ofNat_lt (by have := status_le (searchOf s); omega)]
  rfl

end VG.Proof.Ffdh.X86.Cached.Search
