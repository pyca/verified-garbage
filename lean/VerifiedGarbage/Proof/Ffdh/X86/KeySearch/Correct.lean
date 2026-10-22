module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Finish
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Loop
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Classify

/-! # The key search against its contract (x86)

The entry, the loop from its first state and the finish run the search from
the tape's start (`operation_ok`), which is `keySearch`; so the code meets
`vg_ffdh_generate_key_search`'s contract (`correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Spec.Ffdh
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The search the contract specifies. -/
abbrev searchOf (o : State) : KeySearchResult :=
  keySearch (ofState o).a (ofState o).len ⟨(ofState o).keys, (ofState o).scalars⟩ (randOf o)

theorem tail_zero (o : State) :
    Same ((ofState o).tail (randOf o) 0 (ofState o).keys (ofState o).scalars) (searchOf o) := by
  simp only [Same, KPub.tail, keyTail, after, List.drop_zero, Nat.zero_add, and_self]

theorem operation_ok {o : State} (A : KeySearchABI o) :
    WP isa Impl.Ffdh.X86.KeySearch.code o (Fin o (searchOf o)) := by
  unfold Impl.Ffdh.X86.KeySearch.code
  refine WP.seq (WP.mono (entry_ok A) fun s hs => ?_)
  refine WP.seq (WP.mono (loop_ok hs) fun t ht => ?_)
  exact finish_ok (ht.congr (tail_zero o))

theorem correct (s : State) (h : (Spec.Ffdh.keySearchContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.KeySearch.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.keySearchContract abi stack).post s t := by
  obtain ⟨trace, t, E, F⟩ := operation_ok (keySearchABI_of h)
  refine ⟨trace, t, E, ⟨F.saved, F.ret⟩, ?_⟩
  have out := F.output
  unfold Output at out
  sig_post [Spec.Ffdh.keySearchContract, Spec.Ffdh.keySearchSig, abi, argSlots, argVal, argBytes]
  refine ⟨?_, out, F.policy, F.used⟩
  rw [BitVec.setWidth_append_eq_right, F.eax, toNat_ofNat_lt (by have := status_le (searchOf s); omega)]
  rfl

end VG.Proof.Ffdh.X86.KeySearch
