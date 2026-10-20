module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClear
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore

/-! # Exhausted native searches return zero output and a terminal controller -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_exhausted {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa exhausted s (SearchDone p original (.exhausted used)) := by
  unfold exhausted
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (search_terminal h 3) fun u ⟨h0, hq, hs⟩ => ?_
  have hmov : WP isa (.block [.mov .rdi (.reg .r12)]) u fun v =>
      (v.gpr .rdi = p.control ∧ v.mem = u.mem) ∧ Keep [.rdi] u v := by
    refine WP.keep [.rdi] ?_ rfl
    xrun [h0.r12]
  refine WP.mono hmov fun v ⟨⟨hdv, hmv⟩, kv⟩ => ?_
  have hv := h0.keep kv hmv (by decide)
  refine WP.mono (search_clear hv hdv) fun t ⟨ht, hout, hw, _⟩ => ?_
  refine done_of_live ht rfl rfl ?_ ?_ hout
  · have hs' : word v.mem p.control 112 = BitVec.ofNat 64 3 := by rw [hmv]; exact hs
    exact (hw 14 (by decide)).trans hs'
  · have hq' : word v.mem p.control 24 = BitVec.ofNat 64 0 := by rw [hmv]; exact hq
    exact (hw 3 (by decide)).trans hq'

end VG.Proof.Ffdh.X86_64.Generation
