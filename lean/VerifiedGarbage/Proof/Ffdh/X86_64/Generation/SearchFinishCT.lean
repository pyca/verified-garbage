module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Returning a native search does not expose private saved register values -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search VG.Proof.MlKem.X86_64

structure SearchEndPoint where
  inputs : SearchPublic
  result : Spec.Ffdh.ParameterSearchResult

def SearchCTDone (p : SearchEndPoint) (s : State) : Prop :=
  ∃ original, SearchDone p.inputs original p.result s

private theorem finish_pointer (p : SearchEndPoint) (s : State) (h : SearchCTDone p s) :
    WP isa (.block (finish.take 4)) s fun t => t.gpr .rdx = p.inputs.c.up := by
  obtain ⟨original, h⟩ := h
  have scr := h.input.control_scr h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  xrun [State.ea, field, off, h.r12, h.usedPtr, Nat.reduceMul, BitVec.ofInt_natCast,
    hl 56 (by decide), hl 96 (by decide), hl 112 (by decide), hl 32 (by decide)]

theorem search_finish_ct : RelCT isa (Two SearchCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two SearchCTDone) (.block (finish.take 4 ++ finish.drop 4)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.r12] ?_ (by taint_decide) finish_pointer) ?_)
  · intro p s t ⟨_, h₁⟩ ⟨_, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r12.trans h₂.r12.symm
  · exact two_taint [.rdx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

end VG.Proof.Ffdh.X86_64.Generation
