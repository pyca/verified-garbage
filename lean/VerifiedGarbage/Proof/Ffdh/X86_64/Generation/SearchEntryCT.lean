module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntry
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Native search entry exposes pointers and public policy, never saved registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

private theorem entry_pointer (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block (entryHead.take 2)) s fun t => t.gpr .rax = p.control := by
  have hd : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = p.control :=
    congrArg SearchPublic.control h.2
  have ha : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8 := input_args h 3 (by decide)
  unfold entryHead
  simp only [List.take_succ_cons, List.take_zero]
  xrun [State.ea, BitVec.ofInt_ofNat, hd, ha]

private theorem entry_head_ct : RelCT isa (Two SearchInput) (.block entryHead) (fun _ _ => True) := by
  change RelCT isa (Two SearchInput) (.block (entryHead.take 2 ++ entryHead.drop 2)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.rsp] ?_ (by taint_decide) entry_pointer) ?_)
  · intro p s t h₁ h₂ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (congrArg (fun q => q.c.sp) h₁.2).trans (congrArg (fun q => q.c.sp) h₂.2).symm
  · exact two_taint [.rax] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

def SearchEntryPins (p : SearchPublic) (s : State) : Prop := s.gpr .r12 = p.control ∧ s.gpr .rsp = p.c.sp

private theorem entry_head_pins (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block entryHead) s (SearchEntryPins p) := by
  refine WP.mono (search_entry_head_ok h) fun t ⟨hr, _, k⟩ => ⟨hr, ?_⟩
  exact (k.gpr (by decide)).trans (congrArg (fun q => q.c.sp) h.2)

theorem search_entry_ct : RelCT isa (Two SearchInput) (.block entry) (fun _ _ => True) := by
  unfold entry
  refine RelCT.block_append (RelCT.seq (two_post entry_head_ct entry_head_pins) ?_)
  exact two_taint [.r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

end VG.Proof.Ffdh.X86_64.Generation
