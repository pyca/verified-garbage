module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Native acceptance and rejection use only public memory addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def UsedPins (p : SearchPoint) (s : State) : Prop := s.gpr .rax = p.inputs.c.up ∧ s.gpr .r12 = p.inputs.control

private theorem used_pointer (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block [.mov .rax (.mem (field 7))]) s (UsedPins p) := by
  obtain ⟨original, h⟩ := h
  have scr := h.input.control_scr h.wr
  have hl : InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 56) 8 := scr.ld (by decide)
  have hp : word s.mem p.inputs.control 56 = p.inputs.c.up :=
    h.headers (7, p.inputs.c.up) (by simp [SearchPublic.headers])
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.inputs.c.up)
    (by xrun [State.ea, field, off, h.r12, hl, hp, BitVec.ofInt_natCast, Nat.reduceMul]) rfl)
    fun _ ⟨ha, k⟩ => ⟨ha, (k.gpr (by decide)).trans h.r12⟩

private theorem used_pins : Pins UsedPins [.rax, .r12] := by
  intro p s t h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]

private theorem used_pointer_ct : RelCT isa (Two SearchCTL) (.block [.mov .rax (.mem (field 7))])
    (Two UsedPins) := two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) used_pointer

theorem search_accept_ct : RelCT isa (Two SearchCTL) (.block accept) (fun _ _ => True) := by
  change RelCT isa (Two SearchCTL) (.block ([.mov .rax (.mem (field 7))] ++ accept.drop 1)) _
  exact RelCT.block_append (RelCT.seq used_pointer_ct (two_taint [.rax, .r12] used_pins (by taint_decide)))

theorem search_reject_ct : RelCT isa (Two SearchCTL) (.block reject) (fun _ _ => True) := by
  change RelCT isa (Two SearchCTL) (.block ([.mov .rax (.mem (field 7))] ++ reject.drop 1)) _
  exact RelCT.block_append (RelCT.seq used_pointer_ct (two_taint [.rax, .r12] used_pins (by taint_decide)))

theorem search_request_ct : RelCT isa (Two SearchCTL) (.block request) (fun _ _ => True) :=
  two_taint [.r12, .rsp] search_ctl_pins (by taint_decide)

end VG.Proof.Ffdh.X86_64.Generation
