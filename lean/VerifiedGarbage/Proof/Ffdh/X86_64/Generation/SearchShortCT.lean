module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLeafCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClearCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLeafCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClearCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # The native refill/exhaustion decision depends only on public policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchShortGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  eval .ae s = some (decide (Spec.Ffdh.parameterEntropy p.inputs.c.bits ≤ p.inputs.c.rand.length - p.used))

private theorem short_guard_ready (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block [.mov .rax (.mem (field 11)), .alu .cmp .rax (.mem (field 2))]) s
      (SearchShortGuard p) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (short_guard h) fun t ⟨ht, _, _, he⟩ => ⟨⟨original, ht⟩, he⟩

theorem search_short_ct : RelCT isa (Two SearchCTL) short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) short_guard_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact search_exhausted_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
  · exact search_request_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.Generation
