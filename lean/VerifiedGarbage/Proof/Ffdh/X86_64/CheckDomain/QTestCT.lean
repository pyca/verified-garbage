module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: testing the shared reduction -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (aXc)

private theorem zero_keep (p : CdP) (s : State) (h : QResidue p s) :
    WP isa (seqs (isZero aXc)) s (QResidue p) := by
  obtain ⟨⟨mi, hw, hm, hdl, hq⟩, hr⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; omega
  refine WP.mono (ltArr_ok hw.ctx.good (Nat.le_refl _) (by omega) (by omega)
    (show aXc < 8 by decide) (show aOne < 8 by decide)) fun t ⟨_, hmem, k⟩ => ?_
  refine ⟨⟨mi, hw.keep hmem k (k.gpr (by decide)), hm, hdl, hq⟩, ?_⟩
  obtain ⟨mi', hw', hz⟩ := hr
  exact ⟨mi', hw'.keep hmem k (k.gpr (by decide)), by rw [hmem]; exact hz⟩

private theorem tested (p : CdP) (s : State) (h : QResidue p s) :
    WP isa (seqs (isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))) s (QDivided p) :=
  WP.mono (residue_test h.2) fun _ ⟨⟨⟨mi, hw, _⟩, hz⟩, _⟩ =>
    ⟨⟨mi, hw, h.1.choose_spec.2⟩, hz⟩

theorem test_q_ct : RelCT isa (Two QResidue)
    (seqs (isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))) (Two QDivided) := by
  refine two_post ?_ tested
  refine RelCT.seqs_append (by simp [isZero, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two QResidue) ?_ ?_)
  · simpa only [isZero] using
      (two_post (two_map (fun p : CdP => p.qx.ws) (fun _ _ h => by
        obtain ⟨mi, hw, _⟩ := h.1
        exact ⟨mi, hw.ctx.good, Nat.le_refl _⟩)
        (ltArr_ct (a := aXc) (b := aOne) (by decide) (by decide) (by taint_decide))) zero_keep)
  · exact two_taint [] (pins_nil _) (by taint_decide)

end VG.Proof.Ffdh.X86_64.CheckDomain
