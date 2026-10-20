module

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedPhaseCT
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedPhase
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem publicPhase_ct (M : Mont) : RelCT isa (Two DB)
    (.seq (Folded.fastLoop M.mm) (Folded.finishFused M.mm)) (Two DD) := by
  refine two_post (two_map DPub.E (fun _ _ h => db_pre h) (phase_ct M)) ?_
  intro q s h
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := db_pre h
  obtain ⟨xb,σ,g,_,_,_,_,hone⟩ := h
  have src : Src s q.1.B q.1.Z q.1.ep q.1.eb :=
    ⟨fun i hi => hs.2.2.1 i (by rw [← hs.1]; exact hi),
     fun i hi => hs.bytes i (by rw [← hs.1]; exact hi),
     fun i hi => hs.2.2.2.2 i (by rw [← hs.1]; exact hi)⟩
  refine WP.mono (phase_ok M hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 g.1.n1
    hf.2.2.2.2.1 hf.2.2.2.2.2 rfl hone he hl src hs.1 hL hs.2.1)
    fun t ⟨gt,_,_,ft,kt⟩ => ?_
  exact ⟨xb,σ,g.step (ft.mono (pExpRanges_pdAll _)) kt
    (ft.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (by unfold sMask sFn; omega)),gt⟩

theorem rest_ct (M : Mont) : RelCT isa (Two DRel) (Folded.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp) (by simp [phases]) (RelCT.seq pdSetup_ct ?_)
  refine RelCT.seqs_append (by simp [phases]) (by simp [outSteps]) (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (publicPhase_ct M)
  · exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub)) (fun _ _ h => dd_oPre h) out_ct

end VG.Proof.Bignum.AArch64.FoldedPublic
