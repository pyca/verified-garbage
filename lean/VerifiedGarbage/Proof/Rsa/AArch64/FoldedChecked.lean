module

public import VerifiedGarbage.Proof.Rsa.AArch64.PdChecked
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedPhaseCT
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedPhase
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.PdCT
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCode
public import VerifiedGarbage.Proof.Rsa.Contract

/-! ### `Bignum.AArch64.FoldedCodeCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.FoldedRestCT`, which only this module used -/

section

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
      (by unfold sMask sFn; omega_using [])),gt⟩

theorem rest_ct (M : Mont) : RelCT isa (Two DRel) (Folded.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp) (by simp [phases]) (RelCT.seq pdSetup_ct ?_)
  refine RelCT.seqs_append (by simp [phases]) (by simp [outSteps]) (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (publicPhase_ct M)
  · exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub)) (fun _ _ h => dd_oPre h) out_ct

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64

theorem code_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.code M.mm) :=
  pdCodeWith_constantTime (Folded.code M.mm) (pdCodeWith_ct (Folded.rest M.mm) (rest_ct M))

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end


@[expose] public section
namespace VG.Proof.Rsa.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

theorem checked_correct (M : Mont) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (Folded.checked M.mm) s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s' := by
  refine guarded_correct (VG.Proof.Bignum.AArch64.FoldedPublic.code_correct M) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, hs.x0, hs.x1, hs.x2, hs.x3, hs.x4, hs.x5, hs.x6, hs.mem] at hp
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, ↓reduceIte]
    exact hp nB hl hpre
  · intro s s' h hv hb hax nB _ _
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, hb⟩

theorem checked_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.checked M.mm) :=
  guarded_ct (VG.Proof.Bignum.AArch64.FoldedPublic.code_constantTime M) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.2.2.1
      · exact hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pdPub_same h₁ h₂ hp

theorem checked_verified (M : Mont) :
    Verified target (Folded.checked M.mm) (Proof.Rsa.publicPrecomputedCheckedContract abi) :=
  have hct : ConstantTime isa pdChkContract.pre pdChkContract.pub (Folded.checked M.mm) :=
    checked_constantTime M
  Verified.of_correct (k := pdChkContract) (checked_correct M) hct precomputedChecked_implies

end VG.Proof.Rsa.AArch64.FoldedPublic
