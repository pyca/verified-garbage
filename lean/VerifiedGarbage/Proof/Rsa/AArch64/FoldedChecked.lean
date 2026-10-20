module

public import VerifiedGarbage.Proof.Rsa.AArch64.PdChecked
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCodeCT
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCode
import VerifiedGarbage.Proof.Framework.Omega

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
    Verified target (Folded.checked M.mm) (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  have hct : ConstantTime isa pdChkContract.pre pdChkContract.pub (Folded.checked M.mm) :=
    checked_constantTime M
  Verified.of_correct (k := pdChkContract) (checked_correct M) hct precomputedChecked_implies

end VG.Proof.Rsa.AArch64.FoldedPublic
