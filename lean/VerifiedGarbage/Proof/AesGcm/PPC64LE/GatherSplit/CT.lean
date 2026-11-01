module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.FastCT
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.GatherSplit
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

-- separate module: the dispatch decision depends only on the existing public length.
/-! # Constant time of the split gather caller -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint rel_ite ct_of)


theorem body_rel (hv : Gather.SealOk)
    (hct : ConstantTime isa (Spec.Gcm.sealContract PPC64LE.abi 2672).pre
      (Spec.Gcm.sealContract PPC64LE.abi 2672).pub Impl.AesGcm.PPC64LE.SealGather.sealCode)
    (hs : SplitOk)
    (hsct : ConstantTime isa (Spec.Gcm.sealSplitContract PPC64LE.abi 2800).pre
      (Spec.Gcm.sealSplitContract PPC64LE.abi 2800).pub Impl.AesGcm.PPC64LE.GatherSplit.sealCode)
    {s₁ s₂ e₁ e₂ : State} (h₁ : Layout s₁) (h₂ : Layout s₂) (hq : gatherPub s₁ s₂)
    (he₁ : Gather.Entered s₁ e₁) (he₂ : Gather.Entered s₂ e₂)
    (hn₁ : e₁.gpr .r10=s₁.gpr .r10) (hn₂ : e₂.gpr .r10=s₂.gpr .r10) :
    RelCT isa (Eq2 e₁ e₂) Impl.AesGcm.PPC64LE.GatherSplit.body TT := by
  have pub := hq
  obtain ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ := hq
  have hP : Pf s₁=Pf s₂ := by simp only [Pf,Bs,qsp]
  unfold Impl.AesGcm.PPC64LE.GatherSplit.body
  refine rel_seq (rel_taint [.r12] (by rw [he₁.sp,he₂.sp,hP])
    (by simp [he₁.r12,he₂.r12,hP]) (by taint_decide))
    (select_wp h₁.base he₁ hn₁) (select_wp h₂.base he₂ hn₂) fun u₁ u₂ hu₁ hu₂ => ?_
  have ev₁ := VG.Proof.Gather.PPC64LE.eval_zero (r := .r0) (a := (stackArg s₁ 1 >>> 9).toNat)
    (by rw [hu₁.choice,BitVec.ofNat_toNat,BitVec.setWidth_eq]) (stackArg s₁ 1 >>> 9).isLt
  have ev₂ := VG.Proof.Gather.PPC64LE.eval_zero (r := .r0) (a := (stackArg s₁ 1 >>> 9).toNat)
    (by rw [hu₂.choice,BitVec.ofNat_toNat,BitVec.setWidth_eq,a1]) (stackArg s₁ 1 >>> 9).isLt
  refine rel_ite ev₁ ev₂ (fun _ => Gather.body_rel hv hct h₁.base h₂.base pub hu₁.entered hu₂.entered) (fun _ => ?_)
  have hn : (stackArg s₁ 1 >>> 9).toNat≠0 :=
    of_decide_eq_false ‹decide ((stackArg s₁ 1 >>> 9).toNat=0)=false›
  exact fast_rel hs hsct h₁ h₂ pub hu₁.entered hu₂.entered hu₁.count hu₂.count (nonempty_of_choice h₁.base hn)


theorem sealGather_ct (hv : Gather.SealOk)
    (hct : ConstantTime isa (Spec.Gcm.sealContract PPC64LE.abi 2672).pre
      (Spec.Gcm.sealContract PPC64LE.abi 2672).pub Impl.AesGcm.PPC64LE.SealGather.sealCode)
    (hs : SplitOk)
    (hsct : ConstantTime isa (Spec.Gcm.sealSplitContract PPC64LE.abi 2800).pre
      (Spec.Gcm.sealSplitContract PPC64LE.abi 2800).pub Impl.AesGcm.PPC64LE.GatherSplit.sealCode) :
    ConstantTime isa (fun s => Layout s) gatherPub Impl.AesGcm.PPC64LE.GatherSplit.sealGather := by
  refine ct_of fun s₁ s₂ h₁ h₂ hq => ?_
  have pub := hq
  obtain ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ := hq
  unfold Impl.AesGcm.PPC64LE.GatherSplit.sealGather Impl.AesGcm.PPC64LE.SealGather.withBody
  refine (RelCT.alloc (P := Eq2 s₁ s₂) (R := TT) (fun a b ⟨ha,hb⟩ => by subst a b; exact qsp)
    ((?_ : RelCT isa (Eq2 (allocated 160 s₁) (allocated 160 s₂)) _ TT).mono
      (fun a b ⟨s,t,⟨hs,ht⟩,ha,hb⟩ => by subst s t; exact ⟨ha,hb⟩) fun _ _ h => h)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  refine rel_seq (rel_taint [] (show s₁.sp-BitVec.ofNat 64 160=s₂.sp-BitVec.ofNat 64 160 by rw [qsp])
    (by simp) (by taint_decide)) (entered_wp h₁.base) (entered_wp h₂.base) fun e₁ e₂ he₁ he₂ => ?_
  exact body_rel hv hct hs hsct h₁ h₂ pub he₁.1 he₂.1 he₁.2 he₂.2

end VG.Proof.AesGcm.PPC64LE.GatherSplit
