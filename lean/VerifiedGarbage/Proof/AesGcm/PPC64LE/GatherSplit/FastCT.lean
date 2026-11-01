module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.TailCT
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.CT
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.GatherSplit
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

-- separate module: compose suffix gathering, public call arguments and the verified callee.
/-! # Constant time of the split gather path -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint)


theorem fast_rel (hv : SplitOk)
    (hct : ConstantTime isa (Spec.Gcm.sealSplitContract PPC64LE.abi 2800).pre
      (Spec.Gcm.sealSplitContract PPC64LE.abi 2800).pub Impl.AesGcm.PPC64LE.GatherSplit.sealCode)
    {s₁ s₂ e₁ e₂ : State} (h₁ : Layout s₁) (h₂ : Layout s₂) (hq : gatherPub s₁ s₂)
    (he₁ : Gather.Entered s₁ e₁) (he₂ : Gather.Entered s₂ e₂)
    (hn₁ : e₁.gpr .r10=s₁.gpr .r10) (hn₂ : e₂.gpr .r10=s₂.gpr .r10) (hc : 0<Cnt s₁) :
    RelCT isa (Eq2 e₁ e₂) Impl.AesGcm.PPC64LE.GatherSplit.fast TT := by
  have hd := Gather.entered_desc h₁.base h₂.base hq he₁ he₂
  obtain ⟨q3,q4,q5,q6,q7,q8,q9,q10,qsp,a0,a1,a2,hdesc⟩ := hq
  have hP : Pf s₁=Pf s₂ := by simp only [Pf,Bs,qsp]
  have hc₂ : 0<Cnt s₂ := by simpa only [Cnt,← q10] using hc
  have g₁ := gatherPre_of h₁.base he₁
  have g₂ := gatherPre_of h₂.base he₂
  have g₂' := g₂
  simp only [Src,Dst,Cnt,L,← q9,← q10,← a0,← a1] at g₂'
  obtain ⟨hsource,hlen⟩ := first_agree hd g₁ g₂' hc
  unfold Impl.AesGcm.PPC64LE.GatherSplit.fast
  refine rel_seq (tail_rel hd g₁ g₂' hc (by rw [he₁.sp,he₂.sp,hP]))
    (tail_ok g₁ hc) (tail_ok g₂ hc₂) fun t₁ t₂ ht₁ ht₂ => ?_
  have pt : t₁.sp=t₂.sp := by rw [ht₁.keep.sp,ht₂.keep.sp,he₁.sp,he₂.sp,hP]
  have nr : t₁.gpr .r10=t₂.gpr .r10 := by
    rw [ht₁.keep.gpr _ (by decide),ht₂.keep.gpr _ (by decide),hn₁,hn₂,q10]
  have pr : t₁.gpr .r12=t₂.gpr .r12 := by
    rw [ht₁.keep.gpr _ (by decide),ht₂.keep.gpr _ (by decide),he₁.r12,he₂.r12,hP]
  have sr : t₁.gpr .r7=t₂.gpr .r7 := by
    rw [ht₁.next,ht₂.next]
    simp only [Src,Cnt,q9,q10]
  refine rel_seq (rel_taint [.r7,.r10,.r12] pt (by simp [sr,nr,pr]) (by taint_decide))
    (prepare_ok h₁.base he₁ hn₁ hc ht₁) (prepare_ok h₂.base he₂ hn₂ hc₂ ht₂) fun c₁ c₂ hp₁ hp₂ => ?_
  have pub : (Spec.Gcm.sealSplitContract PPC64LE.abi 2800).pub (callView s₁ e₁ c₁) (callView s₂ e₂ c₂) := by
    apply call_pub
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hp₁.view_gpr (r := .r3) (by decide),hp₂.view_gpr (r := .r3) (by decide)]; exact q3
    · rw [hp₁.view_gpr (r := .r4) (by decide),hp₂.view_gpr (r := .r4) (by decide)]; exact q4
    · rw [hp₁.view_gpr (r := .r5) (by decide),hp₂.view_gpr (r := .r5) (by decide)]; exact q5
    · rw [hp₁.view_gpr (r := .r6) (by decide),hp₂.view_gpr (r := .r6) (by decide)]; exact q6
    · rw [hp₁.view_gpr (r := .r7) (by decide),hp₂.view_gpr (r := .r7) (by decide)]; exact q7
    · rw [hp₁.view_gpr (r := .r8) (by decide),hp₂.view_gpr (r := .r8) (by decide)]; exact q8
    · change c₁.callEntry.gpr .r9=c₂.callEntry.gpr .r9
      rw [State.callEntry_gpr c₁ (by decide),State.callEntry_gpr c₂ (by decide),hp₁.source,hp₂.source]
      simpa only [Src,← q9] using hsource
    · change c₁.callEntry.gpr .r10=c₂.callEntry.gpr .r10
      rw [State.callEntry_gpr c₁ (by decide),State.callEntry_gpr c₂ (by decide),hp₁.length,hp₂.length]
      exact hlen
    · change c₁.sp=c₂.sp
      rw [hp₁.sp,hp₂.sp,hP]
    · rw [hp₁.view_arg (j := 0) (by decide),hp₂.view_arg (j := 0) (by decide)]; exact a0
    · rw [hp₁.view_arg (j := 1) (by decide),hp₂.view_arg (j := 1) (by decide)]; exact a1
    · rw [hp₁.view_arg (j := 2) (by decide),hp₂.view_arg (j := 2) (by decide)]; exact a2
  obtain ⟨cv₁,cw₁⟩ := hp₁.covers h₁.base he₁ hc
  obtain ⟨cv₂,cw₂⟩ := hp₂.covers h₂.base he₂ hc₂
  refine rel_seq (RelCT.callEx hv hct (fun a b ⟨ha,hb⟩ => by
    subst a b
    exact ⟨callRead s₁ e₁,callWrite s₁,callRead s₂ e₂,callWrite s₂,
      call_pre (prepared_layout h₁ he₁ hc hp₁),call_pre (prepared_layout h₂ he₂ hc₂ hp₂),pub,cv₁,cw₁,cv₂,cw₂⟩))
    (called_wp hv h₁ he₁ hc hp₁) (called_wp hv h₂ he₂ hc₂ hp₂) fun z₁ z₂ hz₁ hz₂ => ?_
  exact rel_taint [] (by rw [hz₁.sp,hz₂.sp,hP]) (by simp) (by taint_decide)

end VG.Proof.AesGcm.PPC64LE.GatherSplit
