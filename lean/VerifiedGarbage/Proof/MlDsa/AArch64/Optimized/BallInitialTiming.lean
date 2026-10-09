import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallZeroReady
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCursor

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf pub_eq)

def CursorPair (J : State → State → Prop) (s t : State) : Prop :=
  ∃σ₁ σ₂,sbK.pre σ₁ ∧ sbK.pre σ₂ ∧ sbK.pub σ₁ σ₂ ∧ J σ₁ s ∧ J σ₂ t ∧ s.gpr .x0=t.gpr .x0

 theorem tau_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : tauOf σ₁=tauOf σ₂ := congrArg BitVec.toNat hq.2.2.1
 theorem first_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : firstBytes σ₁=firstBytes σ₂ := by
  simp only [firstBytes,Sp.msg]
  rw [hq.2.2.2.2.2.2]
 theorem tail_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : tailBytes σ₁=tailBytes σ₂ := by
  simp only [tailBytes,Sp.msg]
  rw [hq.2.2.2.2.2.2]

 theorem sponge_step (v : Proof.Sha3.AArch64.Permutation) (hc : SpongeCursor v.callee) :
    RelCT isa (Rel2 sbK.pre sbK.pub (fun σ => J0 (spOf σ) σ))
      (Impl.MlDsa.AArch64.Sample.spongeWith v.callee 136 136)
      (CursorPair fun σ => Resume 136 136 (spOf σ) σ) := by
  intro s t ts tt u z ⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂⟩ es et
  have hh := hc _ _ _ _ _ _ (by
    refine ⟨agree_of (by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1]) (fun r hr => ?_),fun r hr => by simp [SpongePublic,VectorTaint.ofRegs,RegSet.mem_ofList] at hr⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · rw [h₁.env.x25,h₂.env.x25,pub_eq hq]
    · rw [h₁.env.x26,h₂.env.x26,pub_eq hq]
    · rw [h₁.env.x27,h₂.env.x27,pub_eq hq]
    · rw [h₁.x3,h₂.x3,pub_eq hq]
    · exact toNat_inj h₁.x4 (by rw [h₂.x4,pub_eq hq])) es et
  obtain ⟨_,_,e₁,f₁⟩ := spongeResume_ok (Sample.Ball.spOk p₁) v (rate := 136) (outlen := 136) (by decide) (by decide) h₁
  obtain ⟨_,_,e₂,f₂⟩ := spongeResume_ok (Sample.Ball.spOk p₂) v (rate := 136) (outlen := 136) (by decide) (by decide) h₂
  obtain ⟨_,rfl⟩ := Exec.det es e₁
  obtain ⟨_,rfl⟩ := Exec.det et e₂
  exact ⟨hh.1,σ₁,σ₂,p₁,p₂,hq,f₁,f₂,hh.2⟩

 theorem initial_step :
    RelCT isa (CursorPair fun σ => Resume 136 136 (spOf σ) σ)
      (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      (CursorPair Initial) := by
  intro s t ts tt u z ⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂,h0⟩ es et
  have hsp : s.sp=t.sp := by rw [h₁.first.env.sp,h₂.first.env.sp,hq.2.2.2.2.2.1]
  have full₁ := initial_full_ok p₁ h₁
  have full₂ := initial_full_ok p₂ h₂
  obtain ⟨_,_,e₁,f₁⟩ := full₁
  obtain ⟨_,_,e₂,f₂⟩ := full₂
  obtain ⟨_,rfl⟩ := Exec.det es e₁
  obtain ⟨_,rfl⟩ := Exec.det et e₂
  refine ⟨?_,σ₁,σ₂,p₁,p₂,hq,f₁.1,f₂.1,by rw [f₁.2,f₂.2,h0]⟩
  cases es with | seq ez₁ ef₁ =>
   cases et with | seq ez₂ ef₂ =>
    have hz := RelCT.taint (A := VectorTaint.taint) (VectorTaint.ofRegs [.x26])
      (P := fun a b => a.sp=b.sp ∧ a.gpr .x26=b.gpr .x26)
      (fun _ _ hh => ⟨agree_of hh.1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hh.2),fun r hr => by simp [VectorTaint.ofRegs,RegSet.mem_ofList] at hr⟩)
      (c := Impl.MlDsa.AArch64.Optimized.Ball.zeroWide) (by taint_decide)
      _ _ _ _ _ _ ⟨hsp,by rw [h₁.first.env.x26,h₂.first.env.x26,pub_eq hq]⟩ ez₁ ez₂
    obtain ⟨_,_,ze₁,k₁,r₁⟩ := zero_ready p₁ h₁
    obtain ⟨_,_,ze₂,k₂,r₂⟩ := zero_ready p₂ h₂
    obtain ⟨_,rfl⟩ := Exec.det ez₁ ze₁
    obtain ⟨_,rfl⟩ := Exec.det ez₂ ze₂
    have rr₂ := r₂
    rw [← pub_eq hq,← tau_eq hq,← first_eq hq] at rr₂
    have hf := first_relCT (H_length _ _) (by have := (Sample.Ball.params p₁).2.2; omega)
      (a_scr' (Sample.Ball.spOk p₁) (by decide)).symm _ _ _ _ _ _
      ⟨r₁,rr₂,by rw [k₁.sp,k₂.sp]; exact hsp⟩ ef₁ ef₂
    exact congr (congrArg (fun xs ys : List Leak => xs ++ ys) hz.1) hf.1
end VG.Proof.MlDsa.AArch64.Optimized.Ball
