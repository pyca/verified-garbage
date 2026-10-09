import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidthContracts

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Pack
open VG.Proof.MlKem.AArch64 (Only)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

theorem simple_wp_of_four
    (four_ok : ∀{s₀ s:State},simpleBitPackK.pre s₀ → Only [.x9] s₀ s →
      (s₀.gpr .x3).toNat=128 → WP isa (four false) s (fun t=>simpleBitPackK.post s₀ t))
    {s₀ : State} (hp : simpleBitPackK.pre s₀) :
    WP isa simple s₀ (fun t=>simpleBitPackK.post s₀ t) := by
  have hcases := sbp_cases hp.2.2.2.1 hp.2.2.2.2.1
  unfold simple
  refine sel_ok (by decide) (fun s₁ o₁ h=>?_) (fun s₁ o₁ h=>?_) (s:=s₀)
  · exact four_ok hp o₁ h
  refine sel_ok (by decide) (fun s₂ o₂ h₂=>?_) (fun s₂ o₂ h₂=>?_)
  · rw [o₁.get .x3] at h₂
    exact simple_width_wp hp (o₁.trans o₂).mono (d:=6) (c:=8)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide) (.inr (.inl rfl)) (by omega)
  rw [o₁.get .x3] at h₂
  refine sel_ok (by decide) (fun s₃ o₃ h₃=>?_) (fun s₃ o₃ h₃=>?_)
  · exact simple_width_wp hp ((o₁.trans o₂).trans o₃).mono (d:=10) (c:=8)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide) (.inr (.inr (.inr (.inl rfl)))) (by omega)
  · rw [o₂.get .x3,o₁.get .x3] at h₃
    omega

theorem signed_wp_of_four
    (four_ok : ∀{s₀ s:State},bitPackK.pre s₀ → Only [.x9] s₀ s →
      (s₀.gpr .x4).toNat=128 → WP isa (four true) s (fun t=>bitPackK.post s₀ t))
    {s₀ : State} (hp : bitPackK.pre s₀) :
    WP isa signed s₀ (fun t=>bitPackK.post s₀ t) := by
  have hcases := bp_cases hp.2.2.2.1 hp.2.2.2.2.1
  unfold signed
  refine sel_ok (by decide) (fun s₁ o₁ h=>?_) (fun s₁ o₁ h=>?_) (s:=s₀)
  · exact signed_width_wp hp o₁ (B:=2) (d:=3) (c:=8)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide) (.inl rfl) (by omega) (by omega)
  refine sel_ok (by decide) (fun s₂ o₂ h₂=>?_) (fun s₂ o₂ h₂=>?_)
  · rw [o₁.get .x4] at h₂
    exact four_ok hp (o₁.trans o₂).mono h₂
  rw [o₁.get .x4] at h₂
  refine sel_ok (by decide) (fun s₃ o₃ h₃=>?_) (fun s₃ o₃ h₃=>?_)
  · rw [o₂.get .x4,o₁.get .x4] at h₃
    exact signed_width_wp hp ((o₁.trans o₂).trans o₃).mono (B:=4096) (d:=13) (c:=8)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide)
      (.inr (.inr (.inr (.inr rfl)))) (by omega) (by omega)
  rw [o₂.get .x4,o₁.get .x4] at h₃
  refine sel_ok (by decide) (fun s₄ o₄ h₄=>?_) (fun s₄ o₄ h₄=>?_)
  · rw [o₃.get .x4,o₂.get .x4,o₁.get .x4] at h₄
    exact signed_width_wp hp (((o₁.trans o₂).trans o₃).trans o₄).mono (B:=131072) (d:=18) (c:=4)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide)
      (.inr (.inr (.inl rfl))) (by omega) (by omega)
  rw [o₃.get .x4,o₂.get .x4,o₁.get .x4] at h₄
  refine sel_ok (by decide) (fun s₅ o₅ h₅=>?_) (fun s₅ o₅ h₅=>?_)
  · exact signed_width_wp hp ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).mono (B:=524288) (d:=20) (c:=4)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide)
      (.inr (.inr (.inr (.inl rfl)))) (by omega) (by omega)
  · rw [o₄.get .x4,o₃.get .x4,o₂.get .x4,o₁.get .x4] at h₅
    omega

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
