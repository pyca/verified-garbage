import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidth
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack

/-! ## From `KeygenPackWidthContracts.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack
open VG.Proof.MlKem.AArch64 (Only)

theorem simple_width_wp {s₀ s : State} (hp : simpleBitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    {d c : Nat} (hs : Shape d c (d*c/8)) (hc4 : c%4=0) (ht : TailWidth (d*c/8))
    (hd : bitlen (wArg s₀ .x1)=d) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.width false 0 d c) s
      (fun t=>simpleBitPackK.post s₀ t) := by
  obtain ⟨hrd,hwr,hsep,hb,hlen,hle⟩ := hp
  rw [hd] at hlen
  refine WP.mono (width_ok false 0 d c hs hc4 ht s BitVec.toNat ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x2,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x2,hlen,Bool.false_eq_true,↓reduceIte] using hsep
  · intro i hi
    rw [ho.mem,ho.get .x0,←hd]
    exact lt_bitlen (hle i hi)
  · intro i _
    simp [inputValue]
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat=simpleBitPack _ _
    simp only [Bool.false_eq_true,↓reduceIte,ho.get .x2,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,simpleBitPack_eq,natPolyAt_toList,hd]

theorem signed_width_wp {s₀ s : State} (hp : bitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    {B d c : Nat} (hs : Shape d c (d*c/8)) (hc4 : c%4=0) (ht : TailWidth (d*c/8))
    (hB : wArg s₀ .x2=B) (hd : bitlen (wArg s₀ .x1+wArg s₀ .x2)=d) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.width true B d c) s
      (fun t=>bitPackK.post s₀ t) := by
  obtain ⟨hrd,hwr,hsep,hab,hlen,hred,hbnd⟩ := hp
  have hc := bp_cases hab hlen
  have hq : q=8380417 := rfl
  have hB19 : B≤2^19 := by omega
  rw [hd] at hlen
  refine WP.mono (width_ok true B d c hs hc4 ht s (bpVal B) ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x3,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x3,hlen,↓reduceIte] using hsep
  · intro i hi
    rw [ho.mem,ho.get .x0]
    obtain ⟨h₁,h₂⟩ := hbnd i hi
    rw [hB] at h₂
    have hx := hred i hi
    rw [bpVal,←BitVec.ofNat_toNat,subModQ_toNat (by omega) hx,
      ←sub_modPm hx (by omega) h₂,←hd,hB]
    exact lt_bitlen (sub_modPm_le h₁ h₂)
  · intro i hi
    simpa only [fieldValueNat,↓reduceIte] using inputValue_nat true B s.mem (s.gpr .x0) i
      (by omega) (by rw [ho.mem,ho.get .x0];exact hred i hi)
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat=bitPack _ _ _
    simp only [↓reduceIte,ho.get .x3,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,bitPack_eq,bitPack_vals hred (by omega) (fun i hi=>(hbnd i hi).2),hd,hB]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackDispatch.lean` -/

section

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

end
