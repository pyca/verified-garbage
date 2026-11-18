module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourContracts
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.AArch64.Optimized.KeygenPackVerify`, which only this module used -/

section

/-! ## From `KeygenPackTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Pack
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (agree_of)

theorem simple_ct : ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub simple :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x2,.x3])
    (fun _ _ _ _ ⟨h0,h2,h3,hsp⟩=>agree_of hsp (by simp [h0,h2,h3])) (by taint_decide)

theorem signed_ct : ConstantTime isa bitPackK.pre bitPackK.pub signed :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x3,.x4])
    (fun _ _ _ _ ⟨h0,h3,h4,hsp⟩=>agree_of hsp (by simp [h0,h3,h4])) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackVerify.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Pack
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (abi_of)

theorem simple_verified_of_wp
    (hwp : ∀{s:State},simpleBitPackK.pre s → WP isa simple s (fun t=>simpleBitPackK.post s t)) :
    Verified AArch64.target simple (simpleBitPackContract AArch64.abi) := by
  have hcorrect : ∀s,simpleBitPackK.pre s → ∃tr t,Exec isa simple s tr t ∧ abiPreserved s t ∧ simpleBitPackK.post s t := by
    intro s hs
    obtain ⟨tr,t,he,hp⟩ := hwp hs
    exact ⟨tr,t,he,abi_of rfl (by lit_decide) he,hp⟩
  exact Verified.of_correct hcorrect simple_ct
    { pre := by sig_implies_pre [simpleBitPackContract,simpleBitPackSig,simpleBitPackK,AArch64.abi,AArch64.argRegs]
      post := by sig_implies_post [simpleBitPackContract,simpleBitPackSig,simpleBitPackK,AArch64.abi,AArch64.argRegs]
      pub := by sig_implies_pub [simpleBitPackContract,simpleBitPackSig,simpleBitPackK,AArch64.abi,AArch64.argRegs]
      sat := VG.Proof.MlDsa.AArch64.Pack.simpleBitPack_verified.2.2 }

theorem signed_verified_of_wp
    (hwp : ∀{s:State},bitPackK.pre s → WP isa signed s (fun t=>bitPackK.post s t)) :
    Verified AArch64.target signed (bitPackContract AArch64.abi) := by
  have hcorrect : ∀s,bitPackK.pre s → ∃tr t,Exec isa signed s tr t ∧ abiPreserved s t ∧ bitPackK.post s t := by
    intro s hs
    obtain ⟨tr,t,he,hp⟩ := hwp hs
    exact ⟨tr,t,he,abi_of rfl (by lit_decide) he,hp⟩
  exact Verified.of_correct hcorrect signed_ct
    { pre := by sig_implies_pre [bitPackContract,bitPackSig,bitPackK,AArch64.abi,AArch64.argRegs]
      post := by sig_implies_post [bitPackContract,bitPackSig,bitPackK,AArch64.abi,AArch64.argRegs]
      pub := by sig_implies_pub [bitPackContract,bitPackSig,bitPackK,AArch64.abi,AArch64.argRegs]
      sat := VG.Proof.MlDsa.AArch64.Pack.bitPack_verified.2.2 }

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end

/-! ### `MlDsa.AArch64.Optimized.KeygenPackDispatch`, which only this module used -/

section

/-! ## From `KeygenPackWidthContracts.lean` -/

@[expose] public section

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
    rw [bpVal,←BitVec.ofNat_toNat,subModQ_toNat (by omega_using [hq, hB19]) hx,
      ←sub_modPm hx (by omega_using [hq, hB19]) h₂,←hd,hB]
    exact lt_bitlen (sub_modPm_le h₁ h₂)
  · intro i hi
    simpa only [fieldValueNat,↓reduceIte] using inputValue_nat true B s.mem (s.gpr .x0) i
      (by omega_using [hq, hB19]) (by rw [ho.mem,ho.get .x0];exact hred i hi)
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat=bitPack _ _ _
    simp only [↓reduceIte,ho.get .x3,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,bitPack_eq,bitPack_vals hred (by omega_using [hc, hq]) (fun i hi=>(hbnd i hi).2),hd,hB]

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
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide) (.inr (.inl rfl)) (by omega_using [hcases, h₂])
  rw [o₁.get .x3] at h₂
  refine sel_ok (by decide) (fun s₃ o₃ h₃=>?_) (fun s₃ o₃ h₃=>?_)
  · exact simple_width_wp hp ((o₁.trans o₂).trans o₃).mono (d:=10) (c:=8)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide) (.inr (.inr (.inr (.inl rfl)))) (by omega_using [hcases, h, h₂])
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
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide) (.inl rfl) (by omega_using [hcases, h]) (by omega_using [hcases, h])
  refine sel_ok (by decide) (fun s₂ o₂ h₂=>?_) (fun s₂ o₂ h₂=>?_)
  · rw [o₁.get .x4] at h₂
    exact four_ok hp (o₁.trans o₂).mono h₂
  rw [o₁.get .x4] at h₂
  refine sel_ok (by decide) (fun s₃ o₃ h₃=>?_) (fun s₃ o₃ h₃=>?_)
  · rw [o₂.get .x4,o₁.get .x4] at h₃
    exact signed_width_wp hp ((o₁.trans o₂).trans o₃).mono (B:=4096) (d:=13) (c:=8)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide)
      (.inr (.inr (.inr (.inr rfl)))) (by omega_using [hcases, h₃]) (by omega_using [hcases, h₃])
  rw [o₂.get .x4,o₁.get .x4] at h₃
  refine sel_ok (by decide) (fun s₄ o₄ h₄=>?_) (fun s₄ o₄ h₄=>?_)
  · rw [o₃.get .x4,o₂.get .x4,o₁.get .x4] at h₄
    exact signed_width_wp hp (((o₁.trans o₂).trans o₃).trans o₄).mono (B:=131072) (d:=18) (c:=4)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide)
      (.inr (.inr (.inl rfl))) (by omega_using [hcases, h₄]) (by omega_using [hcases, h₄])
  rw [o₃.get .x4,o₂.get .x4,o₁.get .x4] at h₄
  refine sel_ok (by decide) (fun s₅ o₅ h₅=>?_) (fun s₅ o₅ h₅=>?_)
  · exact signed_width_wp hp ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).mono (B:=524288) (d:=20) (c:=4)
      ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩ (by decide)
      (.inr (.inr (.inr (.inl rfl)))) (by omega_using [hcases, h, h₂, h₃, h₄]) (by omega_using [hcases, h, h₂, h₃, h₄])
  · rw [o₄.get .x4,o₃.get .x4,o₂.get .x4,o₁.get .x4] at h₅
    omega

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

theorem simple_verified : Verified AArch64.target simple (simpleBitPackContract AArch64.abi) :=
  simple_verified_of_wp (simple_wp_of_four simple_four_wp)

theorem signed_verified : Verified AArch64.target signed (bitPackContract AArch64.abi) :=
  signed_verified_of_wp (signed_wp_of_four signed_four_wp)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
