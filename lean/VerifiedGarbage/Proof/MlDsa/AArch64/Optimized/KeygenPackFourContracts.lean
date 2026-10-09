import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack
open VG.Proof.MlKem.AArch64 (Only)

theorem simple_four_wp {s₀ s : State} (hp : simpleBitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    (hlen128 : (s₀.gpr .x3).toNat=128) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four false) s
      (fun t=>simpleBitPackK.post s₀ t) := by
  have hcases := sbp_cases hp.2.2.2.1 hp.2.2.2.2.1
  have hd : bitlen (wArg s₀ .x1)=4 := by omega
  obtain ⟨hrd,hwr,hsep,hb,hlen,hle⟩ := hp
  rw [hd] at hlen
  refine WP.mono (four_ok false s BitVec.toNat ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x2,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x2,hlen,Bool.false_eq_true,↓reduceIte] using hsep
  · intro i hi
    change (coeffAt s.mem (s.gpr .x0) i).toNat<2^4
    rw [ho.mem,ho.get .x0,←hd]
    exact lt_bitlen (hle i hi)
  · intro i _
    simp [inputValue]
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat=simpleBitPack _ _
    simp only [Bool.false_eq_true,↓reduceIte,ho.get .x2,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,simpleBitPack_eq,natPolyAt_toList,hd]

theorem signed_four_wp {s₀ s : State} (hp : bitPackK.pre s₀) (ho : Only [.x9] s₀ s)
    (hlen128 : (s₀.gpr .x4).toNat=128) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four true) s
      (fun t=>bitPackK.post s₀ t) := by
  have hcases := bp_cases hp.2.2.2.1 hp.2.2.2.2.1
  have hd : bitlen (wArg s₀ .x1+wArg s₀ .x2)=4 := by omega
  have hB : wArg s₀ .x2=4 := by omega
  obtain ⟨hrd,hwr,hsep,hab,hlen,hred,hbnd⟩ := hp
  have hc := bp_cases hab hlen
  have hq : q=8380417 := rfl
  rw [hd] at hlen
  refine WP.mono (four_ok true s (bpVal 4) ?_ ?_ ?_ ?_ ?_) fun t ⟨hbytes,_,_⟩=>?_
  · rw [ho.get .x0,ho.rd,ho.wr,hrd]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · rw [ho.get .x3,ho.wr,hwr,hlen]
    exact List.mem_singleton_self _
  · simpa only [ho.get .x0,ho.get .x3,hlen,↓reduceIte] using hsep
  · intro i hi
    change bpVal 4 (coeffAt s.mem (s.gpr .x0) i)<2^4
    rw [ho.mem,ho.get .x0]
    obtain ⟨h₁,h₂⟩ := hbnd i hi
    rw [hB] at h₂
    have hx := hred i hi
    rw [bpVal,←BitVec.ofNat_toNat,subModQ_toNat (by omega) hx,
      ←sub_modPm hx (by omega) h₂]
    have hh := lt_bitlen (sub_modPm_le h₁ h₂)
    simpa only [show bitlen (wArg s₀ .x1+4)=4 by simpa only [hB] using hd] using hh
  · intro i hi
    simpa only [fieldValueNat,↓reduceIte] using inputValue_nat true 4 s.mem (s.gpr .x0) i
      (by omega) (by rw [ho.mem,ho.get .x0];exact hred i hi)
  · change VG.Spec.Sha3.bytesAt t.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat=bitPack _ _ _
    simp only [↓reduceIte,ho.get .x3,ho.get .x0,ho.mem] at hbytes
    rw [hlen,hbytes,bitPack_eq,bitPack_vals hred (by omega) (fun i hi=>(hbnd i hi).2),hd,hB]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
