import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTwoContract

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 theorem four_verified : Verified target Four.code (Spec.MlDsa.rejNTT4Contract abi) := by
  refine ⟨?_,?_,(VG.Proof.MlDsa.AArch64.Sample.Rej4.verified true).2.2⟩
  · intro s hs
    obtain ⟨tr,t,he,ht⟩ := four_ok (pre_four hs)
    refine ⟨tr,t,he,ht.abi,?_⟩
    sig_post [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,abi,argRegs]
    exact ht.outcome
  · intro s t tr ur s' t' hs ht hp es et
    have pub : Pub 4 s t := by
      sig_pub [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,abi,argRegs] at hp
      obtain ⟨hsp,hb,h0,h1,h2⟩ := hp
      exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
    exact four_ct _ _ _ _ _ _ (pre_four hs) (pre_four ht) pub es et

 def twoSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,68⟩]
  wr := [⟨0x2000,2048⟩,⟨0x4000,8192⟩]

 theorem two_verified : Verified target Two.code (Spec.MlDsa.rejNTT2Contract abi) := by
  refine ⟨?_,?_,?_⟩
  · intro s hs
    obtain ⟨tr,t,he,ht⟩ := two_ok (pre_two hs)
    refine ⟨tr,t,he,ht.abi,?_⟩
    sig_post [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,abi,argRegs]
    exact ht.outcome
  · intro s t tr ur s' t' hs ht hp es et
    have pub : Pub 2 s t := by
      sig_pub [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,abi,argRegs] at hp
      obtain ⟨hsp,hb,h0,h1,h2⟩ := hp
      exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
    exact two_ct _ _ _ _ _ _ (pre_two hs) (pre_two ht) pub es et
  · sig_implies_sat [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,abi,argRegs]
      [twoSat] using twoSat

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
