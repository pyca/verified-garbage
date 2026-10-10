import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidth
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackDispatch

/-! ## From `KeygenPackTiming.lean` -/

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
