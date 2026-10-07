import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCorrect
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointBoundaryChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPointsTiming

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

/-- Joint verification satisfies the existing correctness, ABI, and public-input contract. -/
theorem jointVerify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    :
    Verified AArch64.target P256Joint.verify
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,?_,implies.sat⟩
  · obtain ⟨t,s',he,ha,hp⟩ := jointVerify_a64 hL hI hT s (implies.pre _ hs)
    exact ⟨t,s',he,ha,implies.post s s' hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact jointVerify_ct_of_points (p256_ok hI) jointPrefix_ct
      (fun _ _ ps pt => jointPoints_relCT (p256_ok hI) hL hT ps pt) jointTail_ct
      _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂))
      (jacPublic_of_spec pub) e₁ e₂

end VG.Proof.Ecdsa.Verify.AArch64
