import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedInverse
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPreserved
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointBoundaryChecks

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem allocatedVerify_ok (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hN : InvToM p256.C.n)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    {s : State} (h : VPre p256 s) :
    WP isa P256Allocated.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t := by
  apply verify_of_joint_inverse (p256_ok hI) hL P256Allocated.inverse P256Allocated.points
    P256Allocated.verify (allocatedMid_ok hI hN) rfl ?_ h
  intro s₀ base g s hm ht P hp hr
  exact WP.mono (Allocated.points_ok (p256_ok hI) hL hT hm ht hp hr)
    fun _ ⟨hf,hrep,_⟩ => ⟨hf,hrep⟩

/-- The allocated verifier satisfies the existing correctness, ABI and public-input contract. -/
theorem allocatedVerify_verified (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hN : InvToM p256.C.n)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target P256Allocated.verify
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,?_,implies.sat⟩
  · obtain ⟨tr,t,he,ha,hp⟩ := allocatedVerify_a64_of_wp
      (fun _ hp => allocatedVerify_ok hL hI hN hT hp)
      (fun hp he => allocatedVerify_restored hL hI hN hT hp he) s (implies.pre _ hs)
    exact ⟨tr,t,he,ha,implies.post s t hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact allocatedVerify_ct_of_points (fun _ hp => allocatedPrefix_ok hI hN hp)
      (allocatedPrefix_ct (p256_ok hI) (allocatedInverse_relCT hI hN) allocatedUv_ct)
      (fun _ _ ps pt => Allocated.allocatedPoints_relCT Allocated.raw_correct (p256_ok hI) hL hT ps pt)
      jointTail_ct _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂))
      (jacPublic_of_spec pub) e₁ e₂

end VG.Proof.Ecdsa.Verify.AArch64
