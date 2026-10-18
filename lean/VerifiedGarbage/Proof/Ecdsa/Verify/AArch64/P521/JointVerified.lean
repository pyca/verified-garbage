module

import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521

theorem verify_ct (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pre
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pub verifyP521 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact Joint.verify_public_ct (p521_ok hI) hL hO (by decide) hT _ _ _ _ _ _
    (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (jacPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    Verified AArch64.target verifyP521
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hO hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hO hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.P521
