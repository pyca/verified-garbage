module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ECDSA over brainpoolP256r1 (FIPS 186-5) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law `h`, the variant
`Variants/BrainpoolP256r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.signApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    code := Impl.Ecdsa.Arm.signBrainpoolP256r1Comb
    verified := Proof.Ecdsa.Arm.BrainpoolP256r1.combSign_verified h.law },
  Spec.Ecdsa.BrainpoolP256r1.verifyApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    code := Impl.Ecdsa.Arm.verifyBrainpoolP256r1Comb
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.combVerify_verified h.law }]

end VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1
