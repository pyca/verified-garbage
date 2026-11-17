module

public import VerifiedGarbage.Proof.Ed25519.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.Ed25519Field.Arm

/-! # Ed25519 (RFC 8032) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Ed25519.Arm

def artifacts : List Artifact :=
  VG.Proof.Variants.Ed25519Field.Arm.variants.flatMap fun (v : Proof.Variants.Ed25519Field.Arm.Variant) => [
    Spec.Ed25519.keyPairApi.artifact Arm.target (Proof.Ed25519.Arm.Scrub.keyPairReg v.umaal v.suffix),
    Spec.Ed25519.signExpandedApi.artifact Arm.target (Proof.Ed25519.Arm.Scrub.signExpandedReg v.umaal v.suffix),
    Spec.Ed25519.verifyApi.artifact Arm.target (Proof.Ed25519.Arm.Scrub.verifyReg v.umaal v.suffix)]

end VG.Artifacts.Ed25519.Arm
