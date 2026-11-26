module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Ed25519Field.Arm
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed25519 (RFC 8032) on ARMv7 -/

namespace VG.Artifacts.Ed25519.Arm

public def artifacts : List (Artifact Arm.target) :=
  VG.Proof.Variants.Ed25519Field.Arm.variants.flatMap fun (v : Proof.Variants.Ed25519Field.Arm.Variant) => [
    Spec.Ed25519.keyPairApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Ed25519.Arm.Fn.keyPair v.umaal
      verified := Proof.Ed25519.Arm.Fn.keyPair v.umaal },
    Spec.Ed25519.signExpandedApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Ed25519.Arm.Fn.signExpanded v.umaal
      verified := Proof.Ed25519.Arm.Fn.signExpanded v.umaal },
    Spec.Ed25519.verifyApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Ed25519.Arm.Fn.verify v.umaal
      verified := Proof.Ed25519.Arm.Fn.verify v.umaal }]

spec_apis artifacts

end VG.Artifacts.Ed25519.Arm
