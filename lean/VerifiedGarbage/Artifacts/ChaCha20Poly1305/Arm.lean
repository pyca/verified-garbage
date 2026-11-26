module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Verified
import VerifiedGarbage.Proof.Variants.Poly1305Blocks.Arm
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on ARMv7 -/

namespace VG.Artifacts.ChaCha20Poly1305.Arm

public def artifacts : List (Artifact Arm.target) :=
  Proof.Variants.Poly1305Blocks.Arm.variants.flatMap fun (v : Proof.Variants.Poly1305Blocks.Arm.Variant) => [
    Spec.ChaCha20Poly1305.sealApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.seal v.umaal
      verified := Proof.ChaCha20Poly1305.Arm.Fn.seal v.umaal },
    Spec.ChaCha20Poly1305.openZeroApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.open v.umaal
      verified := Proof.ChaCha20Poly1305.Arm.Fn.open v.umaal },
    Spec.ChaCha20Poly1305.openToApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.openTo v.umaal
      verified := Proof.ChaCha20Poly1305.Arm.Fn.openTo v.umaal },
    Spec.ChaCha20Poly1305.sealGatherApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.sealGather v.umaal
      verified := Proof.ChaCha20Poly1305.Arm.Fn.sealGather v.umaal }]

spec_apis artifacts

end VG.Artifacts.ChaCha20Poly1305.Arm
