module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Verified
public import VerifiedGarbage.Proof.Variants.Poly1305Blocks.Arm
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.Arm

def artifacts : List Artifact :=
  Proof.Variants.Poly1305Blocks.Arm.variants.flatMap fun (v : Proof.Variants.Poly1305Blocks.Arm.Variant) => [
    Spec.ChaCha20Poly1305.sealApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.seal v.umaal
      verified := .scrubbed (Proof.ChaCha20Poly1305.Arm.Fn.seal v.umaal) },
    Spec.ChaCha20Poly1305.openZeroApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.open v.umaal
      verified := .scrubbed (Proof.ChaCha20Poly1305.Arm.Fn.open v.umaal) },
    Spec.ChaCha20Poly1305.openToApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.openTo v.umaal
      verified := .scrubbed (Proof.ChaCha20Poly1305.Arm.Fn.openTo v.umaal) },
    Spec.ChaCha20Poly1305.sealGatherApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.Arm.Fn.sealGather v.umaal
      verified := .scrubbed (Proof.ChaCha20Poly1305.Arm.Fn.sealGather v.umaal) }]

end VG.Artifacts.ChaCha20Poly1305.Arm
