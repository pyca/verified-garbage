module

public import VerifiedGarbage.Proof.Poly1305.Arm.Init
public import VerifiedGarbage.Proof.Poly1305.Arm.Scrub
public import VerifiedGarbage.Proof.Variants.Poly1305Blocks.Arm
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.TCB.Registration

/-! # Poly1305 (RFC 8439 §2.5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Poly1305.Arm

def artifacts : List Artifact :=
  [Spec.Poly1305.initApi.artifact Arm.target {
    code := Impl.Poly1305.Arm.init
    verified := .unscrubbed Proof.Poly1305.Arm.init_verified }] ++
  (Proof.Variants.Poly1305Blocks.Arm.variants.flatMap fun (v : Proof.Variants.Poly1305Blocks.Arm.Variant) => [
    Spec.Poly1305.updateApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Poly1305.Arm.Fn.update v.umaal
      verified := .scrubbed (Proof.Poly1305.Arm.Fn.update v.umaal) },
    Spec.Poly1305.finalizeApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Poly1305.Arm.Fn.finalize v.umaal
      verified := .scrubbed (Proof.Poly1305.Arm.Fn.finalize v.umaal) }])

end VG.Artifacts.Poly1305.Arm
