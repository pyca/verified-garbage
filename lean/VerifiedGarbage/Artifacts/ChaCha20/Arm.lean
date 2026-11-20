module

public import VerifiedGarbage.Proof.ChaCha20.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # ChaCha20 (RFC 8439) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Fn.init
    verified := .scrubbed Proof.ChaCha20.Arm.Fn.init },
  Spec.ChaCha20.setNonceApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Fn.setNonce
    verified := .scrubbed Proof.ChaCha20.Arm.Fn.setNonce },
  Spec.ChaCha20.applyApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Fn.apply
    verified := .scrubbed Proof.ChaCha20.Arm.Fn.apply }]

end VG.Artifacts.ChaCha20.Arm
