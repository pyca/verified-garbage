module

public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Streaming ChaCha20 (RFC 8439) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Stream.init
    verified := Proof.ChaCha20.Arm.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Stream.setNonce
    verified := Proof.ChaCha20.Arm.Stream.setNonce_verified },
  Spec.ChaCha20.applyApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Stream.apply
    verified := Proof.ChaCha20.Arm.Stream.apply_verified }]

end VG.Artifacts.ChaCha20.Arm
