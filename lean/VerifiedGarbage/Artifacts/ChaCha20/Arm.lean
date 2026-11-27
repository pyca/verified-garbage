module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20 (RFC 8439) on ARMv7 -/

namespace VG.Artifacts.ChaCha20.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.ChaCha20.initApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Fn.init
    verified := Proof.ChaCha20.Arm.Fn.init },
  Spec.ChaCha20.setNonceApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Fn.setNonce
    verified := Proof.ChaCha20.Arm.Fn.setNonce },
  Spec.ChaCha20.applyApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Fn.apply
    verified := Proof.ChaCha20.Arm.Fn.apply }]

spec_apis artifacts

end VG.Artifacts.ChaCha20.Arm
