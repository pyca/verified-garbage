module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-256 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha256.Arm

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact Arm.target {
    code := Impl.Sha256.Arm.Fn.init224
    verified := Proof.Sha256.Arm.Fn.init224 },
  Spec.Sha256.finalize224Api.artifact Arm.target {
    code := Impl.Sha256.Arm.Fn.finalize224
    verified := Proof.Sha256.Arm.Fn.finalize224 },
  Spec.Sha256.digest224Api.artifact Arm.target {
    code := Impl.Sha256.Arm.Fn.digest224
    verified := Proof.Sha256.Arm.Fn.digest224 },
  Spec.Sha256.initApi.artifact Arm.target {
    code := Impl.Sha256.Arm.Fn.init
    verified := Proof.Sha256.Arm.Fn.init },
  Spec.Sha256.updateApi.artifact Arm.target {
    code := Impl.Sha256.Arm.Fn.update
    verified := Proof.Sha256.Arm.Fn.update },
  Spec.Sha256.finalizeApi.artifact Arm.target {
    code := Impl.Sha256.Arm.Fn.finalize
    verified := Proof.Sha256.Arm.Fn.finalize },
  Spec.Sha256.digest256Api.artifact Arm.target {
    code := Impl.Sha256.Arm.Fn.digest
    verified := Proof.Sha256.Arm.Fn.digest }]

end VG.Artifacts.Sha256.Arm
