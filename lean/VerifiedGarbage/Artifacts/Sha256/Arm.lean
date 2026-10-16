module

public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-256 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha256.Arm

def artifacts : List Artifact := [
  Spec.Sha256.compressApi.artifact Arm.target {
    code := Impl.Sha256.Arm.compress
    verified := Proof.Sha256.Arm.Shared.compress },
  Spec.Sha256.initApi.artifact Arm.target {
    code := Impl.Sha256.Arm.Stream.init
    verified := Proof.Sha256.Arm.Shared.init },
  Spec.Sha256.updateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 624 2 Impl.Sha256.Arm.Stream.update
    stack := 624
    verified := Proof.Sha256.Arm.Shared.update },
  Spec.Sha256.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize
    stack := 624
    verified := Proof.Sha256.Arm.Shared.finalize },
  Spec.Sha256.updateScratchApi.artifact Arm.target {
    code := Impl.Sha256.Arm.Stream.update
    verified := Proof.Sha256.Arm.Shared.updateScratch },
  Spec.Sha256.finalizeScratchApi.artifact Arm.target {
    code := Impl.Sha256.Arm.Stream.finalize
    verified := Proof.Sha256.Arm.Shared.finalizeScratch }]

end VG.Artifacts.Sha256.Arm
