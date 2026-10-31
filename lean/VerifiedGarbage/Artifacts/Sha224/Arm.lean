module

public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-224 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha224.Arm

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact Arm.target {
    code := Impl.Sha256.Arm.Stream.init224
    verified := Proof.Sha256.Arm.Shared.init224 },
  Spec.Sha256.finalize224Api.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize224
    stack := 624
    verified := Proof.Sha256.Arm.Shared.finalize224 }]

end VG.Artifacts.Sha224.Arm
