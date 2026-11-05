module

public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances

/-! # SHA-256 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha256.Arm

def artifacts : List Artifact := [
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
  Spec.Sha256.digest256Api.artifact Arm.target {
    code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha256H
    stack := 16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha256H
    verified := Proof.MdStream.Arm.Digest.sha256_digest }]

end VG.Artifacts.Sha256.Arm
