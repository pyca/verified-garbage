module

public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
public import VerifiedGarbage.TCB.Arm.Print

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
    verified := Proof.Sha256.Arm.Shared.finalize224 },
  Spec.Sha256.digest224Api.artifact Arm.target {
    code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha224H
    stack := 16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha224H
    verified := Proof.MdStream.Arm.Digest.sha224_digest }]

end VG.Artifacts.Sha224.Arm
