module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Memory
public import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Scratch

/-! # PBKDF2-HMAC-SHA-384 (RFC 8018) on ARMv7: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha384.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.pbkdf2Api.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha384I) 3
      Proof.Pbkdf2.Whole.Arm.sha384F.pbkdf2
    stack := 24 + Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Whole.Arm.pbkFramed Proof.Pbkdf2.Whole.Arm.sha384
      Proof.Pbkdf2.Whole.Arm.sha384_pbkFrameSat }]

end VG.Artifacts.Pbkdf2Sha384.Arm
