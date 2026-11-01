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

/-! # PBKDF2-HMAC-SHA-512/256 (RFC 8018) on ARMv7: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.pbkdf2Api.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha512_256I) 3
      Proof.Pbkdf2.Whole.Arm.sha512_256F.pbkdf2
    stack := 24 + Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Whole.Arm.pbkFramed Proof.Pbkdf2.Whole.Arm.sha512_256
      Proof.Pbkdf2.Whole.Arm.sha512_256_pbkFrameSat }]

end VG.Artifacts.Pbkdf2Sha512_256.Arm
