module

public import VerifiedGarbage.Proof.Scrypt.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Target

/-! # scrypt (RFC 7914) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.Arm

def artifacts : List (Artifact Arm.target) := [
  Spec.Scrypt.scryptApi.artifact Arm.target {
    code := Impl.Scrypt.Arm.Fn.scrypt
    verified := Proof.Scrypt.Arm.Fn.scrypt }]

end VG.Artifacts.Scrypt.Arm
