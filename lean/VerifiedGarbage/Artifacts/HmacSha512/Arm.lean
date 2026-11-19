module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-512 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.initAnyKeyApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha512InitRegArm,
  Spec.Hmac.sha512I.finalizeApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha512FinRegArm]

end VG.Artifacts.HmacSha512.Arm
