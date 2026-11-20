module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-384 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha384InitRegArm,
  Spec.Hmac.sha384I.finalizeApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha384FinRegArm]

end VG.Artifacts.HmacSha384.Arm
