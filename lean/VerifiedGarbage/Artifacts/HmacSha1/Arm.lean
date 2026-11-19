module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-1 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha1InitRegArm,
  Spec.Hmac.sha1I.finalizeApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha1FinRegArm]

end VG.Artifacts.HmacSha1.Arm
