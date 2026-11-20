module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-256 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha256InitRegArm,
  Spec.Hmac.sha256I.finalizeApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha256FinRegArm]

end VG.Artifacts.HmacSha256.Arm
