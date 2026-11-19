module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-MD5 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.Arm

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.md5InitRegArm,
  Spec.Hmac.md5I.finalizeApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.md5FinRegArm]

end VG.Artifacts.HmacMd5.Arm
