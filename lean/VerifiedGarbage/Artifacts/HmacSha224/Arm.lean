module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-224 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha224.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha224InitRegArm,
  Spec.Hmac.sha224I.finalizeApi.artifact Arm.target Proof.Hmac.Stream.Arm.Scrub.sha224FinRegArm]

end VG.Artifacts.HmacSha224.Arm
