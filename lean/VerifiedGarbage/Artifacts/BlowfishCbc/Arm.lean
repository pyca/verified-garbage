module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cbc
import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CBC on ARMv7 -/

namespace VG.Artifacts.BlowfishCbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cbcEncryptChained
    verified := Proof.Blowfish.Arm.Fn.cbcEncryptChained },
  Spec.Blowfish.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cbcDecryptChained
    verified := Proof.Blowfish.Arm.Fn.cbcDecryptChained }]

spec_apis artifacts

end VG.Artifacts.BlowfishCbc.Arm
