module

public import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Target

/-! # Blowfish-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.Arm

def artifacts : List (Artifact Arm.target) := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cbcEncryptChained
    verified := Proof.Blowfish.Arm.Fn.cbcEncryptChained },
  Spec.Blowfish.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cbcDecryptChained
    verified := Proof.Blowfish.Arm.Fn.cbcDecryptChained }]

end VG.Artifacts.BlowfishCbc.Arm
