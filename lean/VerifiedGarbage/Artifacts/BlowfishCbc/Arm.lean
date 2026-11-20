module

public import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Blowfish-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Blowfish.Arm.Fn.cbcEncryptChained },
  Spec.Blowfish.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Blowfish.Arm.Fn.cbcDecryptChained }]

end VG.Artifacts.BlowfishCbc.Arm
