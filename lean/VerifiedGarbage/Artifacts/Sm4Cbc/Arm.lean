module

public import VerifiedGarbage.Proof.Sm4.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.Arm

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Sm4.Arm.Fn.cbcEncryptChained },
  Spec.Sm4.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Sm4.Arm.Fn.cbcDecryptChained }]

end VG.Artifacts.Sm4Cbc.Arm
