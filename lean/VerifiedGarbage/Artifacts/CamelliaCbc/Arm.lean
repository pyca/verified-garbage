module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.Arm

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cbcEncrypt
    verified := .scrubbed Proof.Camellia.Arm.Fn.cbcEncrypt },
  Spec.Camellia.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cbcDecrypt
    verified := .scrubbed Proof.Camellia.Arm.Fn.cbcDecrypt }]

end VG.Artifacts.CamelliaCbc.Arm
